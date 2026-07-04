{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.assembler;

interface

uses
  SysUtils, Classes, Process, blaise.testing,
  blaise.elfwriter, blaise.assembler.x86_64;

type
  { ---- Instruction/directive encoding regression tests ----
    Byte-level assertions against AssembleToBytes output.  Expected
    encodings cross-checked against GNU as. }
  TAsmEncodingTests = class(TTestCase)
  private
    function ContainsBytes(const ABuf, APat: string): Boolean;
  published
    procedure TestBareMemOperand_StoreViaReg;
    procedure TestBareMemOperand_LoadViaReg;
    procedure TestQuadSymbol_EmitsReloc;
    procedure TestTLSPrefix_PrecedesRex;
    procedure TestRipRelImmStore_AddendMinus8;
    procedure TestBranchUndefined_EmitsReloc;
    procedure TestNoteGnuStack_Present;
    procedure TestUnknownDirective_Raises;
    procedure TestDuplicateLabel_Raises;
    procedure TestRexX_ExtendedIndexImmStore;
    procedure TestMovwImm16_TwoByteImmediate;
    procedure TestErrorMessage_HasLineNumber;
    procedure TestMovqXmmToReg_SseEncoding;
    procedure TestMovqRegToXmm_SseEncoding;
  end;

  { ---- ELF writer unit tests ---- }
  TElfWriterTests = class(TTestCase)
  private
    function ReadU8(const ABuf: string; AOff: Integer): Integer;
    function ReadU16(const ABuf: string; AOff: Integer): Integer;
  published
    procedure TestElfHeader_Magic;
    procedure TestElfHeader_Class64;
    procedure TestElfHeader_DataLSB;
    procedure TestElfHeader_TypeREL;
    procedure TestElfHeader_MachineX86_64;
    procedure TestAppend_TextSection;
    procedure TestAppend_DataSection;
    procedure TestCurrentOffset_Tracks;
    procedure TestDefineSymbol_FindsIt;
    procedure TestExternSymbol_FindsIt;
    procedure TestAlignSection_Pads;
    procedure TestAppendByte_SingleByte;
    procedure TestAppendDWord_FourBytes;
    procedure TestAppendQWord_EightBytes;
    procedure TestReserveBss_NoData;
  end;

  { ---- Internal assembler E2E tests ----
    Invoke the compiler CLI with --backend native --assembler internal,
    then link and run.  This exercises the full pipeline:
    source -> parse -> semantic -> native codegen -> internal assembler
    -> ELF object -> linker -> run. }
  TInternalAsmE2ETests = class(TTestCase)
  private
    FCompiler: string;
    FRTLPath: string;
    FStdlibPath: string;
    FRTL: string;
    FScratch: string;
    FCounter: Integer;
    function ProjectRoot: string;
    function CompilerAvailable: Boolean;
    function RunProc(const AExe: string; const AArgs: array of string;
      out AStdout: string): Integer;
    function RunProcNoArgs(const AExe: string; out AStdout: string): Integer;
    function CompileAndRun(const ASrc: string;
      out AStdout: string; out AExitCode: Integer): Boolean;
  protected
    procedure SetUp; override;
  published
    procedure TestSimpleAdd;
    procedure TestStringOutput;
    procedure TestForLoop;
    procedure TestFunctionCall;
    procedure TestIfElse;
    procedure TestWhileLoop;
    procedure TestBooleanExpr;
    procedure TestNegativeNumbers;
    procedure TestMultipleVars;
    procedure TestNestedCalls;
    procedure TestClassVirtualCall;
    procedure TestFloatArithmetic;
    procedure TestFormatFloatArg;
  end;

implementation

{ Print the "tests skipped" note at most once per suite run, so a CI
  environment that lacks the QBE compiler binary surfaces the skip loudly
  instead of silently reporting green with ~12 ignored tests. }
var
  GInternalAsmSkipNoted: Boolean = False;

{ ---- TAsmEncodingTests ---- }

function TAsmEncodingTests.ContainsBytes(const ABuf, APat: string): Boolean;
begin
  Result := Pos(APat, ABuf) >= 0;
end;

procedure TAsmEncodingTests.TestBareMemOperand_StoreViaReg;
var
  Obj: string;
begin
  { movq %rcx, (%rax) -> 48 89 08.  Emitted constantly by the native
    backend (vtable install, pointer stores); previously unparseable. }
  Obj := AssembleToBytes('movq %rcx, (%rax)' + LineEnding);
  AssertTrue('48 89 08 missing',
    ContainsBytes(Obj, Chr($48) + Chr($89) + Chr($08)));
end;

procedure TAsmEncodingTests.TestBareMemOperand_LoadViaReg;
var
  Obj: string;
begin
  { movq (%rdi), %rax -> 48 8B 07 }
  Obj := AssembleToBytes('movq (%rdi), %rax' + LineEnding);
  AssertTrue('48 8B 07 missing',
    ContainsBytes(Obj, Chr($48) + Chr($8B) + Chr($07)));
end;

procedure TAsmEncodingTests.TestQuadSymbol_EmitsReloc;
var
  Obj: string;
begin
  { .quad <symbol> must produce a .rela.data entry against the symbol,
    not silently emit zero (null vtables). }
  Obj := AssembleToBytes('.data' + LineEnding +
    'vt:' + LineEnding +
    '.quad some_external_method' + LineEnding);
  AssertTrue('.rela.data missing', ContainsBytes(Obj, '.rela.data'));
  AssertTrue('symbol name missing',
    ContainsBytes(Obj, 'some_external_method'));
end;

procedure TAsmEncodingTests.TestTLSPrefix_PrecedesRex;
var
  Obj: string;
begin
  { movq %fs:tv@tpoff, %rax -> 64 48 8B 04 25 ... — the FS segment
    override must precede REX, not follow it. }
  Obj := AssembleToBytes('movq %fs:tv@tpoff, %rax' + LineEnding);
  AssertTrue('64 48 8B prefix order wrong',
    ContainsBytes(Obj, Chr($64) + Chr($48) + Chr($8B) + Chr($04) + Chr($25)));
end;

procedure TAsmEncodingTests.TestRipRelImmStore_AddendMinus8;
var
  Obj: string;
  Pat: string;
begin
  { movq $0, gv(%rip): the PC32 addend must be -8 (disp field is 8
    bytes from instruction end: 4 disp + 4 imm), not -4. }
  Obj := AssembleToBytes('movq $0, gv(%rip)' + LineEnding);
  Pat := Chr($F8) + Chr($FF) + Chr($FF) + Chr($FF)
       + Chr($FF) + Chr($FF) + Chr($FF) + Chr($FF);
  AssertTrue('rela addend -8 missing', ContainsBytes(Obj, Pat));
end;

procedure TAsmEncodingTests.TestBranchUndefined_EmitsReloc;
var
  Obj: string;
begin
  { jmp to an external symbol must emit a relocation, not silently
    encode displacement 0 (a jump to the next instruction). }
  Obj := AssembleToBytes('jmp external_target' + LineEnding);
  AssertTrue('.rela.text missing', ContainsBytes(Obj, '.rela.text'));
  AssertTrue('target symbol missing', ContainsBytes(Obj, 'external_target'));
end;

procedure TAsmEncodingTests.TestNoteGnuStack_Present;
var
  Obj: string;
begin
  Obj := AssembleToBytes('ret' + LineEnding);
  AssertTrue('.note.GNU-stack section missing',
    ContainsBytes(Obj, '.note.GNU-stack'));
end;

procedure TAsmEncodingTests.TestUnknownDirective_Raises;
var
  Raised: Boolean;
begin
  Raised := False;
  try
    AssembleToBytes('.bogus 42' + LineEnding);
  except
    on E: EAssembler do
      Raised := True;
  end;
  AssertTrue('unknown directive must raise EAssembler', Raised);
end;

procedure TAsmEncodingTests.TestDuplicateLabel_Raises;
var
  Raised: Boolean;
begin
  Raised := False;
  try
    AssembleToBytes('dup:' + LineEnding + 'ret' + LineEnding +
      'dup:' + LineEnding + 'ret' + LineEnding);
  except
    on E: EAssembler do
      Raised := True;
  end;
  AssertTrue('duplicate label must raise EAssembler', Raised);
end;

procedure TAsmEncodingTests.TestRexX_ExtendedIndexImmStore;
var
  Obj: string;
begin
  { movq $5, (%rax,%r9,8) -> 4A C7 04 C8 05 00 00 00.
    REX.X must be set for the r9 index register. }
  Obj := AssembleToBytes('movq $5, (%rax,%r9,8)' + LineEnding);
  AssertTrue('4A C7 04 C8 missing (REX.X dropped)',
    ContainsBytes(Obj, Chr($4A) + Chr($C7) + Chr($04) + Chr($C8) + Chr($05)));
end;

procedure TAsmEncodingTests.TestMovwImm16_TwoByteImmediate;
var
  Obj: string;
begin
  { movw $258, %ax -> 66 C7 C0 02 01 — a 16-bit immediate, not 32-bit. }
  Obj := AssembleToBytes('movw $258, %ax' + LineEnding + 'ret' + LineEnding);
  AssertTrue('66 C7 C0 02 01 C3 missing (imm16 wrong size)',
    ContainsBytes(Obj, Chr($66) + Chr($C7) + Chr($C0) + Chr($02) + Chr($01)
      + Chr($C3)));
end;

procedure TAsmEncodingTests.TestErrorMessage_HasLineNumber;
var
  Msg: string;
begin
  Msg := '';
  try
    AssembleToBytes('ret' + LineEnding + '.bogus 1' + LineEnding);
  except
    on E: EAssembler do
      Msg := Exception(E).Message;
  end;
  AssertTrue('error must mention line 2, got: ' + Msg,
    Pos('line 2', Msg) >= 0);
end;

procedure TAsmEncodingTests.TestMovqXmmToReg_SseEncoding;
var
  Obj: string;
begin
  { movq %xmm0, %rax -> 66 48 0F 7E C0 (SSE MOVQ store-from-xmm).  This was
    mis-encoded as the integer `mov %rax,%rax` (48 89 C0), silently dropping the
    xmm value — the cause of float Format() args arriving as garbage.  (issue
    #133 follow-up regression.) }
  Obj := AssembleToBytes('movq %xmm0, %rax' + LineEnding);
  AssertTrue('66 48 0F 7E C0 missing',
    ContainsBytes(Obj, Chr($66) + Chr($48) + Chr($0F) + Chr($7E) + Chr($C0)));
  AssertFalse('must NOT encode as integer mov %rax,%rax (48 89 C0)',
    ContainsBytes(Obj, Chr($48) + Chr($89) + Chr($C0)));
end;

procedure TAsmEncodingTests.TestMovqRegToXmm_SseEncoding;
var
  Obj: string;
begin
  { movq %rax, %xmm0 -> 66 48 0F 6E C0 (SSE MOVQ load-into-xmm). }
  Obj := AssembleToBytes('movq %rax, %xmm0' + LineEnding);
  AssertTrue('66 48 0F 6E C0 missing',
    ContainsBytes(Obj, Chr($66) + Chr($48) + Chr($0F) + Chr($6E) + Chr($C0)));
end;

{ ---- ELF reader helpers ---- }

function TElfWriterTests.ReadU8(const ABuf: string; AOff: Integer): Integer;
begin
  Result := Ord(ABuf[AOff]) and $FF;
end;

function TElfWriterTests.ReadU16(const ABuf: string; AOff: Integer): Integer;
begin
  Result := (Ord(ABuf[AOff]) and $FF)
         or ((Ord(ABuf[AOff + 1]) and $FF) shl 8);
end;

{ ---- TElfWriterTests ---- }

procedure TElfWriterTests.TestElfHeader_Magic;
var
  W: TElfObjectWriter;
  Buf: string;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendByte(eskText, $90);
    Buf := W.Finish();
    AssertEquals($7F, ReadU8(Buf, 0));
    AssertEquals(Ord('E'), ReadU8(Buf, 1));
    AssertEquals(Ord('L'), ReadU8(Buf, 2));
    AssertEquals(Ord('F'), ReadU8(Buf, 3));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestElfHeader_Class64;
var
  W: TElfObjectWriter;
  Buf: string;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendByte(eskText, $90);
    Buf := W.Finish();
    AssertEquals(2, ReadU8(Buf, 4));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestElfHeader_DataLSB;
var
  W: TElfObjectWriter;
  Buf: string;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendByte(eskText, $90);
    Buf := W.Finish();
    AssertEquals(1, ReadU8(Buf, 5));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestElfHeader_TypeREL;
var
  W: TElfObjectWriter;
  Buf: string;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendByte(eskText, $90);
    Buf := W.Finish();
    AssertEquals(1, ReadU16(Buf, 16));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestElfHeader_MachineX86_64;
var
  W: TElfObjectWriter;
  Buf: string;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendByte(eskText, $90);
    Buf := W.Finish();
    AssertEquals(62, ReadU16(Buf, 18));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestAppend_TextSection;
var
  W: TElfObjectWriter;
  Off: Integer;
begin
  W := TElfObjectWriter.Create();
  try
    Off := W.Append(eskText, Chr($55) + Chr($48));
    AssertEquals(0, Off);
    AssertEquals(2, W.CurrentOffset(eskText));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestAppend_DataSection;
var
  W: TElfObjectWriter;
  Off: Integer;
begin
  W := TElfObjectWriter.Create();
  try
    Off := W.Append(eskData, Chr($01) + Chr($02) + Chr($03));
    AssertEquals(0, Off);
    AssertEquals(3, W.CurrentOffset(eskData));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestCurrentOffset_Tracks;
var
  W: TElfObjectWriter;
begin
  W := TElfObjectWriter.Create();
  try
    AssertEquals(0, W.CurrentOffset(eskText));
    W.AppendByte(eskText, $90);
    AssertEquals(1, W.CurrentOffset(eskText));
    W.AppendByte(eskText, $90);
    AssertEquals(2, W.CurrentOffset(eskText));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestDefineSymbol_FindsIt;
var
  W: TElfObjectWriter;
  Idx: Integer;
begin
  W := TElfObjectWriter.Create();
  try
    Idx := W.DefineSymbol('main', eskText, 0, 0, esbGlobal, estFunc);
    AssertTrue(Idx >= 0);
    AssertEquals(Idx, W.FindSymbol('main'));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestExternSymbol_FindsIt;
var
  W: TElfObjectWriter;
  Idx: Integer;
begin
  W := TElfObjectWriter.Create();
  try
    Idx := W.ExternSymbol('_SysWriteStr');
    AssertTrue(Idx >= 0);
    AssertEquals(Idx, W.FindSymbol('_SysWriteStr'));
    AssertEquals(-1, W.FindSymbol('nonexistent'));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestAlignSection_Pads;
var
  W: TElfObjectWriter;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendByte(eskData, $01);
    W.AppendByte(eskData, $02);
    AssertEquals(2, W.CurrentOffset(eskData));
    W.AppendByte(eskData, 0);
    W.AppendByte(eskData, 0);
    AssertEquals(4, W.CurrentOffset(eskData));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestAppendByte_SingleByte;
var
  W: TElfObjectWriter;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendByte(eskText, $CC);
    AssertEquals(1, W.CurrentOffset(eskText));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestAppendDWord_FourBytes;
var
  W: TElfObjectWriter;
  Buf: string;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendByte(eskText, $78);
    W.AppendByte(eskText, $56);
    W.AppendByte(eskText, $34);
    W.AppendByte(eskText, $12);
    AssertEquals(4, W.CurrentOffset(eskText));
    Buf := W.Finish();
    AssertEquals($78, ReadU8(Buf, 64));
    AssertEquals($56, ReadU8(Buf, 65));
    AssertEquals($34, ReadU8(Buf, 66));
    AssertEquals($12, ReadU8(Buf, 67));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestAppendQWord_EightBytes;
var
  W: TElfObjectWriter;
begin
  W := TElfObjectWriter.Create();
  try
    W.AppendByte(eskText, $08);
    W.AppendByte(eskText, $07);
    W.AppendByte(eskText, $06);
    W.AppendByte(eskText, $05);
    W.AppendByte(eskText, $04);
    W.AppendByte(eskText, $03);
    W.AppendByte(eskText, $02);
    W.AppendByte(eskText, $01);
    AssertEquals(8, W.CurrentOffset(eskText));
  finally
    W.Free();
  end;
end;

procedure TElfWriterTests.TestReserveBss_NoData;
var
  W: TElfObjectWriter;
begin
  W := TElfObjectWriter.Create();
  try
    W.ReserveBss(eskBss, 256);
    AssertEquals(256, W.CurrentOffset(eskBss));
  finally
    W.Free();
  end;
end;

{ ---- TInternalAsmE2ETests ---- }

function TInternalAsmE2ETests.ProjectRoot: string;
var
  Dir, Parent: string;
  Steps: Integer;
begin
  Result := GetEnvironmentVariable('BLAISE_PROJECT_ROOT');
  if Result <> '' then
  begin
    Result := IncludeTrailingPathDelimiter(Result);
    Exit;
  end;
  Dir := GetCurrentDir();
  for Steps := 0 to 5 do
  begin
    if DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'vendor/qbe') and
       DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'runtime') then
    begin
      Result := IncludeTrailingPathDelimiter(Dir);
      Exit;
    end;
    Parent := ExtractFileDir(Dir);
    if (Parent = '') or (Parent = Dir) then Break;
    Dir := Parent;
  end;
  Result := IncludeTrailingPathDelimiter(GetCurrentDir());
end;

procedure TInternalAsmE2ETests.SetUp;
begin
  inherited SetUp();
  FCompiler := GetEnvironmentVariable('BLAISE_QBE_COMPILER');
  if FCompiler = '' then
    FCompiler := '/tmp/fp_blaise2';
  if not FileExists(FCompiler) then
    FCompiler := '/tmp/fp_blaise3';
  FRTLPath := ProjectRoot() + 'runtime/src/main/pascal';
  FStdlibPath := ProjectRoot() + 'stdlib/src/main/pascal';
  FRTL := ProjectRoot() + 'compiler/target/blaise_rtl.a';
  FScratch := ProjectRoot() + 'compiler/target/asm_scratch/';
  ForceDirectories(FScratch);
  FCounter := 0;
end;

function TInternalAsmE2ETests.CompilerAvailable: Boolean;
begin
  Result := FileExists(FCompiler) and FileExists(FRTL);
  if (not Result) and (not GInternalAsmSkipNoted) then
  begin
    GInternalAsmSkipNoted := True;
    WriteLn(StdErr, 'note: TInternalAsmE2ETests skipped — compiler binary "',
            FCompiler, '" or RTL "', FRTL, '" not found ',
            '(set BLAISE_QBE_COMPILER to a QBE-backend blaise binary to run them)');
  end;
end;

function TInternalAsmE2ETests.RunProc(const AExe: string;
  const AArgs: array of string; out AStdout: string): Integer;
var
  Proc: TProcess;
  I: Integer;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    for I := 0 to High(AArgs) do
      Proc.Parameters.Add(AArgs[I]);
    Proc.Execute();
    AStdout := '';
    repeat
      Chunk := Proc.ReadOutput();
      AStdout := AStdout + Chunk;
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode;
  finally
    Proc.Free();
  end;
end;

function TInternalAsmE2ETests.RunProcNoArgs(const AExe: string;
  out AStdout: string): Integer;
var
  Proc: TProcess;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    Proc.Execute();
    AStdout := '';
    repeat
      Chunk := Proc.ReadOutput();
      AStdout := AStdout + Chunk;
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode;
  finally
    Proc.Free();
  end;
end;

function TInternalAsmE2ETests.CompileAndRun(const ASrc: string;
  out AStdout: string; out AExitCode: Integer): Boolean;
var
  SrcFile, OutFile, CompOut: string;
  Rc: Integer;
begin
  Result := False;
  if not Self.CompilerAvailable() then Exit;

  FCounter := FCounter + 1;
  SrcFile := FScratch + 'test_asm_' + IntToStr(FCounter) + '.pas';
  OutFile := FScratch + 'test_asm_' + IntToStr(FCounter);

  WriteFile(SrcFile, ASrc);

  Rc := Self.RunProc(FCompiler, [
    '--source', SrcFile,
    '--unit-path', FRTLPath,
    '--unit-path', FStdlibPath,
    '--output', OutFile,
    '--backend', 'native',
    '--assembler', 'internal'
  ], CompOut);
  if Rc <> 0 then
    { A compile failure is a real test failure, not a missing toolchain —
      Fail here so it cannot be masked as Ignore by the caller. }
    Fail('compile failed (rc=' + IntToStr(Rc) + '): ' + CompOut);

  AExitCode := Self.RunProcNoArgs(OutFile, AStdout);
  Result := True;
end;

{ ---- Test methods ---- }

procedure TInternalAsmE2ETests.TestSimpleAdd;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_add;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(3 + 4)' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('7' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestStringOutput;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_str;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(''Hello from internal assembler'')' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('Hello from internal assembler' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestForLoop;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_for;' + LineEnding +
    'var I: Integer;' + LineEnding +
    'begin' + LineEnding +
    '  for I := 1 to 5 do' + LineEnding +
    '    Write(I);' + LineEnding +
    '  WriteLn' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('12345' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestFunctionCall;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_func;' + LineEnding +
    'function Add(A, B: Integer): Integer;' + LineEnding +
    'begin' + LineEnding +
    '  Result := A + B' + LineEnding +
    'end;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(Add(10, 32))' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('42' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestIfElse;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_if;' + LineEnding +
    'var X: Integer;' + LineEnding +
    'begin' + LineEnding +
    '  X := 5;' + LineEnding +
    '  if X > 3 then' + LineEnding +
    '    WriteLn(''yes'')' + LineEnding +
    '  else' + LineEnding +
    '    WriteLn(''no'')' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('yes' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestWhileLoop;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_while;' + LineEnding +
    'var N: Integer;' + LineEnding +
    'begin' + LineEnding +
    '  N := 1;' + LineEnding +
    '  while N <= 3 do' + LineEnding +
    '  begin' + LineEnding +
    '    Write(N);' + LineEnding +
    '    N := N + 1' + LineEnding +
    '  end;' + LineEnding +
    '  WriteLn' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('123' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestBooleanExpr;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_bool;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(True);' + LineEnding +
    '  WriteLn(False);' + LineEnding +
    '  WriteLn(3 = 3);' + LineEnding +
    '  WriteLn(3 <> 4)' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('True' + LineEnding + 'False' + LineEnding +
               'True' + LineEnding + 'True' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestNegativeNumbers;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_neg;' + LineEnding +
    'var X: Integer;' + LineEnding +
    'begin' + LineEnding +
    '  X := -42;' + LineEnding +
    '  WriteLn(X)' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('-42' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestMultipleVars;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_vars;' + LineEnding +
    'var A, B, C: Integer;' + LineEnding +
    'begin' + LineEnding +
    '  A := 10;' + LineEnding +
    '  B := 20;' + LineEnding +
    '  C := A + B;' + LineEnding +
    '  WriteLn(C)' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('30' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestNestedCalls;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_nested;' + LineEnding +
    'function Twice(X: Integer): Integer;' + LineEnding +
    'begin' + LineEnding +
    '  Result := X * 2' + LineEnding +
    'end;' + LineEnding +
    'function AddOne(X: Integer): Integer;' + LineEnding +
    'begin' + LineEnding +
    '  Result := X + 1' + LineEnding +
    'end;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(AddOne(Twice(5)))' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('11' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestClassVirtualCall;
var
  Out_: string;
  EC: Integer;
begin
  { Exercises .quad <symbol> vtable entries and bare (%reg) stores —
    both previously broken in the internal assembler. }
  if not CompileAndRun(
    'program test_class;' + LineEnding +
    'type' + LineEnding +
    '  TGreeter = class' + LineEnding +
    '    function Greet: string; virtual;' + LineEnding +
    '  end;' + LineEnding +
    'function TGreeter.Greet: string;' + LineEnding +
    'begin' + LineEnding +
    '  Result := ''hello''' + LineEnding +
    'end;' + LineEnding +
    'var G: TGreeter;' + LineEnding +
    'begin' + LineEnding +
    '  G := TGreeter.Create;' + LineEnding +
    '  WriteLn(G.Greet());' + LineEnding +
    '  G.Free' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('hello' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestFloatArithmetic;
var
  Out_: string;
  EC: Integer;
begin
  { Exercises SSE loads/stores with bare (%reg) operands (float
    spills) — previously unparseable in the internal assembler. }
  if not CompileAndRun(
    'program test_float;' + LineEnding +
    'var A, B: Double;' + LineEnding +
    'begin' + LineEnding +
    '  A := 1.5;' + LineEnding +
    '  B := A * 2.0;' + LineEnding +
    '  if B = 3.0 then' + LineEnding +
    '    WriteLn(''ok'')' + LineEnding +
    '  else' + LineEnding +
    '    WriteLn(''bad'')' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('ok' + LineEnding, Out_);
end;

procedure TInternalAsmE2ETests.TestFormatFloatArg;
var
  Out_: string;
  EC: Integer;
begin
  { A float argument to Format() is boxed into the array-of-const via
    `movq %xmm0, %rax` (raw IEEE-754 bits).  The internal assembler used to
    mis-encode that as `mov %rax,%rax`, so the value was dropped and the float
    printed as 0.0000.  This is the end-to-end guard for that fix; the e2e test
    harness assembles native via cc, so only the internal-assembler suite
    exercises this path.  (issue #133 follow-up regression.) }
  if not CompileAndRun(
    'program test_fmtfloat;' + LineEnding +
    'uses sysutils;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(Format(''%.4f'', [1.25]))' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals(0, EC);
  AssertEquals('1.2500' + LineEnding, Out_);
end;

{ ---- Registration ---- }

initialization
  RegisterTest(TAsmEncodingTests);
  RegisterTest(TElfWriterTests);
  RegisterTest(TInternalAsmE2ETests);

end.
