{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.cli;

{ CLI-level end-to-end tests for the compiler driver front-end.

  These shell out to the compiler binary and assert on stdout/stderr and
  exit codes.  They cover behaviour the IR-only / unit harness cannot see:

    * FPC-style CLI removal (Step 0): the old -iV/-iTP/-iTO info probe and
      single-dash FPC flags are gone; the binary is double-dash-only now.

    * Driver option contract surfacing (Steps 2-5): --assembler value
      validation, wrong-backend rejection, and that ValidateOptions fires
      even in stdout-only modes (--emit-ir).  These prove the
      drain -> ValidateOptions -> error -> exit-1 wiring in Blaise.pas,
      which is not unit-testable (ParseArgs is a non-exported program
      local). }

interface

uses
  SysUtils, Classes, Process, blaise.testing;

type
  { Invokes the compiler binary directly and inspects the CLI contract. }
  TCLIContractTests = class(TTestCase)
  private
    FCompiler: string;
    FRTLPath: string;
    FStdlibPath: string;
    FRTL: string;
    FScratch: string;
    FCounter: Integer;
    function ProjectRoot: string;
    function CompilerAvailable: Boolean;
    { Run the compiler with the given args; capture combined stdout+stderr. }
    function RunCompiler(const AArgs: array of string;
      out ACombined: string): Integer;
    function WriteScratchSource(const ASrc: string): string;
    { Run a produced binary, capturing stdout/stderr; returns its exit code. }
    function RunBinary(const AExe: string; out ACombined: string): Integer;
    { Compile ASrc with the given backend (empty = default QBE), link against
      the full RTL, run it, and report stdout + exit code.  Used for features
      that need stdlib units loaded + linked, which the in-process e2e harness
      cannot do. }
    function CompileRunFull(const ASrc, ABackend: string;
      out AStdout: string; out AExitCode: Integer): Boolean;
  protected
    procedure SetUp; override;
  published
    { ---- Step 0: FPC CLI removal ---- }
    procedure TestHelpStillWorks;
    procedure TestNormalCompileStillWorks;
    procedure TestFPCVersionProbeGone;
    { ---- Steps 2-5: driver option contract surfacing through the CLI ----
      These prove the drain -> ValidateOptions -> error -> exit-1 wiring in
      Blaise.pas, which is not unit-testable (ParseArgs is a non-exported
      program local). }
    procedure TestAssemblerInternalAccepted;
    procedure TestAssemblerBogusRejected;          { ValidateOptions surfaces }
    procedure TestWrongBackendAssemblerRejected;   { addendum 2: qbe + --assembler }
    procedure TestEmitIrStillValidatesAssembler;   { addendum 1: validate runs in stdout mode }
    procedure TestAssemblerLineInHelp;             { DescribeOptions drives --help }
    { ---- emit-mode must match the explicitly chosen backend ----
      --emit-ir is a QBE-only output mode; --emit-asm is native-only.  When
      the user explicitly selects a backend that cannot produce that output,
      the driver must error instead of silently switching backends. }
    procedure TestEmitIr_WithExplicitNativeBackend_Rejected;
    procedure TestEmitAsm_WithExplicitQbeBackend_Rejected;
    procedure TestEmitIr_WithoutBackend_StillWorks;
    procedure TestEmitIr_WithExplicitQbeBackend_StillWorks;
    { ---- div/mod by zero raises a catchable EDivByZero (needs stdlib) ---- }
    procedure TestDivByZeroCaught_QBE;
    procedure TestDivByZeroCaught_Native;
    procedure TestModByZeroCaught_QBE;
    procedure TestModByZeroCaught_Native;
  end;

implementation

{ Print the "tests skipped" note at most once per suite run, so a CI
  environment that lacks the QBE compiler binary surfaces the skip loudly
  instead of silently reporting green with ~12 ignored tests. }
var
  GCLISkipNoted: Boolean = False;

{ ---- helpers ---- }

function TCLIContractTests.ProjectRoot: string;
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

procedure TCLIContractTests.SetUp;
begin
  inherited SetUp();
  FCompiler := GetEnvironmentVariable('BLAISE_QBE_COMPILER');
  if FCompiler = '' then
    FCompiler := '/tmp/fp_blaise3';
  if not FileExists(FCompiler) then
    FCompiler := '/tmp/fp_blaise2';
  FRTLPath := ProjectRoot() + 'runtime/src/main/pascal';
  FStdlibPath := ProjectRoot() + 'stdlib/src/main/pascal';
  FRTL := ProjectRoot() + 'compiler/target/blaise_rtl.a';
  FScratch := ProjectRoot() + 'compiler/target/cli_scratch/';
  ForceDirectories(FScratch);
  FCounter := 0;
end;

function TCLIContractTests.CompilerAvailable: Boolean;
begin
  Result := FileExists(FCompiler) and FileExists(FRTL);
  if (not Result) and (not GCLISkipNoted) then
  begin
    GCLISkipNoted := True;
    WriteLn(StdErr, 'note: TCLIContractTests skipped — compiler binary "',
            FCompiler, '" or RTL "', FRTL, '" not found ',
            '(set BLAISE_QBE_COMPILER to a QBE-backend blaise binary to run them)');
  end;
end;

function TCLIContractTests.RunCompiler(const AArgs: array of string;
  out ACombined: string): Integer;
var
  Proc: TProcess;
  I: Integer;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := FCompiler;
    for I := 0 to High(AArgs) do
      Proc.Parameters.Add(AArgs[I]);
    { The posix process shim already redirects the child's stderr into the
      same pipe as stdout (dup2(pipe,2) in rtl.platform.posix), so a
      diagnostic printed to StdErr is visible in ReadOutput below. }
    Proc.Execute();
    ACombined := '';
    repeat
      Chunk := Proc.ReadOutput();
      ACombined := ACombined + Chunk;
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode;
  finally
    Proc.Free();
  end;
end;

function TCLIContractTests.WriteScratchSource(const ASrc: string): string;
begin
  FCounter := FCounter + 1;
  Result := FScratch + 'cli_' + IntToStr(FCounter) + '.pas';
  WriteFile(Result, ASrc);
end;

{ ---- Step 0: FPC CLI removal ---- }

procedure TCLIContractTests.TestHelpStillWorks;
var
  Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  EC := RunCompiler(['--help'], Out_);
  AssertEquals('--help exits 0', 0, EC);
  AssertTrue('usage banner present',
    Pos('Usage:', Out_) >= 0);
end;

procedure TCLIContractTests.TestNormalCompileStillWorks;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  Src := WriteScratchSource(
    'program cli_ok;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(42)' + LineEnding +
    'end.');
  EC := RunCompiler([
    '--source', Src,
    '--unit-path', FRTLPath,
    '--unit-path', FStdlibPath,
    '--output', FScratch + 'cli_ok_bin'
  ], Out_);
  AssertEquals('normal compile exits 0: ' + Out_, 0, EC);
end;

procedure TCLIContractTests.TestFPCVersionProbeGone;
var
  Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  { The FPC info-query path is removed.  -iV must no longer print FPC's
    '3.2.2'; it is now an unrecognised flag and fails. }
  EC := RunCompiler(['-iV'], Out_);
  AssertTrue('-iV must not return FPC version 3.2.2',
    Pos('3.2.2', Out_) < 0);
  AssertTrue('-iV must be rejected (non-zero exit)', EC <> 0);
end;

{ ---- Steps 2-5: driver option contract ---- }

procedure TCLIContractTests.TestAssemblerInternalAccepted;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  { --backend native --assembler internal flows through the native driver's
    AcceptOption (drain) and compiles successfully. }
  Src := WriteScratchSource(
    'program cli_asm;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(1)' + LineEnding +
    'end.');
  EC := RunCompiler([
    '--source', Src,
    '--unit-path', FRTLPath,
    '--unit-path', FStdlibPath,
    '--backend', 'native',
    '--assembler', 'internal',
    '--output', FScratch + 'cli_asm_bin'
  ], Out_);
  AssertEquals('--assembler internal must compile: ' + Out_, 0, EC);
end;

procedure TCLIContractTests.TestAssemblerBogusRejected;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  { Bad --assembler value: accepted by AcceptOption, rejected by the native
    driver's ValidateOptions with the exact legacy message.  Proves the
    drain -> ValidateOptions -> error -> exit-1 wiring. }
  Src := WriteScratchSource(
    'program cli_bad;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(1)' + LineEnding +
    'end.');
  EC := RunCompiler([
    '--source', Src,
    '--unit-path', FRTLPath,
    '--unit-path', FStdlibPath,
    '--backend', 'native',
    '--assembler', 'bogus',
    '--output', FScratch + 'cli_bad_bin'
  ], Out_);
  AssertTrue('bad --assembler value must be rejected', EC <> 0);
  AssertTrue('diagnostic must mention internal/external: ' + Out_,
    Pos('internal', Out_) >= 0);
end;

procedure TCLIContractTests.TestWrongBackendAssemblerRejected;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  { Addendum 2 (intentional behaviour change): --assembler is native-only.
    Under --backend qbe the QBE driver returns oaUnknown for it, so the drain
    reports it as an unknown flag and fails (previously silently accepted). }
  Src := WriteScratchSource(
    'program cli_wb;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(1)' + LineEnding +
    'end.');
  EC := RunCompiler([
    '--source', Src,
    '--unit-path', FRTLPath,
    '--unit-path', FStdlibPath,
    '--backend', 'qbe',
    '--assembler', 'internal',
    '--output', FScratch + 'cli_wb_bin'
  ], Out_);
  AssertTrue('--assembler under --backend qbe must be rejected', EC <> 0);
end;

procedure TCLIContractTests.TestEmitIrStillValidatesAssembler;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  { Addendum 1: ValidateOptions runs unconditionally, above the stdout-mode
    toolchain skip.  So a bad --assembler value is rejected even with
    --emit-ir present (which selects the QBE driver for IR output).  Here the
    wrong-backend rule fires first (QBE doesn't own --assembler), which is the
    correct rejection either way — the point is it does NOT silently succeed. }
  Src := WriteScratchSource(
    'program cli_eir;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(1)' + LineEnding +
    'end.');
  EC := RunCompiler([
    '--source', Src,
    '--unit-path', FRTLPath,
    '--unit-path', FStdlibPath,
    '--backend', 'native',
    '--assembler', 'bogus',
    '--emit-ir'
  ], Out_);
  AssertTrue('bad --assembler must be rejected even with --emit-ir', EC <> 0);
end;

procedure TCLIContractTests.TestAssemblerLineInHelp;
var
  Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  { The native driver's DescribeOptions contributes the --assembler line to
    --help; Blaise.pas no longer hard-codes it. }
  EC := RunCompiler(['--help'], Out_);
  AssertEquals('--help exits 0', 0, EC);
  AssertTrue('--help must list --assembler (via DescribeOptions)',
    Pos('--assembler', Out_) >= 0);
end;

procedure TCLIContractTests.TestEmitIr_WithExplicitNativeBackend_Rejected;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { --emit-ir is a QBE-only output mode.  Asking for it under an explicit
    --backend native must fail loudly, not silently emit QBE IR (which
    ignores the requested backend).  --emit-asm is the native equivalent. }
  Src := WriteScratchSource(
    'program cli_ei;' + LineEnding + 'begin WriteLn(1) end.');
  EC := RunCompiler([
    '--source', Src, '--backend', 'native', '--emit-ir'], Out_);
  AssertTrue('--emit-ir + --backend native must be rejected: ' + Out_, EC <> 0);
  AssertTrue('error mentions emit-ir/native mismatch',
    (Pos('--emit-ir', Out_) >= 0) and (Pos('native', Out_) >= 0));
end;

procedure TCLIContractTests.TestEmitAsm_WithExplicitQbeBackend_Rejected;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { Symmetric case: --emit-asm is native-only; requesting it under an
    explicit --backend qbe must fail rather than silently switch to native. }
  Src := WriteScratchSource(
    'program cli_ea;' + LineEnding + 'begin WriteLn(1) end.');
  EC := RunCompiler([
    '--source', Src, '--backend', 'qbe', '--emit-asm'], Out_);
  AssertTrue('--emit-asm + --backend qbe must be rejected: ' + Out_, EC <> 0);
end;

procedure TCLIContractTests.TestEmitIr_WithoutBackend_StillWorks;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { No --backend given: --emit-ir resolves to the QBE default as before.
    The new validation must only fire on an EXPLICIT incompatible backend. }
  Src := WriteScratchSource(
    'program cli_ei2;' + LineEnding + 'begin WriteLn(1) end.');
  EC := RunCompiler(['--source', Src, '--emit-ir'], Out_);
  AssertEquals('--emit-ir with no --backend still emits QBE IR: ' + Out_, 0, EC);
end;

procedure TCLIContractTests.TestEmitIr_WithExplicitQbeBackend_StillWorks;
var
  Src, Out_: string;
  EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  { Explicit --backend qbe + --emit-ir is consistent — must succeed. }
  Src := WriteScratchSource(
    'program cli_ei3;' + LineEnding + 'begin WriteLn(1) end.');
  EC := RunCompiler(['--source', Src, '--backend', 'qbe', '--emit-ir'], Out_);
  AssertEquals('--emit-ir + --backend qbe is consistent: ' + Out_, 0, EC);
end;

function TCLIContractTests.RunBinary(const AExe: string;
  out ACombined: string): Integer;
var
  Proc: TProcess;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    Proc.Execute();
    ACombined := '';
    repeat
      Chunk := Proc.ReadOutput();
      ACombined := ACombined + Chunk;
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode;
  finally
    Proc.Free();
  end;
end;

function TCLIContractTests.CompileRunFull(const ASrc, ABackend: string;
  out AStdout: string; out AExitCode: Integer): Boolean;
var
  SrcPath, BinPath, CompileOut: string;
  EC: Integer;
begin
  Result := False;
  SrcPath := WriteScratchSource(ASrc);
  BinPath := FScratch + 'cli_run_' + IntToStr(FCounter);
  if ABackend = '' then
    EC := RunCompiler(['--source', SrcPath,
      '--unit-path', FRTLPath, '--unit-path', FStdlibPath,
      '--output', BinPath], CompileOut)
  else
    EC := RunCompiler(['--source', SrcPath, '--backend', ABackend,
      '--unit-path', FRTLPath, '--unit-path', FStdlibPath,
      '--output', BinPath], CompileOut);
  if EC <> 0 then
  begin
    AStdout := 'compile failed: ' + CompileOut;
    AExitCode := EC;
    Exit;
  end;
  AExitCode := RunBinary(BinPath, AStdout);
  Result := True;
end;

const
  SrcDivByZeroCaught =
    'program P;' + LineEnding +
    'uses SysUtils;' + LineEnding +
    'var a, b: Integer;' + LineEnding +
    'begin' + LineEnding +
    '  a := 10; b := 0;' + LineEnding +
    '  try' + LineEnding +
    '    WriteLn(a div b)' + LineEnding +
    '  except' + LineEnding +
    '    on E: EDivByZero do WriteLn(''caught: '' + E.Message)' + LineEnding +
    '  end;' + LineEnding +
    '  WriteLn(''after'')' + LineEnding +
    'end.';

  SrcModByZeroCaught =
    'program P;' + LineEnding +
    'uses SysUtils;' + LineEnding +
    'var a, b: Integer;' + LineEnding +
    'begin' + LineEnding +
    '  a := 10; b := 0;' + LineEnding +
    '  try' + LineEnding +
    '    WriteLn(a mod b)' + LineEnding +
    '  except' + LineEnding +
    '    on E: EDivByZero do WriteLn(''mod caught'')' + LineEnding +
    '  end' + LineEnding +
    'end.';

procedure TCLIContractTests.TestDivByZeroCaught_QBE;
var Out_: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  AssertTrue('compile+run', CompileRunFull(SrcDivByZeroCaught, '', Out_, EC));
  AssertEquals('exit code 0 (exception caught, not SIGFPE)', 0, EC);
  AssertTrue('EDivByZero caught with message',
    Pos('caught: Division by zero', Out_) >= 0);
  AssertTrue('execution continued past the catch', Pos('after', Out_) >= 0);
end;

procedure TCLIContractTests.TestDivByZeroCaught_Native;
var Out_: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  AssertTrue('compile+run', CompileRunFull(SrcDivByZeroCaught, 'native', Out_, EC));
  AssertEquals('exit code 0 (exception caught, not SIGFPE)', 0, EC);
  AssertTrue('EDivByZero caught with message',
    Pos('caught: Division by zero', Out_) >= 0);
  AssertTrue('execution continued past the catch', Pos('after', Out_) >= 0);
end;

procedure TCLIContractTests.TestModByZeroCaught_QBE;
var Out_: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  AssertTrue('compile+run', CompileRunFull(SrcModByZeroCaught, '', Out_, EC));
  AssertEquals('exit code 0', 0, EC);
  AssertTrue('mod by zero caught', Pos('mod caught', Out_) >= 0);
end;

procedure TCLIContractTests.TestModByZeroCaught_Native;
var Out_: string; EC: Integer;
begin
  if not CompilerAvailable() then begin Ignore('<toolchain-missing>'); Exit; end;
  AssertTrue('compile+run', CompileRunFull(SrcModByZeroCaught, 'native', Out_, EC));
  AssertEquals('exit code 0', 0, EC);
  AssertTrue('mod by zero caught', Pos('mod caught', Out_) >= 0);
end;

{ ---- Registration ---- }

initialization
  RegisterTest(TCLIContractTests);

end.
