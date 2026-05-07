{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e;

{$mode objfpc}{$H+}

{ End-to-end tests: compile Pascal source through the full pipeline
  (Lexer -> Parser -> Semantic -> CodeGenQBE -> qbe -> cc -> native binary),
  execute the result, and assert on stdout / exit code / valgrind output.

  These tests exist because the IR-only test harness cannot detect
  RTL-contract mismatches. The alloc16-size bug in the exception frame
  (32 instead of 512) shipped past 626 IR-level assertions because none of
  them linked the IR against the RTL and ran it. Any change to code that
  interacts with the C RTL should add an end-to-end case here.

  Tests shell out via TProcess; each test compiles, runs, and cleans up
  one binary. Roughly ~150 ms per test on a dev laptop. Keep the suite
  focused on behaviour the IR harness cannot see (stack layout, RTL calls,
  leak-freedom, dispatch correctness), not on features already covered by
  IR-level assertions. }

interface

uses
  Classes, SysUtils, Process, fpcunit, testregistry,
  uLexer, uParser, uAST, uSemantic, uCodeGenQBE;

type
  TE2ETests = class(TTestCase)
  private
    FQBE:     string;
    FRTL:     string;
    FScratch: string;
    FCounter: Integer;
    function  ProjectRoot: string;
    function  CompileToIR(const ASrc: string): string;
    function  CompileAndRun(const ASrc:       string;
                            out   AStdout:    string;
                            out   AExitCode:  Integer;
                            const AExtraArgs: array of string): Boolean;
    function  RunUnderValgrind(const ASrc: string; out ALog: string): Boolean;
    function  ToolchainAvailable: Boolean;
  protected
    procedure SetUp; override;
    procedure TearDown; override;
  published
    { Regression for the alloc16-32 exception-frame bug:
      a bare try/finally with no locals, virtuals, or RTL use.
      Before the fix, setjmp's 200-byte jmp_buf write overflowed the
      32-byte frame and corrupted the return address. }
    procedure TestRun_BareTryFinally;

    { Locals live in the stack frame around the exception frame.
      If the exception frame is undersized, setjmp clobbers them. }
    procedure TestRun_TryFinally_PreservesLocals;

    { Exception frame must not corrupt caller state when nested. }
    procedure TestRun_NestedTryFinally;

    { Virtual dispatch in expression position inside try/finally —
      the exact pattern that first surfaced the undersize-frame bug. }
    procedure TestRun_VirtualDispatchInsideTryFinally;

    { Phase 2 milestone program: classes, inheritance, virtual, properties,
      try/finally, and 'is' — linked list with owned nodes. Asserts
      expected stdout. Acts as the canonical smoke test for Phase 2. }
    procedure TestRun_Phase2Milestone_Stdout;

    { Valgrind-clean: no leaks and no errors on the milestone program.
      Skipped (not failed) when valgrind is absent. }
    procedure TestRun_Phase2Milestone_Valgrind;

    { Smoke tests for the features added alongside this suite:
      AND/OR/NOT, Exit/Break, multi-arg WriteLn, chained field access. }
    procedure TestRun_BooleanOps_AllExpressions;
    procedure TestRun_MultiArgWriteLn_PrintsAllArgs;
    procedure TestRun_ForBreak_StopsAtFiveHalt;
    procedure TestRun_ExitFromFunction_ReturnsImmediately;
    procedure TestRun_ChainedRecordField_LoadsInner;

    { Universal-ARC e2e coverage: class/interface lifetime under valgrind.
      These programs exercise the insertion passes introduced in the
      class-ownership follow-up and assert leak-freedom. }
    procedure TestRun_ClassArc_NoExplicitFree_Valgrind;
    procedure TestRun_InterfaceArc_CarriesLifetime_Valgrind;

    { [Weak] cycle-break: two class instances referencing each other
      through a [Weak] field stay cycle-free and are valgrind-clean on
      scope exit.  This is the functional proof that the weak-ref
      insertion pass does what it says on the tin. }
    procedure TestRun_WeakRef_BreaksCycle_Valgrind;

    { Destroy as ARC destructor hook: a class with a Destroy method that
      frees an internal malloc buffer goes valgrind-clean when the only
      release is the scope-exit ARC release (no explicit Free call). }
    procedure TestRun_ClassDestroy_FreesBuffer_Valgrind;

    { RTL collections under ARC: a TList<Integer> built inline (no RTL
      unit needed) with a Destroy that frees FData is valgrind-clean. }
    procedure TestRun_TListARC_Valgrind;

    { Phase 3 milestone program: TList + TDictionary under ARC rules.
      Asserts expected stdout and valgrind-clean execution. }
    procedure TestRun_Phase3Milestone_Stdout;
    procedure TestRun_Phase3Milestone_Valgrind;

    { String operation RTL functions: verify correct output at runtime. }
    procedure TestRun_StringOps_Length;
    procedure TestRun_StringOps_Pos;
    procedure TestRun_StringOps_Copy;
    procedure TestRun_StringOps_UpperCase;
    procedure TestRun_StringOps_SameText;
    procedure TestRun_StringOps_IntToStr;
    procedure TestRun_StringOps_StrToInt;
    procedure TestRun_StringOps_StrToInt_Hex;
    procedure TestRun_StringOps_Copy_MaxIntCount;
    procedure TestRun_Int64_PositiveAboveInt32_FormatsCorrectly;
    procedure TestRun_StringOps_Format_IntArg;
    procedure TestRun_StringOps_Format_StrArg;
    procedure TestRun_StringOps_Format_MixedArgs;
    { ------------------------------------------------------------------ }
    { Collections: TObjectList, TStringList                               }
    { ------------------------------------------------------------------ }
    procedure TestRun_TObjectList_AddGetCount;
    procedure TestRun_TObjectList_Delete;
    procedure TestRun_TStringList_AddGet;
    procedure TestRun_TStringList_Find_Sorted;
    procedure TestRun_Collections_Valgrind;
    { ------------------------------------------------------------------ }
    { Self-hosting: file I/O, CLI args, multi-type blocks                 }
    { ------------------------------------------------------------------ }
    procedure TestRun_ParamStr_PrintsArg;
    procedure TestRun_ParamCount_WithArgs;
    procedure TestRun_ReadWriteFile_RoundTrip;
    procedure TestRun_FileExists_TrueAndFalse;
    procedure TestRun_GetEnvVar_Path;
    procedure TestRun_Halt_ExitCode;
    procedure TestRun_MultiTypeBlock_BothClassesWork;
    { ------------------------------------------------------------------ }
    { case statements and enum types                                       }
    { ------------------------------------------------------------------ }
    procedure TestRun_Case_IntegerBranch;
    procedure TestRun_Case_ElseBranch;
    procedure TestRun_Enum_OrdinalValues;
    procedure TestRun_Enum_InCase;
    { ------------------------------------------------------------------ }
    { File path manipulation (step 11)                                    }
    { ------------------------------------------------------------------ }
    procedure TestRun_ChangeFileExt_ChangesExtension;
    procedure TestRun_ExtractFileName_ReturnsName;
    procedure TestRun_ExtractFilePath_ReturnsDir;
    procedure TestRun_IncludeTrailingPathDelimiter_AppendsSlash;
    { ------------------------------------------------------------------ }
    { Process management built-ins (step 8)                               }
    { ------------------------------------------------------------------ }
    procedure TestRun_ProcessBuiltins_CapturesOutput;
    procedure TestRun_ProcessBuiltins_ExitCode;
    { ------------------------------------------------------------------ }
    { Typed except handlers (Step 8)                                      }
    { ------------------------------------------------------------------ }
    procedure TestRun_TypedExcept_CorrectHandlerMatched;
    procedure TestRun_TypedExcept_SubclassMatchesParentHandler;
    procedure TestRun_TypedExcept_UnmatchedReraises;
    procedure TestRun_TypedExcept_BareRaisePropagatesToOuter;
    procedure TestRun_TypedExcept_ElseBodyRunsWhenNoMatch;

    { ------------------------------------------------------------------ }
    { Built-in TObject.ToString                                           }
    { ------------------------------------------------------------------ }
    { Default ToString (no override) returns the runtime class name via
      vtable slot 1.  Exercises the RTL TObject_ToString helper and its
      vtable + typeinfo walk — IR tests cannot validate the helper. }
    procedure TestRun_ToString_DefaultReturnsClassName;
    { An override placed at vtable slot 1 must be reached through Obj.ToString
      even when the static type is the base class — i.e. the FieldAccess
      method-call path must dispatch virtually, not statically. }
    procedure TestRun_ToString_OverrideDispatchedVirtually;
    { When a derived class inherits the override without re-declaring it,
      the inherited slot must still resolve to the override at runtime. }
    procedure TestRun_ToString_InheritedOverrideStillReached;

    { ------------------------------------------------------------------ }
    { OS utility builtins (step 2a)                                      }
    { ------------------------------------------------------------------ }
    procedure TestRun_GetProcessID_ReturnsNonZero;
    procedure TestRun_DirectoryExists_TrueAndFalse;
    procedure TestRun_GetTempDir_ReturnsPath;
    procedure TestRun_ForceDirectories_CreatesTree;
    procedure TestRun_Sleep_DoesNotCrash;

    { TObject.InheritsFrom: class ancestry walk }
    procedure TestRun_InheritsFrom_SameClass_ReturnsTrue;
    procedure TestRun_InheritsFrom_Parent_ReturnsTrue;
    procedure TestRun_InheritsFrom_GrandParent_ReturnsTrue;
    procedure TestRun_InheritsFrom_Unrelated_ReturnsFalse;
    procedure TestRun_InheritsFrom_Reverse_ReturnsFalse;
    procedure TestRun_InheritsFrom_ClassType_Works;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Path discovery                                                       }
{ ------------------------------------------------------------------ }

function TE2ETests.ProjectRoot: string;
var
  Dir, Parent: string;
  Steps:       Integer;
begin
  { Honour an explicit env override first. }
  Result := GetEnvironmentVariable('BLAISE_PROJECT_ROOT');
  if Result <> '' then
  begin
    Result := IncludeTrailingPathDelimiter(Result);
    Exit;
  end;

  { PasBuild runs the test binary from compiler/target/, not the project
    root. Walk up from the CWD looking for the pair of marker directories
    that together uniquely identify this project's root: vendor/qbe and rtl. }
  Dir := GetCurrentDir;
  for Steps := 0 to 5 do
  begin
    if DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'vendor/qbe') and
       DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'rtl') then
    begin
      Result := IncludeTrailingPathDelimiter(Dir);
      Exit;
    end;
    Parent := ExtractFileDir(Dir);
    if (Parent = '') or (Parent = Dir) then Break;
    Dir := Parent;
  end;

  { Fallback: return CWD as-is. Tests that need paths will skip gracefully. }
  Result := IncludeTrailingPathDelimiter(GetCurrentDir);
end;

function TE2ETests.ToolchainAvailable: Boolean;
begin
  Result := FileExists(FQBE) and FileExists(FRTL);
end;

procedure TE2ETests.SetUp;
var Root: string;
begin
  Root := ProjectRoot;
  FQBE := GetEnvironmentVariable('BLAISE_QBE');
  if FQBE = '' then FQBE := Root + 'vendor/qbe/qbe';
  FRTL := GetEnvironmentVariable('BLAISE_RTL');
  if FRTL = '' then FRTL := Root + 'rtl/target/blaise_rtl.a';

  FScratch := Root + 'compiler/target/test-e2e';
  ForceDirectories(FScratch);
  FCounter := 0;
end;

procedure TE2ETests.TearDown;
begin
  { Scratch files are small; leave them on disk for post-mortem debugging
    when a test fails. A fresh SetUp run does not wipe them, but stale
    artefacts from prior runs are overwritten by name collisions. }
end;

{ ------------------------------------------------------------------ }
{ Compile + run pipeline                                               }
{ ------------------------------------------------------------------ }

function TE2ETests.CompileToIR(const ASrc: string): string;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  CG:       TCodeGenQBE;
begin
  Lexer    := nil;
  Parser   := nil;
  Prog     := nil;
  Semantic := nil;
  CG       := nil;
  try
    Lexer    := TLexer.Create(ASrc);
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse;
    Semantic := TSemanticAnalyser.Create;
    Semantic.Analyse(Prog);
    CG       := TCodeGenQBE.Create;
    CG.Generate(Prog);
    Result   := CG.GetOutput;
  finally
    CG.Free;
    Semantic.Free;
    Prog.Free;
    Parser.Free;
    Lexer.Free;
  end;
end;

{ Runs a process, captures stdout+stderr into AStdout, returns exit code.
  Returns -1 if the process could not be started. }
function RunProc(const AExe:      string;
                 const AArgs:     array of string;
                 out   AStdout:   string;
                 AInheritStdErr:  Boolean): Integer;
var
  Proc: TProcess;
  Buf:  array[0..4095] of Byte;
  N:    LongInt;
  S:    string;
  I:    Integer;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    for I := Low(AArgs) to High(AArgs) do
      Proc.Parameters.Add(AArgs[I]);
    Proc.Options := [poUsePipes];
    if AInheritStdErr then
      Proc.Options := Proc.Options + [poStderrToOutPut];
    try
      Proc.Execute;
    except
      Result := -1;
      Exit;
    end;
    AStdout := '';
    while Proc.Running or (Proc.Output.NumBytesAvailable > 0) do
    begin
      if Proc.Output.NumBytesAvailable > 0 then
      begin
        N := Proc.Output.Read(Buf, SizeOf(Buf));
        if N > 0 then
        begin
          SetString(S, PChar(@Buf[0]), N);
          AStdout := AStdout + S;
        end;
      end
      else
        Sleep(1);
    end;
    Result := Proc.ExitCode;
  finally
    Proc.Free;
  end;
end;

function TE2ETests.CompileAndRun(const ASrc:       string;
                                 out   AStdout:    string;
                                 out   AExitCode:  Integer;
                                 const AExtraArgs: array of string): Boolean;
var
  IR:       string;
  Base:     string;
  IRFile:   string;
  AsmFile:  string;
  BinFile:  string;
  ToolOut:  string;
  Rc:       Integer;
  Lst:      TStringList;
begin
  Result    := False;
  AStdout   := '';
  AExitCode := -1;

  Inc(FCounter);
  Base    := IncludeTrailingPathDelimiter(FScratch) +
             'case_' + IntToStr(GetProcessID) + '_' + IntToStr(FCounter);
  IRFile  := Base + '.ssa';
  AsmFile := Base + '.s';
  BinFile := Base;

  IR := CompileToIR(ASrc);

  Lst := TStringList.Create;
  try
    Lst.Text := IR;
    Lst.SaveToFile(IRFile);
  finally
    Lst.Free;
  end;

  Rc := RunProc(FQBE, ['-o', AsmFile, IRFile], ToolOut, True);
  if Rc <> 0 then
  begin
    Fail('qbe failed (exit ' + IntToStr(Rc) + '): ' + ToolOut + #10 +
         'IR file preserved at: ' + IRFile);
    Exit;
  end;

  Rc := RunProc('cc', ['-o', BinFile, AsmFile, FRTL], ToolOut, True);
  if Rc <> 0 then
  begin
    Fail('cc failed (exit ' + IntToStr(Rc) + '): ' + ToolOut + #10 +
         'IR: ' + IRFile + #10 + 'asm: ' + AsmFile);
    Exit;
  end;

  Rc := RunProc(BinFile, AExtraArgs, AStdout, False);
  AExitCode := Rc;
  Result    := True;

  { Clean up on success — keep artefacts on failure for debugging. }
  DeleteFile(AsmFile);
  DeleteFile(IRFile);
  DeleteFile(BinFile);
end;

function TE2ETests.RunUnderValgrind(const ASrc: string;
                                    out   ALog: string): Boolean;
var
  IR:       string;
  Base:     string;
  IRFile:   string;
  AsmFile:  string;
  BinFile:  string;
  ToolOut:  string;
  VgOut:    string;
  Rc:       Integer;
  Lst:      TStringList;
begin
  Result := False;
  ALog   := '';

  Inc(FCounter);
  Base    := IncludeTrailingPathDelimiter(FScratch) +
             'vg_' + IntToStr(GetProcessID) + '_' + IntToStr(FCounter);
  IRFile  := Base + '.ssa';
  AsmFile := Base + '.s';
  BinFile := Base;

  IR := CompileToIR(ASrc);
  Lst := TStringList.Create;
  try
    Lst.Text := IR;
    Lst.SaveToFile(IRFile);
  finally
    Lst.Free;
  end;

  Rc := RunProc(FQBE, ['-o', AsmFile, IRFile], ToolOut, True);
  if Rc <> 0 then Exit;
  Rc := RunProc('cc', ['-o', BinFile, AsmFile, FRTL], ToolOut, True);
  if Rc <> 0 then Exit;

  { --error-exitcode=99 makes valgrind non-zero on errors independent of the
    program's own exit code. --leak-check=full catches reachable-but-unfreed
    heap blocks. stdout+stderr folded so our log contains the HEAP SUMMARY. }
  Rc := RunProc('valgrind',
    ['--error-exitcode=99', '--leak-check=full', '--quiet', BinFile],
    VgOut, True);
  ALog   := VgOut;
  Result := Rc = 0;

  DeleteFile(AsmFile);
  DeleteFile(IRFile);
  DeleteFile(BinFile);
end;

{ ------------------------------------------------------------------ }
{ Tests                                                                }
{ ------------------------------------------------------------------ }

const
  LE = LineEnding;

  SrcBareTryFinally =
    'program P;'                  + LE +
    'begin'                       + LE +
    '  try'                       + LE +
    '    WriteLn(''in_try'')'     + LE +
    '  finally'                   + LE +
    '    WriteLn(''in_finally'')' + LE +
    '  end'                       + LE +
    'end.';

  SrcPreservesLocals =
    'program P;'                  + LE +
    'var A, B, C: Integer;'       + LE +
    'begin'                       + LE +
    '  A := 11;'                  + LE +
    '  B := 22;'                  + LE +
    '  C := 33;'                  + LE +
    '  try'                       + LE +
    '    WriteLn(A);'             + LE +
    '    WriteLn(B);'             + LE +
    '    WriteLn(C)'              + LE +
    '  finally'                   + LE +
    '    WriteLn(A + B + C)'      + LE +
    '  end'                       + LE +
    'end.';

  SrcNestedTryFinally =
    'program P;'                  + LE +
    'begin'                       + LE +
    '  try'                       + LE +
    '    try'                     + LE +
    '      WriteLn(''inner_try'')' + LE +
    '    finally'                 + LE +
    '      WriteLn(''inner_fin'')' + LE +
    '    end'                     + LE +
    '  finally'                   + LE +
    '    WriteLn(''outer_fin'')'  + LE +
    '  end'                       + LE +
    'end.';

  { Virtual dispatch in expression position inside try/finally:
    N.GetTag() reads the result into T. This is the pattern that
    crashed with the undersized exception frame. }
  SrcVirtualDispatchInTry =
    'program P;'                                        + LE +
    'type'                                              + LE +
    '  TNode = class'                                   + LE +
    '    function GetTag: Integer; virtual;'            + LE +
    '  end;'                                            + LE +
    '  TMarkedNode = class(TNode)'                      + LE +
    '    function GetTag: Integer; override;'           + LE +
    '  end;'                                            + LE +
    'function TNode.GetTag: Integer;'                   + LE +
    'begin Result := 0 end;'                            + LE +
    'function TMarkedNode.GetTag: Integer;'             + LE +
    'begin Result := 1 end;'                            + LE +
    'var N: TNode; T: Integer;'                         + LE +
    'begin'                                             + LE +
    '  N := TMarkedNode.Create;'                        + LE +
    '  try'                                             + LE +
    '    T := N.GetTag();'                              + LE +
    '    WriteLn(T)'                                    + LE +
    '  finally'                                         + LE +
    '    N.Free'                                        + LE +
    '  end'                                             + LE +
    'end.';

procedure TE2ETests.TestRun_BareTryFinally;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then
  begin
    Ignore('qbe or RTL not built: qbe=' + FQBE + '  rtl=' + FRTL);
    Exit;
  end;
  AssertTrue('compile+run',
    CompileAndRun(SrcBareTryFinally, Output, RCode, []));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout',
    'in_try' + LE + 'in_finally' + LE, Output);
end;

procedure TE2ETests.TestRun_TryFinally_PreservesLocals;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then
  begin
    Ignore('qbe or RTL not built');
    Exit;
  end;
  AssertTrue('compile+run',
    CompileAndRun(SrcPreservesLocals, Output, RCode, []));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('locals preserved',
    '11' + LE + '22' + LE + '33' + LE + '66' + LE, Output);
end;

procedure TE2ETests.TestRun_NestedTryFinally;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then
  begin
    Ignore('qbe or RTL not built');
    Exit;
  end;
  AssertTrue('compile+run',
    CompileAndRun(SrcNestedTryFinally, Output, RCode, []));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout',
    'inner_try' + LE + 'inner_fin' + LE + 'outer_fin' + LE, Output);
end;

procedure TE2ETests.TestRun_VirtualDispatchInsideTryFinally;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then
  begin
    Ignore('qbe or RTL not built');
    Exit;
  end;
  AssertTrue('compile+run',
    CompileAndRun(SrcVirtualDispatchInTry, Output, RCode, []));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout (virtual -> marked -> 1)', '1' + LE, Output);
end;

procedure TE2ETests.TestRun_Phase2Milestone_Stdout;
var
  Path, Src, Output: string;
  RCode:             Integer;
  Lst:               TStringList;
  Expected:          string;
begin
  if not ToolchainAvailable then
  begin
    Ignore('qbe or RTL not built');
    Exit;
  end;
  Path := ProjectRoot + 'tests/phase2_milestone.pas';
  if not FileExists(Path) then
  begin
    Ignore('phase2_milestone.pas not found at ' + Path);
    Exit;
  end;

  Lst := TStringList.Create;
  try
    Lst.LoadFromFile(Path);
    Src := Lst.Text;
  finally
    Lst.Free;
  end;

  AssertTrue('compile+run milestone',
    CompileAndRun(Src, Output, RCode, []));
  AssertEquals('milestone exit code', 0, RCode);

  Expected :=
    'count=4'             + LE +
    '--- walk ---'        + LE +
    '  value=40'          + LE +
    '  tag=0'             + LE +
    '  marked=0'          + LE +
    '  value=30'          + LE +
    '  tag=1'             + LE +
    '  marked=1'          + LE +
    '  value=20'          + LE +
    '  tag=0'             + LE +
    '  marked=0'          + LE +
    '  value=10'          + LE +
    '  tag=0'             + LE +
    '  marked=0'          + LE +
    'pop=40'              + LE +
    'pop=30'              + LE +
    'count_after_pops=2'  + LE;
  AssertEquals('milestone stdout', Expected, Output);
end;

procedure TE2ETests.TestRun_Phase2Milestone_Valgrind;
var
  Path, Src, Log: string;
  Lst:            TStringList;
  Found, Dummy:   string;
  OK:             Boolean;
begin
  if not ToolchainAvailable then
  begin
    Ignore('qbe or RTL not built');
    Exit;
  end;
  if RunProc('valgrind', ['--version'], Dummy, True) <> 0 then
  begin
    Ignore('valgrind not installed');
    Exit;
  end;
  Path := ProjectRoot + 'tests/phase2_milestone.pas';
  if not FileExists(Path) then
  begin
    Ignore('phase2_milestone.pas not found');
    Exit;
  end;

  Lst := TStringList.Create;
  try
    Lst.LoadFromFile(Path);
    Src := Lst.Text;
  finally
    Lst.Free;
  end;

  OK := RunUnderValgrind(Src, Log);
  if not OK then
  begin
    { valgrind --quiet prints nothing on a clean run, so the log on failure
      is the valuable signal: dump it into the assertion message. }
    Found := Log;
    if Found = '' then Found := '(valgrind produced no output — exit nonzero)';
    Fail('valgrind reported errors or leaks:' + LE + Found);
  end;
end;

{ ------------------------------------------------------------------ }
{ New-feature smoke tests (AND/OR/NOT, Exit/Break, multi-arg WriteLn,
  chained field access).  Kept here rather than a dedicated unit so
  all compile+run coverage lives together. }
{ ------------------------------------------------------------------ }

const
  SrcBoolOps =
    'program P;'                              + LE +
    'var A, B: Boolean;'                      + LE +
    'begin'                                   + LE +
    '  A := True;'                            + LE +
    '  B := False;'                           + LE +
    '  if A and not B then WriteLn(''t1'');'  + LE +
    '  if A or B then WriteLn(''t2'');'       + LE +
    '  if not (A and B) then WriteLn(''t3'')' + LE +
    'end.';

  SrcMultiArg =
    'program P;'                              + LE +
    'var I, J, K: Integer;'                   + LE +
    'begin'                                   + LE +
    '  I := 1; J := 2; K := 3;'               + LE +
    '  WriteLn(I, J, K)'                      + LE +
    'end.';

  SrcForBreak =
    'program P;'                              + LE +
    'var I, Last: Integer;'                   + LE +
    'begin'                                   + LE +
    '  Last := 0;'                            + LE +
    '  for I := 1 to 100 do'                  + LE +
    '  begin'                                 + LE +
    '    Last := I;'                          + LE +
    '    if I = 5 then break'                 + LE +
    '  end;'                                  + LE +
    '  WriteLn(Last)'                         + LE +
    'end.';

  SrcExitFunc =
    'program P;'                              + LE +
    'function FirstPositive(X: Integer): Integer;' + LE +
    'begin'                                   + LE +
    '  if X > 0 then'                         + LE +
    '  begin Result := X; exit end;'          + LE +
    '  Result := 0 - X'                       + LE +
    'end;'                                    + LE +
    'begin'                                   + LE +
    '  WriteLn(FirstPositive(7));'            + LE +
    '  WriteLn(FirstPositive(0 - 9))'         + LE +
    'end.';

  { Universal-ARC on classes: allocate, assign between vars, drop out of
    scope without calling Free.  Under the new rules every variable slot
    holds one retained reference balanced by a scope-exit release.  The
    program is leak-free only if both the per-variable release and the
    per-class field cleanup fire correctly at refcount zero.  We stage
    writes through a local (chained field *writes* are not yet in the
    language; chained reads are). }
  SrcClassArcNoFree =
    'program P;'                                        + LE +
    'type'                                              + LE +
    '  TInner = class'                                  + LE +
    '    V: Integer;'                                   + LE +
    '  end;'                                            + LE +
    '  TOuter = class'                                  + LE +
    '    Child: TInner;'                                + LE +
    '  end;'                                            + LE +
    'var'                                               + LE +
    '  A, B: TOuter;'                                   + LE +
    '  I:    TInner;'                                   + LE +
    'begin'                                             + LE +
    '  A       := TOuter.Create;'                       + LE +
    '  I       := TInner.Create;'                       + LE +
    '  I.V     := 42;'                                  + LE +
    '  A.Child := I;'                                   + LE +
    '  B       := A;'                                   + LE +
    '  WriteLn(B.Child.V)'                              + LE +
    'end.';

  { Universal-ARC on interface references: assigning a class through an
    interface variable addrefs the backing class; on scope exit the
    interface obj slot is released, and the class's final release fires
    its field-cleanup chain.  Without interface-obj ARC this program
    either leaks the backing class or double-frees it on exit.
    Interface *function* calls in expression position are not yet
    supported; we invoke a procedure on the interface which writes
    directly, which is enough to cover the ARC lifetime. }
  SrcInterfaceArcLifetime =
    'program P;'                                        + LE +
    'type'                                              + LE +
    '  IThing = interface'                              + LE +
    '    procedure Emit;'                               + LE +
    '  end;'                                            + LE +
    '  TThing = class(TObject, IThing)'                 + LE +
    '    FValue: Integer;'                              + LE +
    '    procedure Emit;'                               + LE +
    '  end;'                                            + LE +
    'procedure TThing.Emit;'                            + LE +
    'begin'                                             + LE +
    '  WriteLn(Self.FValue)'                            + LE +
    'end;'                                              + LE +
    'var'                                               + LE +
    '  T: TThing;'                                      + LE +
    '  F: IThing;'                                      + LE +
    'begin'                                             + LE +
    '  T        := TThing.Create;'                      + LE +
    '  T.FValue := 17;'                                 + LE +
    '  F        := T;'                                  + LE +
    '  F.Emit'                                          + LE +
    'end.';

  { [Weak] cycle-break: two TNode instances reference each other through a
    [Weak] Other field.  Under strong ARC this would be a refcount cycle
    and leak both nodes; with [Weak] neither side contributes to the
    other's refcount, so scope exit releases both cleanly and the weak
    slots are zeroed before their storage is reclaimed. }
  SrcWeakCycle =
    'program P;'                                        + LE +
    'type'                                              + LE +
    '  TNode = class'                                   + LE +
    '    Value: Integer;'                               + LE +
    '    [Weak] Other: TNode;'                          + LE +
    '  end;'                                            + LE +
    'var'                                               + LE +
    '  A, B: TNode;'                                    + LE +
    'begin'                                             + LE +
    '  A := TNode.Create;'                              + LE +
    '  B := TNode.Create;'                              + LE +
    '  A.Value := 1;'                                   + LE +
    '  B.Value := 2;'                                   + LE +
    '  A.Other := B;'                                   + LE +
    '  B.Other := A;'                                   + LE +
    '  WriteLn(A.Value);'                               + LE +
    '  WriteLn(B.Value)'                                + LE +
    'end.';

  { Destroy as ARC destructor: class allocates an internal buffer via Init,
    Destroy frees it.  No Free call in main — scope-exit ARC handles the
    class lifetime; Destroy is invoked via the field cleanup fn.  The
    program must produce the expected output and pass valgrind. }
  SrcDestroyFreesBuffer =
    'program P;'                                        + LE +
    'type'                                              + LE +
    '  TBuf = class'                                    + LE +
    '    FData: ^Integer;'                              + LE +
    '    procedure Init;'                               + LE +
    '    procedure Destroy;'                            + LE +
    '  end;'                                            + LE +
    'procedure TBuf.Init;'                              + LE +
    'begin'                                             + LE +
    '  Self.FData := GetMem(4 * SizeOf(Integer))'      + LE +
    'end;'                                              + LE +
    'procedure TBuf.Destroy;'                           + LE +
    'begin'                                             + LE +
    '  FreeMem(Self.FData);'                            + LE +
    '  Self.FData := nil'                               + LE +
    'end;'                                              + LE +
    'var B: TBuf;'                                      + LE +
    'begin'                                             + LE +
    '  B := TBuf.Create;'                               + LE +
    '  B.Init;'                                         + LE +
    '  WriteLn(''ok'')'                                 + LE +
    'end.';

  { TList<Integer> with Destroy: proves the pattern that the RTL uses.
    ARC releases the list on scope exit; Destroy frees FData. }
  SrcTListARCValgrind =
    'program P;'                                        + LE +
    'type'                                              + LE +
    '  TList = class'                                   + LE +
    '    FData:     ^Integer;'                          + LE +
    '    FCount:    Integer;'                           + LE +
    '    FCapacity: Integer;'                           + LE +
    '    procedure Grow;'                               + LE +
    '    procedure Add(V: Integer);'                    + LE +
    '    function  Get(I: Integer): Integer;'           + LE +
    '    procedure Destroy;'                            + LE +
    '    property Count: Integer read FCount;'          + LE +
    '  end;'                                            + LE +
    'procedure TList.Grow;'                             + LE +
    'var NewCap: Integer;'                              + LE +
    'begin'                                             + LE +
    '  if Self.FCapacity = 0 then NewCap := 4'         + LE +
    '  else NewCap := Self.FCapacity * 2;'              + LE +
    '  Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(Integer));' + LE +
    '  Self.FCapacity := NewCap'                        + LE +
    'end;'                                              + LE +
    'procedure TList.Add(V: Integer);'                  + LE +
    'var Dest: ^Integer;'                               + LE +
    'begin'                                             + LE +
    '  if Self.FCount = Self.FCapacity then Self.Grow;' + LE +
    '  Dest  := Self.FData + Self.FCount * SizeOf(Integer);' + LE +
    '  Dest^ := V;'                                     + LE +
    '  Self.FCount := Self.FCount + 1'                  + LE +
    'end;'                                              + LE +
    'function TList.Get(I: Integer): Integer;'          + LE +
    'var Src: ^Integer;'                                + LE +
    'begin'                                             + LE +
    '  Src    := Self.FData + I * SizeOf(Integer);'     + LE +
    '  Result := Src^'                                  + LE +
    'end;'                                              + LE +
    'procedure TList.Destroy;'                          + LE +
    'begin'                                             + LE +
    '  FreeMem(Self.FData);'                            + LE +
    '  Self.FData := nil'                               + LE +
    'end;'                                              + LE +
    'var L: TList;'                                     + LE +
    'begin'                                             + LE +
    '  L := TList.Create;'                              + LE +
    '  L.Add(10);'                                      + LE +
    '  L.Add(20);'                                      + LE +
    '  L.Add(30);'                                      + LE +
    '  WriteLn(L.Get(0));'                              + LE +
    '  WriteLn(L.Get(1));'                              + LE +
    '  WriteLn(L.Get(2));'                              + LE +
    '  WriteLn(L.Count)'                                + LE +
    'end.';

  { Chained READ: Pascal zero-initialises records, so O.I.Value defaults
    to 0 without any write.  Exercising the read path is enough for this
    smoke test; chained-WRITE support is tracked separately. }
  SrcChainedRecord =
    'program P;'                              + LE +
    'type'                                    + LE +
    '  TInner = record Value: Integer; end;'  + LE +
    '  TOuter = record I: TInner; end;'       + LE +
    'var O: TOuter; N: Integer;'              + LE +
    'begin'                                   + LE +
    '  N := O.I.Value;'                       + LE +
    '  WriteLn(N)'                            + LE +
    'end.';

procedure TE2ETests.TestRun_BooleanOps_AllExpressions;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then
  begin
    Ignore('qbe or RTL not built');
    Exit;
  end;
  AssertTrue(CompileAndRun(SrcBoolOps, Output, RCode, []));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('all three branches fire',
    't1' + LE + 't2' + LE + 't3' + LE, Output);
end;

procedure TE2ETests.TestRun_MultiArgWriteLn_PrintsAllArgs;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then
  begin
    Ignore('qbe or RTL not built');
    Exit;
  end;
  AssertTrue(CompileAndRun(SrcMultiArg, Output, RCode, []));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('three values concatenated with trailing newline',
    '123' + LE, Output);
end;

procedure TE2ETests.TestRun_ForBreak_StopsAtFiveHalt;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then
  begin
    Ignore('qbe or RTL not built');
    Exit;
  end;
  AssertTrue(CompileAndRun(SrcForBreak, Output, RCode, []));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('loop broke at I=5', '5' + LE, Output);
end;

procedure TE2ETests.TestRun_ExitFromFunction_ReturnsImmediately;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then
  begin
    Ignore('qbe or RTL not built');
    Exit;
  end;
  AssertTrue(CompileAndRun(SrcExitFunc, Output, RCode, []));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('exit early for positive, compute for negative',
    '7' + LE + '9' + LE, Output);
end;

procedure TE2ETests.TestRun_ChainedRecordField_LoadsInner;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then
  begin
    Ignore('qbe or RTL not built');
    Exit;
  end;
  AssertTrue(CompileAndRun(SrcChainedRecord, Output, RCode, []));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('chained read of zero-initialised field', '0' + LE, Output);
end;

procedure TE2ETests.TestRun_ClassArc_NoExplicitFree_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable then
  begin
    Ignore('qbe or RTL not built');
    Exit;
  end;
  { Sanity: program runs and prints 42 }
  AssertTrue(CompileAndRun(SrcClassArcNoFree, Output, RCode, []));
  AssertEquals('exit 0',       0,         RCode);
  AssertEquals('field reread', '42' + LE, Output);
  { Leak-freedom: under valgrind, every class instance must be reclaimed
    by scope-exit releases alone (no Free calls anywhere in the source). }
  if RunProc('valgrind', ['--version'], Log, True) <> 0 then
  begin
    Ignore('valgrind not installed');
    Exit;
  end;
  OK := RunUnderValgrind(SrcClassArcNoFree, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output — exit nonzero)';
    Fail('valgrind reported errors or leaks:' + LE + Log);
  end;
end;

procedure TE2ETests.TestRun_InterfaceArc_CarriesLifetime_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable then
  begin
    Ignore('qbe or RTL not built');
    Exit;
  end;
  AssertTrue(CompileAndRun(SrcInterfaceArcLifetime, Output, RCode, []));
  AssertEquals('exit 0',                  0,         RCode);
  AssertEquals('interface method result', '17' + LE, Output);
  if RunProc('valgrind', ['--version'], Log, True) <> 0 then
  begin
    Ignore('valgrind not installed');
    Exit;
  end;
  OK := RunUnderValgrind(SrcInterfaceArcLifetime, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output — exit nonzero)';
    Fail('valgrind reported errors or leaks:' + LE + Log);
  end;
end;

procedure TE2ETests.TestRun_WeakRef_BreaksCycle_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable then
  begin
    Ignore('qbe or RTL not built');
    Exit;
  end;
  AssertTrue(CompileAndRun(SrcWeakCycle, Output, RCode, []));
  AssertEquals('exit 0',                0,              RCode);
  AssertEquals('values printed via A/B', '1' + LE + '2' + LE, Output);
  if RunProc('valgrind', ['--version'], Log, True) <> 0 then
  begin
    Ignore('valgrind not installed');
    Exit;
  end;
  OK := RunUnderValgrind(SrcWeakCycle, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output — exit nonzero)';
    Fail('valgrind reported errors or leaks:' + LE + Log);
  end;
end;

procedure TE2ETests.TestRun_ClassDestroy_FreesBuffer_Valgrind;
var
  Output: string;
  RCode:  Integer;
  Log:    string;
  OK:     Boolean;
begin
  if not ToolchainAvailable then
  begin
    Ignore('qbe or RTL not built');
    Exit;
  end;
  AssertTrue('compile+run', CompileAndRun(SrcDestroyFreesBuffer, Output, RCode, []));
  AssertEquals('exit 0',  0,          RCode);
  AssertEquals('stdout',  'ok' + LE,  Output);
  if RunProc('valgrind', ['--version'], Log, True) <> 0 then
  begin
    Ignore('valgrind not installed');
    Exit;
  end;
  OK := RunUnderValgrind(SrcDestroyFreesBuffer, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output — exit nonzero)';
    Fail('Destroy did not free buffer — valgrind reports:' + LE + Log);
  end;
end;

procedure TE2ETests.TestRun_TListARC_Valgrind;
var
  Output: string;
  RCode:  Integer;
  Log:    string;
  OK:     Boolean;
begin
  if not ToolchainAvailable then
  begin
    Ignore('qbe or RTL not built');
    Exit;
  end;
  AssertTrue('compile+run', CompileAndRun(SrcTListARCValgrind, Output, RCode, []));
  AssertEquals('exit 0',  0,   RCode);
  AssertEquals('stdout',
    '10' + LE + '20' + LE + '30' + LE + '3' + LE, Output);
  if RunProc('valgrind', ['--version'], Log, True) <> 0 then
  begin
    Ignore('valgrind not installed');
    Exit;
  end;
  OK := RunUnderValgrind(SrcTListARCValgrind, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output — exit nonzero)';
    Fail('TList FData leaked — valgrind reports:' + LE + Log);
  end;
end;

procedure TE2ETests.TestRun_Phase3Milestone_Stdout;
var
  Path, Src, Output: string;
  RCode:             Integer;
  Lst:               TStringList;
  Expected:          string;
begin
  if not ToolchainAvailable then
  begin
    Ignore('qbe or RTL not built');
    Exit;
  end;
  Path := ProjectRoot + 'tests/phase3_milestone.pas';
  if not FileExists(Path) then
  begin
    Ignore('phase3_milestone.pas not found at ' + Path);
    Exit;
  end;
  Lst := TStringList.Create;
  try
    Lst.LoadFromFile(Path);
    Src := Lst.Text;
  finally
    Lst.Free;
  end;
  AssertTrue('compile+run milestone', CompileAndRun(Src, Output, RCode, []));
  AssertEquals('milestone exit code', 0, RCode);
  Expected :=
    'list.count=5'             + LE +
    'list[0]=10'               + LE +
    'list[4]=50'               + LE +
    'count_after_delete=4'     + LE +
    'list[1]_after_delete=30'  + LE +
    'dict.count=4'             + LE +
    'beta=2'                   + LE +
    'has_gamma=1'              + LE +
    'beta_after_update=99'     + LE +
    'count_after_remove=3'     + LE +
    'has_alpha_after_remove=0' + LE;
  AssertEquals('milestone stdout', Expected, Output);
end;

procedure TE2ETests.TestRun_Phase3Milestone_Valgrind;
var
  Path, Src, Log: string;
  Lst:            TStringList;
  Dummy:          string;
  OK:             Boolean;
begin
  if not ToolchainAvailable then
  begin
    Ignore('qbe or RTL not built');
    Exit;
  end;
  if RunProc('valgrind', ['--version'], Dummy, True) <> 0 then
  begin
    Ignore('valgrind not installed');
    Exit;
  end;
  Path := ProjectRoot + 'tests/phase3_milestone.pas';
  if not FileExists(Path) then
  begin
    Ignore('phase3_milestone.pas not found');
    Exit;
  end;
  Lst := TStringList.Create;
  try
    Lst.LoadFromFile(Path);
    Src := Lst.Text;
  finally
    Lst.Free;
  end;
  OK := RunUnderValgrind(Src, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output — exit nonzero)';
    Fail('phase3 milestone has leaks or errors:' + LE + Log);
  end;
end;

{ ------------------------------------------------------------------ }
{ String operation e2e tests                                          }
{ ------------------------------------------------------------------ }

const
  SrcStringLength =
    'program P;'                + LineEnding +
    'var s: string;'            + LineEnding +
    'var n: Integer;'           + LineEnding +
    'begin'                     + LineEnding +
    '  s := ''hello'';'         + LineEnding +
    '  n := Length(s);'         + LineEnding +
    '  WriteLn(n)'              + LineEnding +
    'end.';

  SrcStringPos =
    'program P;'                       + LineEnding +
    'var s, sub: string;'              + LineEnding +
    'var n: Integer;'                  + LineEnding +
    'begin'                            + LineEnding +
    '  s   := ''hello world'';'        + LineEnding +
    '  sub := ''world'';'              + LineEnding +
    '  n   := Pos(sub, s);'            + LineEnding +
    '  WriteLn(n)'                     + LineEnding +
    'end.';

  SrcStringCopy =
    'program P;'                       + LineEnding +
    'var s, t: string;'                + LineEnding +
    'begin'                            + LineEnding +
    '  s := ''hello'';'                + LineEnding +
    '  t := Copy(s, 2, 3);'            + LineEnding +
    '  WriteLn(t)'                     + LineEnding +
    'end.';

  SrcStringUpperCase =
    'program P;'               + LineEnding +
    'var s, t: string;'        + LineEnding +
    'begin'                    + LineEnding +
    '  s := ''hello'';'        + LineEnding +
    '  t := UpperCase(s);'     + LineEnding +
    '  WriteLn(t)'             + LineEnding +
    'end.';

  SrcStringSameText =
    'program P;'                       + LineEnding +
    'var s, t: string;'                + LineEnding +
    'var b: Boolean;'                  + LineEnding +
    'begin'                            + LineEnding +
    '  s := ''Hello'';'                + LineEnding +
    '  t := ''hello'';'                + LineEnding +
    '  b := SameText(s, t);'           + LineEnding +
    '  WriteLn(b)'                     + LineEnding +
    'end.';

  SrcStringIntToStr =
    'program P;'                + LineEnding +
    'var n: Integer;'           + LineEnding +
    'var s: string;'            + LineEnding +
    'begin'                     + LineEnding +
    '  n := 42;'                + LineEnding +
    '  s := IntToStr(n);'       + LineEnding +
    '  WriteLn(s)'              + LineEnding +
    'end.';

  SrcStringStrToInt =
    'program P;'                + LineEnding +
    'var s: string;'            + LineEnding +
    'var n: Integer;'           + LineEnding +
    'begin'                     + LineEnding +
    '  s := ''123'';'           + LineEnding +
    '  n := StrToInt(s);'       + LineEnding +
    '  WriteLn(n)'              + LineEnding +
    'end.';

procedure TE2ETests.TestRun_StringOps_Length;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringLength, Output, RCode, []));
  AssertEquals('Length(''hello'') = 5', '5', Trim(Output));
end;

procedure TE2ETests.TestRun_StringOps_Pos;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringPos, Output, RCode, []));
  AssertEquals('Pos(''world'', ''hello world'') = 7', '7', Trim(Output));
end;

procedure TE2ETests.TestRun_StringOps_Copy;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringCopy, Output, RCode, []));
  AssertEquals('Copy(''hello'', 2, 3) = ''ell''', 'ell', Trim(Output));
end;

procedure TE2ETests.TestRun_StringOps_UpperCase;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringUpperCase, Output, RCode, []));
  AssertEquals('UpperCase(''hello'') = ''HELLO''', 'HELLO', Trim(Output));
end;

procedure TE2ETests.TestRun_StringOps_SameText;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringSameText, Output, RCode, []));
  AssertEquals('SameText(''Hello'', ''hello'') = True (1)', '1', Trim(Output));
end;

procedure TE2ETests.TestRun_StringOps_IntToStr;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringIntToStr, Output, RCode, []));
  AssertEquals('IntToStr(42) = ''42''', '42', Trim(Output));
end;

procedure TE2ETests.TestRun_StringOps_StrToInt;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringStrToInt, Output, RCode, []));
  AssertEquals('StrToInt(''123'') = 123', '123', Trim(Output));
end;

const
  SrcStringStrToIntHex =
    'program P;'                                  + LineEnding +
    'var n: Integer;'                             + LineEnding +
    'begin'                                       + LineEnding +
    '  n := StrToInt(''$FF'');'                   + LineEnding +
    '  WriteLn(n)'                                + LineEnding +
    'end.';

  SrcStringCopyMaxIntCount =
    'program P;'                                  + LineEnding +
    'var s: string;'                              + LineEnding +
    'begin'                                       + LineEnding +
    '  s := Copy(''^Integer'', 2, MaxInt);'       + LineEnding +
    '  WriteLn(s)'                                + LineEnding +
    'end.';

procedure TE2ETests.TestRun_StringOps_StrToInt_Hex;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringStrToIntHex, Output, RCode, []));
  AssertEquals('StrToInt(''$FF'') = 255', '255', Trim(Output));
end;

procedure TE2ETests.TestRun_StringOps_Copy_MaxIntCount;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringCopyMaxIntCount, Output, RCode, []));
  AssertEquals('Copy(''^Integer'', 2, MaxInt) = ''Integer''', 'Integer', Trim(Output));
end;

const
  SrcInt64PositiveAboveInt32 =
    'program P;'                                  + LineEnding +
    'var v: Int64;'                               + LineEnding +
    'begin'                                       + LineEnding +
    '  v := 1000000000;'                          + LineEnding +
    '  v := v + v + 166136261;'                   + LineEnding +
    '  if v < 0 then WriteLn(''neg'')'            + LineEnding +
    '          else WriteLn(''pos'');'            + LineEnding +
    '  WriteLn(IntToStr(v))'                      + LineEnding +
    'end.';

procedure TE2ETests.TestRun_Int64_PositiveAboveInt32_FormatsCorrectly;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInt64PositiveAboveInt32, Output, RCode, []));
  AssertEquals('Int64=2166136261 compares as positive and formats correctly',
    'pos' + LineEnding + '2166136261', Trim(Output));
end;

const
  SrcFormatIntArg =
    'program P;'                           + LineEnding +
    'var n: Integer;'                      + LineEnding +
    'var s: string;'                       + LineEnding +
    'begin'                                + LineEnding +
    '  n := 42;'                           + LineEnding +
    '  s := Format(''val=%d'', n);'        + LineEnding +
    '  WriteLn(s)'                         + LineEnding +
    'end.';

  SrcFormatStrArg =
    'program P;'                           + LineEnding +
    'var t: string;'                       + LineEnding +
    'var s: string;'                       + LineEnding +
    'begin'                                + LineEnding +
    '  t := ''world'';'                    + LineEnding +
    '  s := Format(''hello %s'', t);'      + LineEnding +
    '  WriteLn(s)'                         + LineEnding +
    'end.';

  SrcFormatMixedArgs =
    'program P;'                                 + LineEnding +
    'var name: string;'                          + LineEnding +
    'var age: Integer;'                          + LineEnding +
    'var s: string;'                             + LineEnding +
    'begin'                                      + LineEnding +
    '  name := ''Alice'';'                       + LineEnding +
    '  age  := 30;'                              + LineEnding +
    '  s := Format(''%s=%d'', name, age);'       + LineEnding +
    '  WriteLn(s)'                               + LineEnding +
    'end.';

procedure TE2ETests.TestRun_StringOps_Format_IntArg;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcFormatIntArg, Output, RCode, []));
  AssertEquals('Format int arg', 'val=42', Trim(Output));
end;

procedure TE2ETests.TestRun_StringOps_Format_StrArg;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcFormatStrArg, Output, RCode, []));
  AssertEquals('Format str arg', 'hello world', Trim(Output));
end;

procedure TE2ETests.TestRun_StringOps_Format_MixedArgs;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcFormatMixedArgs, Output, RCode, []));
  AssertEquals('Format mixed args', 'Alice=30', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Collections e2e tests                                               }
{ ------------------------------------------------------------------ }

const
  SrcTObjectListBase2 =
    'type'                                                             + LineEnding +
    '  TObjectList = class'                                            + LineEnding +
    '    FData:     ^Pointer;'                                         + LineEnding +
    '    FCount:    Integer;'                                          + LineEnding +
    '    FCapacity: Integer;'                                          + LineEnding +
    '    procedure Grow;'                                              + LineEnding +
    '    var OldCap, NewCap: Integer;'                                 + LineEnding +
    '    begin'                                                        + LineEnding +
    '      OldCap := Self.FCapacity;'                                  + LineEnding +
    '      if OldCap = 0 then NewCap := 4'                             + LineEnding +
    '      else NewCap := OldCap * 2;'                                 + LineEnding +
    '      Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(Pointer));' + LineEnding +
    '      Self.FCapacity := NewCap'                                   + LineEnding +
    '    end;'                                                         + LineEnding +
    '    function Add(AObject: Pointer): Integer;'                     + LineEnding +
    '    var Dest: ^Pointer;'                                          + LineEnding +
    '    begin'                                                         + LineEnding +
    '      if Self.FCount = Self.FCapacity then Self.Grow;'            + LineEnding +
    '      Dest        := Self.FData + Self.FCount * SizeOf(Pointer);' + LineEnding +
    '      Dest^       := AObject;'                                    + LineEnding +
    '      Self.FCount := Self.FCount + 1;'                            + LineEnding +
    '      Result      := Self.FCount - 1'                             + LineEnding +
    '    end;'                                                         + LineEnding +
    '    function Get(AIndex: Integer): Pointer;'                      + LineEnding +
    '    var Src: ^Pointer;'                                           + LineEnding +
    '    begin'                                                         + LineEnding +
    '      Src    := Self.FData + AIndex * SizeOf(Pointer);'           + LineEnding +
    '      Result := Src^'                                             + LineEnding +
    '    end;'                                                         + LineEnding +
    '    procedure Delete(AIndex: Integer);'                           + LineEnding +
    '    var I: Integer; Dst, Src: ^Pointer;'                          + LineEnding +
    '    begin'                                                         + LineEnding +
    '      I := AIndex;'                                               + LineEnding +
    '      while I < Self.FCount - 1 do'                               + LineEnding +
    '      begin'                                                       + LineEnding +
    '        Dst  := Self.FData + I * SizeOf(Pointer);'                + LineEnding +
    '        Src  := Self.FData + (I + 1) * SizeOf(Pointer);'          + LineEnding +
    '        Dst^ := Src^;'                                            + LineEnding +
    '        I    := I + 1'                                            + LineEnding +
    '      end;'                                                        + LineEnding +
    '      Self.FCount := Self.FCount - 1'                             + LineEnding +
    '    end;'                                                         + LineEnding +
    '    property Count: Integer read FCount;'                         + LineEnding +
    '  end;'                                                           + LineEnding;

  SrcTObjectListAddGetCount =
    'program P;'                                                       + LineEnding +
    SrcTObjectListBase2 +
    'var'                                                              + LineEnding +
    '  L:  TObjectList;'                                               + LineEnding +
    '  P1, P2: Pointer;'                                               + LineEnding +
    'begin'                                                            + LineEnding +
    '  L  := TObjectList.Create;'                                      + LineEnding +
    '  P1 := GetMem(1);'                                               + LineEnding +
    '  P2 := GetMem(1);'                                               + LineEnding +
    '  L.Add(P1);'                                                     + LineEnding +
    '  L.Add(P2);'                                                     + LineEnding +
    '  L.Add(nil);'                                                    + LineEnding +
    '  WriteLn(L.Count);'                                              + LineEnding +
    '  WriteLn(L.Get(0) = P1);'                                        + LineEnding +
    '  WriteLn(L.Get(1) = P2)'                                         + LineEnding +
    'end.';

  SrcTObjectListDelete =
    'program P;'                                                       + LineEnding +
    SrcTObjectListBase2 +
    'var L: TObjectList;'                                              + LineEnding +
    'begin'                                                            + LineEnding +
    '  L := TObjectList.Create;'                                       + LineEnding +
    '  L.Add(GetMem(1));'                                              + LineEnding +
    '  L.Add(GetMem(1));'                                              + LineEnding +
    '  L.Add(GetMem(1));'                                              + LineEnding +
    '  L.Delete(1);'                                                   + LineEnding +
    '  WriteLn(L.Count)'                                               + LineEnding +
    'end.';

  SrcTStringListBase2 =
    'type'                                                             + LineEnding +
    '  TStringList = class'                                            + LineEnding +
    '    FStrings:  ^string;'                                          + LineEnding +
    '    FObjects:  ^Pointer;'                                         + LineEnding +
    '    FCount:    Integer;'                                          + LineEnding +
    '    FCapacity: Integer;'                                          + LineEnding +
    '    procedure Grow;'                                              + LineEnding +
    '    var OldCap, NewCap: Integer;'                                 + LineEnding +
    '    begin'                                                        + LineEnding +
    '      OldCap := Self.FCapacity;'                                  + LineEnding +
    '      if OldCap = 0 then NewCap := 4'                             + LineEnding +
    '      else NewCap := OldCap * 2;'                                 + LineEnding +
    '      Self.FStrings := ReallocMem(Self.FStrings, NewCap * SizeOf(string));'  + LineEnding +
    '      Self.FObjects := ReallocMem(Self.FObjects, NewCap * SizeOf(Pointer));' + LineEnding +
    '      ZeroMem(Self.FStrings + OldCap * SizeOf(string),'           + LineEnding +
    '              (NewCap - OldCap) * SizeOf(string));'               + LineEnding +
    '      Self.FCapacity := NewCap'                                   + LineEnding +
    '    end;'                                                         + LineEnding +
    '    procedure Destroy;'                                           + LineEnding +
    '    var I: Integer; Ptr: ^string;'                                + LineEnding +
    '    begin'                                                         + LineEnding +
    '      I := 0;'                                                    + LineEnding +
    '      while I < Self.FCount do'                                   + LineEnding +
    '      begin'                                                       + LineEnding +
    '        Ptr  := Self.FStrings + I * SizeOf(string);'              + LineEnding +
    '        Ptr^ := nil;'                                             + LineEnding +
    '        I    := I + 1'                                            + LineEnding +
    '      end;'                                                        + LineEnding +
    '      FreeMem(Self.FStrings);'                                    + LineEnding +
    '      FreeMem(Self.FObjects);'                                    + LineEnding +
    '      Self.FStrings  := nil;'                                     + LineEnding +
    '      Self.FObjects  := nil;'                                     + LineEnding +
    '      Self.FCount    := 0;'                                       + LineEnding +
    '      Self.FCapacity := 0'                                        + LineEnding +
    '    end;'                                                         + LineEnding +
    '    function Add(S: string): Integer;'                            + LineEnding +
    '    var StrP: ^string; ObjP: ^Pointer;'                           + LineEnding +
    '    begin'                                                         + LineEnding +
    '      if Self.FCount = Self.FCapacity then Self.Grow;'            + LineEnding +
    '      StrP        := Self.FStrings + Self.FCount * SizeOf(string);' + LineEnding +
    '      ObjP        := Self.FObjects + Self.FCount * SizeOf(Pointer);' + LineEnding +
    '      StrP^       := S;'                                          + LineEnding +
    '      ObjP^       := nil;'                                        + LineEnding +
    '      Result      := Self.FCount;'                                + LineEnding +
    '      Self.FCount := Self.FCount + 1'                             + LineEnding +
    '    end;'                                                         + LineEnding +
    '    function Get(AIndex: Integer): string;'                       + LineEnding +
    '    var Ptr: ^string;'                                            + LineEnding +
    '    begin'                                                         + LineEnding +
    '      Ptr    := Self.FStrings + AIndex * SizeOf(string);'         + LineEnding +
    '      Result := Ptr^'                                             + LineEnding +
    '    end;'                                                         + LineEnding +
    '    function Find(S: string; var Index: Integer): Boolean;'      + LineEnding +
    '    var Lo, Hi, Mid, Cmp: Integer; Ptr: ^string; MStr: string;'  + LineEnding +
    '    begin'                                                         + LineEnding +
    '      Lo := 0; Hi := Self.FCount - 1;'                            + LineEnding +
    '      while Lo <= Hi do'                                          + LineEnding +
    '      begin'                                                       + LineEnding +
    '        Mid  := (Lo + Hi) div 2;'                                 + LineEnding +
    '        Ptr  := Self.FStrings + Mid * SizeOf(string);'            + LineEnding +
    '        MStr := Ptr^;'                                            + LineEnding +
    '        Cmp  := CompareText(S, MStr);'                            + LineEnding +
    '        if Cmp = 0 then'                                          + LineEnding +
    '        begin'                                                     + LineEnding +
    '          Index := Mid; Result := True; Exit'                     + LineEnding +
    '        end'                                                       + LineEnding +
    '        else if Cmp < 0 then Hi := Mid - 1'                       + LineEnding +
    '        else Lo := Mid + 1'                                        + LineEnding +
    '      end;'                                                        + LineEnding +
    '      Index := Lo; Result := False'                               + LineEnding +
    '    end;'                                                         + LineEnding +
    '    property Count: Integer read FCount;'                         + LineEnding +
    '  end;'                                                           + LineEnding;

  SrcTStringListAddGet =
    'program P;'                                                       + LineEnding +
    SrcTStringListBase2 +
    'var'                                                              + LineEnding +
    '  L: TStringList;'                                                + LineEnding +
    'begin'                                                            + LineEnding +
    '  L := TStringList.Create;'                                       + LineEnding +
    '  L.Add(''hello'');'                                               + LineEnding +
    '  L.Add(''world'');'                                               + LineEnding +
    '  WriteLn(L.Count);'                                              + LineEnding +
    '  WriteLn(L.Get(0));'                                             + LineEnding +
    '  WriteLn(L.Get(1))'                                              + LineEnding +
    'end.';

  SrcTStringListFindSorted =
    'program P;'                                                       + LineEnding +
    SrcTStringListBase2 +
    'var'                                                              + LineEnding +
    '  L: TStringList;'                                                + LineEnding +
    '  Idx: Integer;'                                                  + LineEnding +
    '  Found: Boolean;'                                                + LineEnding +
    'begin'                                                            + LineEnding +
    '  L := TStringList.Create;'                                       + LineEnding +
    '  L.Add(''alpha'');'                                               + LineEnding +
    '  L.Add(''beta'');'                                                + LineEnding +
    '  L.Add(''gamma'');'                                               + LineEnding +
    '  Found := L.Find(''beta'', Idx);'                                 + LineEnding +
    '  WriteLn(Found);'                                                + LineEnding +
    '  WriteLn(Idx);'                                                  + LineEnding +
    '  Found := L.Find(''delta'', Idx);'                                + LineEnding +
    '  WriteLn(Found)'                                                 + LineEnding +
    'end.';

  { Combined program: both classes in a single type section }
  SrcCollectionsValgrind =
    'program P;'                                                                   + LineEnding +
    'type'                                                                         + LineEnding +
    '  TObjectList = class'                                                        + LineEnding +
    '    FData: ^Pointer; FCount: Integer; FCapacity: Integer;'                    + LineEnding +
    '    procedure Grow;'                                                          + LineEnding +
    '    var OldCap, NewCap: Integer;'                                             + LineEnding +
    '    begin'                                                                    + LineEnding +
    '      OldCap := Self.FCapacity;'                                              + LineEnding +
    '      if OldCap = 0 then NewCap := 4 else NewCap := OldCap * 2;'             + LineEnding +
    '      Self.FData := ReallocMem(Self.FData, NewCap * SizeOf(Pointer));'        + LineEnding +
    '      Self.FCapacity := NewCap'                                               + LineEnding +
    '    end;'                                                                     + LineEnding +
    '    function Add(AObject: Pointer): Integer;'                                 + LineEnding +
    '    var Dest: ^Pointer;'                                                      + LineEnding +
    '    begin'                                                                    + LineEnding +
    '      if Self.FCount = Self.FCapacity then Self.Grow;'                        + LineEnding +
    '      Dest := Self.FData + Self.FCount * SizeOf(Pointer);'                    + LineEnding +
    '      Dest^ := AObject;'                                                      + LineEnding +
    '      Self.FCount := Self.FCount + 1;'                                        + LineEnding +
    '      Result := Self.FCount - 1'                                              + LineEnding +
    '    end;'                                                                     + LineEnding +
    '    procedure Destroy;'                                                       + LineEnding +
    '    begin'                                                                    + LineEnding +
    '      FreeMem(Self.FData);'                                                   + LineEnding +
    '      Self.FData := nil; Self.FCount := 0; Self.FCapacity := 0'               + LineEnding +
    '    end;'                                                                     + LineEnding +
    '    property Count: Integer read FCount;'                                     + LineEnding +
    '  end;'                                                                       + LineEnding +
    '  TStringList = class'                                                        + LineEnding +
    '    FStrings: ^string; FObjects: ^Pointer;'                                   + LineEnding +
    '    FCount: Integer; FCapacity: Integer;'                                     + LineEnding +
    '    procedure Grow;'                                                          + LineEnding +
    '    var OldCap, NewCap: Integer;'                                             + LineEnding +
    '    begin'                                                                    + LineEnding +
    '      OldCap := Self.FCapacity;'                                              + LineEnding +
    '      if OldCap = 0 then NewCap := 4 else NewCap := OldCap * 2;'             + LineEnding +
    '      Self.FStrings := ReallocMem(Self.FStrings, NewCap * SizeOf(string));'   + LineEnding +
    '      Self.FObjects := ReallocMem(Self.FObjects, NewCap * SizeOf(Pointer));'  + LineEnding +
    '      ZeroMem(Self.FStrings + OldCap * SizeOf(string),'                       + LineEnding +
    '              (NewCap - OldCap) * SizeOf(string));'                           + LineEnding +
    '      Self.FCapacity := NewCap'                                               + LineEnding +
    '    end;'                                                                     + LineEnding +
    '    procedure Destroy;'                                                       + LineEnding +
    '    var I: Integer; Ptr: ^string;'                                            + LineEnding +
    '    begin'                                                                    + LineEnding +
    '      I := 0;'                                                                + LineEnding +
    '      while I < Self.FCount do'                                               + LineEnding +
    '      begin'                                                                  + LineEnding +
    '        Ptr := Self.FStrings + I * SizeOf(string); Ptr^ := nil; I := I + 1'  + LineEnding +
    '      end;'                                                                   + LineEnding +
    '      FreeMem(Self.FStrings); FreeMem(Self.FObjects);'                        + LineEnding +
    '      Self.FStrings := nil; Self.FObjects := nil;'                            + LineEnding +
    '      Self.FCount := 0; Self.FCapacity := 0'                                 + LineEnding +
    '    end;'                                                                     + LineEnding +
    '    function Add(S: string): Integer;'                                        + LineEnding +
    '    var StrP: ^string; ObjP: ^Pointer;'                                       + LineEnding +
    '    begin'                                                                    + LineEnding +
    '      if Self.FCount = Self.FCapacity then Self.Grow;'                        + LineEnding +
    '      StrP := Self.FStrings + Self.FCount * SizeOf(string);'                  + LineEnding +
    '      ObjP := Self.FObjects + Self.FCount * SizeOf(Pointer);'                 + LineEnding +
    '      StrP^ := S; ObjP^ := nil;'                                             + LineEnding +
    '      Result := Self.FCount; Self.FCount := Self.FCount + 1'                  + LineEnding +
    '    end;'                                                                     + LineEnding +
    '    function Get(AIndex: Integer): string;'                                   + LineEnding +
    '    var Ptr: ^string;'                                                        + LineEnding +
    '    begin'                                                                    + LineEnding +
    '      Ptr := Self.FStrings + AIndex * SizeOf(string); Result := Ptr^'         + LineEnding +
    '    end;'                                                                     + LineEnding +
    '    property Count: Integer read FCount;'                                     + LineEnding +
    '  end;'                                                                       + LineEnding +
    'var OL: TObjectList; SL: TStringList;'                                        + LineEnding +
    'begin'                                                                        + LineEnding +
    '  OL := TObjectList.Create;'                                                  + LineEnding +
    '  OL.Add(nil); OL.Add(nil);'                                                  + LineEnding +
    '  SL := TStringList.Create;'                                                  + LineEnding +
    '  SL.Add(''hello''); SL.Add(''world'');'                                       + LineEnding +
    '  WriteLn(OL.Count);'                                                         + LineEnding +
    '  WriteLn(SL.Get(0))'                                                         + LineEnding +
    'end.';

procedure TE2ETests.TestRun_TObjectList_AddGetCount;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTObjectListAddGetCount, Output, RCode, []));
  AssertEquals('count=3', '3', Trim(Copy(Output, 1, Pos(LineEnding, Output) - 1)));
end;

procedure TE2ETests.TestRun_TObjectList_Delete;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTObjectListDelete, Output, RCode, []));
  AssertEquals('count after delete=2', '2', Trim(Output));
end;

procedure TE2ETests.TestRun_TStringList_AddGet;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTStringListAddGet, Output, RCode, []));
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('count=2',   '2',     Lines[0]);
    AssertEquals('get(0)',    'hello', Lines[1]);
    AssertEquals('get(1)',    'world', Lines[2]);
  finally
    Lines.Free;
  end;
end;

procedure TE2ETests.TestRun_TStringList_Find_Sorted;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTStringListFindSorted, Output, RCode, []));
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('found=1 (true)',  '1', Lines[0]);
    AssertEquals('idx=1',           '1', Lines[1]);
    AssertEquals('not found=0',     '0', Lines[2]);
  finally
    Lines.Free;
  end;
end;

procedure TE2ETests.TestRun_Collections_Valgrind;
var
  OK:  Boolean;
  Log: string;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  if RunProc('valgrind', ['--version'], Log, True) <> 0 then
  begin
    Ignore('valgrind not installed');
    Exit;
  end;
  OK := RunUnderValgrind(SrcCollectionsValgrind, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('Collections Valgrind check failed:' + LineEnding + Log);
  end;
end;

{ ------------------------------------------------------------------ }
{ Self-hosting e2e tests                                              }
{ ------------------------------------------------------------------ }

const
  SrcParamStrPrint =
    'program P;'                                      + LineEnding +
    'begin'                                           + LineEnding +
    '  WriteLn(ParamStr(1))'                          + LineEnding +
    'end.';

  SrcParamCountPrint =
    'program P;'                                      + LineEnding +
    'begin'                                           + LineEnding +
    '  WriteLn(ParamCount)'                           + LineEnding +
    'end.';

  SrcReadWriteFile =
    'program P;'                                      + LineEnding +
    'var S: string;'                                  + LineEnding +
    'begin'                                           + LineEnding +
    '  WriteFile(ParamStr(1), ''hello file'');'        + LineEnding +
    '  S := ReadFile(ParamStr(1));'                   + LineEnding +
    '  WriteLn(S)'                                    + LineEnding +
    'end.';

  SrcFileExistsTest =
    'program P;'                                      + LineEnding +
    'begin'                                           + LineEnding +
    '  WriteLn(FileExists(ParamStr(1)));'             + LineEnding +
    '  WriteLn(FileExists(''__no_such_file_xyz__''))' + LineEnding +
    'end.';

  SrcGetEnvVarTest =
    'program P;'                                      + LineEnding +
    'var S: string;'                                  + LineEnding +
    'begin'                                           + LineEnding +
    '  S := GetEnvVar(''BLAISE_TEST_VAR'');'          + LineEnding +
    '  WriteLn(S)'                                    + LineEnding +
    'end.';

  SrcHaltTest =
    'program P;'                                      + LineEnding +
    'begin'                                           + LineEnding +
    '  WriteLn(42);'                                  + LineEnding +
    '  Halt(7)'                                       + LineEnding +
    'end.';

  SrcMultiTypeBlock =
    'program P;'                                      + LineEnding +
    'type'                                            + LineEnding +
    '  TCounter = class'                              + LineEnding +
    '    FN: Integer;'                                + LineEnding +
    '    procedure Inc;'                              + LineEnding +
    '    begin Self.FN := Self.FN + 1 end;'           + LineEnding +
    '    property Value: Integer read FN;'            + LineEnding +
    '  end;'                                          + LineEnding +
    'var N: Integer;'                                 + LineEnding +
    'type'                                            + LineEnding +
    '  TDoubler = class'                              + LineEnding +
    '    function Double(X: Integer): Integer;'       + LineEnding +
    '    begin Result := X * 2 end;'                  + LineEnding +
    '  end;'                                          + LineEnding +
    'var'                                             + LineEnding +
    '  C: TCounter;'                                  + LineEnding +
    '  D: TDoubler;'                                  + LineEnding +
    'begin'                                           + LineEnding +
    '  C := TCounter.Create;'                         + LineEnding +
    '  D := TDoubler.Create;'                         + LineEnding +
    '  C.Inc; C.Inc; C.Inc;'                          + LineEnding +
    '  N := D.Double(C.Value);'                       + LineEnding +
    '  WriteLn(N)'                                    + LineEnding +
    'end.';

procedure TE2ETests.TestRun_ParamStr_PrintsArg;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcParamStrPrint, Output, RCode, ['hello']));
  AssertEquals('ParamStr(1) = hello', 'hello', Trim(Output));
end;

procedure TE2ETests.TestRun_ParamCount_WithArgs;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcParamCountPrint, Output, RCode, ['a', 'b', 'c']));
  AssertEquals('ParamCount = 3', '3', Trim(Output));
end;

procedure TE2ETests.TestRun_ReadWriteFile_RoundTrip;
var
  Output: string;
  RCode:  Integer;
  TmpFile: string;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  TmpFile := GetTempFileName('', 'blaise_rwtest');
  try
    AssertTrue('compile+run',
      CompileAndRun(SrcReadWriteFile, Output, RCode, [TmpFile]));
    AssertEquals('ReadFile content', 'hello file', Trim(Output));
  finally
    if FileExists(TmpFile) then DeleteFile(TmpFile);
  end;
end;

procedure TE2ETests.TestRun_FileExists_TrueAndFalse;
var
  Output: string;
  RCode:  Integer;
  TmpFile: string;
  Lines:   TStringList;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  TmpFile := GetTempFileName('', 'blaise_fe_test');
  { Create the file so it exists }
  with TStringList.Create do begin Add('x'); SaveToFile(TmpFile); Free; end;
  try
    AssertTrue('compile+run',
      CompileAndRun(SrcFileExistsTest, Output, RCode, [TmpFile]));
    Lines := TStringList.Create;
    try
      Lines.Text := Trim(Output);
      AssertEquals('existing file = 1',     '1', Lines[0]);
      AssertEquals('missing file = 0',      '0', Lines[1]);
    finally
      Lines.Free;
    end;
  finally
    if FileExists(TmpFile) then DeleteFile(TmpFile);
  end;
end;

procedure TE2ETests.TestRun_GetEnvVar_Path;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcGetEnvVarTest, Output, RCode, []));
  AssertTrue('GetEnvVar(BLAISE_TEST_VAR) returns empty when unset',
    Trim(Output) = '');
end;

procedure TE2ETests.TestRun_Halt_ExitCode;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  CompileAndRun(SrcHaltTest, Output, RCode, []);
  AssertEquals('WriteLn before Halt', '42', Trim(Output));
  AssertEquals('Halt(7) sets exit code', 7, RCode);
end;

procedure TE2ETests.TestRun_MultiTypeBlock_BothClassesWork;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcMultiTypeBlock, Output, RCode, []));
  AssertEquals('TCounter(3).Double = 6', '6', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ case / enum e2e tests                                               }
{ ------------------------------------------------------------------ }

const
  SrcCaseInt =
    'program P;'                           + LineEnding +
    'var N: Integer;'                      + LineEnding +
    'begin'                                + LineEnding +
    '  N := 2;'                            + LineEnding +
    '  case N of'                          + LineEnding +
    '    1: WriteLn(11);'                  + LineEnding +
    '    2: WriteLn(22);'                  + LineEnding +
    '    3: WriteLn(33)'                   + LineEnding +
    '  end'                                + LineEnding +
    'end.';

  SrcCaseElse =
    'program P;'                           + LineEnding +
    'var N: Integer;'                      + LineEnding +
    'begin'                                + LineEnding +
    '  N := 7;'                            + LineEnding +
    '  case N of'                          + LineEnding +
    '    1: WriteLn(1);'                   + LineEnding +
    '    2: WriteLn(2)'                    + LineEnding +
    '  else'                               + LineEnding +
    '    WriteLn(99)'                      + LineEnding +
    '  end'                                + LineEnding +
    'end.';

  SrcEnumOrdinal =
    'program P;'                                        + LineEnding +
    'type'                                              + LineEnding +
    '  TColor = (cRed, cGreen, cBlue);'                + LineEnding +
    'var C: TColor;'                                    + LineEnding +
    'begin'                                             + LineEnding +
    '  C := cRed;   WriteLn(C);'                       + LineEnding +
    '  C := cGreen; WriteLn(C);'                       + LineEnding +
    '  C := cBlue;  WriteLn(C)'                        + LineEnding +
    'end.';

  SrcEnumCase =
    'program P;'                                        + LineEnding +
    'type'                                              + LineEnding +
    '  TDir = (dNorth, dSouth, dEast, dWest);'         + LineEnding +
    'var D: TDir;'                                      + LineEnding +
    'begin'                                             + LineEnding +
    '  D := dEast;'                                     + LineEnding +
    '  case D of'                                       + LineEnding +
    '    dNorth: WriteLn(0);'                           + LineEnding +
    '    dSouth: WriteLn(1);'                           + LineEnding +
    '    dEast:  WriteLn(2);'                           + LineEnding +
    '    dWest:  WriteLn(3)'                            + LineEnding +
    '  end'                                             + LineEnding +
    'end.';

procedure TE2ETests.TestRun_Case_IntegerBranch;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcCaseInt, Output, RCode, []));
  AssertEquals('case N=2 → 22', '22', Trim(Output));
end;

procedure TE2ETests.TestRun_Case_ElseBranch;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcCaseElse, Output, RCode, []));
  AssertEquals('case N=7 → else → 99', '99', Trim(Output));
end;

procedure TE2ETests.TestRun_Enum_OrdinalValues;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcEnumOrdinal, Output, RCode, []));
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('cRed=0',   '0', Lines[0]);
    AssertEquals('cGreen=1', '1', Lines[1]);
    AssertEquals('cBlue=2',  '2', Lines[2]);
  finally
    Lines.Free;
  end;
end;

procedure TE2ETests.TestRun_Enum_InCase;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcEnumCase, Output, RCode, []));
  AssertEquals('dEast=2', '2', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ File path manipulation (step 11)                                    }
{ ------------------------------------------------------------------ }

const
  SrcChangeFileExtTest =
    'program P;'                                           + LineEnding +
    'begin'                                                + LineEnding +
    '  WriteLn(ChangeFileExt(''test.pas'', ''.bak''));'   + LineEnding +
    '  WriteLn(ChangeFileExt(''noext'', ''.o''));'        + LineEnding +
    '  WriteLn(ChangeFileExt(''a.b.c'', ''''))'           + LineEnding +
    'end.';

  SrcExtractFileNameTest =
    'program P;'                                           + LineEnding +
    'begin'                                                + LineEnding +
    '  WriteLn(ExtractFileName(''/usr/bin/ls''));'         + LineEnding +
    '  WriteLn(ExtractFileName(''ls''))'                   + LineEnding +
    'end.';

  SrcExtractFilePathTest =
    'program P;'                                                      + LineEnding +
    'begin'                                                           + LineEnding +
    '  WriteLn(ExtractFilePath(''/usr/bin/ls''));'                    + LineEnding +
    '  WriteLn(''['' + ExtractFilePath(''ls'') + '']'')'             + LineEnding +
    'end.';

  SrcIncludeTrailingPathDelimiterTest =
    'program P;'                                                    + LineEnding +
    'begin'                                                         + LineEnding +
    '  WriteLn(IncludeTrailingPathDelimiter(''/usr/bin''));'        + LineEnding +
    '  WriteLn(IncludeTrailingPathDelimiter(''/usr/bin/''))'        + LineEnding +
    'end.';

  { Step 8: process built-ins — run 'echo' and capture output }
  SrcProcessBuiltinsCapture =
    'program P;'                                    + LineEnding +
    'var'                                            + LineEnding +
    '  H:     Pointer;'                             + LineEnding +
    '  Output: string;'                             + LineEnding +
    '  Chunk:  string;'                             + LineEnding +
    'begin'                                          + LineEnding +
    '  H := ProcessCreate;'                          + LineEnding +
    '  ProcessSetExe(H, ''echo'');'                  + LineEnding +
    '  ProcessAddArg(H, ''hello from process'');'    + LineEnding +
    '  ProcessExecute(H);'                           + LineEnding +
    '  Output := '''';'                              + LineEnding +
    '  Chunk := ProcessReadOutput(H);'               + LineEnding +
    '  while Chunk <> '''' do'                       + LineEnding +
    '  begin'                                        + LineEnding +
    '    Output := Output + Chunk;'                  + LineEnding +
    '    Chunk := ProcessReadOutput(H)'              + LineEnding +
    '  end;'                                         + LineEnding +
    '  ProcessWaitOnExit(H);'                        + LineEnding +
    '  ProcessFree(H);'                              + LineEnding +
    '  Write(Output)'                                + LineEnding +
    'end.';

  SrcProcessBuiltinsExitCode =
    'program P;'                                    + LineEnding +
    'var'                                            + LineEnding +
    '  H:    Pointer;'                              + LineEnding +
    '  Code: Integer;'                              + LineEnding +
    '  Chunk: string;'                              + LineEnding +
    'begin'                                          + LineEnding +
    '  H := ProcessCreate;'                          + LineEnding +
    '  ProcessSetExe(H, ''true'');'                  + LineEnding +
    '  ProcessExecute(H);'                           + LineEnding +
    '  Chunk := ProcessReadOutput(H);'               + LineEnding +
    '  while Chunk <> '''' do'                       + LineEnding +
    '    Chunk := ProcessReadOutput(H);'             + LineEnding +
    '  ProcessWaitOnExit(H);'                        + LineEnding +
    '  Code := ProcessExitCode(H);'                  + LineEnding +
    '  ProcessFree(H);'                              + LineEnding +
    '  WriteLn(IntToStr(Code))'                      + LineEnding +
    'end.';

procedure TE2ETests.TestRun_ChangeFileExt_ChangesExtension;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcChangeFileExtTest, Output, RCode, []));
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('test.pas→.bak', 'test.bak', Lines[0]);
    AssertEquals('noext→.o',      'noext.o',  Lines[1]);
    AssertEquals('a.b.c→empty',   'a.b',      Lines[2]);
  finally
    Lines.Free;
  end;
end;

procedure TE2ETests.TestRun_ExtractFileName_ReturnsName;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcExtractFileNameTest, Output, RCode, []));
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('/usr/bin/ls → ls', 'ls', Lines[0]);
    AssertEquals('ls → ls',          'ls', Lines[1]);
  finally
    Lines.Free;
  end;
end;

procedure TE2ETests.TestRun_ExtractFilePath_ReturnsDir;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcExtractFilePathTest, Output, RCode, []));
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('/usr/bin/ls → /usr/bin/', '/usr/bin/', Lines[0]);
    AssertEquals('ls → empty',              '[]',        Lines[1]);
  finally
    Lines.Free;
  end;
end;

procedure TE2ETests.TestRun_IncludeTrailingPathDelimiter_AppendsSlash;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIncludeTrailingPathDelimiterTest, Output, RCode, []));
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('/usr/bin → /usr/bin/',   '/usr/bin/', Lines[0]);
    AssertEquals('/usr/bin/ unchanged',    '/usr/bin/', Lines[1]);
  finally
    Lines.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Step 8: process management built-ins                                }
{ ------------------------------------------------------------------ }

procedure TE2ETests.TestRun_ProcessBuiltins_CapturesOutput;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcProcessBuiltinsCapture, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('captured echo output', 'hello from process', Trim(Output));
end;

procedure TE2ETests.TestRun_ProcessBuiltins_ExitCode;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcProcessBuiltinsExitCode, Output, RCode, []));
  AssertEquals('program exit code 0', 0, RCode);
  AssertEquals('true exits with 0', '0', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Typed except handlers — shared source base                         }
{ ------------------------------------------------------------------ }

const
  SrcExcBase2 =
    'program P;'                                      + LineEnding +
    'type'                                            + LineEnding +
    '  Exception = class'                             + LineEnding +
    '    FMessage: string;'                           + LineEnding +
    '    property Message: string read FMessage;'     + LineEnding +
    '  end;'                                          + LineEnding +
    '  EFoo = class(Exception) end;'                  + LineEnding +
    '  EBar = class(EFoo) end;'                       + LineEnding;

  SrcTypedExceptCorrect =
    SrcExcBase2 +
    'var X: Integer;'                                 + LineEnding +
    'begin'                                           + LineEnding +
    '  X := 0;'                                       + LineEnding +
    '  try'                                           + LineEnding +
    '    raise EFoo.Create'                           + LineEnding +
    '  except'                                        + LineEnding +
    '    on E: EFoo do X := 42;'                      + LineEnding +
    '    on E: Exception do X := 1'                   + LineEnding +
    '  end;'                                          + LineEnding +
    '  WriteLn(X)'                                    + LineEnding +
    'end.';

  SrcTypedExceptSubclass =
    SrcExcBase2 +
    'var X: Integer;'                                 + LineEnding +
    'begin'                                           + LineEnding +
    '  X := 0;'                                       + LineEnding +
    '  try'                                           + LineEnding +
    '    raise EBar.Create'                           + LineEnding +
    '  except'                                        + LineEnding +
    '    on E: EFoo do X := 7'                        + LineEnding +
    '  end;'                                          + LineEnding +
    '  WriteLn(X)'                                    + LineEnding +
    'end.';

  SrcTypedExceptElseRun =
    SrcExcBase2 +
    'var X: Integer;'                                 + LineEnding +
    'begin'                                           + LineEnding +
    '  X := 0;'                                       + LineEnding +
    '  try'                                           + LineEnding +
    '    raise EFoo.Create'                           + LineEnding +
    '  except'                                        + LineEnding +
    '    on E: EBar do X := 9'                        + LineEnding +
    '    else X := 5'                                 + LineEnding +
    '  end;'                                          + LineEnding +
    '  WriteLn(X)'                                    + LineEnding +
    'end.';

  SrcTypedExceptBareRaise =
    SrcExcBase2 +
    'var X: Integer;'                                 + LineEnding +
    'begin'                                           + LineEnding +
    '  X := 0;'                                       + LineEnding +
    '  try'                                           + LineEnding +
    '    try'                                         + LineEnding +
    '      raise EFoo.Create'                         + LineEnding +
    '    except'                                      + LineEnding +
    '      on E: EFoo do'                             + LineEnding +
    '      begin'                                     + LineEnding +
    '        X := 1;'                                 + LineEnding +
    '        raise'                                   + LineEnding +
    '      end'                                       + LineEnding +
    '    end'                                         + LineEnding +
    '  except'                                        + LineEnding +
    '    on E: EFoo do X := 2'                        + LineEnding +
    '  end;'                                          + LineEnding +
    '  WriteLn(X)'                                    + LineEnding +
    'end.';

  SrcTypedExceptUnmatched =
    SrcExcBase2 +
    'var X: Integer;'                                 + LineEnding +
    'begin'                                           + LineEnding +
    '  X := 0;'                                       + LineEnding +
    '  try'                                           + LineEnding +
    '    try'                                         + LineEnding +
    '      raise EFoo.Create'                         + LineEnding +
    '    except'                                      + LineEnding +
    '      on E: EBar do X := 9'                      + LineEnding +
    '    end'                                         + LineEnding +
    '  except'                                        + LineEnding +
    '    on E: EFoo do X := 3'                        + LineEnding +
    '  end;'                                          + LineEnding +
    '  WriteLn(X)'                                    + LineEnding +
    'end.';

{ ------------------------------------------------------------------ }
{ Typed except handler — E2E tests                                   }
{ ------------------------------------------------------------------ }

procedure TE2ETests.TestRun_TypedExcept_CorrectHandlerMatched;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTypedExceptCorrect, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('EFoo handler ran', '42', Trim(Output));
end;

procedure TE2ETests.TestRun_TypedExcept_SubclassMatchesParentHandler;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTypedExceptSubclass, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('EBar matches EFoo handler', '7', Trim(Output));
end;

procedure TE2ETests.TestRun_TypedExcept_UnmatchedReraises;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTypedExceptUnmatched, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('unmatched inner re-raises to outer', '3', Trim(Output));
end;

procedure TE2ETests.TestRun_TypedExcept_BareRaisePropagatesToOuter;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTypedExceptBareRaise, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('bare raise propagated to outer handler', '2', Trim(Output));
end;

procedure TE2ETests.TestRun_TypedExcept_ElseBodyRunsWhenNoMatch;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTypedExceptElseRun, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('else body ran when no handler matched', '5', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Built-in TObject.ToString                                           }
{ ------------------------------------------------------------------ }

const
  SrcToStringDefault =
    'program P;'                              + LE +
    'type'                                    + LE +
    '  TFoo = class end;'                     + LE +
    '  TBar = class(TFoo) end;'               + LE +
    'var F: TFoo; B: TBar;'                   + LE +
    'begin'                                   + LE +
    '  F := TFoo.Create;'                     + LE +
    '  WriteLn(F.ToString);'                  + LE +
    '  B := TBar.Create;'                     + LE +
    '  WriteLn(B.ToString)'                   + LE +
    'end.';

  SrcToStringOverride =
    'program P;'                                          + LE +
    'type'                                                + LE +
    '  TFoo = class'                                      + LE +
    '    function ToString: string; override;'            + LE +
    '  end;'                                              + LE +
    '  TBar = class(TFoo)'                                + LE +
    '    function ToString: string; override;'            + LE +
    '  end;'                                              + LE +
    '  function TFoo.ToString: string;'                   + LE +
    '  begin Result := ''foo!'' end;'                     + LE +
    '  function TBar.ToString: string;'                   + LE +
    '  begin Result := ''bar!'' end;'                     + LE +
    'var F: TFoo; B: TFoo;'                               + LE +
    'begin'                                               + LE +
    '  F := TFoo.Create;'                                 + LE +
    '  WriteLn(F.ToString);'                              + LE +
    '  B := TBar.Create;'                                 + LE +
    '  WriteLn(B.ToString)'                               + LE +
    'end.';

  SrcToStringInheritedOverride =
    'program P;'                                          + LE +
    'type'                                                + LE +
    '  TFoo = class'                                      + LE +
    '    function ToString: string; override;'            + LE +
    '  end;'                                              + LE +
    '  TBar = class(TFoo) end;'                           + LE +
    '  function TFoo.ToString: string;'                   + LE +
    '  begin Result := ''foo override'' end;'             + LE +
    'var F: TFoo; B: TFoo;'                               + LE +
    'begin'                                               + LE +
    '  F := TFoo.Create;'                                 + LE +
    '  WriteLn(F.ToString);'                              + LE +
    '  B := TBar.Create;'                                 + LE +
    '  WriteLn(B.ToString)'                               + LE +
    'end.';

procedure TE2ETests.TestRun_ToString_DefaultReturnsClassName;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcToStringDefault, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('default ToString returns class name',
    'TFoo' + LE + 'TBar' + LE, Output);
end;

procedure TE2ETests.TestRun_ToString_OverrideDispatchedVirtually;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcToStringOverride, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('override reached through static base type',
    'foo!' + LE + 'bar!' + LE, Output);
end;

procedure TE2ETests.TestRun_ToString_InheritedOverrideStillReached;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcToStringInheritedOverride, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('inherited override still reached',
    'foo override' + LE + 'foo override' + LE, Output);
end;

{ ------------------------------------------------------------------ }
{ TObject.InheritsFrom                                                }
{ ------------------------------------------------------------------ }

const
  SrcInheritsFromBase =
    'program P;'                          + LineEnding +
    'type TBase = class end;'             + LineEnding +
    'var B: TBase;'                       + LineEnding +
    'begin'                               + LineEnding +
    '  B := TBase.Create;'                + LineEnding +
    '  if B.InheritsFrom(TBase) then'     + LineEnding +
    '    WriteLn(''yes'')'                + LineEnding +
    '  else'                              + LineEnding +
    '    WriteLn(''no'');'                + LineEnding +
    '  B.Free;'                           + LineEnding +
    'end.';

  SrcInheritsFromParent =
    'program P;'                              + LineEnding +
    'type TBase = class end;'                 + LineEnding +
    '     TChild = class(TBase) end;'         + LineEnding +
    'var C: TChild;'                          + LineEnding +
    'begin'                                   + LineEnding +
    '  C := TChild.Create;'                   + LineEnding +
    '  if C.InheritsFrom(TBase) then'         + LineEnding +
    '    WriteLn(''yes'')'                    + LineEnding +
    '  else'                                  + LineEnding +
    '    WriteLn(''no'');'                    + LineEnding +
    '  C.Free;'                               + LineEnding +
    'end.';

  SrcInheritsFromGrandParent =
    'program P;'                                    + LineEnding +
    'type TBase = class end;'                       + LineEnding +
    '     TChild = class(TBase) end;'               + LineEnding +
    '     TGrandChild = class(TChild) end;'         + LineEnding +
    'var G: TGrandChild;'                           + LineEnding +
    'begin'                                         + LineEnding +
    '  G := TGrandChild.Create;'                    + LineEnding +
    '  if G.InheritsFrom(TBase) then'               + LineEnding +
    '    WriteLn(''yes'')'                          + LineEnding +
    '  else'                                        + LineEnding +
    '    WriteLn(''no'');'                          + LineEnding +
    '  G.Free;'                                     + LineEnding +
    'end.';

  SrcInheritsFromUnrelated =
    'program P;'                                  + LineEnding +
    'type TBase = class end;'                     + LineEnding +
    '     TUnrelated = class end;'                + LineEnding +
    'var B: TBase;'                               + LineEnding +
    'begin'                                       + LineEnding +
    '  B := TBase.Create;'                        + LineEnding +
    '  if B.InheritsFrom(TUnrelated) then'        + LineEnding +
    '    WriteLn(''yes'')'                        + LineEnding +
    '  else'                                      + LineEnding +
    '    WriteLn(''no'');'                        + LineEnding +
    '  B.Free;'                                   + LineEnding +
    'end.';

  SrcInheritsFromReverse =
    'program P;'                              + LineEnding +
    'type TBase = class end;'                 + LineEnding +
    '     TChild = class(TBase) end;'         + LineEnding +
    'var B: TBase;'                           + LineEnding +
    'begin'                                   + LineEnding +
    '  B := TBase.Create;'                    + LineEnding +
    '  if B.InheritsFrom(TChild) then'        + LineEnding +
    '    WriteLn(''yes'')'                    + LineEnding +
    '  else'                                  + LineEnding +
    '    WriteLn(''no'');'                    + LineEnding +
    '  B.Free;'                               + LineEnding +
    'end.';

  SrcInheritsFromClassType =
    'program P;'                                  + LineEnding +
    'type TBase = class end;'                     + LineEnding +
    '     TChild = class(TBase) end;'             + LineEnding +
    'var C: TChild;'                              + LineEnding +
    '    CT: Pointer;'                            + LineEnding +
    'begin'                                       + LineEnding +
    '  C := TChild.Create;'                       + LineEnding +
    '  CT := C.ClassType;'                        + LineEnding +
    '  if CT.InheritsFrom(TBase) then'            + LineEnding +
    '    WriteLn(''yes'')'                        + LineEnding +
    '  else'                                      + LineEnding +
    '    WriteLn(''no'');'                        + LineEnding +
    '  C.Free;'                                   + LineEnding +
    'end.';

procedure TE2ETests.TestRun_InheritsFrom_SameClass_ReturnsTrue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritsFromBase, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('same class returns true', 'yes' + LE, Output);
end;

procedure TE2ETests.TestRun_InheritsFrom_Parent_ReturnsTrue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritsFromParent, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('child inherits from parent', 'yes' + LE, Output);
end;

procedure TE2ETests.TestRun_InheritsFrom_GrandParent_ReturnsTrue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritsFromGrandParent, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('grandchild inherits from base', 'yes' + LE, Output);
end;

procedure TE2ETests.TestRun_InheritsFrom_Unrelated_ReturnsFalse;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritsFromUnrelated, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('unrelated class returns false', 'no' + LE, Output);
end;

procedure TE2ETests.TestRun_InheritsFrom_Reverse_ReturnsFalse;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritsFromReverse, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('parent does not inherit from child', 'no' + LE, Output);
end;

procedure TE2ETests.TestRun_InheritsFrom_ClassType_Works;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritsFromClassType, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('ClassType.InheritsFrom works', 'yes' + LE, Output);
end;

{ ================================================================== }
{ OS utility builtins (step 2a)                                      }
{ ================================================================== }

const
  SrcGetProcessID =
    'program P;'                                      + LineEnding +
    'begin'                                           + LineEnding +
    '  WriteLn(GetProcessID)'                         + LineEnding +
    'end.';

  SrcDirectoryExists =
    'program P;'                                      + LineEnding +
    'begin'                                           + LineEnding +
    '  WriteLn(DirectoryExists(''/tmp''));'            + LineEnding +
    '  WriteLn(DirectoryExists(''/__no_such_dir__''))' + LineEnding +
    'end.';

  SrcGetTempDir =
    'program P;'                                      + LineEnding +
    'begin'                                           + LineEnding +
    '  WriteLn(GetTempDir)'                           + LineEnding +
    'end.';

  SrcForceDirectories =
    'program P;'                                      + LineEnding +
    'var Dir: string;'                                + LineEnding +
    'begin'                                           + LineEnding +
    '  Dir := ParamStr(1);'                           + LineEnding +
    '  WriteLn(ForceDirectories(Dir));'               + LineEnding +
    '  WriteLn(DirectoryExists(Dir))'                 + LineEnding +
    'end.';

  SrcSleepTest =
    'program P;'                                      + LineEnding +
    'begin'                                           + LineEnding +
    '  Sleep(1);'                                     + LineEnding +
    '  WriteLn(''ok'')'                               + LineEnding +
    'end.';

procedure TE2ETests.TestRun_GetProcessID_ReturnsNonZero;
var
  Output: string;
  RCode:  Integer;
  PID:    Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcGetProcessID, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  PID := StrToIntDef(Trim(Output), 0);
  AssertTrue('PID > 0', PID > 0);
end;

procedure TE2ETests.TestRun_DirectoryExists_TrueAndFalse;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcDirectoryExists, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('/tmp exists = 1',           '1', Lines[0]);
    AssertEquals('missing dir = 0',           '0', Lines[1]);
  finally
    Lines.Free;
  end;
end;

procedure TE2ETests.TestRun_GetTempDir_ReturnsPath;
var
  Output: string;
  RCode:  Integer;
  Dir:    string;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcGetTempDir, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  Dir := Trim(Output);
  AssertTrue('dir is non-empty', Length(Dir) > 0);
  AssertTrue('dir ends with /', Dir[Length(Dir)] = '/');
end;

procedure TE2ETests.TestRun_ForceDirectories_CreatesTree;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
  Dir:    string;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  Dir := IncludeTrailingPathDelimiter(GetTempDir) +
         'blaise_test_' + IntToStr(GetProcessID) + '/a/b/c';
  try
    AssertTrue('compile+run',
      CompileAndRun(SrcForceDirectories, Output, RCode, [Dir]));
    AssertEquals('exit code 0', 0, RCode);
    Lines := TStringList.Create;
    try
      Lines.Text := Trim(Output);
      AssertEquals('ForceDirectories returned 1', '1', Lines[0]);
      AssertEquals('DirectoryExists returned 1',  '1', Lines[1]);
    finally
      Lines.Free;
    end;
  finally
    { Clean up the test directory tree }
    RemoveDir(Dir);
    RemoveDir(ExtractFilePath(ExcludeTrailingPathDelimiter(Dir)));
    RemoveDir(ExtractFilePath(ExcludeTrailingPathDelimiter(
      ExtractFilePath(ExcludeTrailingPathDelimiter(Dir)))));
    RemoveDir(ExtractFilePath(ExcludeTrailingPathDelimiter(
      ExtractFilePath(ExcludeTrailingPathDelimiter(
        ExtractFilePath(ExcludeTrailingPathDelimiter(Dir)))))));
  end;
end;

procedure TE2ETests.TestRun_Sleep_DoesNotCrash;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcSleepTest, Output, RCode, []));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output is ok', 'ok', Trim(Output));
end;

initialization
  RegisterTest(TE2ETests);

end.
