{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
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
    procedure TestRun_StringOps_Format_IntArg;
    procedure TestRun_StringOps_Format_StrArg;
    procedure TestRun_StringOps_Format_MixedArgs;
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

{ Runs a process, captures stdout into AStdout, returns exit code.
  Returns -1 if the process could not be started. }
function RunProc(const AExe:      string;
                 const AArgs:     array of string;
                 out   AStdout:   string;
                 AInheritStdErr:  Boolean): Integer;
var
  Proc:    TProcess;
  Ss:      TStringStream;
  Buf:     array[0..4095] of Byte;
  N:       LongInt;
  I:       Integer;
begin
  Proc := TProcess.Create(nil);
  Ss   := TStringStream.Create('');
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
    while Proc.Running or (Proc.Output.NumBytesAvailable > 0) do
    begin
      if Proc.Output.NumBytesAvailable > 0 then
      begin
        N := Proc.Output.Read(Buf, SizeOf(Buf));
        if N > 0 then Ss.Write(Buf, N);
      end
      else
        Sleep(2);
    end;
    Result  := Proc.ExitCode;
    AStdout := Ss.DataString;
  finally
    Ss.Free;
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
    Fail('qbe failed (exit ' + IntToStr(Rc) + '): ' + ToolOut + sLineBreak +
         'IR file preserved at: ' + IRFile);
    Exit;
  end;

  Rc := RunProc('cc', ['-o', BinFile, AsmFile, FRTL], ToolOut, True);
  if Rc <> 0 then
  begin
    Fail('cc failed (exit ' + IntToStr(Rc) + '): ' + ToolOut + sLineBreak +
         'IR: ' + IRFile + sLineBreak + 'asm: ' + AsmFile);
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

initialization
  RegisterTest(TE2ETests);

end.
