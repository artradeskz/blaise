{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.base;

{ Shared base class for all E2E test suites.
  Provides toolchain setup, scratch directory management, and two
  CompileAndRun variants:
    - CompileAndRun        : single-program, no RTL units (inline classes)
    - CompileAndRunWithRTL : multi-unit, loads RTL units via TUnitLoader }

interface

uses
  classes, sysutils, process, contnrs, blaise.testing,
  uLexer, uParser, uAST, uSemantic, blaise.codegen.qbe, uUnitLoader,
  blaise.codegen, blaise.codegen.target, blaise.codegen.native;

type
  TBackend = (beQBE, beNative);
  TBackends = set of TBackend;

const
  AllBackends: TBackends = [beQBE, beNative];

function BackendName(ABackend: TBackend): string;

type
  TE2ETestCase = class(TTestCase)
  private
    FQBE:         string;
    FRTL:         string;
    FRTLUnitPath: string;
    FStdlibUnitPath: string;
    FScratch:     string;
    FCounter:     Integer;
    function  ProjectRoot: string;
    function  RunProc(const AExe: string; const AArgs: array of string;
                      out AStdout: string): Integer;
    function  RunProcNoArgs(const AExe: string; out AStdout: string): Integer;
  protected
    function  ToolchainAvailable(): Boolean;
    function  ValgrindAvailable(): Boolean;
    procedure SetUpScratch(const ADirName: string);
    procedure SetUp; override;
    function  CompileAndRun(const ASrc: string;
                            out AStdout: string;
                            out AExitCode: Integer): Boolean; overload;
    function  CompileAndRun(const ASrc: string;
                            out AStdout: string;
                            out AExitCode: Integer;
                            const AExtraArgs: array of string): Boolean; overload;
    { Native-backend equivalent of CompileAndRun: lowers the program to
      assembly via TCodeGenNative (no QBE), links with cc, and runs.  The
      correctness oracle is parity with the QBE path on the same source. }
    function  CompileAndRunNative(const ASrc: string;
                            out AStdout: string;
                            out AExitCode: Integer): Boolean;
    { Compile and run ASrc on the chosen backend.  Shared front-end (lex,
      parse, semantic); the backend selects QBE-text+qbe or direct native
      assembly.  CompileAndRun and CompileAndRunNative both delegate here. }
    function  CompileAndRunOn(ABackend: TBackend; const ASrc: string;
                            out AStdout: string;
                            out AExitCode: Integer): Boolean;
    { Run ASrc on every backend in AllBackends and assert each produces
      AExpectedOut / AExpectedCode.  When a new backend is added to AllBackends,
      all callers pick it up automatically. }
    procedure AssertRunsOnAll(const ASrc, AExpectedOut: string;
                            AExpectedCode: Integer);
    { Run ASrc on a specific set of backends only.  Use when a test should
      exercise fewer than AllBackends (e.g. a feature not yet ported). }
    procedure AssertRunsOn(ABackends: TBackends; const ASrc, AExpectedOut: string;
                            AExpectedCode: Integer);
    { RTL/stdlib equivalents of AssertRunsOn*: compile+run ASrc against the RTL
      and stdlib (multi-unit, TUnitLoader) on every backend and assert parity.
      Use these in RTL/stdlib suites so native gets the same coverage as QBE. }
    procedure AssertRTLRunsOnAll(const ASrc, AExpectedOut: string;
                            AExpectedCode: Integer);
    procedure AssertRTLRunsOn(ABackends: TBackends; const ASrc, AExpectedOut: string;
                            AExpectedCode: Integer);
    procedure AssertRTLRunsOnOne(ABackend: TBackend; const AName, ASrc,
                            AExpectedOut: string; AExpectedCode: Integer);
    { Convenience: RTL/stdlib compile+run on a specific backend (debug off). }
    function  CompileAndRunWithRTLOn(ABackend: TBackend; const ASrc: string;
                            out AStdout: string;
                            out AExitCode: Integer): Boolean;
    { QBE-only RTL compile+run.  Escape hatch for the rare case where native
      has a known, documented gap that is tracked separately — keeps the rest of
      a suite dual-backend while not blocking on the one failing construct.  Add
      a comment at each call site naming the tracked bug. }
    function  CompileAndRunWithRTLQBEOnly(const ASrc: string;
                            out AStdout: string;
                            out AExitCode: Integer): Boolean;
    { Per-backend worker used by AssertRunsOn (separate method because Blaise
      has no nested procedures). }
    procedure AssertRunsOnOne(ABackend: TBackend; const AName, ASrc,
                            AExpectedOut: string; AExpectedCode: Integer);
    function  RunUnderValgrind(const ASrc: string; out ALog: string): Boolean;
    function  CompileAndRunWithRTL(const ASrc: string;
                                   out AStdout: string;
                                   out AExitCode: Integer): Boolean; overload;
    function  CompileAndRunWithRTL(const ASrc: string;
                                   out AStdout: string;
                                   out AExitCode: Integer;
                                   ADebugMode: Boolean): Boolean; overload;
    function  CompileAndRunWithRTLDebug(const ASrc: string;
                                   out AStdout: string;
                                   out AExitCode: Integer;
                                   ADebugMode: Boolean): Boolean;
    function  CompileAndRunWithRTLDebugOn(ABackend: TBackend;
                                   const ASrc: string;
                                   out AStdout: string;
                                   out AExitCode: Integer;
                                   ADebugMode: Boolean): Boolean;
    { Compile a program that USES a user unit written to the scratch dir, so
      the unit (not the program) is the compilation unit.  Exercises the
      multi-unit codegen path.  AUnitName is the unit identifier; AUnitSrc and
      ASrc are full sources.  RTL + stdlib units are also on the search path. }
    function  CompileAndRunWithUnit(const AUnitName, AUnitSrc, ASrc: string;
                                   out AStdout: string;
                                   out AExitCode: Integer): Boolean;
    { Backend-parameterised multi-unit compile+run: lowers the unit(s) + program
      via the QBE or native backend (whole-program model: AppendUnit per
      dependency, then AppendProgram), then links and runs.  The native path
      exercises TX86_64Backend.EmitUnit / AppendProgram. }
    function  CompileAndRunWithUnitOn(ABackend: TBackend;
                                   const AUnitName, AUnitSrc, ASrc: string;
                                   out AStdout: string;
                                   out AExitCode: Integer): Boolean;
    { Native convenience over the multi-unit path. }
    function  CompileAndRunWithUnitNative(const AUnitName, AUnitSrc, ASrc: string;
                                   out AStdout: string;
                                   out AExitCode: Integer): Boolean;
  end;

implementation

{ ------------------------------------------------------------------ }
{ TE2ETestCase                                                         }
{ ------------------------------------------------------------------ }

function TE2ETestCase.ProjectRoot: string;
var
  Dir, Parent: string;
  Steps: Integer;
begin
  Result := GetEnvironmentVariable('BLAISE_PROJECT_ROOT');
  if Result <> '' then begin Result := IncludeTrailingPathDelimiter(Result); Exit end;
  Dir := GetCurrentDir();
  for Steps := 0 to 5 do
  begin
    if DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'vendor/qbe') and
       DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'runtime') then
    begin
      Result := IncludeTrailingPathDelimiter(Dir);
      Exit
    end;
    Parent := ExtractFileDir(Dir);
    if (Parent = '') or (Parent = Dir) then Break;
    Dir := Parent
  end;
  Result := IncludeTrailingPathDelimiter(GetCurrentDir())
end;

function TE2ETestCase.ToolchainAvailable(): Boolean;
begin
  Result := FileExists(FQBE) and FileExists(FRTL)
end;

function TE2ETestCase.ValgrindAvailable(): Boolean;
var Dummy: string;
begin
  Result := RunProc('valgrind', ['--version'], Dummy) = 0
end;

procedure TE2ETestCase.SetUp;
begin
  { Subclasses must call SetUpScratch to set FScratch and FCounter }
  inherited SetUp();
  FCounter := 0;
  FQBE := GetEnvironmentVariable('BLAISE_QBE');
  if FQBE = '' then
    FQBE := ProjectRoot() + 'vendor/qbe/qbe';
  FRTL := GetEnvironmentVariable('BLAISE_RTL');
  if FRTL = '' then
    FRTL := ProjectRoot() + 'runtime/target/blaise_rtl.a';
  FRTLUnitPath := ProjectRoot() + 'runtime/src/main/pascal';
  FStdlibUnitPath := ProjectRoot() + 'stdlib/src/main/pascal'
end;

procedure TE2ETestCase.SetUpScratch(const ADirName: string);
begin
  FScratch := ProjectRoot() + ADirName;
  ForceDirectories(FScratch);
  FCounter := 0
end;

function TE2ETestCase.RunProc(const AExe: string;
                              const AArgs: array of string;
                              out AStdout: string): Integer;
var
  Proc:  TProcess;
  I:     Integer;
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
      AStdout := AStdout + Chunk
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode
  finally
    Proc.Free()
  end
end;

function TE2ETestCase.RunProcNoArgs(const AExe: string;
                                    out AStdout: string): Integer;
var
  Proc:  TProcess;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    Proc.Execute();
    AStdout := '';
    repeat
      Chunk := Proc.ReadOutput();
      AStdout := AStdout + Chunk
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode
  finally
    Proc.Free()
  end
end;

function TE2ETestCase.CompileAndRunOn(ABackend: TBackend; const ASrc: string;
                                     out AStdout: string;
                                     out AExitCode: Integer): Boolean;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  QCG:      TCodeGenQBE;
  NCG:      TCodeGenNative;
  CG:       ICodeGen;
  Emitted:  string;       { QBE IR text, or native assembly text }
  IRFile:   string;
  AsmFile:  string;
  BinFile:  string;
  ToolOut:  string;
  Rc:       Integer;
begin
  Result := False;
  Inc(FCounter);
  IRFile  := FScratch + '/t' + IntToStr(FCounter) + '.ssa';
  AsmFile := FScratch + '/t' + IntToStr(FCounter) + '.s';
  BinFile := FScratch + '/t' + IntToStr(FCounter);

  { Shared front-end; the codegen object differs per backend.  QBE and native
    both implement ICodeGen, but TCodeGenQBE is freed manually (not ARC-held
    via the interface here) while the native object is ARC-managed. }
  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  QCG := nil; CG := nil;
  try
    Lexer    := TLexer.Create(ASrc);
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    if ABackend = beNative then
    begin
      NCG := TCodeGenNative.Create();
      NCG.SetTarget(HostTarget());
      CG  := NCG;            { ARC-managed; released at scope exit }
      CG.Generate(Prog);
      Emitted := CG.GetOutput()
    end
    else
    begin
      QCG := TCodeGenQBE.Create();
      QCG.Generate(Prog);
      Emitted := QCG.GetOutput()
    end
  finally
    QCG.Free();               { nil for the native path — Free(nil) is a no-op }
    { CG (ICodeGen) freed by ARC; do not Free. }
    Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free()
  end;

  if ABackend = beNative then
  begin
    { Native backend emits assembly directly — no QBE step. }
    WriteFile(AsmFile, Emitted)
  end
  else
  begin
    WriteFile(IRFile, Emitted);
    Rc := RunProc(FQBE, ['-o', AsmFile, IRFile], ToolOut);
    if Rc <> 0 then begin AStdout := 'qbe failed: ' + ToolOut; AExitCode := Rc; Exit end
  end;
  Rc := RunProc('cc', ['-o', BinFile, AsmFile, FRTL, '-lm', '-lpthread'], ToolOut);
  if Rc <> 0 then begin AStdout := 'cc failed: ' + ToolOut; AExitCode := Rc; Exit end;
  AExitCode := RunProcNoArgs(BinFile, AStdout);
  Result := True
end;

function TE2ETestCase.CompileAndRun(const ASrc: string;
                                    out AStdout: string;
                                    out AExitCode: Integer): Boolean;
begin
  { QBE-only.  A blanket dual-backend flip here is unsafe: some inline e2e
    programs print non-deterministic values (e.g. GetProcessID) that cannot be
    compared across two separate process runs, and several genuine native gaps
    (StrToDouble/DoubleToStr formatting, InheritsFrom/ToString builtins, class
    const-array, interface-field-assignment-RHS) are still open — see bugs.txt.
    Suites whose programs ARE deterministic and native-clean use AssertRunsOnAll
    instead, which runs both backends.  As the native gaps close, more inline
    suites can migrate to AssertRunsOnAll. }
  Result := Self.CompileAndRunOn(beQBE, ASrc, AStdout, AExitCode)
end;

function TE2ETestCase.CompileAndRunNative(const ASrc: string;
                                          out AStdout: string;
                                          out AExitCode: Integer): Boolean;
begin
  Result := Self.CompileAndRunOn(beNative, ASrc, AStdout, AExitCode)
end;

{ Run ASrc on one backend and assert its stdout/exit match the expected
  values, tagging the failure message with the backend name. }
procedure TE2ETestCase.AssertRunsOnOne(ABackend: TBackend; const AName, ASrc,
                                       AExpectedOut: string; AExpectedCode: Integer);
var
  Output: string;
  RCode:  Integer;
begin
  AssertTrue('[' + AName + '] compile+run',
    Self.CompileAndRunOn(ABackend, ASrc, Output, RCode));
  if RCode <> AExpectedCode then
    AssertEquals('[' + AName + '] exit code (stdout: ' + Output + ')',
      AExpectedCode, RCode)
  else
    AssertEquals('[' + AName + '] exit code', AExpectedCode, RCode);
  AssertEquals('[' + AName + '] stdout', AExpectedOut, Output)
end;

function BackendName(ABackend: TBackend): string;
begin
  case ABackend of
    beQBE:    Result := 'qbe';
    beNative: Result := 'native'
  else
    Result := 'unknown'
  end
end;

procedure TE2ETestCase.AssertRunsOnAll(const ASrc, AExpectedOut: string;
                                       AExpectedCode: Integer);
begin
  Self.AssertRunsOn(AllBackends, ASrc, AExpectedOut, AExpectedCode)
end;

procedure TE2ETestCase.AssertRunsOn(ABackends: TBackends; const ASrc, AExpectedOut: string;
                                    AExpectedCode: Integer);
var
  BE: TBackend;
begin
  for BE := Low(TBackend) to High(TBackend) do
    if BE in ABackends then
      Self.AssertRunsOnOne(BE, BackendName(BE), ASrc, AExpectedOut, AExpectedCode)
end;

function TE2ETestCase.CompileAndRun(const ASrc: string;
                                    out AStdout: string;
                                    out AExitCode: Integer;
                                    const AExtraArgs: array of string): Boolean;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  CG:       TCodeGenQBE;
  IR:       string;
  IRFile:   string;
  AsmFile:  string;
  BinFile:  string;
  ToolOut:  string;
  Rc:       Integer;
begin
  Result := False;
  Inc(FCounter);
  IRFile  := FScratch + '/t' + IntToStr(FCounter) + '.ssa';
  AsmFile := FScratch + '/t' + IntToStr(FCounter) + '.s';
  BinFile := FScratch + '/t' + IntToStr(FCounter);

  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil; CG := nil;
  try
    Lexer    := TLexer.Create(ASrc);
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    CG       := TCodeGenQBE.Create();
    CG.Generate(Prog);
    IR       := CG.GetOutput()
  finally
    CG.Free(); Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free()
  end;

  WriteFile(IRFile, IR);
  Rc := RunProc(FQBE, ['-o', AsmFile, IRFile], ToolOut);
  if Rc <> 0 then begin AStdout := 'qbe failed: ' + ToolOut; AExitCode := Rc; Exit end;
  Rc := RunProc('cc', ['-o', BinFile, AsmFile, FRTL, '-lm', '-lpthread'], ToolOut);
  if Rc <> 0 then begin AStdout := 'cc failed: ' + ToolOut; AExitCode := Rc; Exit end;
  AExitCode := RunProc(BinFile, AExtraArgs, AStdout);
  Result := True
end;

function TE2ETestCase.RunUnderValgrind(const ASrc: string; out ALog: string): Boolean;
var
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  CG:       TCodeGenQBE;
  IR:       string;
  IRFile:   string;
  AsmFile:  string;
  BinFile:  string;
  ToolOut:  string;
  Rc:       Integer;
begin
  Result := False;
  ALog   := '';
  Inc(FCounter);
  IRFile  := FScratch + '/vg' + IntToStr(FCounter) + '.ssa';
  AsmFile := FScratch + '/vg' + IntToStr(FCounter) + '.s';
  BinFile := FScratch + '/vg' + IntToStr(FCounter);

  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil; CG := nil;
  try
    Lexer    := TLexer.Create(ASrc);
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    Semantic.Analyse(Prog);
    CG       := TCodeGenQBE.Create();
    CG.Generate(Prog);
    IR       := CG.GetOutput()
  finally
    CG.Free(); Semantic.Free(); Prog.Free(); Parser.Free(); Lexer.Free()
  end;

  WriteFile(IRFile, IR);
  Rc := RunProc(FQBE, ['-o', AsmFile, IRFile], ToolOut);
  if Rc <> 0 then Exit;
  Rc := RunProc('cc', ['-o', BinFile, AsmFile, FRTL, '-lm', '-lpthread'], ToolOut);
  if Rc <> 0 then Exit;

  Rc := RunProc('valgrind',
    ['--error-exitcode=99', '--leak-check=full', '--quiet', BinFile], ALog);
  Result := Rc = 0
end;

function TE2ETestCase.CompileAndRunWithRTL(const ASrc: string;
                                           out AStdout: string;
                                           out AExitCode: Integer): Boolean;
var
  NOut: string;
  NCode: Integer;
  NOk: Boolean;
begin
  { Run on BOTH backends and require parity.  Historically this helper was
    QBE-only, which left every RTL/stdlib suite that uses it unvalidated on the
    native backend.  We now compile+run the program with QBE first (its result
    is returned so the caller's existing assertions still pin correctness), then
    repeat on native and assert the native stdout/exit code match QBE.  A native
    codegen or RTL-ABI divergence therefore fails the test with a clear message
    rather than going unnoticed.  Debug-mode and *On variants stay single-backend
    for callers that need a specific backend (e.g. leak checks). }
  Result := Self.CompileAndRunWithRTLDebugOn(beQBE, ASrc, AStdout, AExitCode,
                                             False);
  if not Result then Exit;
  NOk := Self.CompileAndRunWithRTLDebugOn(beNative, ASrc, NOut, NCode, False);
  AssertTrue('[native] RTL compile+run', NOk);
  if NCode <> AExitCode then
    AssertEquals('[native] exit code parity with qbe (native stdout: ' +
      NOut + ')', AExitCode, NCode)
  else
    AssertEquals('[native] exit code parity with qbe', AExitCode, NCode);
  AssertEquals('[native] stdout parity with qbe', AStdout, NOut);
end;

function TE2ETestCase.CompileAndRunWithRTL(const ASrc: string;
                                           out AStdout: string;
                                           out AExitCode: Integer;
                                           ADebugMode: Boolean): Boolean;
begin
  Result := CompileAndRunWithRTLDebug(ASrc, AStdout, AExitCode, ADebugMode);
end;

function TE2ETestCase.CompileAndRunWithRTLDebug(const ASrc: string;
                                           out AStdout: string;
                                           out AExitCode: Integer;
                                           ADebugMode: Boolean): Boolean;
begin
  { QBE-backed convenience; the full dual-backend implementation lives in
    CompileAndRunWithRTLDebugOn.  Kept so existing QBE-only callers behave
    exactly as before. }
  Result := Self.CompileAndRunWithRTLDebugOn(beQBE, ASrc, AStdout, AExitCode,
                                             ADebugMode)
end;

function TE2ETestCase.CompileAndRunWithRTLOn(ABackend: TBackend;
                                           const ASrc: string;
                                           out AStdout: string;
                                           out AExitCode: Integer): Boolean;
begin
  Result := Self.CompileAndRunWithRTLDebugOn(ABackend, ASrc, AStdout, AExitCode,
                                             False)
end;

function TE2ETestCase.CompileAndRunWithRTLQBEOnly(const ASrc: string;
                                           out AStdout: string;
                                           out AExitCode: Integer): Boolean;
begin
  Result := Self.CompileAndRunWithRTLDebugOn(beQBE, ASrc, AStdout, AExitCode,
                                             False)
end;

procedure TE2ETestCase.AssertRTLRunsOnAll(const ASrc, AExpectedOut: string;
                                          AExpectedCode: Integer);
begin
  Self.AssertRTLRunsOn(AllBackends, ASrc, AExpectedOut, AExpectedCode)
end;

procedure TE2ETestCase.AssertRTLRunsOn(ABackends: TBackends;
                                       const ASrc, AExpectedOut: string;
                                       AExpectedCode: Integer);
var
  BE: TBackend;
begin
  for BE := Low(TBackend) to High(TBackend) do
    if BE in ABackends then
      Self.AssertRTLRunsOnOne(BE, BackendName(BE), ASrc, AExpectedOut,
                              AExpectedCode)
end;

procedure TE2ETestCase.AssertRTLRunsOnOne(ABackend: TBackend;
                                          const AName, ASrc, AExpectedOut: string;
                                          AExpectedCode: Integer);
var
  Output: string;
  RCode:  Integer;
begin
  AssertTrue('[' + AName + '] compile+run (RTL)',
    Self.CompileAndRunWithRTLOn(ABackend, ASrc, Output, RCode));
  if RCode <> AExpectedCode then
    AssertEquals('[' + AName + '] exit code (stdout: ' + Output + ')',
      AExpectedCode, RCode)
  else
    AssertEquals('[' + AName + '] exit code', AExpectedCode, RCode);
  AssertEquals('[' + AName + '] stdout', AExpectedOut, Output)
end;

function TE2ETestCase.CompileAndRunWithRTLDebugOn(ABackend: TBackend;
                                         const ASrc: string;
                                         out AStdout: string;
                                         out AExitCode: Integer;
                                         ADebugMode: Boolean): Boolean;
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  QCG:         TCodeGenQBE;
  NCG:         TCodeGenNative;
  CG:          ICodeGen;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  Emitted:     string;
  IRFile:      string;
  AsmFile:     string;
  BinFile:     string;
  ToolOut:     string;
  Rc:          Integer;
  I:           Integer;
begin
  Result := False;
  Inc(FCounter);
  IRFile  := FScratch + '/t' + IntToStr(FCounter) + '.ssa';
  AsmFile := FScratch + '/t' + IntToStr(FCounter) + '.s';
  BinFile := FScratch + '/t' + IntToStr(FCounter);

  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  QCG := nil; CG := nil; Loader := nil; Units := nil; SearchPaths := nil;
  try
    Lexer    := TLexer.Create(ASrc);
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units  := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
    if ABackend = beNative then
    begin
      NCG := TCodeGenNative.Create();
      NCG.SetTarget(HostTarget());
      CG  := NCG;
      CG.SetDebugMode(ADebugMode);
      CG.SetSymbolTable(Prog.SymbolTable);
      for I := 0 to Units.Count - 1 do
        CG.AppendUnit(TUnit(Units.Items[I]));
      CG.AppendProgram(Prog);
      Emitted := CG.GetOutput()
    end
    else
    begin
      QCG := TCodeGenQBE.Create();
      QCG.SetDebugMode(ADebugMode);
      QCG.SetSymbolTable(Prog.SymbolTable);
      for I := 0 to Units.Count - 1 do
        QCG.AppendUnit(TUnit(Units.Items[I]));
      QCG.AppendProgram(Prog);
      Emitted := QCG.GetOutput()
    end
  finally
    QCG.Free(); Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free()
  end;

  if ABackend = beNative then
  begin
    WriteFile(AsmFile, Emitted)
  end
  else
  begin
    WriteFile(IRFile, Emitted);
    Rc := RunProc(FQBE, ['-o', AsmFile, IRFile], ToolOut);
    if Rc <> 0 then begin AStdout := 'qbe failed: ' + ToolOut; AExitCode := Rc; Exit end
  end;
  Rc := RunProc('cc', ['-o', BinFile, AsmFile, FRTL, '-lm', '-lpthread'], ToolOut);
  if Rc <> 0 then begin AStdout := 'cc failed: ' + ToolOut; AExitCode := Rc; Exit end;
  AExitCode := RunProcNoArgs(BinFile, AStdout);
  Result := True
end;

function TE2ETestCase.CompileAndRunWithUnit(const AUnitName, AUnitSrc, ASrc: string;
                                            out AStdout: string;
                                            out AExitCode: Integer): Boolean;
begin
  Result := Self.CompileAndRunWithUnitOn(beQBE, AUnitName, AUnitSrc, ASrc,
                                         AStdout, AExitCode)
end;

function TE2ETestCase.CompileAndRunWithUnitNative(const AUnitName, AUnitSrc, ASrc: string;
                                            out AStdout: string;
                                            out AExitCode: Integer): Boolean;
begin
  Result := Self.CompileAndRunWithUnitOn(beNative, AUnitName, AUnitSrc, ASrc,
                                         AStdout, AExitCode)
end;

function TE2ETestCase.CompileAndRunWithUnitOn(ABackend: TBackend;
                                            const AUnitName, AUnitSrc, ASrc: string;
                                            out AStdout: string;
                                            out AExitCode: Integer): Boolean;
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  QCG:         TCodeGenQBE;
  NCG:         TCodeGenNative;
  CG:          ICodeGen;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  Emitted:     string;       { QBE IR text, or native assembly text }
  IRFile, AsmFile, BinFile, ToolOut, UnitFile: string;
  Rc, I:       Integer;
begin
  Result := False;
  Inc(FCounter);
  IRFile   := FScratch + '/t' + IntToStr(FCounter) + '.ssa';
  AsmFile  := FScratch + '/t' + IntToStr(FCounter) + '.s';
  BinFile  := FScratch + '/t' + IntToStr(FCounter);
  UnitFile := FScratch + '/' + AUnitName + '.pas';

  { Write the user unit to the scratch dir so the unit loader resolves it. }
  WriteFile(UnitFile, AUnitSrc);

  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil;
  QCG := nil; CG := nil;
  Loader := nil; Units := nil; SearchPaths := nil;
  try
    Lexer    := TLexer.Create(ASrc);
    Parser   := TParser.Create(Lexer);
    Prog     := Parser.Parse();
    Semantic := TSemanticAnalyser.Create();
    SearchPaths := TStringList.Create();
    SearchPaths.Add(FScratch);            { the written user unit }
    SearchPaths.Add(FRTLUnitPath);
    SearchPaths.Add(FStdlibUnitPath);
    Loader := TUnitLoader.Create(SearchPaths);
    Units  := Loader.LoadAll(Prog.UsedUnits);
    for I := 0 to Units.Count - 1 do
      Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
    Semantic.Analyse(Prog);
    if ABackend = beNative then
    begin
      NCG := TCodeGenNative.Create();
      NCG.SetTarget(HostTarget());
      CG  := NCG;            { ARC-managed; released at scope exit }
    end
    else
    begin
      QCG := TCodeGenQBE.Create();
      CG  := QCG
    end;
    CG.SetSymbolTable(Prog.SymbolTable);
    for I := 0 to Units.Count - 1 do
      CG.AppendUnit(TUnit(Units.Items[I]));
    CG.AppendProgram(Prog);
    Emitted := CG.GetOutput()
  finally
    if ABackend <> beNative then QCG.Free();
    { CG (ICodeGen) for native is freed by ARC; do not Free. }
    Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free()
  end;

  if ABackend = beNative then
    WriteFile(AsmFile, Emitted)
  else
  begin
    WriteFile(IRFile, Emitted);
    Rc := RunProc(FQBE, ['-o', AsmFile, IRFile], ToolOut);
    if Rc <> 0 then begin AStdout := 'qbe failed: ' + ToolOut; AExitCode := Rc; Exit end
  end;
  Rc := RunProc('cc', ['-o', BinFile, AsmFile, FRTL, '-lm', '-lpthread'], ToolOut);
  if Rc <> 0 then begin AStdout := 'cc failed: ' + ToolOut; AExitCode := Rc; Exit end;
  AExitCode := RunProcNoArgs(BinFile, AStdout);
  Result := True
end;

end.
