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
  uLexer, uParser, uAST, uSemantic, uCodeGenQBE, uUnitLoader,
  uCodeGen, blaise.codegen.target, blaise.codegen.native;

type
  { Code-generation backends an e2e test can run against.  The native backend
    currently supports a subset of the language (integer family, control flow,
    direct calls); a test opts into it explicitly (AssertRunsOnBoth, or
    CompileAndRunOn for one backend), so QBE-only features stay QBE-only until
    native catches up. }
  TBackend = (beQBE, beNative);

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
    { Run ASrc on BOTH backends and assert each produces AExpectedOut on stdout
      and AExpectedCode as its exit code.  Failures name the offending backend,
      so a native-only regression is unambiguous.  This is the primary helper
      for tests the native backend supports: write the expected output once,
      exercise both code generators.  (A set-of-backends parameter would read
      better but Blaise does not yet accept a set literal as a set-typed
      argument — see bugs.txt; two booleans avoid that.) }
    procedure AssertRunsOnBoth(const ASrc, AExpectedOut: string;
                            AExpectedCode: Integer);
    { Per-backend worker for AssertRunsOnBoth (separate method because Blaise
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
    { Compile a program that USES a user unit written to the scratch dir, so
      the unit (not the program) is the compilation unit.  Exercises the
      multi-unit codegen path.  AUnitName is the unit identifier; AUnitSrc and
      ASrc are full sources.  RTL + stdlib units are also on the search path. }
    function  CompileAndRunWithUnit(const AUnitName, AUnitSrc, ASrc: string;
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

procedure TE2ETestCase.AssertRunsOnBoth(const ASrc, AExpectedOut: string;
                                        AExpectedCode: Integer);
begin
  Self.AssertRunsOnOne(beQBE, 'qbe', ASrc, AExpectedOut, AExpectedCode);
  Self.AssertRunsOnOne(beNative, 'native', ASrc, AExpectedOut, AExpectedCode)
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
begin
  Result := CompileAndRunWithRTLDebug(ASrc, AStdout, AExitCode, False);
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
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  CG:          TCodeGenQBE;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  IR:          string;
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

  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil; CG := nil;
  Loader := nil; Units := nil; SearchPaths := nil;
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
    CG := TCodeGenQBE.Create();
    CG.SetDebugMode(ADebugMode);
    CG.SetSymbolTable(Prog.SymbolTable);
    for I := 0 to Units.Count - 1 do
      CG.AppendUnit(TUnit(Units.Items[I]));
    CG.AppendProgram(Prog);
    IR := CG.GetOutput()
  finally
    CG.Free(); Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free()
  end;

  WriteFile(IRFile, IR);
  Rc := RunProc(FQBE, ['-o', AsmFile, IRFile], ToolOut);
  if Rc <> 0 then begin AStdout := 'qbe failed: ' + ToolOut; AExitCode := Rc; Exit end;
  Rc := RunProc('cc', ['-o', BinFile, AsmFile, FRTL, '-lm', '-lpthread'], ToolOut);
  if Rc <> 0 then begin AStdout := 'cc failed: ' + ToolOut; AExitCode := Rc; Exit end;
  AExitCode := RunProcNoArgs(BinFile, AStdout);
  Result := True
end;

function TE2ETestCase.CompileAndRunWithUnit(const AUnitName, AUnitSrc, ASrc: string;
                                            out AStdout: string;
                                            out AExitCode: Integer): Boolean;
var
  Lexer:       TLexer;
  Parser:      TParser;
  Prog:        TProgram;
  Semantic:    TSemanticAnalyser;
  CG:          TCodeGenQBE;
  Loader:      TUnitLoader;
  Units:       TObjectList;
  SearchPaths: TStringList;
  IR:          string;
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

  Lexer := nil; Parser := nil; Prog := nil; Semantic := nil; CG := nil;
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
    CG := TCodeGenQBE.Create();
    CG.SetSymbolTable(Prog.SymbolTable);
    for I := 0 to Units.Count - 1 do
      CG.AppendUnit(TUnit(Units.Items[I]));
    CG.AppendProgram(Prog);
    IR := CG.GetOutput()
  finally
    CG.Free(); Semantic.Free();
    Units.Free(); Loader.Free(); SearchPaths.Free();
    Prog.Free(); Parser.Free(); Lexer.Free()
  end;

  WriteFile(IRFile, IR);
  Rc := RunProc(FQBE, ['-o', AsmFile, IRFile], ToolOut);
  if Rc <> 0 then begin AStdout := 'qbe failed: ' + ToolOut; AExitCode := Rc; Exit end;
  Rc := RunProc('cc', ['-o', BinFile, AsmFile, FRTL, '-lm', '-lpthread'], ToolOut);
  if Rc <> 0 then begin AStdout := 'cc failed: ' + ToolOut; AExitCode := Rc; Exit end;
  AExitCode := RunProcNoArgs(BinFile, AStdout);
  Result := True
end;

end.
