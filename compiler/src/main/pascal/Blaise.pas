{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

program Blaise;

{ Blaise Compiler — main entry point.

  Usage:
    blaise --source Hello.pas --output hello
    blaise --source Hello.pas --emit-ir
    blaise --source Hello.pas --output hello --target linux-x86_64

  Generates QBE IR, then shells out to qbe + cc to produce the final
  binary. With --emit-ir, the IR is written to stdout and no binary
  is produced.
}

uses
  SysUtils, Classes, Process, contnrs,
  uLexer, uParser, uAST, uSemantic, uCodeGen, uCodeGenQBE,
  blaise.codegen.target, blaise.codegen.native, uToolchain,
  uUnitLoader, uDebugOPDF, uUnitInterface, uSemanticExport, uSemanticImport,
  uUnitInterfaceIO, uIfaceObject,
  uStrCompat, uConfig;

const
  Version = '0.10.0-dev';
  CompilerName = 'Blaise';

procedure PrintUsage;
begin
  WriteLn('Blaise Compiler v', Version);
  WriteLn('Copyright (c) 2026 Graeme Geldenhuys');
  WriteLn('');
  WriteLn('Usage:');
  WriteLn('  blaise --source <file.pas> --output <binary>');
  WriteLn('  blaise --source <file.pas> --emit-ir');
  WriteLn('');
  WriteLn('Flags:');
  WriteLn('  --source <path>     Pascal source file');
  WriteLn('  --output <path>     Output binary path');
  WriteLn('  --unit-path <dir>   Add directory to unit search path (repeatable)');
  WriteLn('  --backend <id>      qbe (default) | native');
  WriteLn('  --target <os>-<cpu> linux-x86_64 (default), linux-i386, linux-arm64,');
  WriteLn('                      freebsd-x86_64, windows-x86_64, macos-arm64');
  WriteLn('  --emit-ir           Print QBE IR to stdout and exit');
  WriteLn('  --emit-asm          Print native assembly to stdout (requires --backend native)');
  WriteLn('  --emit-iface <dir>  Write each unit''s TUnitInterface as <dir>/<unit>.bif');
  WriteLn('  --skip-dep-codegen  Omit dep unit bodies from emitted IR (separate-compilation path)');
  WriteLn('  --incremental       Compile each dep to its own .o as a side effect');
  WriteLn('  --unit-cache <dir>  Where --incremental writes per-unit .o (default: alongside output)');
  WriteLn('  --debug             Enable runtime memory leak reporting on exit');
  WriteLn('  --debug-opdf        Emit OPDF debug info (.opdf.s companion file)');
  WriteLn('');
  WriteLn('Configuration:');
  WriteLn('  Unit search paths can also be set in blaise.cfg (one unit-path=<dir>');
  WriteLn('  per line). Searched next to the binary, then ~/.blaise.cfg.');
end;

{ Handle FPC -i query flags: -iV (version), -iTP (target processor), -iTO (target OS).
  PasBuild probes the compiler with these before invoking a full compile. }
procedure HandleFPCInfoQuery(const AArg: string);
var
  Query: string;
begin
  Query := Copy(AArg, 3, MaxInt);  { strip leading '-i' }
  if Query = 'V' then
  begin
    WriteLn('3.2.2');
    Halt(0);
  end
  else if Query = 'TP' then
  begin
    WriteLn('x86_64');
    Halt(0);
  end
  else if Query = 'TO' then
  begin
    WriteLn('linux');
    Halt(0);
  end;
  { Unknown -i query — ignore silently }
end;

{ Parse FPC-style arguments emitted by PasBuild when --fpc /path/to/blaise is used.
  Handles: -iV/-iTP/-iTO, -FE<dir>, -Fu<path>, -FU<path>, -o<name>,
           -Mobjfpc, -O<n>, -g, -gl, -CX, -d<define>, and the positional source file. }
function ParseFPCArgs(
  out SourceFile:   string;
  out OutputFile:   string;
  out SearchPaths:  TStringList;
  out OPDFEnabled:  Boolean): Boolean;
var
  I:       Integer;
  Arg:     string;
  OutDir:  string;
  OutName: string;
begin
  Result      := False;
  SourceFile  := '';
  OutputFile  := '';
  OPDFEnabled := False;
  OutDir      := '';
  OutName     := '';
  SearchPaths := TStringList.Create;

  I := 1;
  while I <= ParamCount do
  begin
    Arg := ParamStr(I);

    if StrHead(Arg, 2) = '-i' then
      HandleFPCInfoQuery(Arg)
    else if StrHead(Arg, 3) = '-FE' then
      OutDir := StrCopyTail(Arg, 3)
    else if StrHead(Arg, 3) = '-FU' then
      { unit output directory — ignored }
    else if StrHead(Arg, 3) = '-Fu' then
      SearchPaths.Add(StrCopyTail(Arg, 3))
    else if StrHead(Arg, 2) = '-o' then
      OutName := StrCopyTail(Arg, 2)
    else if StrHead(Arg, 2) = '-M' then
      { mode switch (e.g. -Mobjfpc) — ignored }
    else if StrHead(Arg, 2) = '-O' then
      { optimisation level — ignored }
    else if StrHead(Arg, 2) = '-d' then
      { conditional define — ignored in Phase 1 }
    else if (Arg = '-g') or (Arg = '-gl') then
      OPDFEnabled := True
    else if (Arg = '-CX') or (Arg = '-XX') or (Arg = '-Xs') then
      { other linking flags — ignored }
    else if (Arg = '--help') or (Arg = '-h') then
    begin
      PrintUsage;
      Halt(0);
    end
    else if (Length(Arg) > 0) and (StrAt(Arg, 0) <> Ord('-')) then
    begin
      { Positional argument — the source file }
      if SourceFile = '' then
        SourceFile := Arg;
    end;
    { Any other unrecognised -X flag is silently ignored for forward-compat }

    Inc(I);
  end;

  if SourceFile = '' then
  begin
    WriteLn(StdErr, 'Error: no source file specified');
    SearchPaths.Free;
    Exit;
  end;

  { Build output path from -FE and -o, mirroring FPC behaviour }
  if OutName = '' then
    OutName := ChangeFileExt(ExtractFileName(SourceFile), '');
  if OutDir <> '' then
    OutputFile := IncludeTrailingPathDelimiter(OutDir) + OutName
  else
    OutputFile := OutName;

  Result := True;
end;

{ Returns True when the argument list looks like FPC-style flags (single-dash,
  single-letter prefix) rather than Blaise native (double-dash) flags. }
function IsFPCStyleInvocation: Boolean;
var
  I: Integer;
  Arg: string;
begin
  Result := False;
  for I := 1 to ParamCount do
  begin
    Arg := ParamStr(I);
    if (Length(Arg) >= 2) and (StrAt(Arg, 0) = Ord('-')) and (StrAt(Arg, 1) <> Ord('-')) then
    begin
      Exit(True);
    end;
  end;
end;

function ParseArgs(
  out SourceFile:     string;
  out OutputFile:     string;
  out EmitIR:         Boolean;
  out EmitAsm:        Boolean;
  out OPDFEnabled:    Boolean;
  out DebugMode:      Boolean;
  out UseNative:      Boolean;
  out Target:         TTargetDesc;
  out SearchPaths:    TStringList;
  out SkipDepCodegen: Boolean;
  out EmitIfaceDir:   string;
  out Incremental:    Boolean;
  out UnitCacheDir:   string): Boolean;
var
  I: Integer;
  Arg: string;
begin
  Result         := False;
  SourceFile     := '';
  OutputFile     := '';
  EmitIR         := False;
  EmitAsm        := False;
  OPDFEnabled    := False;
  DebugMode      := False;
  UseNative      := False;
  Target         := HostTarget;
  SkipDepCodegen := False;
  EmitIfaceDir   := '';
  Incremental    := False;
  UnitCacheDir   := '';
  SearchPaths    := TStringList.Create;

  I := 1;
  while I <= ParamCount do
  begin
    Arg := ParamStr(I);
    if (Arg = '--source') and (I < ParamCount) then
    begin
      Inc(I);
      SourceFile := ParamStr(I);
    end
    else if (Arg = '--output') and (I < ParamCount) then
    begin
      Inc(I);
      OutputFile := ParamStr(I);
    end
    else if (Arg = '--unit-path') and (I < ParamCount) then
    begin
      Inc(I);
      SearchPaths.Add(ParamStr(I));
    end
    else if Arg = '--skip-dep-codegen' then
      { Omit dep unit bodies from the main codegen pass — every cross-
        unit call becomes an extern reference.  Caller is responsible
        for linking pre-built dep object files at link time. }
      SkipDepCodegen := True
    else if (Arg = '--emit-iface') and (I < ParamCount) then
    begin
      { Write each compiled unit's TUnitInterface as <Dir>/<Unit>.bif
        for later use as a separate-compilation cache. }
      Inc(I);
      EmitIfaceDir := ParamStr(I);
    end
    else if Arg = '--incremental' then
      { Phase 6c-H: compile each source-loaded dep to a stand-alone
        .o (with embedded iface) as a side effect of the program
        build.  Implies --skip-dep-codegen for the main IR (deps
        are not inlined; they're linked from the per-unit .o
        files instead).  Next compile auto-discovers the .o's
        and skips parsing the .pas entirely. }
      Incremental := True
    else if (Arg = '--unit-cache') and (I < ParamCount) then
    begin
      Inc(I);
      UnitCacheDir := ParamStr(I);
    end
    else if Arg = '--emit-ir' then
      EmitIR := True
    else if Arg = '--emit-asm' then
      EmitAsm := True
    else if Arg = '--debug' then
      DebugMode := True
    else if Arg = '--debug-opdf' then
      OPDFEnabled := True
    else if (Arg = '--backend') and (I < ParamCount) then
    begin
      Inc(I);
      if ParamStr(I) = 'qbe' then
        UseNative := False
      else if ParamStr(I) = 'native' then
        UseNative := True
      else
      begin
        WriteLn(StdErr, 'Error: --backend must be ''qbe'' or ''native''');
        SearchPaths.Free;
        Exit;
      end;
    end
    else if (Arg = '--target') and (I < ParamCount) then
    begin
      Inc(I);
      if not ParseTargetName(ParamStr(I), Target) then
      begin
        WriteLn(StdErr, 'Error: unknown --target ''', ParamStr(I), '''');
        SearchPaths.Free;
        Exit;
      end;
    end
    else if (Arg = '--help') or (Arg = '-h') then
    begin
      PrintUsage;
      Halt(0);
    end
    else
    begin
      WriteLn(StdErr, 'Unknown flag: ', Arg);
      SearchPaths.Free;
      Exit;
    end;
    Inc(I);
  end;

  if SourceFile = '' then
  begin
    WriteLn(StdErr, 'Error: --source is required');
    SearchPaths.Free;
    Exit;
  end;
  if (not EmitIR) and (not EmitAsm) and (OutputFile = '') then
  begin
    WriteLn(StdErr, 'Error: --output is required (or use --emit-ir / --emit-asm)');
    SearchPaths.Free;
    Exit;
  end;

  Result := True;
end;

function ReadProcessChunk(AProc: TProcess): string;
begin
  Result := AProc.ReadOutput
end;

function RunProcess(const AExe: string; AArgs: TStringList;
  out AOutput: string): Integer;
var
  Proc:  TProcess;
  Chunk: string;
  I:     Integer;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    for I := 0 to AArgs.Count - 1 do
      Proc.Parameters.Add(AArgs.Strings[I]);
    Proc.Execute;
    AOutput := '';
    repeat
      Chunk := ReadProcessChunk(Proc);
      AOutput := AOutput + Chunk;
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit;
    Result := Proc.ExitCode;
  finally
    Proc.Free;
  end;
end;

{ Locate the Blaise RTL static library.
  Search order:
    1. BLAISE_RTL environment variable (explicit override)
    2. Same directory as this compiler binary (installed layout) }
function FindRTL: string;
var
  BinDir: string;
begin
  Result := GetEnvironmentVariable('BLAISE_RTL');
  if (Result <> '') and FileExists(Result) then
    Exit;
  BinDir := ExtractFilePath(ParamStr(0));
  Result  := IncludeTrailingPathDelimiter(BinDir) + 'blaise_rtl.a';
  if FileExists(Result) then
    Exit;
  Result := '';
end;

{ Unit-as-top-level: qbe → .s → cc -c → .o.  Stops at the object
  file so the caller can link multiple unit-objects + a program
  object together.  No RTL, no -lm/-lpthread — those are link-time
  concerns.

  When ABifFile is non-empty, also embeds those bytes into the
  resulting .o via uElfObject into a non-loaded ELF section.  Keeps
  the on-disk .o + iface inseparable so the loader can read the
  iface straight out of the .o without a parallel filename. }
procedure CompileUnitToObject(const AIRFile, AOutputFile,
                              ABifFile: string);
var
  AsmFile:  string;
  Msg:      string;
  ExitCode: Integer;
  Args:     TStringList;
begin
  AsmFile := ChangeFileExt(AIRFile, '.s');
  Args := TStringList.Create;
  try
    Args.Add('-o');
    Args.Add(AsmFile);
    Args.Add(AIRFile);
    ExitCode := RunProcess('qbe', Args, Msg);
  finally
    Args.Free;
  end;
  if ExitCode <> 0 then
  begin
    WriteLn(StdErr, 'qbe error (exit ', ExitCode, '):');
    Write(StdErr, Msg);
    Halt(1);
  end;

  Args := TStringList.Create;
  try
    Args.Add('-c');           { compile only, no link }
    Args.Add('-o');
    Args.Add(AOutputFile);
    Args.Add(AsmFile);
    ExitCode := RunProcess('cc', Args, Msg);
  finally
    Args.Free;
  end;
  if ExitCode <> 0 then
  begin
    WriteLn(StdErr, 'cc -c error (exit ', ExitCode, '):');
    Write(StdErr, Msg);
    Halt(1);
  end;

  DeleteFile(AsmFile);

  if (ABifFile <> '') and FileExists(ABifFile) then
    if not EmbedBifInObject(AOutputFile, ABifFile, ofELF) then
      Halt(1);
end;

procedure CompileToNative(const AIRFile, AOutputFile, AOPDFAsmFile: string;
                          AExtraObjects: TStringList = nil);
var
  AsmFile, RTLPath: string;
  Msg:              string;
  ExitCode:         Integer;
  Args:             TStringList;
  I:                Integer;
begin
  AsmFile := ChangeFileExt(AIRFile, '.s');
  RTLPath := FindRTL;

  Args := TStringList.Create;
  try
    Args.Add('-o');
    Args.Add(AsmFile);
    Args.Add(AIRFile);
    ExitCode := RunProcess('qbe', Args, Msg);
  finally
    Args.Free;
  end;
  if ExitCode <> 0 then
  begin
    WriteLn(StdErr, 'qbe error (exit ', ExitCode, '):');
    Write(StdErr, Msg);
    Halt(1);
  end;

  Args := TStringList.Create;
  try
    Args.Add('-o');
    Args.Add(AOutputFile);
    if AOPDFAsmFile <> '' then
      Args.Add('-no-pie');  { OPDF addresses are absolute; PIE relocation breaks them }
    Args.Add(AsmFile);
    if (AOPDFAsmFile <> '') and FileExists(AOPDFAsmFile) then
      Args.Add(AOPDFAsmFile);
    { Pre-built dep object files (auto-discovered by the loader).
      Linked alongside the main object so their symbols resolve
      what AppendUnit skipped. }
    if AExtraObjects <> nil then
      for I := 0 to AExtraObjects.Count - 1 do
        Args.Add(AExtraObjects.Strings[I]);
    if RTLPath <> '' then
      Args.Add(RTLPath);
    Args.Add('-lm');       { math functions (sqrt, sin, cos, etc.) }
    Args.Add('-lpthread'); { POSIX threads (blaise_thread unit) }
    ExitCode := RunProcess('cc', Args, Msg);
  finally
    Args.Free;
  end;

  if ExitCode <> 0 then
  begin
    WriteLn(StdErr, 'cc error (exit ', ExitCode, '):');
    Write(StdErr, Msg);
    Halt(1);
  end;

  DeleteFile(AsmFile);
end;

{ Link a native-backend assembly file (.s) into the final binary.  The native
  backend has already produced the assembly (no qbe step); this only drives the
  cc link, reusing the same link line as CompileToNative.  Tool + RTL paths are
  resolved through uToolchain so env-var overrides and target awareness apply. }
procedure CompileToNativeDirect(const AAsmFile, AOutputFile: string;
  const ATarget: TTargetDesc; const AOPDFAsmFile: string);
var
  TC:       TToolchain;
  Msg:      string;
  ExitCode: Integer;
  Args:     TStringList;
begin
  TC := ResolveToolchain(ATarget);

  Args := TStringList.Create;
  try
    Args.Add('-o');
    Args.Add(AOutputFile);
    if AOPDFAsmFile <> '' then
      Args.Add('-no-pie');  { OPDF addresses are absolute; PIE relocation breaks them }
    Args.Add(AAsmFile);
    if (AOPDFAsmFile <> '') and FileExists(AOPDFAsmFile) then
      Args.Add(AOPDFAsmFile);
    if TC.RTLPath <> '' then
      Args.Add(TC.RTLPath);
    Args.Add('-lm');       { math functions (sqrt, sin, cos, etc.) }
    Args.Add('-lpthread'); { POSIX threads (blaise_thread unit) }
    ExitCode := RunProcess(TC.Linker.Path, Args, Msg);
  finally
    Args.Free;
  end;

  if ExitCode <> 0 then
  begin
    WriteLn(StdErr, 'link error (exit ', ExitCode, '):');
    Write(StdErr, Msg);
    Halt(1);
  end;
end;

var
  SourceFile, OutputFile: string;
  SearchPaths: TStringList;
  ConfigPaths: TStringList;
  EmitIR:      Boolean;
  EmitAsm:     Boolean;
  OPDFEnabled: Boolean;
  DebugMode:   Boolean;
  UseNative:   Boolean;
  Target:      TTargetDesc;
  OPDFAsmFile: string;
  SkipDepCodegen: Boolean;
  EmitIfaceDir: string;
  Incremental:    Boolean;
  UnitCacheDir:   string;
  Source:   TStringList;
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  TopUnit:  TUnit;            { non-nil when the source begins with 'unit',
                                in which case Prog stays nil and the
                                pipeline runs in unit-only mode. }
  IsUnitMode: Boolean;        { mirrors TopUnit's non-nil status but
                                survives past TopUnit.Free in the finally
                                block, so the post-codegen output dispatch
                                can pick CompileUnitToObject. }
  TopIfacePath: string;       { Temp .bif file produced for the top
                                unit, embedded into the output .o by
                                CompileUnitToObject and then deleted.
                                Empty when not in unit mode. }
  PrebuiltObjPaths: TStringList; { Auto-discovered dep .o files,
                                copied off the loader before its Free
                                so the link-step dispatch can still
                                see them. }
  Semantic: TSemanticAnalyser;
  NativeCG: TCodeGenNative;
  CG:       ICodeGen;
  OE:       TOPDFEmitter;
  Loader:   TUnitLoader;
  Units:    TObjectList;
  UnitIfaces: TObjectList;   { owned TUnitInterface, in dependency order
                               (leaves first).  Populated alongside the
                               existing AnalyseUnitForExport pass.
                               Phase 5 of the loader work: build the
                               cache during every real compile so
                               downstream phases (consumer migration)
                               can rely on it.  Currently the cache
                               isn't queried yet — building it surfaces
                               any ExportUnitInterface bugs against real
                               codebases. }
  I:        Integer;
  IR:       string;
  IRFile:   string;
  AsmFile:     string;
  UnitName:    string;
  UnitPath:    string;
  UnitOPath:   string;   { per-dep .o output path in --incremental mode }
  UnitBifPath: string;   { per-dep iface temp path }
  UnitIR:      string;   { per-dep IR text under --incremental }

begin
  SearchPaths    := nil;
  OPDFEnabled    := False;
  DebugMode      := False;
  OPDFAsmFile    := '';
  SkipDepCodegen := False;
  EmitIfaceDir   := '';
  Incremental    := False;
  UnitCacheDir   := '';
  TopUnit        := nil;
  IsUnitMode     := False;
  if IsFPCStyleInvocation then
  begin
    if not ParseFPCArgs(SourceFile, OutputFile, SearchPaths, OPDFEnabled) then
    begin
      PrintUsage;
      Halt(1);
    end;
    EmitIR  := False;
    EmitAsm := False;
  end
  else
  begin
    if not ParseArgs(SourceFile, OutputFile, EmitIR, EmitAsm, OPDFEnabled, DebugMode,
                     UseNative, Target, SearchPaths, SkipDepCodegen, EmitIfaceDir,
                     Incremental, UnitCacheDir) then
    begin
      PrintUsage;
      Halt(1);
    end;
  end;

  ConfigPaths := TStringList.Create;
  try
    LoadConfigPaths(ConfigPaths);
    for I := ConfigPaths.Count - 1 downto 0 do
      SearchPaths.Insert(0, ConfigPaths.Strings[I]);
  finally
    ConfigPaths.Free;
  end;

  if not FileExists(SourceFile) then
  begin
    WriteLn(StdErr, 'Error: source file not found: ', SourceFile);
    Halt(1);
  end;

  Source := TStringList.Create;
  try
    Source.LoadFromFile(SourceFile);
  except
    on E: Exception do
    begin
      WriteLn(StdErr, 'Error reading source: ', Exception(E).Message);
      Halt(1);
    end;
  end;

  Lexer      := nil;
  Parser     := nil;
  Prog       := nil;
  TopIfacePath := '';
  PrebuiltObjPaths := TStringList.Create;
  Semantic   := nil;
  { CG (ICodeGen) is zero-initialised by default; no explicit nil-assignment
    (stage-1 mis-compiles interface-global nil stores — see EmitAssign note). }
  Loader     := nil;
  Units      := nil;
  UnitIfaces := nil;
  try
    try
      Lexer  := TLexer.Create(Source.Text, SourceFile);
      Parser := TParser.Create(Lexer);
      IsUnitMode := Parser.IsUnitTopLevel;
      if IsUnitMode then
        TopUnit := Parser.ParseUnit
      else
        Prog := Parser.Parse;
    except
      on E: Exception do
      begin
        WriteLn(StdErr, 'Parse error: ', Exception(E).Message);
        Halt(1);
      end;
    end;

    try
      Semantic := TSemanticAnalyser.Create;
      if (SearchPaths <> nil) then
      begin
        if IsUnitMode and (TopUnit.UsedUnits.Count > 0) then
        begin
          Loader := TUnitLoader.Create(SearchPaths);
          Units  := Loader.LoadAll(TopUnit.UsedUnits);
        end
        else if (Prog <> nil) and (Prog.UsedUnits.Count > 0) then
        begin
          Loader := TUnitLoader.Create(SearchPaths);
          Units  := Loader.LoadAll(Prog.UsedUnits);
        end;
        if Units <> nil then
        begin
          UnitIfaces := TObjectList.Create(True);  { owns TUnitInterface }
          { Auto-discovered prebuilt ifaces: import each into the
            shared FTable before AnalyseUnitForExport runs on the
            source-loaded deps.  Order is dependency-leaf-first so
            cross-references resolve. }
          for I := 0 to Loader.PrebuiltIfaces.Count - 1 do
            ImportUnitInterface(
              TUnitInterface(Loader.PrebuiltIfaces.Items[I]),
              Semantic.GetSymbolTable, Semantic);
          for I := 0 to Units.Count - 1 do
          begin
            Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
            { Build the self-contained interface artifact for each dep.
              Each unit gets the previously-built ifaces as its ADeps
              so cross-unit type references resolve to qualified names. }
            UnitIfaces.Add(ExportUnitInterface(TUnit(Units.Items[I]),
                                               UnitIfaces,
                                               Semantic.GetSymbolTable));
            { Emit on-disk artifact when --emit-iface DIR was passed.
              Naming is <DIR>/<UnitName>.bif — flat directory, lower-
              cased unit name is intentional so case-insensitive
              filesystems behave.  Caller is responsible for ensuring
              DIR exists. }
            if EmitIfaceDir <> '' then
              WriteUnitInterfaceToFile(
                TUnitInterface(UnitIfaces.Items[I]),
                IncludeTrailingPathDelimiter(EmitIfaceDir) +
                  LowerCase(TUnit(Units.Items[I]).Name) + '.bif');
          end;
        end;
      end;
      if IsUnitMode then
      begin
        { Unit-as-top-level: same analysis pass deps go through, no
          program 'main' to wrap.  Sym tables and class layouts
          end up in Semantic's FTable just like for a regular dep. }
        Semantic.AnalyseUnitForExport(TopUnit);
        { Always produce the iface — it's about to be embedded into
          the .o by CompileUnitToObject.  The dedicated --emit-iface
          DIR remains as a debug aid that also writes a loose .bif
          alongside the embedded copy. }
        { Build the iface path deterministically alongside the
          output so we don't depend on a SysUtils helper that may
          not be on the bootstrap binary's RTL.  The .bif.tmp
          extension keeps it out of the way of any .bif emitted
          by --emit-iface in the same dir. }
        if OutputFile <> '' then
          TopIfacePath := OutputFile + '.bif.tmp'
        else
          TopIfacePath := LowerCase(TopUnit.Name) + '.bif.tmp';
        WriteUnitInterfaceToFile(
          ExportUnitInterface(TopUnit, UnitIfaces, Semantic.GetSymbolTable),
          TopIfacePath);
        if EmitIfaceDir <> '' then
          WriteUnitInterfaceToFile(
            ExportUnitInterface(TopUnit, UnitIfaces, Semantic.GetSymbolTable),
            IncludeTrailingPathDelimiter(EmitIfaceDir) +
              LowerCase(TopUnit.Name) + '.bif');
      end
      else
        Semantic.Analyse(Prog);
    except
      on E: ESemanticError do
      begin
        WriteLn(StdErr, 'Semantic error: ', Exception(E).Message);
        Halt(1);
      end;
      on E: EUnitNotFound do
      begin
        WriteLn(StdErr, 'Unit not found: ', Exception(E).Message);
        Halt(1);
      end;
      on E: ECircularDependency do
      begin
        WriteLn(StdErr, 'Circular dependency: ', Exception(E).Message);
        Halt(1);
      end;
      on E: Exception do
      begin
        WriteLn(StdErr, 'Compiler error: ', Exception(E).Message);
        Halt(1);
      end;
    end;

    { Phase 6c-H: incremental mode — compile each source-loaded dep
      to its own .o (with embedded iface) before the main codegen
      runs.  Sets SkipDepCodegen so the main IR doesn't redundantly
      inline dep bodies; the per-unit .o files feed the link step
      via PrebuiltObjPaths.  Side effect: filesystem gains an .o
      next to (or in --unit-cache) each dep's source.  Next compile
      will auto-discover these and skip parsing the .pas. }
    if Incremental and (Units <> nil) and (Units.Count > 0) then
    begin
      for I := 0 to Units.Count - 1 do
      begin
        UnitOPath := UnitCacheDir;
        if UnitOPath <> '' then
          UnitOPath := IncludeTrailingPathDelimiter(UnitOPath) +
                       LowerCase(TUnit(Units.Items[I]).Name) + '.o'
        else if OutputFile <> '' then
          UnitOPath := IncludeTrailingPathDelimiter(ExtractFilePath(OutputFile)) +
                       LowerCase(TUnit(Units.Items[I]).Name) + '.o'
        else
          UnitOPath := LowerCase(TUnit(Units.Items[I]).Name) + '.o';

        { Per-unit codegen: fresh TCodeGenQBE, shared symbol table. }
        CG := TCodeGenQBE.Create;
        try
          CG.SetSymbolTable(Semantic.GetSymbolTable);
          CG.AppendUnit(TUnit(Units.Items[I]));
          UnitIR := CG.GetOutput;
        finally
          CG.Free;
          CG := nil;
        end;

        IRFile := UnitOPath + '.ssa.tmp';
        Source := TStringList.Create;
        try
          Source.Text := UnitIR;
          Source.SaveToFile(IRFile);
        finally
          Source.Free;
          Source := nil;
        end;

        UnitBifPath := UnitOPath + '.bif.tmp';
        WriteUnitInterfaceToFile(
          TUnitInterface(UnitIfaces.Items[I]), UnitBifPath);

        CompileUnitToObject(IRFile, UnitOPath, UnitBifPath);

        DeleteFile(IRFile);
        DeleteFile(UnitBifPath);

        PrebuiltObjPaths.Add(UnitOPath);
      end;
      SkipDepCodegen := True;
    end;

    try
      { CG is an ICodeGen (ARC-managed) — no manual Free.  Backend selection:
        --emit-ir ALWAYS uses the QBE backend (fixpoint + RTL Makefile depend
        on byte-identical QBE IR), so the native backend is engaged only for
        actual native output.  --emit-asm implies --backend native.
        Otherwise --backend native selects TCodeGenNative for the configured target. }
      if (UseNative or EmitAsm) and not EmitIR then
      begin
        NativeCG := TCodeGenNative.Create;
        NativeCG.SetTarget(Target);
        CG := NativeCG;
      end
      else
        CG := TCodeGenQBE.Create;
      CG.SetDebugMode(DebugMode);
      if IsUnitMode then
      begin
        { Unit-as-top-level: emit just the unit's bodies, no program wrapping, no @main. }
        CG.SetSymbolTable(Semantic.GetSymbolTable);
        if (Units <> nil) and not SkipDepCodegen then
          for I := 0 to Units.Count - 1 do
            CG.AppendUnit(TUnit(Units.Items[I]));
        CG.AppendUnit(TopUnit);
      end
      else if (Units <> nil) and (Units.Count > 0) then
      begin
        CG.SetSymbolTable(Prog.SymbolTable);
        if not SkipDepCodegen then
          for I := 0 to Units.Count - 1 do
            CG.AppendUnit(TUnit(Units.Items[I]));
        CG.AppendProgram(Prog);
      end
      else
        CG.Generate(Prog);
      IR := CG.GetOutput;
      { CG (ICodeGen) is released by ARC at program scope exit.  We avoid an
        explicit `CG := nil` here: the stage-1 release binary mis-compiles an
        explicit nil-assignment to an interface-typed global (emits a bare
        single-slot store against an undefined $CG symbol).  That codegen gap
        is fixed in this tree (EmitAssign interface-nil case in uCodeGenQBE),
        but stage-1 predates the fix, so the driver must not rely on it. }

      if OPDFEnabled then
      begin
        OPDFAsmFile := ChangeFileExt(OutputFile, '.opdf.s');
        OE := TOPDFEmitter.Create(Prog, SourceFile);
        try
          OE.EmitToFile(OPDFAsmFile);
        finally
          OE.Free;
        end;
      end;
    except
      on E: Exception do
      begin
        WriteLn(StdErr, 'Code generation error: ', Exception(E).Message);
        Halt(1);
      end;
    end;
  finally
    UnitIfaces.Free;  { must free before Units — TUnitInterface entries
                       hold cloned AST that points at nothing in Units,
                       but the destructor order is still cleaner first }
    { Capture the prebuilt object paths off the loader before
      Loader.Free wipes them — needed by the link-step dispatch
      below the finally block. }
    if Loader <> nil then
      for I := 0 to Loader.PrebuiltObjectPaths.Count - 1 do
        PrebuiltObjPaths.Add(Loader.PrebuiltObjectPaths.Strings[I]);
    Units.Free;
    Loader.Free;
    SearchPaths.Free;
    { CG is ICodeGen (ARC-managed) — released via assignment/scope, not Free. }
    Semantic.Free;
    Prog.Free;
    Parser.Free;
    Lexer.Free;
    Source.Free;
  end;

  { --emit-ir / --emit-asm: write output to stdout and fall through to normal
    program exit so the main block's scope-exit ARC cleanup runs.  Calling
    Halt(0) here would lower to libc exit(), skipping every Pascal stack frame
    and leaving main's locals unreleased — defeating the leak tracker. }
  if EmitIR then
    Write(IR)
  else if EmitAsm then
    Write(IR)
  else if UseNative then
  begin
    { Native backend: IR holds target assembly text.  Write it to a .s file
      and link via the same cc driver the QBE path uses. }
    AsmFile := ChangeFileExt(OutputFile, '.s');
    try
      Source := TStringList.Create();
      try
        Source.Text := IR;
        Source.SaveToFile(AsmFile);
      finally
        Source.Free();
      end;
    except
      on E: Exception do
      begin
        WriteLn(StdErr, 'Error writing assembly: ', Exception(E).Message);
        Halt(1);
      end;
    end;

    CompileToNativeDirect(AsmFile, OutputFile, Target, OPDFAsmFile);
    DeleteFile(AsmFile);
    if OPDFAsmFile <> '' then
      DeleteFile(OPDFAsmFile);
  end
  else
  begin
    IRFile := ChangeFileExt(OutputFile, '.ssa');
    try
      Source := TStringList.Create();
      try
        Source.Text := IR;
        Source.SaveToFile(IRFile);
      finally
        Source.Free();
      end;
    except
      on E: Exception do
      begin
        WriteLn(StdErr, 'Error writing IR: ', Exception(E).Message);
        Halt(1);
      end;
    end;

    if IsUnitMode then
    begin
      CompileUnitToObject(IRFile, OutputFile, TopIfacePath);
      if (TopIfacePath <> '') and FileExists(TopIfacePath) then
        DeleteFile(TopIfacePath);
    end
    else
    begin
      { Auto-discovered prebuilt dep object paths feed straight into the cc command line. }
      if PrebuiltObjPaths.Count > 0 then
        CompileToNative(IRFile, OutputFile, OPDFAsmFile, PrebuiltObjPaths)
      else
        CompileToNative(IRFile, OutputFile, OPDFAsmFile);
    end;
    PrebuiltObjPaths.Free;
    DeleteFile(IRFile);
    if OPDFAsmFile <> '' then
      DeleteFile(OPDFAsmFile);
  end;
end.
