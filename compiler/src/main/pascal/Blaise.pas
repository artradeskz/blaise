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

  Backend-specific work (codegen construction, IR lowering, linking)
  is dispatched through the TBackendDriver registry
  (blaise.codegen.driver); this file owns the shared pipeline only.
  With --emit-ir / --emit-asm, the backend's IR text is written to
  stdout and no binary is produced.
}

uses
  SysUtils, Classes, contnrs,
  uLexer, uParser, uAST, uSemantic, blaise.codegen,
  blaise.codegen.target,
  blaise.codegen.driver,
  blaise.codegen.qbe.driver,
  blaise.codegen.native.driver,
  uUnitLoader, uDebugOPDF, uDebugFacts, uUnitInterface, uSemanticExport, uSemanticImport,
  uUnitInterfaceIO, uIfaceObject, uASTDump,
  blaise.frontend.opts, uConfig;

type
  { Alias so existing signatures (ParseArgs out param, locals) read
    unchanged.  The underlying enum lives in blaise.codegen.driver and
    is shared with every consumer of the driver registry. }
  TBackend = TBackendKind;

const
  Version = '0.12.0';
  CompilerName = 'Blaise';

{ Build the --backend usage fragment from the registered drivers, with
  the default (bkQBE) entry marked.  Keeps the flag parser and the usage
  text from drifting out of sync with the registry when a backend is
  added. }
function BackendUsageLine: string;
var
  Names: TStringList;
  I: Integer;
  K: TBackendKind;
begin
  Result := '';
  Names := RegisteredBackendNames();
  try
    for I := 0 to Names.Count - 1 do
    begin
      if I > 0 then
        Result := Result + ' | ';
      Result := Result + Names.Strings[I];
      if ParseBackendName(Names.Strings[I], K) then
      begin
        if K = bkNative then
          Result := Result + ' (default)'
        else if K = bkQBE then
          Result := Result + ' (deprecated)';
      end;
    end;
  finally
    Names.Free();
  end;
end;

procedure PrintUsage;
var
  DriverLines: TStringList;
  K: TBackendKind;
  D: TBackendDriver;
  I: Integer;
begin
  WriteLn('Blaise Compiler v', Version);
  WriteLn('Copyright (c) 2026 Graeme Geldenhuys');
  WriteLn('');
  WriteLn('Usage:');
  WriteLn('  blaise --source <file.pas> --output <binary>');
  WriteLn('  blaise --source <file.pas> --emit-ir');
  WriteLn('');
  WriteLn('Flags:');
  WriteLn(FormatFlagLine('--source <path>', 'Pascal source file'));
  WriteLn(FormatFlagLine('--output <path>', 'Output binary path'));
  WriteLn(FormatFlagLine('--unit-path <dir>',
    'Add directory to unit search path (repeatable)'));
  WriteLn(FormatFlagLine('--define <sym> | -d <sym>',
    'Define a conditional-compilation symbol (repeatable)'));
  WriteLn(FormatFlagLine('--backend <id>', BackendUsageLine()));
  WriteLn(FormatFlagLine('--target <os>-<cpu>',
    'linux-x86_64 (default), linux-i386, linux-arm64,'));
  WriteLn(FormatFlagLine('', 'freebsd-x86_64, windows-x86_64, macos-arm64'));
  WriteLn(FormatFlagLine('--emit-ir', 'Print QBE IR to stdout and exit'));
  WriteLn(FormatFlagLine('--emit-asm',
    'Print native assembly to stdout (requires --backend native)'));
  { Backend-private flags: each registered driver contributes its own
    lines (already column-formatted via FormatFlagLine) so this block does
    not hard-code per-backend flags like --assembler. }
  DriverLines := TStringList.Create();
  try
    for K := bkQBE to bkNative do
    begin
      D := GetDriver(K);
      if D <> nil then
        D.DescribeOptions(DriverLines);
    end;
    for I := 0 to DriverLines.Count - 1 do
      WriteLn(DriverLines.Strings[I]);
  finally
    DriverLines.Free();
  end;
  WriteLn(FormatFlagLine('--emit-iface <dir>',
    'Write each unit''s TUnitInterface as <dir>/<unit>.bif'));
  WriteLn(FormatFlagLine('--skip-dep-codegen',
    'Omit dep unit bodies from emitted IR (separate-compilation path)'));
  WriteLn(FormatFlagLine('--no-incremental',
    'Disable per-unit .o emission; build a single whole-program object'));
  WriteLn(FormatFlagLine('--unit-cache <dir>',
    'Where per-unit .o files are written (default: alongside output)'));
  WriteLn(FormatFlagLine('--dump-ast',
    'Print the resolved AST to stdout after semantic analysis'));
  WriteLn(FormatFlagLine('--debug',
    'Enable runtime memory leak reporting on exit'));
  WriteLn(FormatFlagLine('--debug-opdf',
    'Emit OPDF debug info (.opdf.s companion file)'));
  WriteLn('');
  WriteLn('Configuration:');
  WriteLn('  Unit search paths can also be set in blaise.cfg (one unit-path=<dir>');
  WriteLn('  per line). Searched next to the binary, then ~/.blaise.cfg.');
end;

{ Populate the two caller-constructed opts objects from the command line.
  AFront carries front-end-only state (paths, separate-compilation flags,
  the EmitIR/EmitAsm output-mode policy flags, and the requested Backend
  kind that is the input to driver selection); AOpts carries the
  cross-cutting knobs a backend driver reads (Target, OPDFEnabled,
  DebugMode, UseInternalAsm).  Returns False (and writes a diagnostic) on a
  bad flag; the caller owns and frees both objects regardless. }
{ Apply each -d/--define symbol in ADefines to ALexer's conditional-compilation
  table.  No-op when ADefines is nil/empty. }
procedure AddDefinesTo(ALexer: TLexer; ADefines: TStringList);
var
  I: Integer;
begin
  if ADefines = nil then Exit;
  for I := 0 to ADefines.Count - 1 do
    ALexer.AddDefine(ADefines.Strings[I]);
end;

function ParseArgs(AFront: TFrontEndOpts; AOpts: TBackendOpts;
  APendingFlags, APendingArgs: TStringList): Boolean;
var
  I: Integer;
  Arg, NextArg: string;
begin
  Result := False;
  AFront.SourceFile     := '';
  AFront.OutputFile     := '';
  AFront.EmitIR         := False;
  AFront.EmitAsm        := False;
  AFront.DumpAST        := False;
  AFront.Backend        := bkNative;
  AFront.BackendExplicit := False;
  AFront.SkipDepCodegen := False;
  AFront.EmitIfaceDir   := '';
  AFront.Incremental    := True;   { default-on; --no-incremental opts out }
  AFront.UnitCacheDir   := '';
  AOpts.OPDFEnabled     := False;
  AOpts.DebugMode       := False;
  AOpts.Target          := HostTarget();
  AOpts.UseInternalAsm  := False;

  I := 1;
  while I <= ParamCount() do
  begin
    Arg := ParamStr(I);
    if (Arg = '--source') and (I < ParamCount()) then
    begin
      Inc(I);
      AFront.SourceFile := ParamStr(I);
    end
    else if (Arg = '--output') and (I < ParamCount()) then
    begin
      Inc(I);
      AFront.OutputFile := ParamStr(I);
    end
    else if (Arg = '--unit-path') and (I < ParamCount()) then
    begin
      Inc(I);
      AFront.SearchPaths.Add(ParamStr(I));
    end
    else if ((Arg = '--define') or (Arg = '-d')) and (I < ParamCount()) then
    begin
      { Define a conditional-compilation symbol (FPC -dSYM / Delphi -D).
        Visible to IFDEF directives in the program and every unit it compiles. }
      Inc(I);
      AFront.Defines.Add(ParamStr(I));
    end
    else if Arg = '--skip-dep-codegen' then
      { Omit dep unit bodies from the main codegen pass — every cross-
        unit call becomes an extern reference.  Caller is responsible
        for linking pre-built dep object files at link time. }
      AFront.SkipDepCodegen := True
    else if (Arg = '--emit-iface') and (I < ParamCount()) then
    begin
      { Write each compiled unit's TUnitInterface as <Dir>/<Unit>.bif
        for later use as a separate-compilation cache. }
      Inc(I);
      AFront.EmitIfaceDir := ParamStr(I);
    end
    else if Arg = '--no-incremental' then
      { Incremental compilation is the default: each source-loaded dep
        is compiled to a stand-alone .o (with embedded iface) as a side
        effect of the program build, implying --skip-dep-codegen for the
        main IR (deps are not inlined; they're linked from the per-unit
        .o files instead) and letting the next compile auto-discover the
        .o's and skip parsing the .pas.  --no-incremental disables that
        and builds a single whole-program object instead. }
      AFront.Incremental := False
    else if (Arg = '--unit-cache') and (I < ParamCount()) then
    begin
      Inc(I);
      AFront.UnitCacheDir := ParamStr(I);
    end
    else if Arg = '--emit-ir' then
      AFront.EmitIR := True
    else if Arg = '--emit-asm' then
      AFront.EmitAsm := True
    else if Arg = '--dump-ast' then
      AFront.DumpAST := True
    else if Arg = '--debug' then
      AOpts.DebugMode := True
    else if Arg = '--debug-opdf' then
      AOpts.OPDFEnabled := True
    else if (Arg = '--backend') and (I < ParamCount()) then
    begin
      Inc(I);
      if not ParseBackendName(ParamStr(I), AFront.Backend) then
      begin
        WriteLn(StdErr, 'Error: --backend ', ParamStr(I),
          ' is not a registered backend (', BackendUsageLine(), ')');
        Exit;
      end;
      AFront.BackendExplicit := True;
    end
    else if (Arg = '--target') and (I < ParamCount()) then
    begin
      Inc(I);
      if not ParseTargetName(ParamStr(I), AOpts.Target) then
      begin
        WriteLn(StdErr, 'Error: unknown --target ''', ParamStr(I), '''');
        Exit;
      end;
      GTarget := AOpts.Target;
    end
    else if (Arg = '--help') or (Arg = '-h') then
    begin
      PrintUsage();
      Halt(0);
    end
    else
    begin
      { Not a shared/front-end flag.  Defer it: the parser does not yet
        know which driver will be selected, nor whether the flag takes a
        value.  Append (flag, lookahead) where lookahead is the next token
        iff it exists and does not itself begin with '--' (so it is a
        plausible value, not the next flag).  The post-loop drain offers
        each pending flag to the resolved driver and only then decides
        whether the lookahead was consumed as a value or is a standalone
        unknown flag. }
      APendingFlags.Add(Arg);
      if (I < ParamCount()) then
      begin
        NextArg := ParamStr(I + 1);
        if (Length(NextArg) >= 2) and (Copy(NextArg, 0, 2) = '--') then
          APendingArgs.Add('')
        else
          APendingArgs.Add(NextArg);
      end
      else
        APendingArgs.Add('');
    end;
    Inc(I);
  end;

  if AFront.SourceFile = '' then
  begin
    WriteLn(StdErr, 'Error: --source is required');
    Exit;
  end;
  if (not AFront.EmitIR) and (not AFront.EmitAsm) and (not AFront.DumpAST) and
     (AFront.OutputFile = '') then
  begin
    WriteLn(StdErr, 'Error: --output is required (or use --emit-ir / --emit-asm / --dump-ast)');
    Exit;
  end;

  Result := True;
end;

{ Lower one unit's IR to a .o through the driver, then embed the .bif.
  Returns '' on success.  The .bif embedding is an object-format concern
  shared across backends, so it stays here rather than in the driver. }
function CompileUnitToObjectSafe(ADriver: TBackendDriver;
  const AIRFile, AOutputFile, ABifFile: string;
  AOpts: TBackendOpts): string;
begin
  Result := ADriver.LowerToObject(AIRFile, AOutputFile, AOpts);
  if Result <> '' then Exit;

  if (ABifFile <> '') and FileExists(ABifFile) then
    if not EmbedBifInObject(AOutputFile, ABifFile, ofELF) then
      Exit('Failed to embed .bif in ' + AOutputFile);
end;

{ Unit-as-top-level: IR -> .o via the driver.  Stops at the object file
  so the caller can link multiple unit-objects + a program object
  together.  No RTL, no -lm/-lpthread -- those are link-time concerns.

  When ABifFile is non-empty, also embeds those bytes into the
  resulting .o via uElfObject into a non-loaded ELF section.  Keeps
  the on-disk .o + iface inseparable so the loader can read the
  iface straight out of the .o without a parallel filename. }
procedure CompileUnitToObject(ADriver: TBackendDriver;
  const AIRFile, AOutputFile, ABifFile: string; AOpts: TBackendOpts);
var
  Err: string;
begin
  Err := CompileUnitToObjectSafe(ADriver, AIRFile, AOutputFile, ABifFile, AOpts);
  if Err <> '' then
  begin
    WriteLn(StdErr, Err);
    Halt(1);
  end;
end;

type
  TCompileWorker = class(TThread)
    WorkUnit: TUnit;
    Iface: TUnitInterface;
    SymTable: TSymbolTable;
    OPath: string;
    Error: string;
    Driver: TBackendDriver;   { set by dispatcher; supplies CreateUnitCodeGen + lowering }
    Opts: TBackendOpts;       { shared read-only opts bag, set by dispatcher }
  protected
    procedure Execute; override;
  end;

procedure TCompileWorker.Execute;
var
  WCG: ICodeGen;
  WIR: string;
  WIRFile: string;
  WBifFile: string;
  WSource: TStringList;
  WFacts: TDbgFacts;
  WOPDF: TOPDFEmitter;
begin
  Self.Error := '';
  try
    WCG := Self.Driver.CreateUnitCodeGen(Self.Opts);
    if WCG = nil then
    begin
      { The dispatcher only hands out drivers whose SupportsIncremental
        is True; a nil codegen here is a driver-contract violation. }
      Self.Error := Self.Driver.Name() +
        ' driver claims incremental support but CreateUnitCodeGen returned nil';
      Exit;
    end;
    WCG.SetSymbolTable(Self.SymTable);
    WCG.AppendUnit(Self.WorkUnit);
    WIR := WCG.GetOutput();

    { Per-unit OPDF debug info: when --debug-opdf is on AND this worker's
      codegen produced exact debug facts (native backend), build a unit-mode
      OPDF emitter for THIS unit and append its self-contained .opdf section
      to the unit's IR.  At link time the linker concatenates every unit's
      and the program's .opdf section into one, so pdr can break inside any
      unit.  Mirrors the whole-program path in the main driver.

      QBE backend: GetDebugFacts returns nil (QBE assigns frames/addresses
      itself), so per-unit OPDF is skipped here.  A per-unit .opdf.s sidecar
      is impractical in the incremental pipeline; native is the debug backend
      per CLAUDE.md, so QBE incremental units carry no per-unit OPDF. }
    if Self.Opts.OPDFEnabled then
    begin
      WFacts := WCG.GetDebugFacts();
      if WFacts <> nil then
      begin
        WOPDF := TOPDFEmitter.CreateForUnit(Self.WorkUnit, Self.SymTable,
                                            Self.WorkUnit.SourceFile);
        try
          WOPDF.SetFacts(WFacts);
          WIR := WIR + LineEnding + WOPDF.GetOutput();
        finally
          WOPDF.Free();
        end;
      end;
    end;

    WCG := nil;  { release the ARC handle so codegen memory is freed before lowering }

    WIRFile := Self.OPath + Self.Driver.IRFileExt() + '.tmp';
    WSource := TStringList.Create();
    try
      WSource.Text := WIR;
      WSource.SaveToFile(WIRFile);
    finally
      WSource.Free();
    end;

    WBifFile := Self.OPath + '.bif.tmp';
    WriteUnitInterfaceToFile(Self.Iface, WBifFile);

    Self.Error := CompileUnitToObjectSafe(Self.Driver,
      WIRFile, Self.OPath, WBifFile, Self.Opts);

    DeleteFile(WIRFile);
    DeleteFile(WBifFile);
  except
    on E: Exception do
      Self.Error := 'Worker exception: ' + Exception(E).Message;
  end;
end;

var
  SourceFile, OutputFile: string;
  SearchPaths: TStringList;
  ConfigPaths: TStringList;
  EmitIR:      Boolean;
  EmitAsm:     Boolean;
  DumpAST:     Boolean;
  OPDFEnabled: Boolean;
  DebugMode:   Boolean;
  Backend:     TBackend;
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
                                survives past TopUnit.Free() in the finally
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
  Semantic:  TSemanticAnalyser;
  CG:        ICodeGen;
  Driver:    TBackendDriver;  { resolved backend driver for top-program codegen }
  Opts:      TBackendOpts;    { flag bag passed through Driver.CreateCodeGen }
  Front:     TFrontEndOpts;   { front-end-only flag bag, populated by ParseArgs }
  ToolErr:   string;          { CheckToolchain result ('' on success) }
  ValidErr:  string;          { Driver.ValidateOptions result ('' on success) }
  PendingFlags: TStringList;  { deferred unknown flags (driver-private) }
  PendingArgs:  TStringList;  { lookahead token per pending flag ('' if none) }
  PendIdx:   Integer;         { drain cursor over the pending lists }
  PendFlag:  string;
  WorkerDriver: TBackendDriver;  { driver for the incremental worker pool }
  OE:        TOPDFEmitter;
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
  LinkErr:  string;      { Driver.LinkProgram result ('' on success) }
  UnitOPath:   string;   { per-dep .o output path in incremental mode }
  Workers:  TObjectList; { TCompileWorker threads for parallel incremental }
  Worker:   TCompileWorker;

begin
  OPDFAsmFile    := '';
  TopUnit        := nil;
  IsUnitMode     := False;

  { Parse the command line into the two opts objects.  ParseArgs populates
    both (front-end state into Front, cross-cutting backend knobs into
    Opts); the caller owns and frees them.  Built up front so the
    incremental worker dispatch and the top-program codegen construction
    read one shared Opts.  ARC-managed — released at program exit. }
  Front := TFrontEndOpts.Create();
  Opts := TBackendOpts.Create();
  PendingFlags := TStringList.Create();
  PendingArgs := TStringList.Create();
  if not ParseArgs(Front, Opts, PendingFlags, PendingArgs) then
  begin
    PrintUsage();
    Halt(1);
  end;

  { Seed the working locals from the opts objects.  Keeping the locals lets
    the (large) main body read them unchanged; the parser owns the objects.
    SearchPaths is the object's owned list (not copied) so config-path
    insertion below mutates the canonical list. }
  SourceFile     := Front.SourceFile;
  OutputFile     := Front.OutputFile;
  EmitIR         := Front.EmitIR;
  EmitAsm        := Front.EmitAsm;
  DumpAST        := Front.DumpAST;
  Backend        := Front.Backend;
  SearchPaths    := Front.SearchPaths;
  SkipDepCodegen := Front.SkipDepCodegen;
  EmitIfaceDir   := Front.EmitIfaceDir;
  Incremental    := Front.Incremental;
  UnitCacheDir   := Front.UnitCacheDir;
  OPDFEnabled    := Opts.OPDFEnabled;
  DebugMode      := Opts.DebugMode;
  Target         := Opts.Target;
  { UseInternalAsm is not seeded here: --assembler now flows through the
    driver's AcceptOption during the post-PickTopDriver drain, which writes
    Opts.UseInternalAsm.  Downstream link code reads Opts.UseInternalAsm
    directly. }

  ConfigPaths := TStringList.Create();
  try
    LoadConfigPaths(ConfigPaths);
    for I := ConfigPaths.Count - 1 downto 0 do
      SearchPaths.Insert(0, ConfigPaths.Strings[I]);
  finally
    ConfigPaths.Free();
  end;

  if (UnitCacheDir <> '') and (SearchPaths.IndexOf(UnitCacheDir) < 0) then
    SearchPaths.Add(UnitCacheDir);

  { Emit-mode / backend compatibility.  --emit-ir prints QBE IR and
    --emit-asm prints native assembly; PickTopDriver routes each to the
    backend that produces it, ignoring --backend.  That silent override is
    fine for the default backend, but when the user EXPLICITLY asked for a
    backend that cannot produce the requested output we must reject it
    rather than quietly switch — backend-specific output modes belong to
    their backend. }
  if Front.BackendExplicit and EmitIR and (not GetDriver(Backend).ClaimsEmitIR()) then
  begin
    WriteLn(StdErr, 'Error: --emit-ir prints QBE IR and is not supported by ',
      '--backend native; use --emit-asm for native assembly');
    Halt(1);
  end;
  if Front.BackendExplicit and EmitAsm and (Backend <> bkNative) then
  begin
    WriteLn(StdErr, 'Error: --emit-asm prints native assembly and is not ',
      'supported by --backend qbe; use --emit-ir for QBE IR');
    Halt(1);
  end;

  { Resolve the top-program driver once.  All backend-selection policy
    lives in PickTopDriver; everything downstream dispatches through
    the driver. }
  Driver := PickTopDriver(Backend, EmitIR, EmitAsm);

  { Drain the deferred backend-private flags (Chain of Responsibility).
    Each pending flag is offered to the resolved driver.  When the driver
    consumes a VALUE (oaConsumedValue), the loop will also have appended
    that value token as its OWN pending entry (the parse loop did not yet
    know the flag took a value), so skip the next entry when it matches
    the consumed token.  An oaUnknown flag is a genuine unknown flag and
    fails with the historical message and exit code. }
  PendIdx := 0;
  while PendIdx < PendingFlags.Count do
  begin
    PendFlag := PendingFlags.Strings[PendIdx];
    case Driver.AcceptOption(PendFlag, PendingArgs.Strings[PendIdx], Opts) of
      oaConsumedValue:
        begin
          { The lookahead token was this flag's value.  If the next
            pending entry is that same token (appended standalone by the
            parse loop), skip it so it is not re-reported as unknown. }
          if (PendIdx + 1 < PendingFlags.Count) and
             (PendingArgs.Strings[PendIdx] <> '') and
             (PendingFlags.Strings[PendIdx + 1] = PendingArgs.Strings[PendIdx]) then
            Inc(PendIdx);
        end;
      oaConsumedFlag:
        ; { mine, no value taken }
      oaUnknown:
        begin
          WriteLn(StdErr, 'Unknown flag: ', PendFlag);
          Halt(1);
        end;
    end;
    Inc(PendIdx);
  end;

  { Post-parse validation with the resolved driver and opts visible
    (Template Method seam).  Runs UNCONDITIONALLY — these are flag-
    combination rules (e.g. a bad --assembler value, OPDF-vs-LLVM), not
    toolchain-reachability checks, so they must fire even in the
    stdout-only modes that skip the toolchain probe below. }
  ValidErr := Driver.ValidateOptions(Opts);
  if ValidErr <> '' then
  begin
    WriteLn(StdErr, 'Error: ', ValidErr);
    Halt(1);
  end;

  { Pre-flight the backend toolchain before the front-end runs, so a
    missing tool surfaces immediately rather than after a full parse +
    semantic pass.  Stdout-only modes (--emit-ir / --emit-asm /
    --dump-ast) produce no binary and need no external tools — they must
    never be blocked by a toolchain probe. }
  if not (EmitIR or EmitAsm or DumpAST) then
  begin
    ToolErr := Driver.CheckToolchain(Opts);
    if ToolErr <> '' then
    begin
      WriteLn(StdErr, ToolErr);
      Halt(1);
    end;
  end;

  if not FileExists(SourceFile) then
  begin
    WriteLn(StdErr, 'Error: source file not found: ', SourceFile);
    Halt(1);
  end;

  Source := TStringList.Create();
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
  PrebuiltObjPaths := TStringList.Create();
  Semantic   := nil;
  { CG (ICodeGen) is zero-initialised by default; no explicit nil-assignment
    (stage-1 mis-compiles interface-global nil stores — see EmitAssign note). }
  Loader     := nil;
  Units      := nil;
  UnitIfaces := nil;
  try
    try
      Lexer  := TLexer.Create(Source.Text, SourceFile);
      AddDefinesTo(Lexer, Front.Defines);
      Parser := TParser.Create(Lexer);
      IsUnitMode := Parser.IsUnitTopLevel();
      if IsUnitMode then
        TopUnit := Parser.ParseUnit()
      else
        Prog := Parser.Parse();
    except
      on E: Exception do
      begin
        WriteLn(StdErr, 'Parse error: ', Exception(E).Message);
        Halt(1);
      end;
    end;

    try
      Semantic := TSemanticAnalyser.Create();
      if (SearchPaths <> nil) then
      begin
        if IsUnitMode and (TopUnit.UsedUnits.Count > 0) then
        begin
          Loader := TUnitLoader.Create(SearchPaths, Front.Defines);
          Units  := Loader.LoadAll(TopUnit.UsedUnits);
        end
        else if (Prog <> nil) and (Prog.UsedUnits.Count > 0) then
        begin
          Loader := TUnitLoader.Create(SearchPaths, Front.Defines);
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
          begin
            ImportUnitInterface(
              TUnitInterface(Loader.PrebuiltIfaces.Items[I]),
              Semantic.GetSymbolTable(), Semantic);
            Semantic.RegisterUnitIface(
              TUnitInterface(Loader.PrebuiltIfaces.Items[I]));
          end;
          for I := 0 to Units.Count - 1 do
          begin
            Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
            { Build the self-contained interface artifact for each dep.
              Each unit gets the previously-built ifaces as its ADeps
              so cross-unit type references resolve to qualified names. }
            UnitIfaces.Add(ExportUnitInterface(TUnit(Units.Items[I]),
                                               UnitIfaces,
                                               Semantic.GetSymbolTable()));
            Semantic.RegisterUnitIface(
              TUnitInterface(UnitIfaces.Items[UnitIfaces.Count - 1]));
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
          ExportUnitInterface(TopUnit, UnitIfaces, Semantic.GetSymbolTable()),
          TopIfacePath);
        if EmitIfaceDir <> '' then
          WriteUnitInterfaceToFile(
            ExportUnitInterface(TopUnit, UnitIfaces, Semantic.GetSymbolTable()),
            IncludeTrailingPathDelimiter(EmitIfaceDir) +
              LowerCase(TopUnit.Name) + '.bif');
      end
      else
        Semantic.Analyse(Prog);

      if DumpAST then
      begin
        if IsUnitMode then
          DumpUnit(TopUnit)
        else if Prog <> nil then
          DumpProgram(Prog);
        Halt(0);
      end;
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
        WriteLn(StdErr, 'Compiler error [', Exception(E).ClassName, ']: ', Exception(E).Message);
        Halt(1);
      end;
    end;

    { Phase 6c-H: incremental mode -- compile each source-loaded dep
      to its own .o (with embedded iface) before the main codegen
      runs.  Sets SkipDepCodegen so the main IR doesn't redundantly
      inline dep bodies; the per-unit .o files feed the link step
      via PrebuiltObjPaths.  Side effect: filesystem gains an .o
      next to (or in --unit-cache) each dep's source.  Next compile
      will auto-discover these and skip parsing the .pas.

      Each unit is compiled in a separate worker thread for parallel
      codegen + qbe + cc.  The symbol table is read-only at this point
      (semantic analysis is complete), so concurrent reads are safe. }
    if Incremental and (not EmitIR) and (not EmitAsm) and (not DumpAST)
       and (Units <> nil) and (Units.Count > 0) then
    begin
      { Pick a driver for the workers.  Prefer the top-program backend
        when it supports per-unit emission; otherwise fall back to QBE —
        QBE-emitted .o files link cleanly alongside any backend's
        top-program object, so the cache stays usable. }
      WorkerDriver := GetDriver(Backend);
      if not WorkerDriver.SupportsIncremental() then
        WorkerDriver := GetDriver(bkQBE);
      Workers := TObjectList.Create(True);
      try
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

          Worker := TCompileWorker.Create(True);
          Worker.WorkUnit := TUnit(Units.Items[I]);
          Worker.Iface := TUnitInterface(UnitIfaces.Items[I]);
          { In unit-mode (the top source is a `unit`) Prog is nil — the symbol
            table comes from the semantic pass, not a program node.  Using
            Prog.SymbolTable there dereferences nil and crashes the incremental
            worker setup. }
          if Prog <> nil then
            Worker.SymTable := Prog.SymbolTable
          else
            Worker.SymTable := Semantic.GetSymbolTable();
          Worker.OPath := UnitOPath;
          Worker.Driver := WorkerDriver;
          Worker.Opts := Opts;
          Workers.Add(Worker);
          PrebuiltObjPaths.Add(UnitOPath);
        end;
        for I := 0 to Workers.Count - 1 do
          TCompileWorker(Workers.Items[I]).Start();
        for I := 0 to Workers.Count - 1 do
        begin
          TCompileWorker(Workers.Items[I]).WaitFor();
          if TCompileWorker(Workers.Items[I]).Error <> '' then
          begin
            WriteLn(StdErr, TCompileWorker(Workers.Items[I]).Error);
            Halt(1);
          end;
        end;
      finally
        Workers.Free();
      end;
      SkipDepCodegen := True;
    end;

    try
      { CG is an ICodeGen (ARC-managed) — no manual Free.  Backend
        selection policy lives in PickTopDriver (--emit-ir always forces
        QBE for fixpoint / RTL Makefile compatibility; --emit-asm implies
        native); the per-backend construction details — class to
        instantiate, knobs to wire — live behind Driver.CreateCodeGen. }
      if IsUnitMode then
        CG := Driver.CreateUnitCodeGen(Opts)
      else
        CG := Driver.CreateCodeGen(Opts);
      if IsUnitMode then
      begin
        { Unit-as-top-level: emit just the unit's bodies, no program wrapping, no @main. }
        CG.SetSymbolTable(Semantic.GetSymbolTable());
        if (Units <> nil) and not SkipDepCodegen then
          for I := 0 to Units.Count - 1 do
            CG.AppendUnit(TUnit(Units.Items[I]));
        CG.AppendUnit(TopUnit);
      end
      else if ((Units <> nil) and (Units.Count > 0)) or
              ((Loader <> nil) and (Loader.PrebuiltIfaces.Count > 0)) then
      begin
        CG.SetSymbolTable(Prog.SymbolTable);
        { Prebuilt (cached) ifaces are ALWAYS compiled into their own objects —
          their bodies are never appended here, regardless of SkipDepCodegen.
          So they must be noted as imported units unconditionally: the program
          startup must call each one's <Unit>_init (if it has an initialization
          section), and the backend must treat globals owned by these units as
          external references rather than re-defining them (otherwise the link
          step reports a multiple definition — the cached .o owns the symbol).

          They are loaded leaf-first and any source units depend on them, so
          their inits must run before the source deps' inits.  On a full rebuild
          every dep is cached, so this is the only loop that fires. }
        if Loader <> nil then
          for I := 0 to Loader.PrebuiltIfaces.Count - 1 do
            CG.NoteDepInitUnit(
              TUnitInterface(Loader.PrebuiltIfaces.Items[I]).Name,
              TUnitInterface(Loader.PrebuiltIfaces.Items[I]).HasInitialization);
        if not SkipDepCodegen then
        begin
          { Source-loaded deps are compiled inline into this object — append
            their bodies; they are not imported, so do not note them. }
          if Units <> nil then
            for I := 0 to Units.Count - 1 do
              CG.AppendUnit(TUnit(Units.Items[I]));
        end
        else
        begin
          { Incremental / separate-compilation: source dep bodies are compiled
            into their own objects (skipped here).  Note each so $main calls its
            <Unit>_init and the backend references its globals externally. }
          if Units <> nil then
            for I := 0 to Units.Count - 1 do
              CG.NoteDepInitUnit(TUnit(Units.Items[I]).Name,
                (TUnit(Units.Items[I]).InitStmts <> nil) and
                (TUnit(Units.Items[I]).InitStmts.Count > 0));
        end;
        CG.AppendProgram(Prog);
      end
      else
      begin
        { Unit-less program: the backend still needs the symbol table for
          class symbol prefixes and OPDF Self typing; the analyser (the
          table's uses-chain provider) outlives codegen here. }
        CG.SetSymbolTable(Prog.SymbolTable);
        CG.Generate(Prog);
      end;
      IR := CG.GetOutput();
      { CG (ICodeGen) is released by ARC at program scope exit.  We avoid an
        explicit `CG := nil` here: the stage-1 release binary mis-compiles an
        explicit nil-assignment to an interface-typed global (emits a bare
        single-slot store against an undefined $CG symbol).  That codegen gap
        is fixed in this tree (EmitAssign interface-nil case in blaise.codegen.qbe),
        but stage-1 predates the fix, so the driver must not rely on it. }

      if OPDFEnabled then
      begin
        OE := TOPDFEmitter.Create(Prog, SourceFile);
        try
          { Native backend: codegen collected exact debug facts (frame
            offsets, per-statement labels, function end labels).  Append the
            OPDF section to the SAME assembly text — local labels resolve in
            one object file, no symbol exports needed, and line records get
            statement granularity.  QBE backend: no facts are available (QBE
            assigns frames/addresses itself), keep the separate .opdf.s with
            the approximate AST-walk records. }
          OE.SetFacts(CG.GetDebugFacts());
          if CG.GetDebugFacts() <> nil then
            IR := IR + LineEnding + OE.GetOutput()
          else
          begin
            OPDFAsmFile := ChangeFileExt(OutputFile, '.opdf.s');
            OE.EmitToFile(OPDFAsmFile);
          end;
        finally
          OE.Free();
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
    UnitIfaces.Free();  { must free before Units — TUnitInterface entries
                       hold cloned AST that points at nothing in Units,
                       but the destructor order is still cleaner first }
    { Capture the prebuilt object paths off the loader before
      Loader.Free wipes them — needed by the link-step dispatch
      below the finally block. }
    if Loader <> nil then
    begin
      for I := 0 to Loader.PrebuiltObjectPaths.Count - 1 do
        PrebuiltObjPaths.Add(Loader.PrebuiltObjectPaths.Strings[I]);
      { Impl-only dependency objects: linked but not semantically imported. }
      for I := 0 to Loader.LinkOnlyObjects.Count - 1 do
        if PrebuiltObjPaths.IndexOf(Loader.LinkOnlyObjects.Strings[I]) < 0 then
          PrebuiltObjPaths.Add(Loader.LinkOnlyObjects.Strings[I]);
    end;
    Units.Free();
    Loader.Free();
    SearchPaths.Free();
    { CG is ICodeGen (ARC-managed) — released via assignment/scope, not Free. }
    Semantic.Free();
    Prog.Free();
    Parser.Free();
    Lexer.Free();
    Source.Free();
  end;

  { --emit-ir / --emit-asm: write output to stdout and fall through to normal
    program exit so the main block's scope-exit ARC cleanup runs.  Calling
    Halt(0) here would lower to libc exit(), skipping every Pascal stack frame
    and leaving main's locals unreleased — defeating the leak tracker. }
  if EmitIR or EmitAsm then
    { Driver was picked to match the flag (QBE for --emit-ir, native for
      --emit-asm — see PickTopDriver), so IR already holds the text the
      user asked for. }
    Write(IR)
  else
  begin
    { Backend-neutral output dispatch: write the IR to a file with the
      driver's extension (.ssa for QBE; .s for native — its IR IS the
      assembly), then lower + link through the driver.  OPDFAsmFile may
      have been bound to a sidecar path during the OPDF emit above, so
      refresh it onto Opts before the drivers read it. }
    Opts.OPDFAsmFile := OPDFAsmFile;
    IRFile := ChangeFileExt(OutputFile, Driver.IRFileExt());
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
      CompileUnitToObject(Driver, IRFile, OutputFile, TopIfacePath, Opts);
      if (TopIfacePath <> '') and FileExists(TopIfacePath) then
        DeleteFile(TopIfacePath);
    end
    else
    begin
      { Auto-discovered prebuilt dep object paths feed straight into the
        link line. }
      LinkErr := Driver.LinkProgram(IRFile, OutputFile, Opts, PrebuiltObjPaths);
      if LinkErr <> '' then
      begin
        WriteLn(StdErr, LinkErr);
        Halt(1);
      end;
    end;
    PrebuiltObjPaths.Free();
    DeleteFile(IRFile);
    if OPDFAsmFile <> '' then
      DeleteFile(OPDFAsmFile);
  end;
end.
