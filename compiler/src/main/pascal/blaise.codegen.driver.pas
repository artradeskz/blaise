{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.driver;

{ Cross-backend driver abstraction.

  Each backend registers a TBackendDriver subclass singleton.  Blaise.pas
  and TCompileWorker drive the shared pipeline through the base class and
  stop branching on the backend kind for per-backend tool invocation,
  file extensions, and codegen construction.

  Responsibilities a driver OWNS:

    * Codegen construction: which ICodeGen to create and how to apply its
      backend-specific knobs (e.g. the native backend's SetTarget).

    * IR-text artefact shape: the file extension used for the emitted IR,
      so the shared pipeline can pick the right file name without a
      backend switch.

    * Lowering and linking: turning the emitted IR file into a
      relocatable object (per-unit incremental path) or the final linked
      binary (program path).  The QBE driver runs qbe + cc; the native
      driver runs cc on its assembly directly, or the in-process
      assembler + linker driver when --assembler internal is selected.

  Responsibilities a driver does NOT own:

    * Warm-cache discovery, source-hash validation, prebuilt-object
      probing.  Those stay in uUnitLoader and are backend-agnostic.
      SupportsWarmCache exists only as a hint for future "this backend's
      .o isn't trusted for cache reuse yet" gating.

    * .bif embedding into unit objects — an object-format concern shared
      across backends; it stays with the caller (Blaise.pas).

  The architecture follows Andrew Haines' unify_backend_interface
  proposal, with a class-based dispatch surface (virtual methods on an
  abstract base) instead of an interface so shared behaviour — toolchain
  resolution, the common link line — lives in the base class.

  Lifetime: driver singletons are registered once at unit initialization
  into a fixed array of class references.  They are ARC-managed globals,
  released by the program-exit global release pass (the codebase norm for
  unit-level singletons — no explicit finalization needed). }

interface

uses
  Classes,
  blaise.codegen,
  blaise.codegen.target,
  uToolchain;

type
  TBackendKind = (bkQBE, bkNative);

  { Result of offering an unrecognised flag to a driver (Chain of
    Responsibility). }
  TOptionAccept = (
    oaUnknown,        { not my flag — keep trying / report unknown }
    oaConsumedFlag,   { mine, took no value argument }
    oaConsumedValue   { mine, consumed the following arg as its value }
  );

  { Cross-cutting flags that affect codegen, lowering, and linking.
    Built once by the Blaise.pas flag parser and shared (read-only) with
    the compile workers.  Adding a new backend knob is a field here plus
    the driver that reads it; Blaise.pas does not branch on backend to
    apply it. }
  TBackendOpts = class
  public
    Target: TTargetDesc;
    DebugMode: Boolean;       { codegen debug / leak tracking }
    OPDFEnabled: Boolean;     { OPDF code shaping }
    OPDFAsmFile: string;      { OPDF sidecar path, if any }
    UseInternalAsm: Boolean;  { --assembler internal (native backend) }
    AssemblerExplicit: Boolean;  { True when user passed --assembler }
    AssemblerChoiceBad: Boolean;  { a --assembler value was given that is
                                neither 'internal' nor 'external'; the
                                native driver's ValidateOptions rejects it }
    UseInternalLinker: Boolean;  { --linker internal (native backend) }
    LinkerExplicit: Boolean;     { True when user passed --linker }
    LinkerChoiceBad: Boolean;    { --linker value not 'internal' or 'external' }
  end;

  TBackendDriver = class
  public
    { Static description of the backend. }
    function Kind: TBackendKind; virtual; abstract;
    function Name: string; virtual; abstract;       { '--backend' identifier }
    function IRFileExt: string; virtual; abstract;  { '.ssa' | '.s' }

    { True when the driver can emit a per-unit linkable artefact for the
      --incremental worker pool.  A driver returning True here MUST
      return a non-nil codegen from CreateUnitCodeGen — the worker fails
      loudly otherwise. }
    function SupportsIncremental: Boolean; virtual;

    { True when uUnitLoader may reuse this backend's .o + .bif on a
      content-hash match.  QBE = true today; native = false until it
      learns to write .bif sidecars and the loader trusts them. }
    function SupportsWarmCache: Boolean; virtual;

    { The external tools this backend needs for ATarget, as resolvable
      specs.  uToolchain.ResolveSpec turns each into a path (env override,
      $BLAISE_TOOLCHAIN_PREFIX, cross-triple prefix, $PATH, host ext).  The
      base lists the shared linker (cc, or the mingw cross-linker for a
      Windows target); a backend overrides to add its own (e.g. the LLVM
      driver appends llc) — call inherited and extend. }
    function DescribeTools(const ATarget: TTargetDesc): TToolSpecArray; virtual;

    { Resolve one named tool from DescribeTools for ATarget; '' if the
      backend declares no such tool. }
    function ToolPath(const AName: string; const ATarget: TTargetDesc): string;

    { Verify any tools the backend needs are reachable.  Returns '' on
      success, an error message otherwise.  Called once before the
      front-end runs (skipped for stdout-only modes, which need no
      toolchain). }
    function CheckToolchain(AOpts: TBackendOpts): string; virtual;

    { Construct the backend's code generator and apply opts.  Returns an
      ARC-managed ICodeGen — do not Free. }
    function CreateCodeGen(AOpts: TBackendOpts): ICodeGen; virtual; abstract;

    { Per-unit codegen for the parallel incremental worker, configured to
      emit a single unit's IR with exports visible to sibling units.
      Default nil: the driver does not support separate-unit emission and
      the dispatcher falls back to the QBE driver. }
    function CreateUnitCodeGen(AOpts: TBackendOpts): ICodeGen; virtual;

    { Lower one unit's IR file to a relocatable object (--incremental
      worker path and unit-as-top-level mode).  Returns '' on success,
      an error message otherwise.  Default fails loudly: a driver that
      claims SupportsIncremental must override this. }
    function LowerToObject(const AIRFile, AObjFile: string;
      AOpts: TBackendOpts): string; virtual;

    { Lower the top program's IR file and link the final binary —
      including the OPDF sidecar, prebuilt dep objects, the RTL archive,
      and -lm/-lpthread.  Returns '' on success, an error message
      otherwise.  AExtraObjects may be nil. }
    function LinkProgram(const AIRFile, AOutputFile: string;
      AOpts: TBackendOpts; AExtraObjects: TStringList): string; virtual; abstract;

    { --- Option contract (Chain of Responsibility + Template Method) --- }

    { The common parser, on a flag it does not own, offers it here.  The
      driver writes any parsed state into the shared AOpts (the same
      TBackendOpts the drivers later read).  Returns oaConsumedValue when
      it took ANextArg as the flag's value, oaConsumedFlag when the flag
      stood alone, oaUnknown when the flag is not this driver's.  Default
      oaUnknown. }
    function AcceptOption(const AFlag, ANextArg: string;
      AOpts: TBackendOpts): TOptionAccept; virtual;

    { Contribute this backend's flag lines to --help.  One (flag,
      description) pair per AddOptionLine call; FormatFlagLine owns the
      column layout so driver lines never drift from the shared block.
      Default: nothing. }
    procedure DescribeOptions(ALines: TStringList); virtual;

    { Post-parse validation with the resolved TBackendOpts visible.
      Returns '' when valid, else a user-facing message.  THIS is where
      cross-cutting rules live ("OPDF debug info is not supported by the
      LLVM backend").  Default ''. }
    function ValidateOptions(AOpts: TBackendOpts): string; virtual;

    { Selection policy: does this backend produce the IR text that
      --emit-ir prints?  QBE = True (fixpoint / RTL-Makefile contract on
      byte-identical QBE IR); native = False (its IR IS assembly, surfaced
      via --emit-asm).  PickTopDriver asks this instead of hard-coding
      bkQBE.  Default False. }
    function ClaimsEmitIR: Boolean; virtual;

  protected
    { The shared linker tool spec for ATarget (cc/clang, or the mingw
      cross-linker for a Windows target).  A subclass's DescribeTools builds
      its array from this plus its own tools — the parser has no
      expression-position `inherited`, so this is the reuse seam. }
    function LinkerToolSpec(const ATarget: TTargetDesc): TToolSpec;

    { Shared link line: cc-driver resolved via uToolchain (env overrides
      and target awareness apply), input file, OPDF sidecar, extra
      objects, RTL archive, -lm, -lpthread.  Used by every driver's
      LinkProgram. }
    function LinkViaToolchain(const AInputFile, AOutputFile: string;
      AOpts: TBackendOpts; AExtraObjects: TStringList): string;
  end;

{ Run an external tool, capturing combined output.  Shared by the
  drivers; exposed because the lowering steps run from worker threads
  as well as the main compile path. }
function RunProcess(const AExe: string; AArgs: TStringList;
  out AOutput: string): Integer;

{ Format one --help flag line with the shared 2-space indent and flag
  column.  Single source of truth for the column width so the common
  usage block (Blaise.pas PrintUsage) and each driver's DescribeOptions
  cannot drift.  Example:
    FormatFlagLine('--assembler <id>', 'internal | external (default: external)')
  produces '  --assembler <id>    internal | external (default: external)'. }
function FormatFlagLine(const AFlag, ADesc: string): string;

{ Registry.  Each backend unit registers its singleton in its
  initialization block; consumers fetch by kind.  Looking up an
  unregistered kind raises an exception (programmer error — the backend
  unit wasn't pulled into the uses clause). }

procedure RegisterDriver(ADriver: TBackendDriver);
function GetDriver(AKind: TBackendKind): TBackendDriver;

{ Enumerate registered backends in TBackendKind ordinal order.  Returns a
  TStringList of Name values; caller owns and frees.  Drives --backend
  validation and the usage printer so neither hard-codes the list. }
function RegisteredBackendNames: TStringList;

{ Parse a --backend identifier against the registered drivers.  Returns
  False on an unknown name; caller writes the user-facing error. }
function ParseBackendName(const AName: string; out AKind: TBackendKind): Boolean;

{ The single backend-selection policy decision.  --emit-ir always forces
  QBE (the fixpoint check + RTL Makefile depend on byte-identical QBE
  IR); --emit-asm implies native (its IR IS the .s text the consumer
  expects); otherwise --backend selects directly. }
function PickTopDriver(ABackend: TBackendKind;
  AEmitIR, AEmitAsm: Boolean): TBackendDriver;

implementation

uses
  SysUtils,
  Process,
  uToolchain;

{ Indexed by Ord(TBackendKind).  The bound is a literal because the
  parser only accepts integer literals on array decls; keep the upper
  bound in sync with the enum's highest ordinal (bkNative = 1). }
var
  GDrivers: array[0..1] of TBackendDriver;

function TBackendDriver.SupportsIncremental: Boolean;
begin
  Result := False;
end;

function TBackendDriver.SupportsWarmCache: Boolean;
begin
  Result := False;
end;

function TBackendDriver.LinkerToolSpec(const ATarget: TTargetDesc): TToolSpec;
begin
  { Shared linker slot.  A target tool (HostTool=False): native build uses
    cc/clang; a Windows target cross-links via the mingw clang driver
    (x86_64-w64-mingw32-clang) and never falls back to the host cc. }
  Result.Name     := 'linker';
  Result.EnvVar   := 'BLAISE_LINKER';
  SetLength(Result.Cands, 2);
  Result.Cands[0] := 'cc';
  Result.Cands[1] := 'clang';
  Result.HostTool := False;
  if ATarget.OS = osWindows then
    Result.CrossPrefix := 'x86_64-w64-mingw32-'
  else
    Result.CrossPrefix := '';
end;

function TBackendDriver.DescribeTools(const ATarget: TTargetDesc): TToolSpecArray;
begin
  SetLength(Result, 1);
  Result[0] := Self.LinkerToolSpec(ATarget);
end;

function TBackendDriver.ToolPath(const AName: string;
  const ATarget: TTargetDesc): string;
var
  Specs: TToolSpecArray;
  I:     Integer;
begin
  Result := '';
  Specs := Self.DescribeTools(ATarget);
  for I := 0 to High(Specs) do
    if SameText(Specs[I].Name, AName) then
      Exit(ResolveSpec(Specs[I], ATarget));
end;

function TBackendDriver.CheckToolchain(AOpts: TBackendOpts): string;
begin
  { No tools to probe by default.  AOpts is part of the signature so a
    backend probe can read e.g. AOpts.Target. }
  Result := '';
end;

function TBackendDriver.AcceptOption(const AFlag, ANextArg: string;
  AOpts: TBackendOpts): TOptionAccept;
begin
  Result := oaUnknown;
end;

procedure TBackendDriver.DescribeOptions(ALines: TStringList);
begin
  { No backend-private flags by default. }
end;

function TBackendDriver.ValidateOptions(AOpts: TBackendOpts): string;
begin
  Result := '';
end;

function TBackendDriver.ClaimsEmitIR: Boolean;
begin
  Result := False;
end;

function TBackendDriver.CreateUnitCodeGen(AOpts: TBackendOpts): ICodeGen;
begin
  Result := nil;
end;

function TBackendDriver.LowerToObject(const AIRFile, AObjFile: string;
  AOpts: TBackendOpts): string;
begin
  Result := Self.Name() +
    ' backend does not support per-unit object lowering';
end;

function TBackendDriver.LinkViaToolchain(const AInputFile, AOutputFile: string;
  AOpts: TBackendOpts; AExtraObjects: TStringList): string;
var
  TC: TToolchain;
  Args: TStringList;
  Msg: string;
  ExitCode: Integer;
  I: Integer;
begin
  Result := '';
  TC := ResolveToolchain(AOpts.Target);
  { Every Blaise program needs blaise_rtl.a; an empty RTLPath means it was not
    found beside the compiler binary or via $BLAISE_RTL.  Linking without it
    yields a flood of undefined-reference errors from the external linker (or,
    on the internal linker, a silently broken binary) — fail with a clear
    message instead. }
  if TC.RTLPath = '' then
    Exit('runtime archive blaise_rtl.a not found '
      + '(looked beside the compiler binary and in $BLAISE_RTL); '
      + 'cannot link a Blaise program without the RTL');
  Args := TStringList.Create();
  try
    Args.Add('-o');
    Args.Add(AOutputFile);
    Args.Add(AInputFile);
    { Linker resolved via DescribeTools so a Windows target picks the mingw
      cross-linker and a Windows host adds the .exe extension. }
    { OPDF sidecar (QBE backend only — the native backend appends its
      exact-facts OPDF section to the main assembly instead). }
    if (AOpts.OPDFAsmFile <> '') and FileExists(AOpts.OPDFAsmFile) then
      Args.Add(AOpts.OPDFAsmFile);
    { Pre-built dep object files (auto-discovered by the loader or
      produced by the --incremental workers). }
    if AExtraObjects <> nil then
      for I := 0 to AExtraObjects.Count - 1 do
        Args.Add(AExtraObjects.Strings[I]);
    Args.Add(TC.RTLPath);
    Args.Add('-lm');       { math functions (sqrt, sin, cos, etc.) }
    Args.Add('-lpthread'); { POSIX threads (blaise_thread unit) }
    ExitCode := RunProcess(Self.ToolPath('linker', AOpts.Target), Args, Msg);
  finally
    Args.Free();
  end;
  if ExitCode <> 0 then
    Result := 'link error (exit ' + IntToStr(ExitCode) + '): ' + Msg;
end;

function FormatFlagLine(const AFlag, ADesc: string): string;
const
  { Matches the shared usage block in Blaise.pas PrintUsage: 2-space
    indent, flag field padded so the description starts at column 20. }
  Indent = '  ';
  FlagFieldWidth = 18;
var
  Pad: Integer;
begin
  Result := Indent + AFlag;
  Pad := FlagFieldWidth - Length(AFlag);
  if Pad < 1 then
    Pad := 1;   { always at least one space before the description }
  while Pad > 0 do
  begin
    Result := Result + ' ';
    Pad := Pad - 1;
  end;
  Result := Result + ADesc;
end;

function ReadProcessChunk(AProc: TProcess): string;
begin
  Result := AProc.ReadOutput()
end;

function RunProcess(const AExe: string; AArgs: TStringList;
  out AOutput: string): Integer;
var
  Proc: TProcess;
  Chunk: string;
  I: Integer;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    for I := 0 to AArgs.Count - 1 do
      Proc.Parameters.Add(AArgs.Strings[I]);
    Proc.Execute();
    AOutput := '';
    repeat
      Chunk := ReadProcessChunk(Proc);
      AOutput := AOutput + Chunk;
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode;
  finally
    Proc.Free();
  end;
end;

procedure RegisterDriver(ADriver: TBackendDriver);
begin
  GDrivers[Ord(ADriver.Kind())] := ADriver;
end;

function GetDriver(AKind: TBackendKind): TBackendDriver;
begin
  Result := GDrivers[Ord(AKind)];
  if Result = nil then
    raise Exception.Create(
      'blaise.codegen.driver: no driver registered for backend kind ' +
      IntToStr(Ord(AKind)) + ' (unit not pulled into uses clause?)');
end;

function RegisteredBackendNames: TStringList;
var
  I: Integer;
begin
  Result := TStringList.Create();
  for I := 0 to 1 do
    if GDrivers[I] <> nil then
      Result.Add(GDrivers[I].Name());
end;

function ParseBackendName(const AName: string; out AKind: TBackendKind): Boolean;
var
  I: Integer;
begin
  Result := False;
  for I := 0 to 1 do
    if (GDrivers[I] <> nil) and SameText(AName, GDrivers[I].Name()) then
    begin
      AKind := GDrivers[I].Kind();
      Result := True;
      Exit;
    end;
end;

function PickTopDriver(ABackend: TBackendKind;
  AEmitIR, AEmitAsm: Boolean): TBackendDriver;
var
  I: Integer;
begin
  if AEmitIR then
  begin
    { --emit-ir prints the IR text of whichever backend claims it.  Ask
      the drivers instead of hard-coding bkQBE, so a future IR-producing
      backend (LLVM) needs no carve-out here. }
    for I := 0 to 1 do
      if (GDrivers[I] <> nil) and GDrivers[I].ClaimsEmitIR() then
        Exit(GDrivers[I]);
    { No registered backend claims --emit-ir: fall back to QBE, the
      historical owner of the byte-identical IR contract. }
    Result := GetDriver(bkQBE);
  end
  else if AEmitAsm then
    Result := GetDriver(bkNative)
  else
    Result := GetDriver(ABackend);
end;

end.
