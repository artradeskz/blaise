{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines, Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uToolchain;

{ Resolution of the external tools the Blaise driver shells out to and the
  install-relative path to the Blaise RTL archive.

  Lives separately from Blaise.pas so the policy — env-var overrides, PATH
  probing, install-dir lookups — is in one place.

  Resolution is uniform across all slots:

    1. Explicit env-var override (BLAISE_QBE, BLAISE_AS, BLAISE_LINKER,
       BLAISE_RTL).  If set and the file exists, use it verbatim.
    2. Walk $PATH for a list of candidate basenames in preference order.
    3. Fall back to the first candidate basename — RunProcess surfaces a
       "not found" error at exec time if the tool was actually needed.

  This trimmed version was ported from a contributor LLVM-backend branch.  The
  LLVM-specific slots (llc / opt / llvm-dlltool, Windows import libs, well-
  known LLVM install-dir probing) were dropped: the native backend emits
  assembly text and links with a cc driver, exactly like the QBE path. }

interface

uses
  blaise.codegen.target;

type
  { Variant of a tool, determining the CLI syntax callers emit. }
  TToolKind = (
    tkUnknown,        { resolver couldn't classify }
    tkAs,             { as -o OUT IN.s — GNU assembler }
    tkCCDriver,       { cc / gcc / clang-as-driver — GNU link line }
    tkQBE             { qbe -o OUT IN.ssa }
  );

  TTool = record
    Path: string;     { absolute path on a hit, basename on miss }
    Kind: TToolKind;  { set by the per-tool resolver }
  end;

  TToolchain = record
    QBE:        TTool;   { QBE backend only }
    Assembler:  TTool;   { native backend: assemble .s -> .o (reserved) }
    Linker:     TTool;   { both backends: link final binary }
    RTLPath:    string;  { '' if not found }
  end;

{ One-shot resolver — call once per native/QBE compile, read the resulting
  record for every subprocess + library path. }
function ResolveToolchain(const ATarget: TTargetDesc): TToolchain;

{ Per-tool resolvers — exported for diagnostics + selective use. }
function ResolveQBE: TTool;
function ResolveAssembler: TTool;
function ResolveLinker(const ATarget: TTargetDesc): TTool;
function FindRTLArchive(const ATarget: TTargetDesc): string;

{ Walks $PATH for the first file named ABaseName that exists.  Returns the
  absolute path on hit, '' on miss.  On Windows hosts also tries '.exe'. }
function WhichInPath(const ABaseName: string): string;

implementation

uses
  SysUtils;

{ Host path conventions.  The Blaise compiler currently runs only on POSIX
  hosts (linux/freebsd/macos), so the host directory delimiter is '/' and the
  PATH list separator is ':'.  These describe the HOST the compiler runs on,
  not the --target it generates code for (cross-compilation does not change how
  we probe the local $PATH).  When a Windows host build lands, switch these to
  query the active platform RTL. }

{ ------------------------------------------------------------------ }
{ PATH walker                                                          }
{ ------------------------------------------------------------------ }

function IsWindowsHost: Boolean;
begin
  Result := False;
end;

function PathSep: string;
begin
  Result := PathSeparator;  { ':' on POSIX }
end;

function TrySingleName(const ADir, ABaseName: string): string;
var
  Candidate: string;
begin
  Candidate := IncludeTrailingPathDelimiter(ADir) + ABaseName;
  if FileExists(Candidate) then
  begin
    Result := Candidate;
    Exit;
  end;
  { Blaise Pos: -1 = not found.  `< 0` is the "not present" test. }
  if IsWindowsHost and (Pos('.exe', LowerCase(ABaseName)) < 0) then
  begin
    Candidate := IncludeTrailingPathDelimiter(ADir) + ABaseName + '.exe';
    if FileExists(Candidate) then
    begin
      Result := Candidate;
      Exit;
    end;
  end;
  Result := '';
end;

function WhichInPath(const ABaseName: string): string;
var
  Path, Entry: string;
  SepPos:      Integer;
  Hit:         string;
begin
  Result := '';
  if ABaseName = '' then Exit;
  Path := GetEnvironmentVariable('PATH');
  while Length(Path) > 0 do
  begin
    { Blaise Pos/Copy are 0-based; -1 = not found.  Consume one PATH entry
      per iteration. }
    SepPos := Pos(PathSep, Path);
    if SepPos >= 0 then
    begin
      Entry := Copy(Path, 0, SepPos);
      Path  := Copy(Path, SepPos + 1, MaxInt);
    end
    else
    begin
      Entry := Path;
      Path  := '';
    end;
    if Entry = '' then Continue;
    Hit := TrySingleName(Entry, ABaseName);
    if Hit <> '' then
    begin
      Result := Hit;
      Exit;
    end;
  end;
end;

{ ------------------------------------------------------------------ }
{ Generic resolver                                                     }
{ ------------------------------------------------------------------ }

{ Resolve one candidate string.  If it contains a path separator, treat it as
  a path and FileExists-check directly; otherwise PATH-walk for the basename. }
function TryCandidate(const ACand: string): string;
begin
  Result := '';
  if ACand = '' then Exit;
  if (Pos('/', ACand) >= 0) or (Pos('\', ACand) >= 0) then
  begin
    if FileExists(ACand) then Result := ACand;
  end
  else
    Result := WhichInPath(ACand);
end;

{ Two-stage probe — env override, then candidate-walk (each candidate may be a
  bare basename -> PATH-search or a path -> FileExists), then bare-name
  fallback so RunProcess surfaces a clean error at invoke time. }
function ResolveToolPath(const AEnvVar, ACandA, ACandB: string): string;
var
  EnvPath, Hit: string;
begin
  Result := '';
  if AEnvVar <> '' then
  begin
    EnvPath := GetEnvironmentVariable(AEnvVar);
    if (EnvPath <> '') and FileExists(EnvPath) then
    begin
      Result := EnvPath;
      Exit;
    end;
  end;
  Hit := TryCandidate(ACandA);
  if Hit <> '' then begin Result := Hit; Exit end;
  Hit := TryCandidate(ACandB);
  if Hit <> '' then begin Result := Hit; Exit end;
  if ACandA <> '' then
    Result := ACandA
  else
    Result := ACandB;
end;

{ ------------------------------------------------------------------ }
{ Per-tool resolvers                                                   }
{ ------------------------------------------------------------------ }

function ResolveQBE: TTool;
begin
  Result.Path := ResolveToolPath('BLAISE_QBE', 'qbe', '');
  Result.Kind := tkQBE;
end;

function ResolveAssembler: TTool;
begin
  Result.Path := ResolveToolPath('BLAISE_AS', 'as', '');
  Result.Kind := tkAs;
end;

function ResolveLinker(const ATarget: TTargetDesc): TTool;
begin
  Result.Path := ResolveToolPath('BLAISE_LINKER', 'cc', '');
  Result.Kind := tkCCDriver;
end;

{ ------------------------------------------------------------------ }
{ Install-relative paths                                               }
{ ------------------------------------------------------------------ }

function CompilerBinDir: string;
begin
  Result := ExtractFilePath(ParamStr(0));
end;

function FindRTLArchive(const ATarget: TTargetDesc): string;
var
  BinDir: string;
begin
  Result := GetEnvironmentVariable('BLAISE_RTL');
  if (Result <> '') and FileExists(Result) then Exit;
  BinDir := CompilerBinDir;
  Result := IncludeTrailingPathDelimiter(BinDir) + 'blaise_rtl.a';
  if FileExists(Result) then Exit;
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Top-level resolver                                                   }
{ ------------------------------------------------------------------ }

function ResolveToolchain(const ATarget: TTargetDesc): TToolchain;
begin
  Result.QBE       := ResolveQBE;
  Result.Assembler := ResolveAssembler;
  Result.Linker    := ResolveLinker(ATarget);
  Result.RTLPath   := FindRTLArchive(ATarget);
end;

end.
