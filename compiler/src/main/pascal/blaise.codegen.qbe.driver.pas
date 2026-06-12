{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.qbe.driver;

{ TBackendDriver subclass for the QBE backend.

  Owns the answers Blaise.pas used to compute via `if Backend = bkQBE`:
  which ICodeGen to instantiate (TCodeGenQBE) and its knob setup, the IR
  file extension (.ssa), and the qbe -> .s -> cc lowering/link steps.

  Architecture follows Andrew Haines' unify_backend_interface proposal.

  Pull this unit into Blaise.pas's uses clause; the initialization block
  registers the singleton driver. }

interface

uses
  Classes,
  blaise.codegen,
  blaise.codegen.qbe,
  blaise.codegen.driver;

type
  TQBEBackendDriver = class(TBackendDriver)
  public
    function Kind: TBackendKind; override;
    function Name: string; override;
    function IRFileExt: string; override;
    function SupportsIncremental: Boolean; override;
    function SupportsWarmCache: Boolean; override;
    function CreateCodeGen(AOpts: TBackendOpts): ICodeGen; override;
    function CreateUnitCodeGen(AOpts: TBackendOpts): ICodeGen; override;
    function LowerToObject(const AIRFile, AObjFile: string;
      AOpts: TBackendOpts): string; override;
    function LinkProgram(const AIRFile, AOutputFile: string;
      AOpts: TBackendOpts; AExtraObjects: TStringList): string; override;
  protected
    { qbe AIRFile -> AAsmFile.  Returns '' on success. }
    function LowerToAsm(const AIRFile, AAsmFile: string;
      AOpts: TBackendOpts): string;
  end;

implementation

uses
  SysUtils,
  uToolchain;

function TQBEBackendDriver.Kind: TBackendKind;
begin
  Result := bkQBE;
end;

function TQBEBackendDriver.Name: string;
begin
  Result := 'qbe';
end;

function TQBEBackendDriver.IRFileExt: string;
begin
  Result := '.ssa';
end;

function TQBEBackendDriver.SupportsIncremental: Boolean;
begin
  Result := True;
end;

function TQBEBackendDriver.SupportsWarmCache: Boolean;
begin
  { QBE-emitted .o files participate in the warm cache: each parallel
    unit worker writes a .o + embedded .bif, uUnitLoader discovers them
    on the next compile and hash-matches against the .pas to decide
    whether to skip recompilation. }
  Result := True;
end;

function TQBEBackendDriver.CreateCodeGen(AOpts: TBackendOpts): ICodeGen;
var
  CG: TCodeGenQBE;
begin
  CG := TCodeGenQBE.Create();
  CG.SetDebugMode(AOpts.DebugMode);
  CG.SetOpdfMode(AOpts.OPDFEnabled);
  { TCodeGenQBE has no target knob; AOpts.Target only affects the
    link step. }
  Result := CG;
end;

function TQBEBackendDriver.CreateUnitCodeGen(AOpts: TBackendOpts): ICodeGen;
var
  CG: TCodeGenQBE;
begin
  { Same as CreateCodeGen plus SetExportAll(True) so sibling units in
    the link can resolve this unit's globals.  The knob is applied here
    so TCompileWorker relies on ICodeGen alone — no backend casts. }
  CG := TCodeGenQBE.Create();
  CG.SetDebugMode(AOpts.DebugMode);
  CG.SetOpdfMode(AOpts.OPDFEnabled);
  CG.SetExportAll(True);
  Result := CG;
end;

function TQBEBackendDriver.LowerToAsm(const AIRFile, AAsmFile: string;
  AOpts: TBackendOpts): string;
var
  Args: TStringList;
  Msg: string;
  ExitCode: Integer;
begin
  Result := '';
  Args := TStringList.Create();
  try
    Args.Add('-o');
    Args.Add(AAsmFile);
    Args.Add(AIRFile);
    ExitCode := RunProcess(ResolveQBE().Path, Args, Msg);
  finally
    Args.Free();
  end;
  if ExitCode <> 0 then
    Result := 'qbe error (exit ' + IntToStr(ExitCode) + '): ' + Msg;
end;

function TQBEBackendDriver.LowerToObject(const AIRFile, AObjFile: string;
  AOpts: TBackendOpts): string;
var
  AsmFile: string;
  Args: TStringList;
  Msg: string;
  ExitCode: Integer;
begin
  AsmFile := ChangeFileExt(AIRFile, '.s');
  Result := Self.LowerToAsm(AIRFile, AsmFile, AOpts);
  if Result <> '' then Exit;

  Args := TStringList.Create();
  try
    Args.Add('-c');
    Args.Add('-o');
    Args.Add(AObjFile);
    Args.Add(AsmFile);
    ExitCode := RunProcess(ResolveLinker(AOpts.Target).Path, Args, Msg);
  finally
    Args.Free();
  end;
  if ExitCode <> 0 then
    Exit('cc -c error (exit ' + IntToStr(ExitCode) + '): ' + Msg);

  DeleteFile(AsmFile);
end;

function TQBEBackendDriver.LinkProgram(const AIRFile, AOutputFile: string;
  AOpts: TBackendOpts; AExtraObjects: TStringList): string;
var
  AsmFile: string;
begin
  AsmFile := ChangeFileExt(AIRFile, '.s');
  Result := Self.LowerToAsm(AIRFile, AsmFile, AOpts);
  if Result <> '' then Exit;
  Result := Self.LinkViaToolchain(AsmFile, AOutputFile, AOpts, AExtraObjects);
  { The intermediate .s is this driver's own artefact.  Keep it on link
    failure as a debugging aid (matches the pre-driver behaviour). }
  if Result = '' then
    DeleteFile(AsmFile);
end;

initialization
  RegisterDriver(TQBEBackendDriver.Create());

end.
