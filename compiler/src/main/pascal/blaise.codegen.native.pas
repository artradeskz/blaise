{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.native;

{ Native code-generation backend — emits target assembly directly from the
  AST, replacing the external QBE tool (docs/toolchain-independence.adoc,
  Phase 5).

  Structure (two layers):

    TCodeGenNative   implements ICodeGen; walks the AST (the same TProgram /
                     TUnit the QBE backend receives) and drives a per-target
                     TNativeBackend.  GetOutput returns assembly text.

    TNativeBackend   abstract base over per-architecture machine-code lowering
                     (instruction selection, register allocation, assembly
                     printing, ABI).  Concrete subclasses live in
                     blaise.codegen.native.<arch> — TX86_64Backend first.

  This unit is currently a SHELL (milestone M0b): the interface, target
  selection, and backend factory are wired up, but code emission is not yet
  implemented and raises ENativeCodeGenError so an attempted native compile
  fails loudly with a clear message rather than producing nothing. }

interface

uses
  SysUtils, uAST, uSymbolTable, uCodeGen,
  blaise.codegen.target, blaise.codegen.native.backend;

type
  { ICodeGen implementation that lowers the AST to native assembly. }
  TCodeGenNative = class(TObject, ICodeGen)
  private
    FTarget:    TTargetDesc;
    FSymTable:  TSymbolTable;
    FDebugMode: Boolean;
    FBackend:   TNativeBackend;
    FOutput:    string;
    procedure EnsureBackend;
  public
    constructor Create;
    destructor Destroy; override;

    { Backend-specific configuration — set before the object is used as an
      ICodeGen.  Not part of the ICodeGen contract. }
    procedure SetTarget(const ATarget: TTargetDesc);

    { ICodeGen }
    procedure Generate(AProg: TProgram);
    procedure GenerateUnit(AUnit: TUnit);
    procedure SetSymbolTable(ASymTable: TSymbolTable);
    procedure SetDebugMode(AEnabled: Boolean);
    procedure AppendUnit(AUnit: TUnit);
    procedure AppendProgram(AProg: TProgram);
    function  GetOutput: string;
  end;

{ Construct the backend for a target, or raise ENativeCodeGenError if no
  native backend is implemented for it. }
function CreateNativeBackend(const ATarget: TTargetDesc): TNativeBackend;

implementation

uses
  blaise.codegen.native.x86_64;

{ ------------------------------------------------------------------ }
{ Backend factory                                                     }
{ ------------------------------------------------------------------ }

function CreateNativeBackend(const ATarget: TTargetDesc): TNativeBackend;
begin
  if (ATarget.OS = osLinux) and (ATarget.CPU = cpuX86_64) then
    Result := TX86_64Backend.Create(ATarget)
  else
    raise ENativeCodeGenError.Create(
      'native backend not yet implemented for target ' + TargetName(ATarget));
end;

{ ------------------------------------------------------------------ }
{ TCodeGenNative                                                      }
{ ------------------------------------------------------------------ }

constructor TCodeGenNative.Create;
begin
  inherited Create;
  MakeTarget(osLinux, cpuX86_64, FTarget);
  FSymTable  := nil;
  FDebugMode := False;
  FBackend   := nil;
  FOutput    := '';
end;

destructor TCodeGenNative.Destroy;
begin
  FBackend.Free;
  inherited Destroy;
end;

procedure TCodeGenNative.SetTarget(const ATarget: TTargetDesc);
begin
  FTarget := ATarget;
end;

procedure TCodeGenNative.EnsureBackend;
begin
  if FBackend = nil then
    FBackend := CreateNativeBackend(FTarget);
end;

procedure TCodeGenNative.SetSymbolTable(ASymTable: TSymbolTable);
begin
  FSymTable := ASymTable;
end;

procedure TCodeGenNative.SetDebugMode(AEnabled: Boolean);
begin
  FDebugMode := AEnabled;
end;

procedure TCodeGenNative.Generate(AProg: TProgram);
begin
  Self.EnsureBackend;
  raise ENativeCodeGenError.Create(
    'native code generation is not yet implemented (target ' +
    TargetName(FTarget) + ')');
end;

procedure TCodeGenNative.GenerateUnit(AUnit: TUnit);
begin
  Self.EnsureBackend;
  raise ENativeCodeGenError.Create(
    'native code generation is not yet implemented (target ' +
    TargetName(FTarget) + ')');
end;

procedure TCodeGenNative.AppendUnit(AUnit: TUnit);
begin
  Self.EnsureBackend;
  raise ENativeCodeGenError.Create(
    'native code generation is not yet implemented (target ' +
    TargetName(FTarget) + ')');
end;

procedure TCodeGenNative.AppendProgram(AProg: TProgram);
begin
  Self.EnsureBackend;
  raise ENativeCodeGenError.Create(
    'native code generation is not yet implemented (target ' +
    TargetName(FTarget) + ')');
end;

function TCodeGenNative.GetOutput: string;
begin
  Result := FOutput;
end;

end.
