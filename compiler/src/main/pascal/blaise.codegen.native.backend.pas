{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.native.backend;

{ Abstract per-architecture machine-code lowering base for the native code
  generator.

  Lives in its own unit (separate from blaise.codegen.native) so the concrete
  per-CPU backends — blaise.codegen.native.x86_64 etc. — can subclass it
  without a circular dependency back to the driver unit that constructs them.

  A concrete subclass implements instruction selection, register allocation,
  ABI lowering, and assembly printing for one target CPU.  Shared, non-abstract
  helpers (the naive stack-slot allocator, cross-target emit utilities) will be
  added here as the backend grows.

  ARC lowering note (for the coming i386 / arm64 backends): the *decision* logic
  for ARC is already target-independent — `NativeExprOwnsRef` (a free function
  over the AST) decides whether a value owns +1, and the field-kind walk in the
  x86-64 backend's EmitRecordFieldReleases / EmitGlobalReleases decides *which*
  fields/globals need a release.  Only the leaf emission (which register holds
  the base, which mnemonic loads/stores it) is CPU-specific.  When a second
  backend lands, lift those walkers here as template methods whose leaf steps
  (load-field-ptr, call-release, store-zero) are abstract per-CPU primitives,
  rather than duplicating the field-kind dispatch in each subclass. }

interface

uses
  SysUtils, uAST, uSymbolTable, strutils, blaise.codegen.target;

type
  ENativeCodeGenError = class(Exception);

  TNativeBackend = class
  protected
    FTarget:   TTargetDesc;
    FSymTable: TSymbolTable;     { not owned }
    { Assembly text is built append-only and read once at the end, so a
      TStringBuilder (single growable buffer, no per-line heap string and no
      O(N^2) final concat) is the right structure — the same approach the QBE
      backend's TIRBuffer uses. }
    FAsm:      TStringBuilder;

    { Append one line of assembly (a newline is added). }
    procedure Emit(const ALine: string);
    { Append a blank separator line. }
    procedure EmitBlank;

    { ---- target-specific program lowering (abstract) ---- }

    { Emit the program entry function ($main): label, frame setup, the
      _SetArgs runtime call, then lower the program body, then return 0. }
    procedure EmitProgram(AProg: TProgram); virtual; abstract;
  public
    constructor Create(const ATarget: TTargetDesc); virtual;
    destructor Destroy; override;

    procedure SetSymbolTable(ASymTable: TSymbolTable);

    { Lower a whole program to assembly text and return it. }
    function GenerateProgram(AProg: TProgram): string;

    property Target: TTargetDesc read FTarget;
  end;

  TNativeBackendClass = class of TNativeBackend;

implementation

constructor TNativeBackend.Create(const ATarget: TTargetDesc);
begin
  inherited Create();
  FTarget   := ATarget;
  FSymTable := nil;
  FAsm      := TStringBuilder.Create();
end;

destructor TNativeBackend.Destroy;
begin
  FAsm.Free();
  inherited Destroy();
end;

procedure TNativeBackend.SetSymbolTable(ASymTable: TSymbolTable);
begin
  FSymTable := ASymTable;
end;

procedure TNativeBackend.Emit(const ALine: string);
begin
  FAsm.AppendLine(ALine);
end;

procedure TNativeBackend.EmitBlank;
begin
  FAsm.AppendLine;
end;

function TNativeBackend.GenerateProgram(AProg: TProgram): string;
begin
  FAsm.Clear();
  Self.EmitProgram(AProg);
  Result := FAsm.ToString();
end;

end.
