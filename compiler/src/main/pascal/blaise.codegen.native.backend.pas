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
  SysUtils, uAST, uSymbolTable, blaise.codegen, strutils, blaise.codegen.target, uDebugFacts;

type
  ENativeCodeGenError = class(Exception);

  TNativeBackend = class
  protected
    FTarget:    TTargetDesc;
    FSymTable:  TSymbolTable;     { not owned }
    FDebugMode: Boolean;
    { Separate-compilation (incremental unit) mode: suppress the once-per-program
      TObject/TCustomAttribute system defs, which the program object provides —
      emitting them in each unit object would collide at link time. }
    FSeparateCompile: Boolean;
    FFinalized: Boolean;
    { Assembly text is built append-only and read once at the end, so a
      TStringBuilder (single growable buffer, no per-line heap string and no
      O(N^2) final concat) is the right structure — the same approach the QBE
      backend's TIRBuffer uses. }
    FAsm:      TStringBuilder;

    { Append one line of assembly (a newline is added). }
    procedure Emit(const ALine: string);
    { Append a blank separator line. }
    procedure EmitBlank;

    function IsRecordManagedClean(ARec: TRecordTypeDesc): Boolean;
    function IsRecordAllIntegerLeaves(ARec: TRecordTypeDesc): Boolean;
    function IsRecordAllFloatLeaves(ARec: TRecordTypeDesc): Boolean;
    function IsRecordAllIntOrFloatLeaves(ARec: TRecordTypeDesc): Boolean;
    function EightbyteIsSSE(ARec: TRecordTypeDesc; AStartByte: Integer): Boolean;
    function ClassifyRecordReturn(ARec: TRecordTypeDesc): TRecReturnClass;

    { ---- target-specific program lowering (abstract) ---- }

    { Emit the program entry function ($main): label, frame setup, the
      _SetArgs runtime call, then lower the program body, then return 0. }
    procedure EmitProgram(AProg: TProgram); virtual; abstract;
    { Emit a dependency unit's bodies + data (no $main) into the shared buffer
      for the whole-program multi-unit model. }
    procedure EmitUnit(AUnit: TUnit); virtual; abstract;
    { Emit accumulated data (.data/.bss/.rodata) after all units have been
      processed.  Called once from GenerateUnit or GetOutput — never from
      EmitUnit itself, because in unit-mode the driver appends dep units
      first and the data section must materialise only once at the end. }
    procedure FinalizeEmit; virtual;
  public
    constructor Create(const ATarget: TTargetDesc); virtual;
    destructor Destroy; override;

    { Multi-unit (whole-program) codegen: AppendUnit per dependency, then
      AppendProgram — neither clears the buffer, so units + program accumulate
      into one assembly text retrieved via GetOutput. }
    procedure AppendUnit(AUnit: TUnit);
    procedure AppendProgram(AProg: TProgram);
    { Separate-compilation init-call registration: record a dep unit whose body
      is compiled elsewhere so $main still calls its <Unit>_init.  Concrete
      backends that maintain an init-call list override this; the default is a
      no-op. }
    procedure NoteDepInitUnit(const AUnitName: string;
      AHasInit: Boolean); virtual;
    function  GetOutput: string;

    procedure SetSymbolTable(ASymTable: TSymbolTable);
    procedure SetSeparateCompile(AEnabled: Boolean);
    { OPDF debug-facts sink — concrete backends that support exact debug
      info override this; the default ignores the facts object. }
    procedure SetDebugFacts(AFacts: TDbgFacts); virtual;
    procedure SetDebugMode(AEnabled: Boolean);

    { Lower a whole program to assembly text and return it. }
    function GenerateProgram(AProg: TProgram): string;
    { Lower a single unit (in isolation) to assembly text and return it. }
    function GenerateUnit(AUnit: TUnit): string;

    property Target: TTargetDesc read FTarget;
  end;

  TNativeBackendClass = class of TNativeBackend;

implementation

procedure TNativeBackend.SetDebugFacts(AFacts: TDbgFacts);
begin
  { Default: backend does not collect debug facts. }
end;

procedure TNativeBackend.FinalizeEmit;
begin
end;

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

procedure TNativeBackend.SetSeparateCompile(AEnabled: Boolean);
begin
  FSeparateCompile := AEnabled;
end;

procedure TNativeBackend.SetDebugMode(AEnabled: Boolean);
begin
  FDebugMode := AEnabled;
end;

procedure TNativeBackend.Emit(const ALine: string);
begin
  FAsm.AppendLine(ALine);
end;

procedure TNativeBackend.EmitBlank;
begin
  FAsm.AppendLine;
end;

{ The record-return ABI classifier and its leaf predicates now live as shared
  free functions in blaise.codegen (byte-identical to the QBE backend's former
  twin).  These methods delegate so existing Self.X call sites are unchanged. }
function TNativeBackend.IsRecordManagedClean(ARec: TRecordTypeDesc): Boolean;
begin
  Result := RecretManagedClean(ARec);
end;

function TNativeBackend.IsRecordAllIntegerLeaves(ARec: TRecordTypeDesc): Boolean;
begin
  Result := RecretAllIntegerLeaves(ARec);
end;

function TNativeBackend.IsRecordAllFloatLeaves(ARec: TRecordTypeDesc): Boolean;
begin
  Result := RecretAllFloatLeaves(ARec);
end;

function TNativeBackend.IsRecordAllIntOrFloatLeaves(ARec: TRecordTypeDesc): Boolean;
begin
  Result := RecretAllIntOrFloatLeaves(ARec);
end;

function TNativeBackend.EightbyteIsSSE(ARec: TRecordTypeDesc;
  AStartByte: Integer): Boolean;
begin
  Result := RecretEightbyteIsSSE(ARec, AStartByte);
end;

function TNativeBackend.ClassifyRecordReturn(ARec: TRecordTypeDesc): TRecReturnClass;
begin
  Result := RecretClassify(ARec, FTarget);
end;

function TNativeBackend.GenerateProgram(AProg: TProgram): string;
begin
  FAsm.Clear();
  Self.EmitProgram(AProg);
  Result := FAsm.ToString();
end;

function TNativeBackend.GenerateUnit(AUnit: TUnit): string;
begin
  FAsm.Clear();
  FSeparateCompile := True;
  Self.EmitUnit(AUnit);
  Self.FinalizeEmit();
  Result := FAsm.ToString();
end;

procedure TNativeBackend.AppendUnit(AUnit: TUnit);
begin
  { No clear — units and the program accumulate into one buffer. }
  Self.EmitUnit(AUnit);
end;

procedure TNativeBackend.AppendProgram(AProg: TProgram);
begin
  { No clear — emit the program after the already-appended units. }
  Self.EmitProgram(AProg);
end;

procedure TNativeBackend.NoteDepInitUnit(const AUnitName: string;
  AHasInit: Boolean);
begin
  { Default: no init-call list to maintain.  The x86_64 backend overrides. }
end;

function TNativeBackend.GetOutput: string;
begin
  if FSeparateCompile and (not FFinalized) then
    Self.FinalizeEmit();
  Result := FAsm.ToString();
end;

end.
