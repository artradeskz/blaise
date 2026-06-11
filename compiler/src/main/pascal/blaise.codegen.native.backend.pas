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
  public
    constructor Create(const ATarget: TTargetDesc); virtual;
    destructor Destroy; override;

    { Multi-unit (whole-program) codegen: AppendUnit per dependency, then
      AppendProgram — neither clears the buffer, so units + program accumulate
      into one assembly text retrieved via GetOutput. }
    procedure AppendUnit(AUnit: TUnit);
    procedure AppendProgram(AProg: TProgram);
    function  GetOutput: string;

    procedure SetSymbolTable(ASymTable: TSymbolTable);
    { OPDF debug-facts sink — concrete backends that support exact debug
      info override this; the default ignores the facts object. }
    procedure SetDebugFacts(AFacts: TDbgFacts); virtual;
    procedure SetDebugMode(AEnabled: Boolean);

    { Lower a whole program to assembly text and return it. }
    function GenerateProgram(AProg: TProgram): string;

    property Target: TTargetDesc read FTarget;
  end;

  TNativeBackendClass = class of TNativeBackend;

implementation

procedure TNativeBackend.SetDebugFacts(AFacts: TDbgFacts);
begin
  { Default: backend does not collect debug facts. }
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

function TNativeBackend.IsRecordManagedClean(ARec: TRecordTypeDesc): Boolean;
var
  I: Integer;
  F: TFieldInfo;
begin
  Result := False;
  if ARec = nil then Exit;
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Items[I]);
    case F.TypeDesc.Kind of
      tyString, tyClass, tyInterface, tyDynArray:
        Exit;
      tyRecord:
        if not Self.IsRecordManagedClean(TRecordTypeDesc(F.TypeDesc)) then Exit;
    end;
  end;
  Result := True;
end;

function TNativeBackend.IsRecordAllIntegerLeaves(ARec: TRecordTypeDesc): Boolean;
var
  I: Integer;
  F: TFieldInfo;
begin
  Result := False;
  if ARec = nil then Exit;
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Items[I]);
    case F.TypeDesc.Kind of
      tyInteger, tyInt64, tyUInt32, tyUInt64,
      tySmallInt, tyWord, tyByte, tyBoolean,
      tyEnum, tyPointer, tyProcedural, tyMetaClass:
        ;
      tyRecord:
        if not Self.IsRecordAllIntegerLeaves(TRecordTypeDesc(F.TypeDesc)) then Exit;
    else
      Exit;
    end;
  end;
  Result := True;
end;

function TNativeBackend.IsRecordAllFloatLeaves(ARec: TRecordTypeDesc): Boolean;
var
  I: Integer;
  F: TFieldInfo;
begin
  Result := False;
  if ARec = nil then Exit;
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Items[I]);
    case F.TypeDesc.Kind of
      tyDouble, tySingle: ;
      tyRecord:
        if not Self.IsRecordAllFloatLeaves(TRecordTypeDesc(F.TypeDesc)) then Exit;
    else
      Exit;
    end;
  end;
  Result := True;
end;

function TNativeBackend.IsRecordAllIntOrFloatLeaves(ARec: TRecordTypeDesc): Boolean;
var
  I: Integer;
  F: TFieldInfo;
begin
  Result := False;
  if ARec = nil then Exit;
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Items[I]);
    case F.TypeDesc.Kind of
      tyInteger, tyInt64, tyUInt32, tyUInt64,
      tySmallInt, tyWord, tyByte, tyBoolean,
      tyEnum, tyPointer, tyProcedural, tyMetaClass,
      tyDouble, tySingle: ;
      tyRecord:
        if not Self.IsRecordAllIntOrFloatLeaves(TRecordTypeDesc(F.TypeDesc)) then Exit;
    else
      Exit;
    end;
  end;
  Result := True;
end;

function TNativeBackend.EightbyteIsSSE(ARec: TRecordTypeDesc;
  AStartByte: Integer): Boolean;
var
  I, Off: Integer;
  F:      TFieldInfo;
begin
  Result := False;
  if ARec = nil then Exit;
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F   := TFieldInfo(ARec.Fields.Items[I]);
    Off := F.Offset;
    if (Off < AStartByte) or (Off >= AStartByte + 8) then Continue;
    case F.TypeDesc.Kind of
      tyDouble, tySingle:
        Exit(True);
      tyRecord:
        if Self.EightbyteIsSSE(TRecordTypeDesc(F.TypeDesc),
                          AStartByte - Off) then Exit(True);
    end;
  end;
end;

function TNativeBackend.ClassifyRecordReturn(ARec: TRecordTypeDesc): TRecReturnClass;
var
  Sz:               Integer;
  Eb0SSE, Eb1SSE:   Boolean;
begin
  Result := rcSret;
  if (ARec = nil) or (ARec.Kind <> tyRecord) then Exit;
  if ARec.Fields.Count = 0 then Exit;
  if not Self.IsRecordManagedClean(ARec) then Exit;
  Sz := ARec.TotalSize();

  if FTarget.OS = osWindows then
  begin
    if Self.IsRecordAllIntOrFloatLeaves(ARec) then
      Result := rcWin64Agg;
    Exit;
  end;

  if Self.IsRecordAllIntegerLeaves(ARec) then
  begin
    case Sz of
      1, 2, 4, 8:                       Result := rcInt1;
      9, 10, 11, 12, 13, 14, 15, 16:    Result := rcInt2;
    end;
    Exit;
  end;

  if Self.IsRecordAllFloatLeaves(ARec) then
  begin
    case Sz of
      4, 8:                            Result := rcSSE1;
      9, 10, 11, 12, 13, 14, 15, 16:   Result := rcSSE2;
    end;
    Exit;
  end;

  if not Self.IsRecordAllIntOrFloatLeaves(ARec) then Exit;
  case Sz of
    9, 10, 11, 12, 13, 14, 15, 16:
      begin
        Eb0SSE := Self.EightbyteIsSSE(ARec, 0);
        Eb1SSE := Self.EightbyteIsSSE(ARec, 8);
        if      (not Eb0SSE) and Eb1SSE then Result := rcIntSSE
        else if Eb0SSE and (not Eb1SSE) then Result := rcSSEInt;
      end;
  end;
end;

function TNativeBackend.GenerateProgram(AProg: TProgram): string;
begin
  FAsm.Clear();
  Self.EmitProgram(AProg);
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

function TNativeBackend.GetOutput: string;
begin
  Result := FAsm.ToString();
end;

end.
