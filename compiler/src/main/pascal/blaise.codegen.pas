{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen;

{ Backend-neutral code-generator contract.

  Both the QBE backend (blaise.codegen.qbe.TCodeGenQBE) and the native backend
  (blaise.codegen.native.TCodeGenNative) implement ICodeGen, so the
  driver in Blaise.pas runs one codegen sequence against the interface
  rather than branching per backend.

  ICodeGen covers only what the driver invokes polymorphically.  Backend-
  specific configuration (e.g. the native backend's SetTarget) stays on the
  concrete class and is applied before the object is assigned to an ICodeGen
  variable.

  Lifetime: ICodeGen is ARC-managed.  Assign a freshly-created concrete
  codegen to an ICodeGen variable and let it go out of scope — no manual
  Free.  (Mixing an explicit Free with ARC would double-free.) }

interface

uses
  uAST, uSymbolTable, uDebugFacts, blaise.codegen.target;

type
  TRecReturnClass = (
    rcSret,
    rcInt1,
    rcInt2,
    rcSSE1,
    rcSSE2,
    rcIntSSE,
    rcSSEInt,
    rcWin64Agg
  );

  ICodeGen = interface
    { Single-file program compilation: reset output and emit all IR. }
    procedure Generate(AProg: TProgram);

    { Single-unit compilation in isolation. }
    procedure GenerateUnit(AUnit: TUnit);

    { Provide the global symbol table before AppendUnit/AppendProgram so
      class typeinfo, vtable, and field-cleanup data can be emitted. }
    procedure SetSymbolTable(ASymTable: TSymbolTable);

    { Enable backend debug/leak-tracking behaviour. }
    procedure SetDebugMode(AEnabled: Boolean);

    { Enable OPDF-debug code shaping.  When on, the backend emits class vtables
      as exported (global) symbols so the separately-assembled .opdf section can
      reference them across object files (the OPDF class record stores each
      class's VMTAddress for runtime dynamic-type resolution).  Off by default,
      so normal builds are byte-for-byte unchanged. }
    procedure SetOpdfMode(AEnabled: Boolean);

    { Codegen-collected debug facts for the OPDF emitter (exact frame
      offsets, per-statement line labels, function extents).  Only the
      native backend produces them; the QBE backend returns nil and the
      OPDF emitter falls back to its approximate AST walk. }
    function  GetDebugFacts: TDbgFacts;

    { Multi-unit compilation: append unit IR to existing output without
      resetting the output buffer or string-literal table. }
    procedure AppendUnit(AUnit: TUnit);

    { Append program IR after one or more AppendUnit calls. }
    procedure AppendProgram(AProg: TProgram);

    { Incremental / separate-compilation: when a dependency unit's BODY is
      compiled elsewhere (its own .o) and therefore NOT emitted here via
      AppendUnit, the program startup must still call that unit's
      <Unit>_init() if it has an initialization section.  This registers the
      unit name into the init-call list (in dependency order) WITHOUT emitting
      any body, so AppendProgram's $main emits `call $<Unit>_init()` and the
      call resolves against the symbol exported by the per-unit object.
      AHasInit selects whether the unit actually has an init section; units
      without one are skipped (no spurious call). }
    procedure NoteDepInitUnit(const AUnitName: string; AHasInit: Boolean);

    { Retrieve the complete generated output (QBE IR text for the QBE
      backend; target assembly text for the native backend). }
    function GetOutput: string;
  end;

{ ----------------------------------------------------------------------
  Shared System V / Win64 record-return ABI classifier.

  Both the QBE backend and the native x86-64 backend must agree, byte for
  byte, on how a record-typed return value is passed (sret vs register, and
  which register class).  The decision is a pure walk over the record's field
  layout plus the target OS — no backend state — so it lives here as free
  functions that both backends call, instead of being carried as two
  drift-prone twins.  Only RecretClassify consults the target (the Win64
  aggregate rule); the leaf predicates are target-independent type walks. }

{ True when ARec (and every nested record) contains no managed fields
  (string / class / interface / dynamic array) — a precondition for any
  register return. }
function RecretManagedClean(ARec: TRecordTypeDesc): Boolean;
{ True when every leaf field is an integer-class scalar (or a nested record
  thereof). }
function RecretAllIntegerLeaves(ARec: TRecordTypeDesc): Boolean;
{ True when every leaf field is a float (Double/Single) or a nested record
  thereof. }
function RecretAllFloatLeaves(ARec: TRecordTypeDesc): Boolean;
{ True when every leaf field is an integer- or float-class scalar. }
function RecretAllIntOrFloatLeaves(ARec: TRecordTypeDesc): Boolean;
{ True when the eightbyte starting at AStartByte holds any float leaf — i.e.
  the eightbyte is SSE-classified under the SysV mixed-class rules. }
function RecretEightbyteIsSSE(ARec: TRecordTypeDesc; AStartByte: Integer): Boolean;
{ Classify ARec's return-passing for ATarget's OS. }
function RecretClassify(ARec: TRecordTypeDesc;
  const ATarget: TTargetDesc): TRecReturnClass;

{ ----------------------------------------------------------------------
  Shared ARC ownership-transfer predicate.

  True when AExpr, used as an r-value, leaves an ARC-managed value at
  refcount +1 that the consuming site must NOT AddRef again (it consumes the
  transferred reference).  Covers function/method calls and method-backed
  property reads returning a class, string, or dynamic array.  The decision is
  a pure walk over the AST node + its resolved type — no backend state — so it
  is single-sourced here and both backends call it (formerly the byte-identical
  twins ExprOwnsRef / NativeExprOwnsRef). }
function ArcExprOwnsRef(AExpr: TASTExpr): Boolean;

implementation

function RecretManagedClean(ARec: TRecordTypeDesc): Boolean;
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
        if not RecretManagedClean(TRecordTypeDesc(F.TypeDesc)) then Exit;
    end;
  end;
  Result := True;
end;

function RecretAllIntegerLeaves(ARec: TRecordTypeDesc): Boolean;
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
        if not RecretAllIntegerLeaves(TRecordTypeDesc(F.TypeDesc)) then Exit;
    else
      Exit;
    end;
  end;
  Result := True;
end;

function RecretAllFloatLeaves(ARec: TRecordTypeDesc): Boolean;
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
        if not RecretAllFloatLeaves(TRecordTypeDesc(F.TypeDesc)) then Exit;
    else
      Exit;
    end;
  end;
  Result := True;
end;

function RecretAllIntOrFloatLeaves(ARec: TRecordTypeDesc): Boolean;
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
        if not RecretAllIntOrFloatLeaves(TRecordTypeDesc(F.TypeDesc)) then Exit;
    else
      Exit;
    end;
  end;
  Result := True;
end;

function RecretEightbyteIsSSE(ARec: TRecordTypeDesc; AStartByte: Integer): Boolean;
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
        if RecretEightbyteIsSSE(TRecordTypeDesc(F.TypeDesc),
                          AStartByte - Off) then Exit(True);
    end;
  end;
end;

function RecretClassify(ARec: TRecordTypeDesc;
  const ATarget: TTargetDesc): TRecReturnClass;
var
  Sz:               Integer;
  Eb0SSE, Eb1SSE:   Boolean;
begin
  Result := rcSret;
  if (ARec = nil) or (ARec.Kind <> tyRecord) then Exit;
  if ARec.Fields.Count = 0 then Exit;
  if not RecretManagedClean(ARec) then Exit;
  Sz := ARec.TotalSize();

  if ATarget.OS = osWindows then
  begin
    if RecretAllIntOrFloatLeaves(ARec) then
      Result := rcWin64Agg;
    Exit;
  end;

  if RecretAllIntegerLeaves(ARec) then
  begin
    case Sz of
      1, 2, 4, 8:                       Result := rcInt1;
      9, 10, 11, 12, 13, 14, 15, 16:    Result := rcInt2;
    end;
    Exit;
  end;

  if RecretAllFloatLeaves(ARec) then
  begin
    case Sz of
      4, 8:                            Result := rcSSE1;
      9, 10, 11, 12, 13, 14, 15, 16:   Result := rcSSE2;
    end;
    Exit;
  end;

  if not RecretAllIntOrFloatLeaves(ARec) then Exit;
  case Sz of
    9, 10, 11, 12, 13, 14, 15, 16:
      begin
        Eb0SSE := RecretEightbyteIsSSE(ARec, 0);
        Eb1SSE := RecretEightbyteIsSSE(ARec, 8);
        if      (not Eb0SSE) and Eb1SSE then Result := rcIntSSE
        else if Eb0SSE and (not Eb1SSE) then Result := rcSSEInt;
      end;
  end;
end;

function ArcExprOwnsRef(AExpr: TASTExpr): Boolean;
var
  FA: TFieldAccessExpr;
  MC: TMethodCallExpr;
  IE: TIdentExpr;
begin
  Result := False;
  if AExpr = nil then Exit;
  if AExpr.ResolvedType = nil then Exit;
  { Ownership transfer applies to every ARC-managed return value, not just
    classes: a function/method returning a String or dynamic array leaves
    its Result at refcount +1 (the callee AddRef'd on `Result := x` and did
    not release Result at scope exit).  The caller's assignment site must
    therefore NOT AddRef again — it consumes that transferred reference.
    Without covering tyString/tyDynArray here the assignment branches emit a
    spurious _StringAddRef/_DynArrayAddRef on the call result, which is never
    balanced and leaks one buffer per call. }
  if not (AExpr.ResolvedType.Kind in [tyClass, tyDynArray])
     and not AExpr.ResolvedType.IsString() then Exit;
  if AExpr is TIdentExpr then
  begin
    IE := TIdentExpr(AExpr);
    if IE.IsImplicitSelfMethod then
      Exit(True);
  end;
  { Constructor calls via TFieldAccessExpr (TFoo.Create) — do NOT own. }
  if AExpr is TFieldAccessExpr then
  begin
    FA := TFieldAccessExpr(AExpr);
    if FA.IsConstructorCall then Exit;
    if FA.IsMethodCall then begin Result := True; Exit end;
    { Method-backed property read (read GetX): the getter returns +1.
      Field-backed reads (read FX) emit a plain load and do NOT own. }
    if (FA.PropRead <> nil) and (FA.PropRead.ReadMethod <> '') then
      Exit(True);
  end;
  { TMethodCallExpr: constructor calls do NOT own; all other method calls DO. }
  if AExpr is TMethodCallExpr then
  begin
    MC := TMethodCallExpr(AExpr);
    if not MC.IsConstructorCall then Result := True;
    Exit;
  end;
  if AExpr is TFuncCallExpr then
  begin
    if (TFuncCallExpr(AExpr).ResolvedDecl <> nil) or
       TFuncCallExpr(AExpr).IsIndirectCall then
      Result := True;
    Exit;
  end;
  { Indexed property subscript: L[I] desugars to Subscript(FieldAccess(Items))
    where Items has a ReadMethod.  The subscript emitter delegates to the
    getter — the result inherits the +1. }
  if AExpr is TStringSubscriptExpr then
  begin
    if (TStringSubscriptExpr(AExpr).StrExpr is TFieldAccessExpr) and
       (TFieldAccessExpr(TStringSubscriptExpr(AExpr).StrExpr).PropRead <> nil) and
       (TFieldAccessExpr(TStringSubscriptExpr(AExpr).StrExpr).PropRead.ReadMethod <> '') then
      Result := True;
  end;
end;

end.
