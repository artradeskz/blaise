{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

unit uCodeGenQBE;

{$mode objfpc}{$H+}

{ QBE IR emitter for Blaise.
  String layout: Phase 1 uses raw NUL-terminated bytes (no ARC header).
  WriteLn/Write are built-ins resolved directly to libc printf calls.
  Records are stack-allocated; field access uses pointer arithmetic. }

interface

uses
  SysUtils, StrUtils, Classes, uAST, uSymbolTable;

type
  ECodeGenError = class(Exception);

  TCodeGenQBE = class
  private
    FOutput:          TStringList;
    FStrLits:         TStringList;  { index → raw value; label = $__s<index> }
    FStrLitsEmitted:  Integer;      { count of $__s<N> already written to output }
    FTempCount:       Integer;
    FLabelCount:      Integer;
    FCurrentBlock: TBlock;       { block currently being emitted; set by EmitBlock }
    FBreakLabels:    TStringList;  { stack of active loop-end labels; top = innermost }
    FContinueLabels: TStringList;  { stack of active loop-continue labels; top = innermost }
    FExitLabel:    string;       { label to jmp to for 'exit'; '' = main program }
    FSymTable:     TSymbolTable; { set via SetSymbolTable; used by AppendUnit for class data }

    function  AllocTemp: string;
    function  AllocLabel(const APrefix: string): string;
    function  CoerceArg(const AArgTemp: string; AArgExpr: TASTExpr; const AParamQType: string): string;
    function  EmitStrLit(const AValue: string): string;
    procedure EmitLine(const ALine: string);
    procedure EmitPendingStrLits;
    procedure EmitDataSection;
    procedure EmitMainHeader;
    procedure EmitMainFooter;
    procedure EmitTypeInfoDefs(AProg: TProgram);
    procedure EmitVTableDefs(AProg: TProgram);
    procedure EmitMethodDefs(AProg: TProgram);
    procedure EmitInterfaceDefs(AProg: TProgram);
    procedure EmitFieldCleanupDefs(AProg: TProgram);
    procedure EmitFieldCleanupFn(const AMangledName: string;
                                 ARec: TRecordTypeDesc);
    procedure EmitMethodDef(const ATypeName: string; AMethod: TMethodDecl);
    procedure EmitStandaloneDefs(AProg: TProgram);
    procedure EmitStandaloneDef(ADecl: TMethodDecl);
    procedure EmitFuncDef(ADecl: TMethodDecl; AExported: Boolean);
    procedure EmitBlock(ABlock: TBlock);
    procedure EmitVarAllocs(ABlock: TBlock);
    procedure EmitGlobalVarData(ABlock: TBlock);
    procedure EmitParamAllocs(AMethod: TMethodDecl; AClassType: TRecordTypeDesc);
    procedure EmitArcCleanup(ABlock: TBlock);
    procedure EmitExcPathArcCleanup(ABlock: TBlock);
    procedure EmitStmt(AStmt: TASTStmt);
    procedure EmitIfStmt(AStmt: TIfStmt);
    procedure EmitWhileStmt(AStmt: TWhileStmt);
    procedure EmitRepeatStmt(AStmt: TRepeatStmt);
    procedure EmitForStmt(AStmt: TForStmt);
    procedure EmitTryFinallyStmt(AStmt: TTryFinallyStmt);
    procedure EmitTryExceptStmt(AStmt: TTryExceptStmt);
    procedure EmitRaiseStmt(AStmt: TRaiseStmt);
    procedure EmitCompoundStmt(AStmt: TCompoundStmt);
    procedure EmitAssignment(AAssign: TAssignment);
    procedure EmitFieldAssignment(AAssign: TFieldAssignment);
    procedure EmitMethodCall(ACall: TMethodCallStmt);
    procedure EmitInheritedCall(ACall: TInheritedCallStmt);
    procedure EmitCaseStmt(AStmt: TCaseStmt);
    procedure EmitProcCall(ACall: TProcCall);
    procedure EmitPointerWrite(AStmt: TPointerWriteStmt);
    procedure EmitStaticSubscriptAssign(AStmt: TStaticSubscriptAssign);
    procedure EmitWrite(ACall: TProcCall; ANewline: Boolean);
    function  EmitExpr(AExpr: TASTExpr): string;
    function  EmitIsExpr(AExpr: TIsExpr): string;
    function  EmitAsExpr(AExpr: TAsExpr): string;
    function  EmitStringSubscriptExpr(AExpr: TStringSubscriptExpr): string;
    function  EmitAddrOfExpr(AExpr: TAddrOfExpr): string;
    function  EmitArrayLiteralExpr(AExpr: TArrayLiteralExpr): string;
    function  EmitSetLiteralExpr(AExpr: TArrayLiteralExpr): string;
    { Returns a QBE temp holding a pointer to the storage of a record or class
      instance referenced by AExpr.  Used by chained field access to traverse
      base nodes without loading record aggregates as scalars. }
    function  EmitInstancePtr(AExpr: TASTExpr): string;
    function  FieldPtr(const ARecordVar: string; AOffset: Integer): string;
    { Returns the QBE address token for a variable: '$Name' for globals,
      '%_var_Name' for locals. }
    function  VarRef(const AName: string; AIsGlobal: Boolean): string;
    { Returns a QBE temp (or address token) that holds the address to pass as a
      var-param actual argument.  When the actual argument is itself a var param
      its local slot contains a pointer — emit loadl to obtain the original
      caller's address.  For plain locals/globals VarRef suffices. }
    function  EmitVarArgAddr(AIdent: TIdentExpr): string;
    { Emit a record-returning function/method call with an explicit sret address.
      The callee receives ASretAddr as its first (hidden) parameter and writes
      the result there instead of returning it.  Handles TFuncCallExpr,
      TMethodCallExpr, and TFieldAccessExpr.IsMethodCall. }
    procedure EmitRecordCallSret(AExpr: TASTExpr; const ASretAddr: string);
    { Emit a field-by-field ARC-aware copy from ASrcAddr to ADestAddr for a
      record described by ARec.  String fields use AddRef/Release; class fields
      use ClassAddRef/ClassRelease; other fields are copied with a plain store. }
    procedure EmitRecordCopy(ARec: TRecordTypeDesc;
                             const ADestAddr, ASrcAddr: string);
    { Returns True if AExpr is a function or method call that returns a record.
      Used in EmitAssignment to choose the sret path over a storel. }
    function  IsRecordCall(AExpr: TASTExpr): Boolean;
    { Release every ARC-managed field of a record at AAddr in-line (no copy).
      Used before overwriting a record slot to prevent reference leaks. }
    procedure EmitRecordReleaseFields(ARec: TRecordTypeDesc; const AAddr: string);
    function  QbeTypeOf(AType: TTypeDesc): string;
    function  QbeEscapeString(const AStr: string): string;
    { Mangle a type name for use in QBE symbols: '<' → '_', '>' → '', ',' → '_' }
    function  QBEMangle(const AName: string): string;
  public
    constructor Create;
    destructor Destroy; override;
    procedure Generate(AProg: TProgram);
    procedure GenerateUnit(AUnit: TUnit);
    { Multi-unit compilation: append unit IR to existing output.
      Does not reset the output buffer or string-literal table so that
      all units and the final program can share a single QBE IR file
      with globally-unique string-literal labels. }
    { Provide the global symbol table so AppendUnit can emit class typeinfo,
      vtable, and field-cleanup data.  Must be called before AppendUnit when
      the units contain class type definitions.  Prog.SymbolTable is correct. }
    procedure SetSymbolTable(ASymTable: TSymbolTable);
    procedure AppendUnit(AUnit: TUnit);
    { Append program IR to existing output (companion to AppendUnit).
      Emits any remaining string literals and the $main function. }
    procedure AppendProgram(AProg: TProgram);
    function  GetOutput: string;
  end;

implementation

constructor TCodeGenQBE.Create;
begin
  inherited Create;
  FOutput          := TStringList.Create;
  FStrLits         := TStringList.Create;
  FStrLits.CaseSensitive := True;
  FBreakLabels     := TStringList.Create;
  FContinueLabels  := TStringList.Create;
  FTempCount       := 0;
  FStrLitsEmitted  := 0;
end;

destructor TCodeGenQBE.Destroy;
begin
  FBreakLabels.Free;
  FContinueLabels.Free;
  FOutput.Free;
  FStrLits.Free;
  inherited Destroy;
end;

function TCodeGenQBE.AllocTemp: string;
begin
  Result := Format('%%_t%d', [FTempCount]);
  Inc(FTempCount);
end;

function TCodeGenQBE.AllocLabel(const APrefix: string): string;
begin
  Result := Format('%s_%d', [APrefix, FLabelCount]);
  Inc(FLabelCount);
end;

function TCodeGenQBE.CoerceArg(const AArgTemp: string; AArgExpr: TASTExpr;
  const AParamQType: string): string;
var
  ExtTemp: string;
begin
  if (AParamQType = 'l') and (AArgExpr <> nil) and
     (AArgExpr.ResolvedType <> nil) and
     (QbeTypeOf(AArgExpr.ResolvedType) = 'w') then
  begin
    ExtTemp := AllocTemp;
    EmitLine(Format('  %s =l extsw %s', [ExtTemp, AArgTemp]));
    Result := ExtTemp;
  end
  else
    Result := AArgTemp;
end;

function TCodeGenQBE.EmitStrLit(const AValue: string): string;
var
  Idx: Integer;
begin
  Idx := FStrLits.IndexOf(AValue);
  if Idx < 0 then
    Idx := FStrLits.Add(AValue);
  Result := Format('$__s%d', [Idx]);
end;

procedure TCodeGenQBE.EmitLine(const ALine: string);
begin
  FOutput.Add(ALine);
end;

procedure TCodeGenQBE.EmitPendingStrLits;
var
  I:      Integer;
  StrLen: Integer;
begin
  { Emit only the string literals not yet written.  Each literal carries a
    12-byte ARC header: refcnt=-1 (immortal), length, capacity.
    The string pointer is the header pointer; char data begins at ptr+12. }
  if FStrLits.Count > FStrLitsEmitted then
  begin
    if FStrLitsEmitted = 0 then
      EmitLine('# String literals');
    for I := FStrLitsEmitted to FStrLits.Count - 1 do
    begin
      StrLen := Length(FStrLits.Strings[I]);
      EmitLine(Format('data $__s%d = { w -1, w %d, w %d, b "%s", b 0 }',
        [I, StrLen, StrLen, QbeEscapeString(FStrLits.Strings[I])]));
    end;
    FStrLitsEmitted := FStrLits.Count;
  end;
end;

procedure TCodeGenQBE.EmitDataSection;
begin
  EmitPendingStrLits;
  { printf format strings. Always emitted: a program with no string literals
    can still call WriteLn(Integer) or a bare WriteLn, and those reference
    $__fmt_d_nl / $__fmt_nl unconditionally. Omitting these definitions
    produces a link-time "undefined reference" failure that the IR-only test
    harness cannot see. }
  EmitLine('data $__fmt_s_nl = { b "%s\n", b 0 }');
  EmitLine('data $__fmt_s    = { b "%s", b 0 }');
  EmitLine('data $__fmt_d_nl = { b "%d\n", b 0 }');
  EmitLine('data $__fmt_d    = { b "%d", b 0 }');
  EmitLine('data $__fmt_nl   = { b "\n", b 0 }');
  EmitLine('');
end;

procedure TCodeGenQBE.EmitMainHeader;
begin
  EmitLine('export function w $main(w %argc, l %argv) {');
  EmitLine('@start');
  EmitLine('  call $_SetArgs(w %argc, l %argv)');
end;

procedure TCodeGenQBE.EmitMainFooter;
begin
  EmitLine('  ret 0');
  EmitLine('}');
end;

function TCodeGenQBE.QbeTypeOf(AType: TTypeDesc): string;
begin
  case AType.Kind of
    tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum: Result := 'w';
    tySet: if TSetTypeDesc(AType).BitCount <= 32 then Result := 'w' else Result := 'l';
    tyInt64, tyString:                      Result := 'l';
    tyRecord:                               Result := 'l';  { pointer to aggregate }
    tyClass:                                Result := 'l';  { heap pointer }
    tyPointer:                              Result := 'l';  { pointer (typed or untyped) }
    tyOpenArray:                            Result := 'l';  { data pointer (high idx is separate) }
    tyStaticArray:                          Result := 'l';  { base pointer to stack buffer }
    tyPChar:                                Result := 'l';  { opaque C pointer }
  else
    Result := 'w';
  end;
end;

procedure TCodeGenQBE.EmitVarAllocs(ABlock: TBlock);
var
  I, J:     Integer;
  Decl:     TVarDecl;
  VarName:  string;
  RT:       TRecordTypeDesc;
  RecSize:  Integer;
  RecAlign: Integer;
  SAT:      TStaticArrayTypeDesc;
  ArrSize:  Integer;
  ArrAlign: Integer;
begin
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(ABlock.Decls.Items[I]);
    if Decl.ResolvedType = nil then
      raise ECodeGenError.Create(Format(
        'Variable ''%s'' has no resolved type — semantic pass required',
        [Decl.Names.Strings[0]]));
    if Decl.IsGlobal then
      Continue;  { global vars are emitted in the data section, not as stack allocs }

    for J := 0 to Decl.Names.Count - 1 do
    begin
      VarName := Decl.Names.Strings[J];
      case Decl.ResolvedType.Kind of
        tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum:
          begin
            EmitLine(Format('  %%_var_%s =l alloc4 1', [VarName]));
            EmitLine(Format('  storew 0, %%_var_%s', [VarName]));
          end;

        tyInt64:
          begin
            EmitLine(Format('  %%_var_%s =l alloc8 1', [VarName]));
            EmitLine(Format('  storel 0, %%_var_%s', [VarName]));
          end;

        tyString:
          begin
            EmitLine(Format('  %%_var_%s =l alloc8 1', [VarName]));
            EmitLine(Format('  storel 0, %%_var_%s', [VarName]));
          end;

        tyRecord:
          begin
            RT       := TRecordTypeDesc(Decl.ResolvedType);
            RecSize  := RT.TotalSize;
            RecAlign := RT.MaxAlign;
            if RecAlign >= 8 then
              EmitLine(Format('  %%_var_%s =l alloc8 %d', [VarName, RecSize]))
            else
              EmitLine(Format('  %%_var_%s =l alloc4 %d', [VarName, RecSize]));
            { Zero-initialise record storage: Pascal records default to 0 and
              QBE's SSA checker requires every loaded slot to have at least
              one prior store. }
            if RecSize > 0 then
              EmitLine(Format('  call $memset(l %%_var_%s, w 0, l %d)',
                [VarName, RecSize]));
          end;

        tyClass:
          begin
            { Class var holds a heap pointer — allocate one pointer slot, nil-init }
            EmitLine(Format('  %%_var_%s =l alloc8 1', [VarName]));
            EmitLine(Format('  storel 0, %%_var_%s', [VarName]));
          end;

        tyPointer:
          begin
            { Pointer var (typed or untyped) — allocate one pointer slot, nil-init }
            EmitLine(Format('  %%_var_%s =l alloc8 1', [VarName]));
            EmitLine(Format('  storel 0, %%_var_%s', [VarName]));
          end;

        tyPChar:
          begin
            { PChar var — opaque C pointer slot, nil-init }
            EmitLine(Format('  %%_var_%s =l alloc8 1', [VarName]));
            EmitLine(Format('  storel 0, %%_var_%s', [VarName]));
          end;

        tySet:
          begin
            { Set var: 32-bit bitmask for ≤32 members, 64-bit for 33–64 }
            if TSetTypeDesc(Decl.ResolvedType).BitCount <= 32 then
            begin
              EmitLine(Format('  %%_var_%s =l alloc4 1', [VarName]));
              EmitLine(Format('  storew 0, %%_var_%s', [VarName]));
            end
            else
            begin
              EmitLine(Format('  %%_var_%s =l alloc8 1', [VarName]));
              EmitLine(Format('  storel 0, %%_var_%s', [VarName]));
            end;
          end;

        tyStaticArray:
          begin
            SAT      := TStaticArrayTypeDesc(Decl.ResolvedType);
            ArrSize  := SAT.ByteSize;
            ArrAlign := SAT.AllocAlign;
            if ArrAlign >= 8 then
              EmitLine(Format('  %%_var_%s =l alloc8 %d', [VarName, ArrSize]))
            else
              EmitLine(Format('  %%_var_%s =l alloc4 %d', [VarName, ArrSize]));
            if ArrSize > 0 then
              EmitLine(Format('  call $memset(l %%_var_%s, w 0, l %d)',
                [VarName, ArrSize]));
          end;

        tyInterface:
          begin
            { Interface var = fat pointer: obj slot + itab slot, both nil-init }
            EmitLine(Format('  %%_var_%s_obj  =l alloc8 1', [VarName]));
            EmitLine(Format('  storel 0, %%_var_%s_obj',    [VarName]));
            EmitLine(Format('  %%_var_%s_itab =l alloc8 1', [VarName]));
            EmitLine(Format('  storel 0, %%_var_%s_itab',   [VarName]));
          end;

      else
        raise ECodeGenError.Create(Format(
          'Unsupported type kind %d for variable ''%s''',
          [Ord(Decl.ResolvedType.Kind), VarName]));
      end;
    end;
  end;
end;

procedure TCodeGenQBE.EmitGlobalVarData(ABlock: TBlock);
{ Emit QBE data-section entries for program-level global variables.
  These live at $Name (pointer-sized slots, zero-initialised) rather than
  as per-function stack allocs.  Called once from Generate before the
  function bodies are written. }
var
  I, J:    Integer;
  Decl:    TVarDecl;
  VarName: string;
  RT:      TRecordTypeDesc;
begin
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(ABlock.Decls.Items[I]);
    if not Decl.IsGlobal then Continue;
    if Decl.ResolvedType = nil then Continue;
    for J := 0 to Decl.Names.Count - 1 do
    begin
      VarName := Decl.Names.Strings[J];
      case Decl.ResolvedType.Kind of
        tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum:
          EmitLine(Format('data $%s = { w 0 }', [VarName]));
        tySet:
          if TSetTypeDesc(Decl.ResolvedType).BitCount <= 32 then
            EmitLine(Format('data $%s = { w 0 }', [VarName]))
          else
            EmitLine(Format('data $%s = { l 0 }', [VarName]));
        tyInt64:
          EmitLine(Format('data $%s = { l 0 }', [VarName]));
        tyString, tyClass, tyPointer:
          EmitLine(Format('data $%s = { l 0 }', [VarName]));
        tyInterface:
          begin
            EmitLine(Format('data $%s_obj  = { l 0 }', [VarName]));
            EmitLine(Format('data $%s_itab = { l 0 }', [VarName]));
          end;
        tyRecord:
          begin
            RT := TRecordTypeDesc(Decl.ResolvedType);
            if RT.TotalSize > 0 then
              EmitLine(Format('data $%s = { z %d }', [VarName, RT.TotalSize]))
            else
              EmitLine(Format('data $%s = { l 0 }', [VarName]));
          end;
      else
        EmitLine(Format('data $%s = { l 0 }', [VarName]));
      end;
    end;
  end;
end;

procedure TCodeGenQBE.EmitArcCleanup(ABlock: TBlock);
{ Release every ARC-managed local variable (string, class, or interface) at
  block exit.  Mirrors the insertion pattern used at assignment sites: each
  slot holds one retained reference from its first assignment; scope exit
  must balance that with one release.  Interface vars carry a fat pointer
  (obj + itab); only the obj slot is refcounted.  Weak vars use _WeakClear
  against the slot address rather than a strong release on the slot value. }
var
  I, J:    Integer;
  Decl:    TVarDecl;
  VarName: string;
  ValTemp: string;
  RelFn:   string;
  IsIntf:  Boolean;
begin
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(ABlock.Decls.Items[I]);
    if Decl.ResolvedType = nil then Continue;
    IsIntf := Decl.ResolvedType.Kind = tyInterface;
    if Decl.IsWeak then
    begin
      { Weak class or interface local — unregister from the weak table
        without touching refcounts.  The zero-out happens automatically
        as _WeakClear writes 0 to *slot. }
      for J := 0 to Decl.Names.Count - 1 do
      begin
        VarName := Decl.Names.Strings[J];
        if IsIntf then
          EmitLine(Format('  call $_WeakClear(l %s_obj)', [VarRef(VarName, Decl.IsGlobal)]))
        else
          EmitLine(Format('  call $_WeakClear(l %s)', [VarRef(VarName, Decl.IsGlobal)]));
      end;
      Continue;
    end;
    if Decl.ResolvedType.IsString then
      RelFn := '$_StringRelease'
    else if Decl.ResolvedType.Kind = tyClass then
      RelFn := '$_ClassRelease'
    else if IsIntf then
      RelFn := '$_ClassRelease'  { obj slot release; itab is static }
    else if Decl.ResolvedType.Kind = tyRecord then
    begin
      { Record local: release each ARC-managed field at scope exit }
      for J := 0 to Decl.Names.Count - 1 do
      begin
        VarName := Decl.Names.Strings[J];
        EmitRecordReleaseFields(TRecordTypeDesc(Decl.ResolvedType),
          VarRef(VarName, Decl.IsGlobal));
      end;
      Continue;
    end
    else
      Continue;
    for J := 0 to Decl.Names.Count - 1 do
    begin
      VarName := Decl.Names.Strings[J];
      ValTemp := AllocTemp;
      if IsIntf then
        EmitLine(Format('  %s =l loadl %s_obj', [ValTemp, VarRef(VarName, Decl.IsGlobal)]))
      else
        EmitLine(Format('  %s =l loadl %s', [ValTemp, VarRef(VarName, Decl.IsGlobal)]));
      EmitLine(Format('  call %s(l %s)', [RelFn, ValTemp]));
    end;
  end;
end;

procedure TCodeGenQBE.EmitBlock(ABlock: TBlock);
var
  I: Integer;
begin
  FCurrentBlock := ABlock;
  EmitVarAllocs(ABlock);
  for I := 0 to ABlock.Stmts.Count - 1 do
    EmitStmt(TASTStmt(ABlock.Stmts.Items[I]));
  { Fall-through to exit label so 'exit' and normal flow share cleanup. }
  if FExitLabel <> '' then
  begin
    EmitLine(Format('  jmp @%s', [FExitLabel]));
    EmitLine('@' + FExitLabel);
  end;
  EmitArcCleanup(ABlock);
end;

procedure TCodeGenQBE.EmitExcPathArcCleanup(ABlock: TBlock);
var
  I, J:    Integer;
  Decl:    TVarDecl;
  VarName: string;
  ValTemp: string;
  RelFn:   string;
  IsIntf:  Boolean;
begin
  if ABlock = nil then Exit;
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(ABlock.Decls.Items[I]);
    if Decl.ResolvedType = nil then Continue;
    IsIntf := Decl.ResolvedType.Kind = tyInterface;
    if Decl.IsWeak then
    begin
      { Weak locals on an exception path: unregister and zero the slot
        so a subsequent nested handler's cleanup sees nil. }
      for J := 0 to Decl.Names.Count - 1 do
      begin
        VarName := Decl.Names.Strings[J];
        if IsIntf then
          EmitLine(Format('  call $_WeakClear(l %s_obj)', [VarRef(VarName, Decl.IsGlobal)]))
        else
          EmitLine(Format('  call $_WeakClear(l %s)', [VarRef(VarName, Decl.IsGlobal)]));
      end;
      Continue;
    end;
    if Decl.ResolvedType.IsString then
      RelFn := '$_StringRelease'
    else if Decl.ResolvedType.Kind = tyClass then
      RelFn := '$_ClassRelease'
    else if IsIntf then
      RelFn := '$_ClassRelease'
    else if Decl.ResolvedType.Kind = tyRecord then
    begin
      { Record local on exception path: release ARC fields }
      for J := 0 to Decl.Names.Count - 1 do
      begin
        VarName := Decl.Names.Strings[J];
        EmitRecordReleaseFields(TRecordTypeDesc(Decl.ResolvedType),
          VarRef(VarName, Decl.IsGlobal));
      end;
      Continue;
    end
    else
      Continue;
    for J := 0 to Decl.Names.Count - 1 do
    begin
      VarName := Decl.Names.Strings[J];
      ValTemp := AllocTemp;
      if IsIntf then
      begin
        EmitLine(Format('  %s =l loadl %s_obj', [ValTemp, VarRef(VarName, Decl.IsGlobal)]));
        EmitLine(Format('  call %s(l %s)', [RelFn, ValTemp]));
        EmitLine(Format('  storel 0, %s_obj', [VarRef(VarName, Decl.IsGlobal)]));
      end
      else
      begin
        EmitLine(Format('  %s =l loadl %s', [ValTemp, VarRef(VarName, Decl.IsGlobal)]));
        EmitLine(Format('  call %s(l %s)', [RelFn, ValTemp]));
        EmitLine(Format('  storel 0, %s', [VarRef(VarName, Decl.IsGlobal)]));
      end;
    end;
  end;
end;

procedure TCodeGenQBE.EmitStmt(AStmt: TASTStmt);
var
  DeadLbl: string;
begin
  if AStmt = nil then
    raise ECodeGenError.Create('EmitStmt called with nil statement');
  if AStmt is TTryFinallyStmt then
    EmitTryFinallyStmt(TTryFinallyStmt(AStmt))
  else if AStmt is TTryExceptStmt then
    EmitTryExceptStmt(TTryExceptStmt(AStmt))
  else if AStmt is TRaiseStmt then
    EmitRaiseStmt(TRaiseStmt(AStmt))
  else if AStmt is TForStmt then
    EmitForStmt(TForStmt(AStmt))
  else if AStmt is TWhileStmt then
    EmitWhileStmt(TWhileStmt(AStmt))
  else if AStmt is TRepeatStmt then
    EmitRepeatStmt(TRepeatStmt(AStmt))
  else if AStmt is TIfStmt then
    EmitIfStmt(TIfStmt(AStmt))
  else if AStmt is TCompoundStmt then
    EmitCompoundStmt(TCompoundStmt(AStmt))
  else if AStmt is TFieldAssignment then
    EmitFieldAssignment(TFieldAssignment(AStmt))
  else if AStmt is TPointerWriteStmt then
    EmitPointerWrite(TPointerWriteStmt(AStmt))
  else if AStmt is TStaticSubscriptAssign then
    EmitStaticSubscriptAssign(TStaticSubscriptAssign(AStmt))
  else if AStmt is TAssignment then
    EmitAssignment(TAssignment(AStmt))
  else if AStmt is TMethodCallStmt then
    EmitMethodCall(TMethodCallStmt(AStmt))
  else if AStmt is TInheritedCallStmt then
    EmitInheritedCall(TInheritedCallStmt(AStmt))
  else if AStmt is TCaseStmt then
    EmitCaseStmt(TCaseStmt(AStmt))
  else if AStmt is TProcCall then
    EmitProcCall(TProcCall(AStmt))
  else if AStmt is TExitStmt then
  begin
    if FExitLabel <> '' then
      EmitLine(Format('  jmp @%s', [FExitLabel]))
    else
      EmitLine('  ret 0');
    { QBE basic blocks must follow a terminator with a new labelled block. }
    DeadLbl := AllocLabel('after_exit');
    EmitLine('@' + DeadLbl);
  end
  else if AStmt is TBreakStmt then
  begin
    if FBreakLabels.Count = 0 then
      raise ECodeGenError.Create('break outside loop');
    EmitLine(Format('  jmp @%s',
      [FBreakLabels.Strings[FBreakLabels.Count - 1]]));
    DeadLbl := AllocLabel('after_break');
    EmitLine('@' + DeadLbl);
  end
  else if AStmt is TContinueStmt then
  begin
    if FContinueLabels.Count = 0 then
      raise ECodeGenError.Create('continue outside loop');
    EmitLine(Format('  jmp @%s',
      [FContinueLabels.Strings[FContinueLabels.Count - 1]]));
    DeadLbl := AllocLabel('after_continue');
    EmitLine('@' + DeadLbl);
  end
  else
    raise ECodeGenError.Create(Format('Unknown statement node type at line %d', [AStmt.Line]));
end;

procedure TCodeGenQBE.EmitIfStmt(AStmt: TIfStmt);
var
  CondTemp:  string;
  LblThen:   string;
  LblElse:   string;
  LblEnd:    string;
begin
  LblThen := AllocLabel('if_then');
  LblEnd  := AllocLabel('if_end');

  CondTemp := EmitExpr(AStmt.Condition);

  if AStmt.ElseStmt <> nil then
  begin
    LblElse := AllocLabel('if_else');
    EmitLine(Format('  jnz %s, @%s, @%s', [CondTemp, LblThen, LblElse]));
    EmitLine('@' + LblThen);
    EmitStmt(AStmt.ThenStmt);
    EmitLine(Format('  jmp @%s', [LblEnd]));
    EmitLine('@' + LblElse);
    EmitStmt(AStmt.ElseStmt);
    EmitLine(Format('  jmp @%s', [LblEnd]));
  end
  else
  begin
    EmitLine(Format('  jnz %s, @%s, @%s', [CondTemp, LblThen, LblEnd]));
    EmitLine('@' + LblThen);
    EmitStmt(AStmt.ThenStmt);
    EmitLine(Format('  jmp @%s', [LblEnd]));
  end;

  EmitLine('@' + LblEnd);
end;

procedure TCodeGenQBE.EmitTryFinallyStmt(AStmt: TTryFinallyStmt);
var
  LblTry:    string;
  LblFinExc: string;
  LblEnd:    string;
  FrameTemp: string;
  SjrTemp:   string;
  ExcTemp:   string;
  I:         Integer;
begin
  LblTry    := AllocLabel('try_body');
  LblFinExc := AllocLabel('fin_exc');
  LblEnd    := AllocLabel('fin_end');

  { Stack-allocate exception frame (512 bytes, 16-byte aligned).
    jbuf is at offset 0 so frame ptr can be passed directly to setjmp.
    512 bytes accommodates jmp_buf on Linux x86_64 (200 B) and macOS ARM64 (~312 B). }
  FrameTemp := AllocTemp;
  EmitLine(Format('  %s =l alloc16 512', [FrameTemp]));
  EmitLine(Format('  call $_PushExcFrame(l %s)', [FrameTemp]));

  SjrTemp := AllocTemp;
  EmitLine(Format('  %s =w call $setjmp(l %s)', [SjrTemp, FrameTemp]));
  EmitLine(Format('  jnz %s, @%s, @%s', [SjrTemp, LblFinExc, LblTry]));

  { Normal path: run try body, pop frame, run finally body }
  EmitLine('@' + LblTry);
  for I := 0 to AStmt.TryBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.TryBody.Stmts.Items[I]));
  EmitLine('  call $_PopExcFrame()');
  for I := 0 to AStmt.FinallyBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.FinallyBody.Stmts.Items[I]));
  EmitLine(Format('  jmp @%s', [LblEnd]));

  { Exception path: capture exception, pop frame, run finally body, release
    in-scope ARC vars (prevent leaks on unwind), then re-raise }
  EmitLine('@' + LblFinExc);
  ExcTemp := AllocTemp;
  EmitLine(Format('  %s =l call $_CurrentException()', [ExcTemp]));
  EmitLine('  call $_PopExcFrame()');
  for I := 0 to AStmt.FinallyBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.FinallyBody.Stmts.Items[I]));
  EmitExcPathArcCleanup(FCurrentBlock);
  EmitLine(Format('  call $_Reraise(l %s)', [ExcTemp]));
  EmitLine(Format('  jmp @%s', [LblEnd]));  { unreachable — satisfies QBE block exit }

  EmitLine('@' + LblEnd);
end;

procedure TCodeGenQBE.EmitTryExceptStmt(AStmt: TTryExceptStmt);
var
  LblTry:    string;
  LblExcept: string;
  LblEnd:    string;
  FrameTemp: string;
  SjrTemp:   string;
  I:         Integer;
begin
  LblTry    := AllocLabel('try_body');
  LblExcept := AllocLabel('except_handler');
  LblEnd    := AllocLabel('except_end');

  { Stack-allocate exception frame (512 bytes, 16-byte aligned).
    Matches the size contract in blaise_exc.c — must hold jmp_buf (200 B on
    Linux x86_64, ~312 B on macOS ARM64) plus two pointer fields. }
  FrameTemp := AllocTemp;
  EmitLine(Format('  %s =l alloc16 512', [FrameTemp]));
  EmitLine(Format('  call $_PushExcFrame(l %s)', [FrameTemp]));

  SjrTemp := AllocTemp;
  EmitLine(Format('  %s =w call $setjmp(l %s)', [SjrTemp, FrameTemp]));
  EmitLine(Format('  jnz %s, @%s, @%s', [SjrTemp, LblExcept, LblTry]));

  { Normal path: run try body, pop frame on clean exit }
  EmitLine('@' + LblTry);
  for I := 0 to AStmt.TryBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.TryBody.Stmts.Items[I]));
  EmitLine('  call $_PopExcFrame()');
  EmitLine(Format('  jmp @%s', [LblEnd]));

  { Exception path: frame still at top (exception set), pop then handle }
  EmitLine('@' + LblExcept);
  EmitLine('  call $_PopExcFrame()');
  for I := 0 to AStmt.ExceptBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.ExceptBody.Stmts.Items[I]));
  EmitLine(Format('  jmp @%s', [LblEnd]));

  EmitLine('@' + LblEnd);
end;

procedure TCodeGenQBE.EmitRaiseStmt(AStmt: TRaiseStmt);
var
  ObjTemp: string;
begin
  if AStmt.Expr <> nil then
  begin
    ObjTemp := EmitExpr(AStmt.Expr);
    EmitLine(Format('  call $_Raise(l %s)', [ObjTemp]));
  end
  else
    { Bare re-raise: pass null; RTL retrieves current exception }
    EmitLine('  call $_Raise(l 0)');
end;

procedure TCodeGenQBE.EmitForStmt(AStmt: TForStmt);
var
  LblCond:  string;
  LblBody:  string;
  LblNext:  string;  { continue target — increment step }
  LblEnd:   string;
  StartT:   string;
  EndT:     string;
  CurT:     string;
  CmpT:     string;
  StepT:    string;
  CmpOp:    string;
  StepOp:   string;
begin
  LblCond := AllocLabel('for_cond');
  LblBody := AllocLabel('for_body');
  LblNext := AllocLabel('for_next');
  LblEnd  := AllocLabel('for_end');

  { Evaluate start and store into loop variable }
  StartT := EmitExpr(AStmt.StartExpr);
  EmitLine(Format('  storew %s, %s', [StartT, VarRef(AStmt.VarName, AStmt.IsGlobal)]));

  { Evaluate end value once into a temp }
  EndT := EmitExpr(AStmt.EndExpr);

  { Jump to condition (terminates current block) }
  EmitLine(Format('  jmp @%s', [LblCond]));

  { Condition block: test loop variable against end value }
  EmitLine('@' + LblCond);
  CurT := AllocTemp;
  EmitLine(Format('  %s =w loadw %s', [CurT, VarRef(AStmt.VarName, AStmt.IsGlobal)]));
  CmpT := AllocTemp;
  if AStmt.IsDownTo then
    CmpOp := 'csgew'   { I >= End }
  else
    CmpOp := 'cslew';  { I <= End }
  EmitLine(Format('  %s =w %s %s, %s', [CmpT, CmpOp, CurT, EndT]));
  EmitLine(Format('  jnz %s, @%s, @%s', [CmpT, LblBody, LblEnd]));

  { Body block }
  EmitLine('@' + LblBody);
  FBreakLabels.Add(LblEnd);
  FContinueLabels.Add(LblNext);
  try
    EmitStmt(AStmt.Body);
  finally
    FBreakLabels.Delete(FBreakLabels.Count - 1);
    FContinueLabels.Delete(FContinueLabels.Count - 1);
  end;
  EmitLine(Format('  jmp @%s', [LblNext]));

  { Increment or decrement loop variable (continue target) }
  EmitLine('@' + LblNext);
  CurT  := AllocTemp;
  StepT := AllocTemp;
  EmitLine(Format('  %s =w loadw %s', [CurT, VarRef(AStmt.VarName, AStmt.IsGlobal)]));
  if AStmt.IsDownTo then
    StepOp := 'sub'
  else
    StepOp := 'add';
  EmitLine(Format('  %s =w %s %s, 1', [StepT, StepOp, CurT]));
  EmitLine(Format('  storew %s, %s', [StepT, VarRef(AStmt.VarName, AStmt.IsGlobal)]));
  EmitLine(Format('  jmp @%s', [LblCond]));

  { Continuation block }
  EmitLine('@' + LblEnd);
end;

procedure TCodeGenQBE.EmitWhileStmt(AStmt: TWhileStmt);
var
  LblCond: string;
  LblBody: string;
  LblEnd:  string;
  CondTemp: string;
begin
  LblCond := AllocLabel('while_cond');
  LblBody := AllocLabel('while_body');
  LblEnd  := AllocLabel('while_end');

  { Jump into the condition block (terminates current block) }
  EmitLine(Format('  jmp @%s', [LblCond]));

  { Condition evaluation block }
  EmitLine('@' + LblCond);
  CondTemp := EmitExpr(AStmt.Condition);
  EmitLine(Format('  jnz %s, @%s, @%s', [CondTemp, LblBody, LblEnd]));

  { Loop body block }
  EmitLine('@' + LblBody);
  FBreakLabels.Add(LblEnd);
  FContinueLabels.Add(LblCond);
  try
    EmitStmt(AStmt.Body);
  finally
    FBreakLabels.Delete(FBreakLabels.Count - 1);
    FContinueLabels.Delete(FContinueLabels.Count - 1);
  end;
  EmitLine(Format('  jmp @%s', [LblCond]));

  { Continuation block }
  EmitLine('@' + LblEnd);
end;

procedure TCodeGenQBE.EmitRepeatStmt(AStmt: TRepeatStmt);
var
  LblBody: string;
  LblCond: string;
  LblEnd:  string;
  CondTemp: string;
begin
  LblBody := AllocLabel('repeat_body');
  LblCond := AllocLabel('repeat_cond');
  LblEnd  := AllocLabel('repeat_end');

  { Jump into the body — repeat always executes at least once }
  EmitLine(Format('  jmp @%s', [LblBody]));

  { Body block }
  EmitLine('@' + LblBody);
  FBreakLabels.Add(LblEnd);
  FContinueLabels.Add(LblCond);
  try
    EmitCompoundStmt(AStmt.Body);
  finally
    FBreakLabels.Delete(FBreakLabels.Count - 1);
    FContinueLabels.Delete(FContinueLabels.Count - 1);
  end;
  EmitLine(Format('  jmp @%s', [LblCond]));

  { Condition block — true means exit, false means repeat }
  EmitLine('@' + LblCond);
  CondTemp := EmitExpr(AStmt.Condition);
  EmitLine(Format('  jnz %s, @%s, @%s', [CondTemp, LblEnd, LblBody]));

  { Continuation block }
  EmitLine('@' + LblEnd);
end;

procedure TCodeGenQBE.EmitCompoundStmt(AStmt: TCompoundStmt);
var
  I: Integer;
begin
  for I := 0 to AStmt.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.Stmts.Items[I]));
end;

procedure TCodeGenQBE.EmitAssignment(AAssign: TAssignment);
var
  ValTemp, OldTemp, QType, StoreInstr, PtrTemp: string;
  IntfDesc:  TInterfaceTypeDesc;
  ClassRT:   TRecordTypeDesc;
  ItabName:  string;
  AE:        TAsExpr;
  ObjTemp:   string;
  ItabTemp:  string;
  CheckTemp: string;
  LblOk:     string;
  LblFail:   string;
  LblEnd:    string;
  ISFld:     TFieldInfo;
  ISAddrT:   string;
  ExtTemp:   string;
begin
  if AAssign.Expr.ResolvedType = nil then
    raise ECodeGenError.Create(Format(
      'Expression in assignment to ''%s'' has no resolved type', [AAssign.Name]));

  { Implicit Self.Field assignment: bare field name like FPos := ... }
  if AAssign.ImplicitSelfField <> nil then
  begin
    ISFld   := TFieldInfo(AAssign.ImplicitSelfField);
    { Compute destination address = Self + field offset }
    ObjTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_Self', [ObjTemp]));
    if ISFld.Offset > 0 then
    begin
      ISAddrT := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', [ISAddrT, ObjTemp, ISFld.Offset]));
      ObjTemp := ISAddrT;
    end;
    { Record field: ARC-correct copy or direct sret }
    if ISFld.TypeDesc.Kind = tyRecord then
    begin
      ClassRT := TRecordTypeDesc(ISFld.TypeDesc);
      if IsRecordCall(AAssign.Expr) then
      begin
        EmitRecordReleaseFields(ClassRT, ObjTemp);
        EmitLine(Format('  call $memset(l %s, w 0, l %d)', [ObjTemp, ClassRT.TotalSize]));
        EmitRecordCallSret(AAssign.Expr, ObjTemp);
      end
      else
      begin
        ValTemp := EmitExpr(AAssign.Expr);
        EmitRecordCopy(ClassRT, ObjTemp, ValTemp);
      end;
      Exit;
    end;
    ValTemp := EmitExpr(AAssign.Expr);
    QType := QbeTypeOf(ISFld.TypeDesc);
    if QType = 'w' then
      EmitLine(Format('  storew %s, %s', [ValTemp, ObjTemp]))
    else
    begin
      if QbeTypeOf(AAssign.Expr.ResolvedType) = 'w' then
      begin
        ExtTemp := AllocTemp;
        EmitLine(Format('  %s =l extsw %s', [ExtTemp, ValTemp]));
        ValTemp := ExtTemp;
      end;
      { ARC for class/string field stored via implicit Self.Field }
      if ISFld.TypeDesc.IsString then
      begin
        OldTemp := AllocTemp;
        EmitLine(Format('  %s =l loadl %s', [OldTemp, ObjTemp]));
        EmitLine(Format('  call $_StringAddRef(l %s)',  [ValTemp]));
        EmitLine(Format('  call $_StringRelease(l %s)', [OldTemp]));
      end
      else if ISFld.TypeDesc.Kind = tyClass then
      begin
        OldTemp := AllocTemp;
        EmitLine(Format('  %s =l loadl %s', [OldTemp, ObjTemp]));
        EmitLine(Format('  call $_ClassAddRef(l %s)',  [ValTemp]));
        EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
      end;
      EmitLine(Format('  storel %s, %s', [ValTemp, ObjTemp]));
    end;
    Exit;
  end;

  { Interface as-cast: F := T as IFoo — use _GetItab for runtime itab lookup.
    ARC: the obj slot holds a strong reference to the backing class instance,
    so retain the new obj and release the prior contents of F's obj slot
    before storing.  The itab slot is a pointer to static rodata and is not
    refcounted. }
  if (AAssign.ResolvedLhsType <> nil) and
     (AAssign.ResolvedLhsType.Kind = tyInterface) and
     (AAssign.Expr is TAsExpr) and
     (AAssign.Expr.ResolvedType.Kind = tyInterface) then
  begin
    AE        := TAsExpr(AAssign.Expr);
    IntfDesc  := TInterfaceTypeDesc(AAssign.ResolvedLhsType);
    ObjTemp   := EmitExpr(AE.Obj);
    ItabTemp  := AllocTemp;
    EmitLine(Format('  %s =l call $_GetItab(l %s, l $typeinfo_%s)',
      [ItabTemp, ObjTemp, AE.TypeName]));
    CheckTemp := AllocTemp;
    LblOk   := AllocLabel('as_ok');
    LblFail := AllocLabel('as_fail');
    LblEnd  := AllocLabel('as_end');
    EmitLine(Format('  %s =w cnel %s, 0', [CheckTemp, ItabTemp]));
    EmitLine(Format('  jnz %s, @%s, @%s', [CheckTemp, LblOk, LblFail]));
    EmitLine('@' + LblFail);
    EmitLine('  call $_Raise_InvalidCast()');
    EmitLine(Format('  jmp @%s', [LblEnd]));
    EmitLine('@' + LblOk);
    if AAssign.IsWeakLhs then
      EmitLine(Format('  call $_WeakAssign(l %s_obj, l %s)',
        [VarRef(AAssign.Name, AAssign.IsGlobal), ObjTemp]))
    else
    begin
      OldTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s_obj', [OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
      EmitLine(Format('  call $_ClassAddRef(l %s)',  [ObjTemp]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
      EmitLine(Format('  storel %s, %s_obj',  [ObjTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    end;
    EmitLine(Format('  storel %s, %s_itab', [ItabTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    EmitLine('@' + LblEnd);
    Exit;
  end;

  { Interface direct assignment: F := T where T is a class implementing the
    interface.  Under ARC, the obj slot co-owns the backing class instance
    and must be retained on store / released when overwritten — or, for
    weak interface references, routed through _WeakAssign. }
  if (AAssign.ResolvedLhsType <> nil) and
     (AAssign.ResolvedLhsType.Kind = tyInterface) and
     (AAssign.Expr.ResolvedType.Kind = tyClass) then
  begin
    IntfDesc := TInterfaceTypeDesc(AAssign.ResolvedLhsType);
    ClassRT  := TRecordTypeDesc(AAssign.Expr.ResolvedType);
    ItabName := '$itab_' + ClassRT.Name + '_' + IntfDesc.Name;
    ValTemp  := EmitExpr(AAssign.Expr);
    if AAssign.IsWeakLhs then
      EmitLine(Format('  call $_WeakAssign(l %s_obj, l %s)',
        [VarRef(AAssign.Name, AAssign.IsGlobal), ValTemp]))
    else
    begin
      OldTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s_obj', [OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
      EmitLine(Format('  call $_ClassAddRef(l %s)',  [ValTemp]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
      EmitLine(Format('  storel %s, %s_obj',  [ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    end;
    EmitLine(Format('  storel %s, %s_itab', [ItabName, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    Exit;
  end;

  { Interface-to-interface direct assignment: F := G where both sides are
    interface-typed.  Copy obj and itab from G's fat pointer to F's; for
    strong F, retain the backing object and release F's prior obj ref;
    for weak F, route the obj through _WeakAssign. }
  if (AAssign.ResolvedLhsType <> nil) and
     (AAssign.ResolvedLhsType.Kind = tyInterface) and
     (AAssign.Expr.ResolvedType.Kind = tyInterface) and
     (AAssign.Expr is TIdentExpr) then
  begin
    ObjTemp  := AllocTemp;
    ItabTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s_obj',
      [ObjTemp, VarRef(TIdentExpr(AAssign.Expr).Name, TIdentExpr(AAssign.Expr).IsGlobal)]));
    EmitLine(Format('  %s =l loadl %s_itab',
      [ItabTemp, VarRef(TIdentExpr(AAssign.Expr).Name, TIdentExpr(AAssign.Expr).IsGlobal)]));
    if AAssign.IsWeakLhs then
    begin
      EmitLine(Format('  call $_WeakAssign(l %s_obj, l %s)',
        [VarRef(AAssign.Name, AAssign.IsGlobal), ObjTemp]));
      EmitLine(Format('  storel %s, %s_itab', [ItabTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
      Exit;
    end;
    OldTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s_obj', [OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    EmitLine(Format('  call $_ClassAddRef(l %s)',  [ObjTemp]));
    EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
    EmitLine(Format('  storel %s, %s_obj',  [ObjTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    EmitLine(Format('  storel %s, %s_itab', [ItabTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    Exit;
  end;

  if AAssign.IsVarParam then
  begin
    { Var param: load the stored pointer, then store the value through it }
    QType   := QbeTypeOf(AAssign.Expr.ResolvedType);
    ValTemp := EmitExpr(AAssign.Expr);
    PtrTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_%s', [PtrTemp, AAssign.Name]));
    if QType = 'w' then StoreInstr := 'storew'
                   else StoreInstr := 'storel';
    EmitLine(Format('  %s %s, %s', [StoreInstr, ValTemp, PtrTemp]));
  end
  else if (AAssign.ResolvedLhsType <> nil) and
          (AAssign.ResolvedLhsType.Kind = tyRecord) then
  begin
    { Record assignment: use sret (directly into dest) or field-by-field copy }
    ClassRT := TRecordTypeDesc(AAssign.ResolvedLhsType);
    if IsRecordCall(AAssign.Expr) then
    begin
      { Release old ARC fields, zero the slot, then call function with dest as sret }
      EmitRecordReleaseFields(ClassRT, VarRef(AAssign.Name, AAssign.IsGlobal));
      EmitLine(Format('  call $memset(l %s, w 0, l %d)',
        [VarRef(AAssign.Name, AAssign.IsGlobal), ClassRT.TotalSize]));
      EmitRecordCallSret(AAssign.Expr, VarRef(AAssign.Name, AAssign.IsGlobal));
    end
    else
    begin
      { RHS is a record variable: get its address then ARC-copy field-by-field }
      ValTemp := EmitExpr(AAssign.Expr);
      EmitRecordCopy(ClassRT, VarRef(AAssign.Name, AAssign.IsGlobal), ValTemp);
    end;
  end
  else if AAssign.Expr.ResolvedType.IsString then
  begin
    { ARC: load old, compute new, retain new, release old, store new }
    OldTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', [OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    ValTemp := EmitExpr(AAssign.Expr);
    EmitLine(Format('  call $_StringAddRef(l %s)', [ValTemp]));
    EmitLine(Format('  call $_StringRelease(l %s)', [OldTemp]));
    EmitLine(Format('  storel %s, %s', [ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
  end
  else if AAssign.IsWeakLhs and (AAssign.Expr.ResolvedType.Kind = tyClass) then
  begin
    { Weak class-typed assignment: bypass the strong refcount entirely.
      _WeakAssign takes the slot *address* (so it can zero it later when
      the target is released) and the new value; it handles unregistering
      any prior registration for this slot. }
    ValTemp := EmitExpr(AAssign.Expr);
    EmitLine(Format('  call $_WeakAssign(l %s, l %s)',
      [VarRef(AAssign.Name, AAssign.IsGlobal), ValTemp]));
  end
  else if AAssign.Expr.ResolvedType.Kind = tyClass then
  begin
    { ARC: load old class reference, evaluate new, retain new, release old,
      store new.  Matches the string ARC idiom one-for-one. }
    OldTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', [OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    ValTemp := EmitExpr(AAssign.Expr);
    EmitLine(Format('  call $_ClassAddRef(l %s)', [ValTemp]));
    EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
    EmitLine(Format('  storel %s, %s', [ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
  end
  else
  begin
    { Use LHS type (if known) for the store instruction, so that assigning a
      small int to an Int64 variable uses storel rather than storew. }
    if (AAssign.ResolvedLhsType <> nil) and
       (QbeTypeOf(AAssign.ResolvedLhsType) = 'l') then
    begin
      ValTemp := EmitExpr(AAssign.Expr);
      if QbeTypeOf(AAssign.Expr.ResolvedType) = 'w' then
      begin
        ExtTemp := AllocTemp;
        EmitLine(Format('  %s =l extsw %s', [ExtTemp, ValTemp]));
        ValTemp := ExtTemp;
      end;
      EmitLine(Format('  storel %s, %s', [ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    end
    else
    begin
      QType   := QbeTypeOf(AAssign.Expr.ResolvedType);
      ValTemp := EmitExpr(AAssign.Expr);
      if QType = 'w' then StoreInstr := 'storew'
                     else StoreInstr := 'storel';
      EmitLine(Format('  %s %s, %s', [StoreInstr, ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    end;
  end;
end;

function TCodeGenQBE.EmitInstancePtr(AExpr: TASTExpr): string;
var
  Id:     TIdentExpr;
  Fld:    TFieldAccessExpr;
  Base:   string;
  Ptr:    string;
  Loaded: string;
  SelfT:  string;
  ImplFld: TFieldInfo;
begin
  if AExpr is TIdentExpr then
  begin
    Id := TIdentExpr(AExpr);
    { Implicit Self field used as a chain base: load value through Self }
    if Id.IsImplicitSelf then
    begin
      ImplFld := TFieldInfo(Id.ImplicitFieldInfo);
      SelfT   := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_Self', [SelfT]));
      if ImplFld.Offset > 0 then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', [Ptr, SelfT, ImplFld.Offset]));
        SelfT := Ptr;
      end;
      Loaded := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [Loaded, SelfT]));
      Result := Loaded;
      Exit;
    end;
    if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyClass) then
    begin
      Loaded := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [Loaded, VarRef(Id.Name, Id.IsGlobal)]));
      Result := Loaded;
    end
    else
      Result := VarRef(Id.Name, Id.IsGlobal);  { inline record }
    Exit;
  end;

  if AExpr is TFieldAccessExpr then
  begin
    Fld := TFieldAccessExpr(AExpr);
    if Fld.Base <> nil then
      Base := EmitInstancePtr(Fld.Base)
    else
    begin
      { Leaf: RecordName-based access, same rules as for TIdentExpr. }
      if (Fld.ResolvedType = nil) then
        raise ECodeGenError.Create('Chained base has no resolved type');
      if Fld.IsClassAccess then
      begin
        Loaded := AllocTemp;
        EmitLine(Format('  %s =l loadl %s', [Loaded, VarRef(Fld.RecordName, Fld.IsGlobal)]));
        Base := Loaded;
      end
      else
        Base := VarRef(Fld.RecordName, Fld.IsGlobal);
    end;
    if Fld.FieldInfo = nil then
      raise ECodeGenError.Create(
        'Chained field access ''' + Fld.FieldName + ''' has no resolved field info');
    if Fld.FieldInfo.Offset > 0 then
    begin
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d',
        [Ptr, Base, Fld.FieldInfo.Offset]));
    end
    else
      Ptr := Base;
    { If this field is a class pointer, load it to get the heap object pointer.
      If it is an inline record, the pointer itself points to the storage. }
    if Fld.FieldInfo.TypeDesc.Kind = tyClass then
    begin
      Loaded := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [Loaded, Ptr]));
      Result := Loaded;
    end
    else
      Result := Ptr;
    Exit;
  end;

  { Other expression shapes (method calls, typecasts, etc.) — evaluate the
    expression and use the resulting value as the pointer. }
  if (AExpr.ResolvedType <> nil) and
     (AExpr.ResolvedType.Kind in [tyClass, tyInterface, tyPointer, tyRecord]) then
  begin
    Result := EmitExpr(AExpr);
    Exit;
  end;
  raise ECodeGenError.Create('EmitInstancePtr: unsupported base expression');
end;

function TCodeGenQBE.FieldPtr(const ARecordVar: string; AOffset: Integer): string;
var
  PtrTemp: string;
begin
  if AOffset = 0 then
  begin
    Result := Format('%%_var_%s', [ARecordVar]);
  end
  else
  begin
    PtrTemp := AllocTemp;
    EmitLine(Format('  %s =l add %%_var_%s, %d', [PtrTemp, ARecordVar, AOffset]));
    Result := PtrTemp;
  end;
end;

function TCodeGenQBE.VarRef(const AName: string; AIsGlobal: Boolean): string;
begin
  if AIsGlobal then
    Result := '$' + AName
  else
    Result := '%_var_' + AName;
end;

function TCodeGenQBE.EmitVarArgAddr(AIdent: TIdentExpr): string;
var
  SelfT: string;
  ImplFld: TFieldInfo;
begin
  if AIdent.IsVarParam then
  begin
    // The local slot holds the caller's pointer — load it so we pass the
    // original address, not the address of the local slot.
    Result := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_%s', [Result, AIdent.Name]));
  end
  else if AIdent.IsImplicitSelf then
  begin
    // Field of Self — compute address as Self pointer + field offset.
    ImplFld := TFieldInfo(AIdent.ImplicitFieldInfo);
    SelfT := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_Self', [SelfT]));
    if ImplFld.Offset > 0 then
    begin
      Result := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', [Result, SelfT, ImplFld.Offset]));
    end
    else
      Result := SelfT;
  end
  else
    Result := VarRef(AIdent.Name, AIdent.IsGlobal);
end;

function TCodeGenQBE.IsRecordCall(AExpr: TASTExpr): Boolean;
var
  MDecl: TMethodDecl;
  FldA:  TFieldAccessExpr;
begin
  Result := False;
  if AExpr is TFuncCallExpr then
  begin
    if TFuncCallExpr(AExpr).ResolvedDecl = nil then Exit;
    MDecl := TMethodDecl(TFuncCallExpr(AExpr).ResolvedDecl);
    Result := (MDecl.ResolvedReturnType <> nil) and
              (MDecl.ResolvedReturnType.Kind = tyRecord);
  end
  else if AExpr is TMethodCallExpr then
  begin
    if TMethodCallExpr(AExpr).ResolvedMethod = nil then Exit;
    MDecl := TMethodDecl(TMethodCallExpr(AExpr).ResolvedMethod);
    Result := (MDecl.ResolvedReturnType <> nil) and
              (MDecl.ResolvedReturnType.Kind = tyRecord);
  end
  else if AExpr is TFieldAccessExpr then
  begin
    FldA := TFieldAccessExpr(AExpr);
    if not FldA.IsMethodCall then Exit;
    if FldA.ResolvedMethod = nil then Exit;
    MDecl := TMethodDecl(FldA.ResolvedMethod);
    Result := (MDecl.ResolvedReturnType <> nil) and
              (MDecl.ResolvedReturnType.Kind = tyRecord);
  end;
end;

procedure TCodeGenQBE.EmitRecordCopy(ARec: TRecordTypeDesc;
  const ADestAddr, ASrcAddr: string);
var
  I:        Integer;
  F:        TFieldInfo;
  SrcField: string;
  DstField: string;
  ValTemp:  string;
  OldTemp:  string;
begin
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Items[I]);
    if F.TypeDesc = nil then Continue;
    if F.Offset > 0 then
    begin
      SrcField := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', [SrcField, ASrcAddr, F.Offset]));
      DstField := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', [DstField, ADestAddr, F.Offset]));
    end
    else
    begin
      SrcField := ASrcAddr;
      DstField := ADestAddr;
    end;
    if F.TypeDesc.IsString then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [ValTemp, SrcField]));
      OldTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [OldTemp, DstField]));
      EmitLine(Format('  call $_StringAddRef(l %s)', [ValTemp]));
      EmitLine(Format('  call $_StringRelease(l %s)', [OldTemp]));
      EmitLine(Format('  storel %s, %s', [ValTemp, DstField]));
    end
    else if F.TypeDesc.Kind = tyClass then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [ValTemp, SrcField]));
      OldTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [OldTemp, DstField]));
      EmitLine(Format('  call $_ClassAddRef(l %s)', [ValTemp]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
      EmitLine(Format('  storel %s, %s', [ValTemp, DstField]));
    end
    else if QbeTypeOf(F.TypeDesc) = 'w' then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =w loadw %s', [ValTemp, SrcField]));
      EmitLine(Format('  storew %s, %s', [ValTemp, DstField]));
    end
    else
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [ValTemp, SrcField]));
      EmitLine(Format('  storel %s, %s', [ValTemp, DstField]));
    end;
  end;
end;

procedure TCodeGenQBE.EmitRecordCallSret(AExpr: TASTExpr;
  const ASretAddr: string);
var
  FCallExpr: TFuncCallExpr;
  MCallExpr: TMethodCallExpr;
  FldAccess: TFieldAccessExpr;
  MDecl:     TMethodDecl;
  ArgLine:   string;
  ArgTemp:   string;
  SelfTemp:  string;
  Par:       TMethodParam;
  I:         Integer;
  FuncName:  string;
  Ptr:       string;
begin
  if AExpr is TFuncCallExpr then
  begin
    FCallExpr := TFuncCallExpr(AExpr);
    MDecl := TMethodDecl(FCallExpr.ResolvedDecl);
    if FCallExpr.IsImplicitSelfMethod then
    begin
      SelfTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_Self', [SelfTemp]));
      FuncName := '$' + QBEMangle(MDecl.OwnerTypeName + '_' + FCallExpr.Name);
      ArgLine  := Format('l %s, l %s', [ASretAddr, SelfTemp]);
    end
    else
    begin
      FuncName := '$' + QBEMangle(FCallExpr.Name);
      ArgLine  := Format('l %s', [ASretAddr]);
    end;
    for I := 0 to FCallExpr.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Items[I]);
      if Par.IsVarParam then
        ArgLine := ArgLine + Format(', l %s',
          [EmitVarArgAddr(TIdentExpr(TASTExpr(FCallExpr.Args.Items[I])))])
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(FCallExpr.Args.Items[I]));
        ArgLine := ArgLine + Format(', %s %s',
          [QbeTypeOf(Par.ResolvedType), ArgTemp]);
      end;
    end;
    EmitLine(Format('  call %s(%s)', [FuncName, ArgLine]));
  end
  else if AExpr is TMethodCallExpr then
  begin
    MCallExpr := TMethodCallExpr(AExpr);
    MDecl := TMethodDecl(MCallExpr.ResolvedMethod);
    SelfTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s',
      [SelfTemp, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)]));
    FuncName := '$' + QBEMangle(MDecl.OwnerTypeName + '_' + MCallExpr.Name);
    ArgLine  := Format('l %s, l %s', [ASretAddr, SelfTemp]);
    for I := 0 to MCallExpr.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Items[I]);
      if Par.IsVarParam then
        ArgLine := ArgLine + Format(', l %s',
          [EmitVarArgAddr(TIdentExpr(TASTExpr(MCallExpr.Args.Items[I])))])
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Items[I]));
        ArgLine := ArgLine + Format(', %s %s',
          [QbeTypeOf(Par.ResolvedType), ArgTemp]);
      end;
    end;
    EmitLine(Format('  call %s(%s)', [FuncName, ArgLine]));
  end
  else if AExpr is TFieldAccessExpr then
  begin
    FldAccess := TFieldAccessExpr(AExpr);
    MDecl := TMethodDecl(FldAccess.ResolvedMethod);
    if FldAccess.IsImplicitSelf then
    begin
      { FLexer.Next from inside a TParser method: load Self, add offset, load class ptr }
      SelfTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_Self', [SelfTemp]));
      if FldAccess.ImplicitBaseInfo.Offset > 0 then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d',
          [Ptr, SelfTemp, FldAccess.ImplicitBaseInfo.Offset]));
        SelfTemp := Ptr;
      end;
      if FldAccess.IsClassAccess then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l loadl %s', [Ptr, SelfTemp]));
        SelfTemp := Ptr;
      end;
    end
    else
    begin
      SelfTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s',
        [SelfTemp, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
    end;
    FuncName := '$' + QBEMangle(MDecl.OwnerTypeName + '_' + FldAccess.FieldName);
    ArgLine  := Format('l %s, l %s', [ASretAddr, SelfTemp]);
    EmitLine(Format('  call %s(%s)', [FuncName, ArgLine]));
  end;
end;

procedure TCodeGenQBE.EmitRecordReleaseFields(ARec: TRecordTypeDesc;
  const AAddr: string);
var
  I:       Integer;
  F:       TFieldInfo;
  FldAddr: string;
  ValT:    string;
begin
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Items[I]);
    if F.TypeDesc = nil then Continue;
    if not (F.TypeDesc.IsString or (F.TypeDesc.Kind = tyClass)) then Continue;
    if F.Offset > 0 then
    begin
      FldAddr := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', [FldAddr, AAddr, F.Offset]));
    end
    else
      FldAddr := AAddr;
    ValT := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', [ValT, FldAddr]));
    if F.TypeDesc.IsString then
      EmitLine(Format('  call $_StringRelease(l %s)', [ValT]))
    else
      EmitLine(Format('  call $_ClassRelease(l %s)', [ValT]));
  end;
end;

procedure TCodeGenQBE.EmitFieldAssignment(AAssign: TFieldAssignment);
var
  Ptr, PtrTemp, ValTemp, OldTemp, QType, StoreInstr, ExtTemp: string;
  IsArc: Boolean;
  IsStr: Boolean;
  SelfPtr: string;
  IdxTemp: string;
  IdxQType: string;
begin
  { Method-backed property write: emit a call to the setter }
  if AAssign.PropWriteInfo <> nil then
  begin
    ValTemp := EmitExpr(AAssign.Expr);
    if AAssign.IsImplicitSelf then
    begin
      SelfPtr := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_Self', [SelfPtr]));
      if AAssign.ImplicitBaseInfo.Offset > 0 then
      begin
        PtrTemp := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d',
          [PtrTemp, SelfPtr, AAssign.ImplicitBaseInfo.Offset]));
        SelfPtr := PtrTemp;
      end;
      if AAssign.IsClassAccess then
      begin
        PtrTemp := AllocTemp;
        EmitLine(Format('  %s =l loadl %s', [PtrTemp, SelfPtr]));
        SelfPtr := PtrTemp;
      end;
    end
    else
    begin
      SelfPtr := AllocTemp;
      EmitLine(Format('  %s =l loadl %s',
        [SelfPtr, VarRef(AAssign.RecordName, AAssign.IsGlobal)]));
    end;
    QType := QbeTypeOf(AAssign.PropWriteInfo.TypeDesc);
    if AAssign.PropIndexExpr <> nil then
    begin
      IdxTemp  := EmitExpr(AAssign.PropIndexExpr);
      IdxQType := QbeTypeOf(AAssign.PropWriteInfo.IndexTypeDesc);
      EmitLine(Format('  call $%s_%s(l %s, %s %s, %s %s)',
        [QBEMangle(AAssign.PropOwnerType), AAssign.PropWriteInfo.WriteMethod,
         SelfPtr, IdxQType, IdxTemp, QType, ValTemp]));
    end
    else
      EmitLine(Format('  call $%s_%s(l %s, %s %s)',
        [QBEMangle(AAssign.PropOwnerType), AAssign.PropWriteInfo.WriteMethod,
         SelfPtr, QType, ValTemp]));
    Exit;
  end;

  if AAssign.FieldInfo = nil then
    raise ECodeGenError.Create(Format(
      'Field assignment ''%s.%s'' has no resolved field info',
      [AAssign.RecordName, AAssign.FieldName]));

  ValTemp := EmitExpr(AAssign.Expr);

  if AAssign.ObjExpr <> nil then
  begin
    { Receiver is an arbitrary expression — emit it, then offset to the field.
      EmitExpr already returns the class instance pointer value for class-typed
      expressions, so no extra dereference is needed here. }
    PtrTemp := EmitExpr(AAssign.ObjExpr);
    if AAssign.FieldInfo.Offset > 0 then
    begin
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', [Ptr, PtrTemp, AAssign.FieldInfo.Offset]));
    end
    else
      Ptr := PtrTemp;
  end
  else if AAssign.IsImplicitSelf then
  begin
    { Implicit Self.Base.Field — Base is a field of Self }
    PtrTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_Self', [PtrTemp]));
    if AAssign.ImplicitBaseInfo.Offset > 0 then
    begin
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d',
        [Ptr, PtrTemp, AAssign.ImplicitBaseInfo.Offset]));
      PtrTemp := Ptr;
    end;
    if AAssign.IsClassAccess then
    begin
      { Base field holds a class pointer; load it }
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [Ptr, PtrTemp]));
      PtrTemp := Ptr;
    end;
    if AAssign.FieldInfo.Offset > 0 then
    begin
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d',
        [Ptr, PtrTemp, AAssign.FieldInfo.Offset]));
    end
    else
      Ptr := PtrTemp;
  end
  else if AAssign.IsClassAccess then
  begin
    { Load the heap pointer stored in the class variable }
    PtrTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', [PtrTemp, VarRef(AAssign.RecordName, AAssign.IsGlobal)]));
    if AAssign.FieldInfo.Offset > 0 then
    begin
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', [Ptr, PtrTemp, AAssign.FieldInfo.Offset]));
    end
    else
      Ptr := PtrTemp;
  end
  else
    Ptr := FieldPtr(AAssign.RecordName, AAssign.FieldInfo.Offset);

  IsStr := AAssign.FieldInfo.TypeDesc.IsString;
  IsArc := IsStr or (AAssign.FieldInfo.TypeDesc.Kind = tyClass);
  if AAssign.FieldInfo.IsWeak then
  begin
    { Weak class field: store through _WeakAssign so the runtime can zero
      the field slot if the target is freed while the weak ref is live. }
    EmitLine(Format('  call $_WeakAssign(l %s, l %s)', [Ptr, ValTemp]));
  end
  else if IsArc then
  begin
    { ARC for ARC-managed field storage: retain the new value and release the
      old field contents before overwriting, so neither reference leaks. }
    OldTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', [OldTemp, Ptr]));
    if IsStr then
    begin
      EmitLine(Format('  call $_StringAddRef(l %s)',  [ValTemp]));
      EmitLine(Format('  call $_StringRelease(l %s)', [OldTemp]));
    end
    else
    begin
      EmitLine(Format('  call $_ClassAddRef(l %s)',   [ValTemp]));
      EmitLine(Format('  call $_ClassRelease(l %s)',  [OldTemp]));
    end;
    EmitLine(Format('  storel %s, %s', [ValTemp, Ptr]));
  end
  else
  begin
    QType := QbeTypeOf(AAssign.FieldInfo.TypeDesc);
    if QType = 'w' then StoreInstr := 'storew'
                   else
                   begin
                     StoreInstr := 'storel';
                     { Sign-extend if the value is word-typed but the field needs l }
                     if QbeTypeOf(AAssign.Expr.ResolvedType) = 'w' then
                     begin
                       ExtTemp := AllocTemp;
                       EmitLine(Format('  %s =l extsw %s', [ExtTemp, ValTemp]));
                       ValTemp := ExtTemp;
                     end;
                   end;
    EmitLine(Format('  %s %s, %s', [StoreInstr, ValTemp, Ptr]));
  end;
end;

procedure TCodeGenQBE.EmitMethodCall(ACall: TMethodCallStmt);
var
  RT:       TRecordTypeDesc;
  MDecl:    TMethodDecl;
  SelfTemp: string;
  Par:      TMethodParam;
  ArgTemp:  string;
  ArgLine:  string;
  I:        Integer;
  QType:    string;
  FuncName: string;
  VTblTemp: string;
  FPtrTemp: string;
  SlotOff:  Integer;
  IntfDesc: TInterfaceTypeDesc;
begin
  { Interface method dispatch: load obj + itab, index by method slot }
  if (ACall.ResolvedClassType <> nil) and
     (ACall.ResolvedClassType.Kind = tyInterface) then
  begin
    IntfDesc := TInterfaceTypeDesc(ACall.ResolvedClassType);
    SelfTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s_obj', [SelfTemp, VarRef(ACall.ObjectName, ACall.IsGlobal)]));
    VTblTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s_itab', [VTblTemp, VarRef(ACall.ObjectName, ACall.IsGlobal)]));
    SlotOff  := IntfDesc.MethodIndex(ACall.Name) * 8;
    FPtrTemp := AllocTemp;
    if SlotOff = 0 then
      EmitLine(Format('  %s =l loadl %s', [FPtrTemp, VTblTemp]))
    else
    begin
      ArgTemp := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', [ArgTemp, VTblTemp, SlotOff]));
      EmitLine(Format('  %s =l loadl %s',   [FPtrTemp, ArgTemp]));
    end;
    EmitLine(Format('  call %s(l %s)', [FPtrTemp, SelfTemp]));
    Exit;
  end;

  { Call on an arbitrary receiver expression: evaluate and use as Self }
  if ACall.ObjExpr <> nil then
  begin
    SelfTemp := EmitExpr(ACall.ObjExpr);
    RT    := TRecordTypeDesc(ACall.ResolvedClassType);
    MDecl := TMethodDecl(ACall.ResolvedMethod);
    if (MDecl = nil) and SameText(ACall.Name, 'Free') then
    begin
      EmitLine(Format('  call $_ClassRelease(l %s)', [SelfTemp]));
      Exit;
    end;
    ArgLine := Format('l %s', [SelfTemp]);
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Items[I]);
      if Par.IsVarParam then
        ArgLine := ArgLine + Format(', l %s',
          [EmitVarArgAddr(TIdentExpr(TASTExpr(ACall.Args.Items[I])))])
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
        QType   := QbeTypeOf(Par.ResolvedType);
        ArgLine := ArgLine + Format(', %s %s', [QType, ArgTemp]);
      end;
    end;
    if MDecl.OwnerTypeName <> '' then
      FuncName := '$' + MDecl.OwnerTypeName + '_' + ACall.Name
    else
      FuncName := '$' + RT.Name + '_' + ACall.Name;
    EmitLine(Format('  call %s(%s)', [FuncName, ArgLine]));
    Exit;
  end;

  { Built-in Free: release the instance (decrement refcount; free at zero)
    and nil out the slot.  Under universal ARC, Free is a sanctioned synonym
    for immediate release — if other references remain, the block survives
    until their scope exits release them too.  Zeroing the slot makes a
    subsequent scope-exit release a safe no-op. }
  if (ACall.ResolvedMethod = nil) and SameText(ACall.Name, 'Free') then
  begin
    SelfTemp := AllocTemp;
    if ACall.IsImplicitSelf then
    begin
      { Free called on Self.Field: load Self, get field slot address, load value,
        release, then zero the slot. }
      EmitLine(Format('  %s =l loadl %%_var_Self', [SelfTemp]));
      if ACall.ImplicitBaseInfo.Offset > 0 then
      begin
        FPtrTemp := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d',
          [FPtrTemp, SelfTemp, ACall.ImplicitBaseInfo.Offset]));
      end
      else
        FPtrTemp := SelfTemp;
      ArgTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [ArgTemp, FPtrTemp]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [ArgTemp]));
      EmitLine(Format('  storel 0, %s', [FPtrTemp]));
      Exit;
    end;
    EmitLine(Format('  %s =l loadl %s', [SelfTemp, VarRef(ACall.ObjectName, ACall.IsGlobal)]));
    EmitLine(Format('  call $_ClassRelease(l %s)', [SelfTemp]));
    EmitLine(Format('  storel 0, %s', [VarRef(ACall.ObjectName, ACall.IsGlobal)]));
    Exit;
  end;

  RT    := TRecordTypeDesc(ACall.ResolvedClassType);
  MDecl := TMethodDecl(ACall.ResolvedMethod);

  { Load the object pointer (Self) from the caller's variable slot }
  SelfTemp := AllocTemp;
  if ACall.IsImplicitSelf then
  begin
    { Load Self, add field offset, load the class pointer from there }
    EmitLine(Format('  %s =l loadl %%_var_Self', [SelfTemp]));
    if ACall.ImplicitBaseInfo.Offset > 0 then
    begin
      FPtrTemp := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d',
        [FPtrTemp, SelfTemp, ACall.ImplicitBaseInfo.Offset]));
      SelfTemp := FPtrTemp;
    end;
    FPtrTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', [FPtrTemp, SelfTemp]));
    SelfTemp := FPtrTemp;
  end
  else if ACall.IsVarParam then
  begin
    { Var/out param: local slot holds caller's address — dereference twice }
    FPtrTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_%s', [FPtrTemp, ACall.ObjectName]));
    EmitLine(Format('  %s =l loadl %s', [SelfTemp, FPtrTemp]));
  end
  else
    EmitLine(Format('  %s =l loadl %s', [SelfTemp, VarRef(ACall.ObjectName, ACall.IsGlobal)]));

  { Build argument string: l Self, then each explicit arg }
  ArgLine := Format('l %s', [SelfTemp]);
  for I := 0 to ACall.Args.Count - 1 do
  begin
    Par := TMethodParam(MDecl.Params.Items[I]);
    if Par.IsVarParam then
      ArgLine := ArgLine + Format(', l %s',
        [EmitVarArgAddr(TIdentExpr(TASTExpr(ACall.Args.Items[I])))])
    else
    begin
      ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
      QType   := QbeTypeOf(Par.ResolvedType);
      ArgTemp := CoerceArg(ArgTemp, TASTExpr(ACall.Args.Items[I]), QType);
      ArgLine := ArgLine + Format(', %s %s', [QType, ArgTemp]);
    end;
  end;

  if MDecl.VTableSlot >= 0 then
  begin
    { Virtual dispatch: load vptr from instance[0], then load fptr from vtable.
      Slot 0 of vtable is typeinfo, so method N is at offset (N+1)*8. }
    VTblTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', [VTblTemp, SelfTemp]));
    FPtrTemp := AllocTemp;
    SlotOff  := (MDecl.VTableSlot + 1) * 8;
    ArgTemp  := AllocTemp;
    EmitLine(Format('  %s =l add %s, %d', [ArgTemp, VTblTemp, SlotOff]));
    EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
    EmitLine(Format('  call %s(%s)', [FPtrTemp, ArgLine]));
  end
  else
  begin
    { Static dispatch }
    if MDecl.OwnerTypeName <> '' then
      FuncName := '$' + MDecl.OwnerTypeName + '_' + ACall.Name
    else
      FuncName := '$' + RT.Name + '_' + ACall.Name;
    EmitLine(Format('  call %s(%s)', [FuncName, ArgLine]));
  end;
end;

procedure TCodeGenQBE.EmitCaseStmt(AStmt: TCaseStmt);
var
  SelTemp:     string;
  ValTemp:     string;
  CmpTemp:     string;
  NextLbl:     string;
  BranchLbl:   string;
  ElseLbl:     string;
  EndLbl:      string;
  Branch:      TCaseBranch;
  I, J:        Integer;
  BranchLabels: TStringList;
begin
  SelTemp  := EmitExpr(AStmt.Selector);
  EndLbl   := AllocLabel('case_end');
  ElseLbl  := AllocLabel('case_else');

  BranchLabels := TStringList.Create;
  try
    for I := 0 to AStmt.Branches.Count - 1 do
      BranchLabels.Add(AllocLabel('case_br'));

    { Dispatch block: for each branch test all its values;
      on no match fall through to next branch test or else }
    for I := 0 to AStmt.Branches.Count - 1 do
    begin
      Branch    := TCaseBranch(AStmt.Branches.Items[I]);
      BranchLbl := BranchLabels.Strings[I];
      for J := 0 to Branch.Values.Count - 1 do
      begin
        ValTemp := EmitExpr(TASTExpr(Branch.Values.Items[J]));
        CmpTemp := AllocTemp;
        NextLbl := AllocLabel('case_next');
        EmitLine(Format('  %s =w ceqw %s, %s', [CmpTemp, SelTemp, ValTemp]));
        EmitLine(Format('  jnz %s, @%s, @%s', [CmpTemp, BranchLbl, NextLbl]));
        EmitLine('@' + NextLbl);
      end;
    end;
    EmitLine(Format('  jmp @%s', [ElseLbl]));

    { Branch bodies }
    for I := 0 to AStmt.Branches.Count - 1 do
    begin
      Branch    := TCaseBranch(AStmt.Branches.Items[I]);
      BranchLbl := BranchLabels.Strings[I];
      EmitLine('@' + BranchLbl);
      EmitStmt(Branch.Stmt);
      EmitLine(Format('  jmp @%s', [EndLbl]));
    end;

    EmitLine('@' + ElseLbl);
    if AStmt.ElseStmt <> nil then
      EmitStmt(AStmt.ElseStmt);
    EmitLine(Format('  jmp @%s', [EndLbl]));

    EmitLine('@' + EndLbl);
  finally
    BranchLabels.Free;
  end;
end;

procedure TCodeGenQBE.EmitInheritedCall(ACall: TInheritedCallStmt);
var
  MDecl:    TMethodDecl;
  SelfTemp: string;
  ArgLine:  string;
  ArgTemp:  string;
  Par:      TMethodParam;
  QType:    string;
  I:        Integer;
begin
  { TObject inherited calls are no-ops — no method body exists }
  if ACall.ResolvedMethod = nil then Exit;

  MDecl := TMethodDecl(ACall.ResolvedMethod);

  { Load Self from the current method's local slot }
  SelfTemp := AllocTemp;
  EmitLine(Format('  %s =l loadl %%_var_Self', [SelfTemp]));

  { Build arg string: l Self, then each explicit arg }
  ArgLine := Format('l %s', [SelfTemp]);
  for I := 0 to ACall.Args.Count - 1 do
  begin
    Par     := TMethodParam(MDecl.Params.Items[I]);
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
    QType   := QbeTypeOf(Par.ResolvedType);
    ArgLine := ArgLine + Format(', %s %s', [QType, ArgTemp]);
  end;

  { Always a direct (static) call — inherited bypasses vtable dispatch }
  EmitLine(Format('  call $%s_%s(%s)',
    [MDecl.OwnerTypeName, ACall.Name, ArgLine]));
end;

procedure TCodeGenQBE.EmitParamAllocs(AMethod: TMethodDecl;
  AClassType: TRecordTypeDesc);
var
  I:   Integer;
  Par: TMethodParam;
begin
  { Self: store incoming pointer into a local slot }
  EmitLine('  %_var_Self =l alloc8 1');
  EmitLine('  storel %_par_Self, %_var_Self');

  { Explicit params }
  for I := 0 to AMethod.Params.Count - 1 do
  begin
    Par := TMethodParam(AMethod.Params.Items[I]);
    if Par.IsOpenArray then
    begin
      { Open array arrives as two params: data ptr + high index }
      EmitLine(Format('  %%_var_%s =l alloc8 1', [Par.ParamName]));
      EmitLine(Format('  storel %%_par_%s, %%_var_%s',
        [Par.ParamName, Par.ParamName]));
      EmitLine(Format('  %%_var_%s_high =l alloc8 1', [Par.ParamName]));
      EmitLine(Format('  storel %%_par_%s_high, %%_var_%s_high',
        [Par.ParamName, Par.ParamName]));
      Continue;
    end;
    if Par.IsVarParam then
    begin
      { Var param arrives as a pointer — spill pointer into a local slot }
      EmitLine(Format('  %%_var_%s =l alloc8 1', [Par.ParamName]));
      EmitLine(Format('  storel %%_par_%s, %%_var_%s',
        [Par.ParamName, Par.ParamName]));
    end
    else
    case Par.ResolvedType.Kind of
      tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum:
        begin
          EmitLine(Format('  %%_var_%s =l alloc4 1', [Par.ParamName]));
          EmitLine(Format('  storew %%_par_%s, %%_var_%s',
            [Par.ParamName, Par.ParamName]));
        end;
      tyInt64, tyString, tyClass:
        begin
          EmitLine(Format('  %%_var_%s =l alloc8 1', [Par.ParamName]));
          EmitLine(Format('  storel %%_par_%s, %%_var_%s',
            [Par.ParamName, Par.ParamName]));
        end;
    else
      EmitLine(Format('  %%_var_%s =l alloc8 1', [Par.ParamName]));
      EmitLine(Format('  storel %%_par_%s, %%_var_%s',
        [Par.ParamName, Par.ParamName]));
    end;
  end;
end;

procedure TCodeGenQBE.EmitMethodDef(const ATypeName: string;
  AMethod: TMethodDecl);
var
  Sig:           string;
  I:             Integer;
  Par:           TMethodParam;
  FuncName:      string;
  IsFunc:        Boolean;
  RetQType:      string;
  RetTemp:       string;
  SavedExitLbl:  string;
  ValTemp:       string;
begin
  FuncName := '$' + ATypeName + '_' + AMethod.Name;
  IsFunc   := AMethod.ResolvedReturnType <> nil;

  { Build parameter signature.
    sret functions: l %_par__sret comes first, then l %_par_Self.
    Regular methods: just l %_par_Self first. }
  if IsFunc and (AMethod.ResolvedReturnType.Kind = tyRecord) then
    Sig := 'l %_par__sret, l %_par_Self'
  else
    Sig := 'l %_par_Self';
  for I := 0 to AMethod.Params.Count - 1 do
  begin
    Par := TMethodParam(AMethod.Params.Items[I]);
    if Par.IsOpenArray then
      Sig := Sig + Format(', l %%_par_%s, l %%_par_%s_high',
        [Par.ParamName, Par.ParamName])
    else if Par.IsVarParam then
      Sig := Sig + Format(', l %%_par_%s', [Par.ParamName])
    else
      Sig := Sig + Format(', %s %%_par_%s',
        [QbeTypeOf(Par.ResolvedType), Par.ParamName]);
  end;

  if IsFunc then
  begin
    RetQType := QbeTypeOf(AMethod.ResolvedReturnType);
    if AMethod.ResolvedReturnType.Kind = tyRecord then
      { sret: function becomes void }
      EmitLine(Format('function %s(%s) {', [FuncName, Sig]))
    else
      EmitLine(Format('function %s %s(%s) {', [RetQType, FuncName, Sig]));
  end
  else
    EmitLine(Format('function %s(%s) {', [FuncName, Sig]));

  EmitLine('@start');
  EmitParamAllocs(AMethod, nil);

  { ARC: addref class value params on entry — balances the release pass at
    method exit.  Strings in method params are not ARC-managed yet (existing
    gap); classes are covered here because the whole Phase 3 follow-up is
    specifically about class ARC parity. }
  for I := 0 to AMethod.Params.Count - 1 do
  begin
    Par := TMethodParam(AMethod.Params.Items[I]);
    if Par.IsVarParam then Continue;
    if Par.ResolvedType.Kind = tyClass then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_ClassAddRef(l %s)', [ValTemp]));
    end;
  end;

  { For function methods, allocate/alias a zero-initialised Result slot }
  if IsFunc then
  begin
    if AMethod.ResolvedReturnType.Kind = tyRecord then
      { sret: Result IS the caller's buffer — no allocation needed }
      EmitLine('  %_var_Result =l copy %_par__sret')
    else if RetQType = 'w' then
    begin
      EmitLine('  %_var_Result =l alloc4 1');
      EmitLine('  storew 0, %_var_Result');
    end
    else
    begin
      EmitLine('  %_var_Result =l alloc8 1');
      EmitLine('  storel 0, %_var_Result');
    end;
  end;

  SavedExitLbl := FExitLabel;
  FExitLabel   := AllocLabel('method_exit');
  try
    EmitBlock(AMethod.Body);
  finally
    FExitLabel := SavedExitLbl;
  end;

  { ARC: release class value params on exit. }
  for I := 0 to AMethod.Params.Count - 1 do
  begin
    Par := TMethodParam(AMethod.Params.Items[I]);
    if Par.IsVarParam then Continue;
    if Par.ResolvedType.Kind = tyClass then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [ValTemp]));
    end;
  end;

  if IsFunc then
  begin
    if AMethod.ResolvedReturnType.Kind = tyRecord then
      EmitLine('  ret')  { sret: caller's buffer already holds result }
    else
    begin
      RetTemp := AllocTemp;
      if RetQType = 'w' then
        EmitLine(Format('  %s =w loadw %%_var_Result', [RetTemp]))
      else
        EmitLine(Format('  %s =l loadl %%_var_Result', [RetTemp]));
      EmitLine(Format('  ret %s', [RetTemp]));
    end;
  end
  else
    EmitLine('  ret');

  EmitLine('}');
  EmitLine('');
end;

procedure TCodeGenQBE.EmitTypeInfoDefs(AProg: TProgram);
{ Emit one $typeinfo_T data item per class type.
  Layout: l parent_typeinfo_or_zero, l impllist_or_zero
  TypeInfo is at vtable slot 0; _IsInstance walks parent chain.
  impllist is NULL-terminated array of (typeinfo_intf, itab) pairs for _ImplementsInterface.

  TObject is the built-in root class; any user class with an explicit
  class(TObject, IFoo) parent list resolves Parent to TObject's
  TRecordTypeDesc, so we emit a typeinfo stub for TObject unconditionally
  to satisfy the linker.  Its parent slot is nil and its impllist slot
  is nil because TObject implements no interfaces. }
var
  I:         Integer;
  TD:        TTypeDecl;
  TDesc:     TTypeDesc;
  RT:        TRecordTypeDesc;
  GI:        TGenericInstance;
  ParentStr: string;
  ImplStr:   string;
  MName:     string;
begin
  EmitLine('data $typeinfo_TObject = { l 0, l 0 }');

  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    if RT.Parent <> nil then
      ParentStr := '$typeinfo_' + RT.Parent.Name
    else
      ParentStr := '0';
    if RT.ImplementsCount > 0 then
      ImplStr := '$impllist_' + TD.Name
    else
      ImplStr := '0';
    EmitLine('data $typeinfo_' + TD.Name +
             ' = { l ' + ParentStr + ', l ' + ImplStr + ' }');
  end;

  { Generic instances }
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI    := TGenericInstance(AProg.GenericInstances.Items[I]);
    RT    := TRecordTypeDesc(GI.TypeDesc);
    MName := QBEMangle(GI.TypeName);
    if RT.Parent <> nil then
      ParentStr := '$typeinfo_' + QBEMangle(RT.Parent.Name)
    else
      ParentStr := '0';
    ImplStr := '0';
    EmitLine('data $typeinfo_' + MName + ' = { l ' + ParentStr + ', l ' + ImplStr + ' }');
  end;

  EmitLine('');
end;

procedure TCodeGenQBE.EmitVTableDefs(AProg: TProgram);
{ Vtable layout: slot 0 = $typeinfo_T pointer, slots 1..N = virtual method ptrs.
  Dispatch uses (VTableSlot + 1) * 8 to skip the typeinfo slot. }
var
  I, S:  Integer;
  TD:    TTypeDecl;
  TDesc: TTypeDesc;
  RT:    TRecordTypeDesc;
  GI:    TGenericInstance;
  E:     TVTableEntry;
  Line:  string;
  MName: string;
begin
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    if not RT.HasVTable then Continue;
    { TypeInfo pointer is always the first vtable entry }
    Line := 'data $vtable_' + TD.Name + ' = { l $typeinfo_' + TD.Name;
    for S := 0 to RT.VTableCount - 1 do
    begin
      E    := RT.VTableEntryAt(S);
      Line := Line + ', l ' + E.ImplName;
    end;
    Line := Line + ' }';
    EmitLine(Line);
  end;

  { Generic instances }
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI    := TGenericInstance(AProg.GenericInstances.Items[I]);
    RT    := TRecordTypeDesc(GI.TypeDesc);
    if not RT.HasVTable then Continue;
    MName := QBEMangle(GI.TypeName);
    Line  := 'data $vtable_' + MName + ' = { l $typeinfo_' + MName;
    for S := 0 to RT.VTableCount - 1 do
    begin
      E    := RT.VTableEntryAt(S);
      Line := Line + ', l ' + QBEMangle(E.ImplName);
    end;
    Line := Line + ' }';
    EmitLine(Line);
  end;

  EmitLine('');
end;

procedure TCodeGenQBE.EmitInterfaceDefs(AProg: TProgram);
{ Emit typeinfo blocks for interfaces and itab/impllist blocks for class-interface pairs.
  Interface typeinfo: data $typeinfo_IFoo = ( l 0 )  -- address IS the identity token
  Itab: data $itab_TFoo_IFoo = ( l $TFoo_DoIt, l $TFoo_GetVal )
  Impllist: data $impllist_TFoo = ( l $typeinfo_IFoo, l $itab_TFoo_IFoo, l 0 )
  Methods in declaration order; impllist is NULL-terminated (ti, itab) pair array. }
var
  I, J, K:     Integer;
  TD:          TTypeDecl;
  TDesc:       TTypeDesc;
  IntfDesc:    TInterfaceTypeDesc;
  ClassRT:     TRecordTypeDesc;
  ItabLine:    string;
  ImplLine:    string;
  MethName:    string;
  IntfMangle:  string;
  GII:         TGenericInterfaceInstance;
begin
  { Typeinfo blocks for every plain interface }
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if not (TD.Def is TInterfaceTypeDef) then Continue;
    EmitLine('data $typeinfo_' + TD.Name + ' = { l 0 }');
  end;

  { Typeinfo blocks for generic interface instantiations }
  for I := 0 to AProg.GenericIntfInstances.Count - 1 do
  begin
    GII := TGenericInterfaceInstance(AProg.GenericIntfInstances.Items[I]);
    EmitLine('data $typeinfo_' + GII.InstName + ' = { l 0 }');
  end;

  { Itab and impllist blocks for each implementing class }
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    ClassRT := TRecordTypeDesc(TDesc);
    if ClassRT.ImplementsCount = 0 then Continue;

    { One itab per interface }
    for J := 0 to ClassRT.ImplementsCount - 1 do
    begin
      IntfDesc   := ClassRT.ImplementsIntfAt(J);
      IntfMangle := QBEMangle(IntfDesc.Name);
      ItabLine   := 'data $itab_' + TD.Name + '_' + IntfMangle + ' = {';
      for K := 0 to IntfDesc.MethodCount - 1 do
      begin
        MethName := IntfDesc.MethodName(K);
        if K = 0 then
          ItabLine := ItabLine + ' l $' + TD.Name + '_' + MethName
        else
          ItabLine := ItabLine + ', l $' + TD.Name + '_' + MethName;
      end;
      ItabLine := ItabLine + ' }';
      EmitLine(ItabLine);
    end;

    { One impllist per class: NULL-terminated (typeinfo_intf, itab) pairs }
    ImplLine := 'data $impllist_' + TD.Name + ' = {';
    for J := 0 to ClassRT.ImplementsCount - 1 do
    begin
      IntfDesc   := ClassRT.ImplementsIntfAt(J);
      IntfMangle := QBEMangle(IntfDesc.Name);
      if J = 0 then
        ImplLine := ImplLine + ' l $typeinfo_' + IntfMangle +
                               ', l $itab_' + TD.Name + '_' + IntfMangle
      else
        ImplLine := ImplLine + ', l $typeinfo_' + IntfMangle +
                               ', l $itab_' + TD.Name + '_' + IntfMangle;
    end;
    ImplLine := ImplLine + ', l 0 }';
    EmitLine(ImplLine);
  end;
  EmitLine('');
end;

procedure TCodeGenQBE.EmitFieldCleanupFn(const AMangledName: string;
                                         ARec: TRecordTypeDesc);
{ Emit a QBE function $_FieldCleanup_<Name>(l %self) that releases every
  ARC-managed field the instance holds.  The function is invoked from
  _ClassRelease at refcount zero, before the backing block is freed.

  The most-derived class's cleanup is authoritative: inherited fields are
  already merged into this class's Fields list by the semantic analyser
  (see uSemantic.pas — parent fields are copied into the derived
  TRecordTypeDesc during Pass 2), so iterating Fields here covers own and
  inherited fields uniformly.  We therefore do not chain to a parent
  cleanup — doing so would release each inherited field twice.

  A cleanup function is emitted for every class even when it has no
  ARC-managed fields — the no-op call keeps the constructor call site
  uniform and is negligible at runtime. }
var
  I:      Integer;
  F:      TFieldInfo;
  Temp:   string;
  PtrT:   string;
begin
  EmitLine(Format('function $_FieldCleanup_%s(l %%self) {', [AMangledName]));
  EmitLine('@start');
  { If the class declares a Destroy method, invoke it first so it can release
    raw resources (e.g. FreeMem of internal buffers) before ARC field cleanup. }
  if ARec.HasDestroyMethod then
    EmitLine(Format('  call $%s_Destroy(l %%self)', [AMangledName]));
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Items[I]);
    if F.TypeDesc = nil then Continue;
    if not (F.TypeDesc.IsString or (F.TypeDesc.Kind = tyClass)) then
      Continue;
    if F.Offset > 0 then
    begin
      PtrT := AllocTemp;
      EmitLine(Format('  %s =l add %%self, %d', [PtrT, F.Offset]));
    end
    else
      PtrT := '%self';
    if F.IsWeak then
    begin
      { Weak field: unregister from the weak table without decrementing
        any refcount.  _WeakClear zeros *Ptr for us. }
      EmitLine(Format('  call $_WeakClear(l %s)', [PtrT]));
      Continue;
    end;
    Temp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', [Temp, PtrT]));
    if F.TypeDesc.IsString then
      EmitLine(Format('  call $_StringRelease(l %s)', [Temp]))
    else
      EmitLine(Format('  call $_ClassRelease(l %s)', [Temp]));
  end;
  EmitLine('  ret');
  EmitLine('}');
  EmitLine('');
end;

procedure TCodeGenQBE.EmitFieldCleanupDefs(AProg: TProgram);
{ Emit a _FieldCleanup_<T> function for every declared class and every
  generic class instantiation.  The constructor lowering references these
  functions by name; see the _ClassAlloc call in EmitExpr. }
var
  I:     Integer;
  TD:    TTypeDecl;
  TDesc: TTypeDesc;
  RT:    TRecordTypeDesc;
  GI:    TGenericInstance;
begin
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    EmitFieldCleanupFn(TD.Name, RT);
  end;
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AProg.GenericInstances.Items[I]);
    RT := TRecordTypeDesc(GI.TypeDesc);
    EmitFieldCleanupFn(QBEMangle(GI.TypeName), RT);
  end;
end;

procedure TCodeGenQBE.EmitMethodDefs(AProg: TProgram);
var
  I, J:  Integer;
  TD:    TTypeDecl;
  CD:    TClassTypeDef;
  GI:    TGenericInstance;
  MDecl: TMethodDecl;
begin
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then
      Continue;
    CD := TClassTypeDef(TD.Def);
    for J := 0 to CD.Methods.Count - 1 do
      if TMethodDecl(CD.Methods.Items[J]).Body <> nil then
        EmitMethodDef(TD.Name, TMethodDecl(CD.Methods.Items[J]));
  end;

  { Generic instances — emit with mangled type name }
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AProg.GenericInstances.Items[I]);
    for J := 0 to GI.ClassDef.Methods.Count - 1 do
    begin
      MDecl := TMethodDecl(GI.ClassDef.Methods.Items[J]);
      if MDecl.Body <> nil then
        EmitMethodDef(QBEMangle(GI.TypeName), MDecl);
    end;
  end;
end;

procedure TCodeGenQBE.EmitFuncDef(ADecl: TMethodDecl; AExported: Boolean);
var
  Sig:          string;
  I:            Integer;
  Par:          TMethodParam;
  FuncName:     string;
  IsFunc:       Boolean;
  RetQType:     string;
  RetTemp:      string;
  ValTemp:      string;
  Prefix:       string;
  SavedExitLbl: string;
begin
  if ADecl.IsExternal then Exit;  { no body to emit for external declarations }
  FuncName := '$' + QBEMangle(ADecl.Name);
  IsFunc   := ADecl.ResolvedReturnType <> nil;
  if AExported then Prefix := 'export ' else Prefix := '';

  Sig := '';
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Items[I]);
    if Sig <> '' then Sig := Sig + ', ';
    if Par.IsOpenArray then
      Sig := Sig + Format('l %%_par_%s, l %%_par_%s_high',
        [Par.ParamName, Par.ParamName])
    else if Par.IsVarParam then
      Sig := Sig + Format('l %%_par_%s', [Par.ParamName])
    else
      Sig := Sig + Format('%s %%_par_%s', [QbeTypeOf(Par.ResolvedType), Par.ParamName]);
  end;

  if IsFunc then
  begin
    RetQType := QbeTypeOf(ADecl.ResolvedReturnType);
    if ADecl.ResolvedReturnType.Kind = tyRecord then
    begin
      { sret: prepend hidden result-buffer pointer; function becomes void }
      if Sig <> '' then Sig := 'l %_par__sret, ' + Sig
      else Sig := 'l %_par__sret';
      EmitLine(Format('%sfunction %s(%s) {', [Prefix, FuncName, Sig]));
    end
    else
      EmitLine(Format('%sfunction %s %s(%s) {', [Prefix, RetQType, FuncName, Sig]));
  end
  else
    EmitLine(Format('%sfunction %s(%s) {', [Prefix, FuncName, Sig]));

  EmitLine('@start');

  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Items[I]);
    if Par.IsOpenArray then
    begin
      { Open array: spill data pointer and high index into separate slots }
      EmitLine(Format('  %%_var_%s =l alloc8 1', [Par.ParamName]));
      EmitLine(Format('  storel %%_par_%s, %%_var_%s',
        [Par.ParamName, Par.ParamName]));
      EmitLine(Format('  %%_var_%s_high =l alloc8 1', [Par.ParamName]));
      EmitLine(Format('  storel %%_par_%s_high, %%_var_%s_high',
        [Par.ParamName, Par.ParamName]));
      Continue;
    end;
    if Par.IsVarParam then
    begin
      { Var param: spill the pointer into a local slot }
      EmitLine(Format('  %%_var_%s =l alloc8 1', [Par.ParamName]));
      EmitLine(Format('  storel %%_par_%s, %%_var_%s',
        [Par.ParamName, Par.ParamName]));
    end
    else
    begin
      case Par.ResolvedType.Kind of
        tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum:
          begin
            EmitLine(Format('  %%_var_%s =l alloc4 1', [Par.ParamName]));
            EmitLine(Format('  storew %%_par_%s, %%_var_%s',
              [Par.ParamName, Par.ParamName]));
          end;
      else
        EmitLine(Format('  %%_var_%s =l alloc8 1', [Par.ParamName]));
        EmitLine(Format('  storel %%_par_%s, %%_var_%s',
          [Par.ParamName, Par.ParamName]));
      end;
    end;
  end;

  { ARC: addref string and class value params on entry (callee owns a
    retained copy that is balanced by the release pass at function exit). }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Items[I]);
    if Par.IsVarParam or Par.IsOpenArray then Continue;
    if Par.ResolvedType.Kind = tyString then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_StringAddRef(l %s)', [ValTemp]));
    end
    else if Par.ResolvedType.Kind = tyClass then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_ClassAddRef(l %s)', [ValTemp]));
    end;
  end;

  if IsFunc then
  begin
    if ADecl.ResolvedReturnType.Kind = tyRecord then
      { sret: Result IS the caller's buffer — no allocation needed }
      EmitLine('  %_var_Result =l copy %_par__sret')
    else if RetQType = 'w' then
    begin
      EmitLine('  %_var_Result =l alloc4 1');
      EmitLine('  storew 0, %_var_Result');
    end
    else
    begin
      EmitLine('  %_var_Result =l alloc8 1');
      EmitLine('  storel 0, %_var_Result');
    end;
  end;

  SavedExitLbl := FExitLabel;
  FExitLabel   := AllocLabel('func_exit');
  try
    EmitBlock(ADecl.Body);
  finally
    FExitLabel := SavedExitLbl;
  end;

  { ARC: release string and class value params on exit (balances the
    addref inserted at function entry). }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Items[I]);
    if Par.IsVarParam or Par.IsOpenArray then Continue;
    if Par.ResolvedType.Kind = tyString then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_StringRelease(l %s)', [ValTemp]));
    end
    else if Par.ResolvedType.Kind = tyClass then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [ValTemp]));
    end;
  end;

  if IsFunc then
  begin
    if ADecl.ResolvedReturnType.Kind = tyRecord then
      EmitLine('  ret')  { sret: caller's buffer already holds result }
    else
    begin
      RetTemp := AllocTemp;
      if RetQType = 'w' then
        EmitLine(Format('  %s =w loadw %%_var_Result', [RetTemp]))
      else
        EmitLine(Format('  %s =l loadl %%_var_Result', [RetTemp]));
      EmitLine(Format('  ret %s', [RetTemp]));
    end;
  end
  else
    EmitLine('  ret');

  EmitLine('}');
  EmitLine('');
end;

procedure TCodeGenQBE.EmitStandaloneDef(ADecl: TMethodDecl);
begin
  EmitFuncDef(ADecl, False);
end;

procedure TCodeGenQBE.EmitStandaloneDefs(AProg: TProgram);
var
  I:    Integer;
  Decl: TMethodDecl;
begin
  for I := 0 to AProg.Block.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(AProg.Block.ProcDecls.Items[I]);
    { Class method impls had their body transferred — skip here. }
    if Decl.OwnerTypeName <> '' then Continue;
    { Generic templates — concrete instances are emitted via GenericFuncInstances. }
    if Decl.TypeParams <> nil then Continue;
    { Forward declarations — impl appears later in ProcDecls }
    if Decl.Body = nil then Continue;
    EmitStandaloneDef(Decl);
  end;
  { Emit each concrete generic function instance }
  for I := 0 to AProg.GenericFuncInstances.Count - 1 do
    EmitStandaloneDef(
      TGenericFuncInstance(AProg.GenericFuncInstances.Items[I]).MethodDecl);
end;

procedure TCodeGenQBE.EmitProcCall(ACall: TProcCall);
var
  UCaseName: string;
  MDecl:     TMethodDecl;
  Par:       TMethodParam;
  ArgTemp:   string;
  ArgTemp2:  string;
  SizeTemp:  string;
  ArgLine:   string;
  I:         Integer;
begin
  { User-defined procedure }
  if ACall.ResolvedDecl <> nil then
  begin
    MDecl := TMethodDecl(ACall.ResolvedDecl);
    if ACall.IsImplicitSelfMethod then
    begin
      { Implicit Self.Method — load Self pointer and pass as first arg }
      ArgTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_Self', [ArgTemp]));
      ArgLine := Format('l %s', [ArgTemp]);
      for I := 0 to ACall.Args.Count - 1 do
      begin
        Par     := TMethodParam(MDecl.Params.Items[I]);
        ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
        ArgTemp := CoerceArg(ArgTemp, TASTExpr(ACall.Args.Items[I]), QbeTypeOf(Par.ResolvedType));
        ArgLine := ArgLine + Format(', %s %s',
          [QbeTypeOf(Par.ResolvedType), ArgTemp]);
      end;
      EmitLine(Format('  call $%s_%s(%s)',
        [MDecl.OwnerTypeName, ACall.Name, ArgLine]));
      Exit;
    end;
    ArgLine := '';
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Items[I]);
      if ArgLine <> '' then ArgLine := ArgLine + ', ';
      if Par.IsOpenArray then
      begin
        if TASTExpr(ACall.Args.Items[I]) is TArrayLiteralExpr then
        begin
          ArgTemp := EmitArrayLiteralExpr(TArrayLiteralExpr(TASTExpr(ACall.Args.Items[I])));
          ArgLine := ArgLine + Format('l %s, l %d',
            [ArgTemp, TArrayLiteralExpr(TASTExpr(ACall.Args.Items[I])).Elements.Count - 1]);
        end
        else
        begin
          { Forward an open-array param variable }
          ArgTemp  := EmitExpr(TASTExpr(ACall.Args.Items[I]));
          ArgTemp2 := AllocTemp;
          EmitLine(Format('  %s =l loadl %%_var_%s_high',
            [ArgTemp2, TIdentExpr(TASTExpr(ACall.Args.Items[I])).Name]));
          ArgLine := ArgLine + Format('l %s, l %s', [ArgTemp, ArgTemp2]);
        end;
      end
      else if Par.IsVarParam then
        ArgLine := ArgLine + Format('l %s',
          [EmitVarArgAddr(TIdentExpr(TASTExpr(ACall.Args.Items[I])))])
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
        ArgTemp := CoerceArg(ArgTemp, TASTExpr(ACall.Args.Items[I]), QbeTypeOf(Par.ResolvedType));
        ArgLine := ArgLine + Format('%s %s', [QbeTypeOf(Par.ResolvedType), ArgTemp]);
      end;
    end;
    if MDecl.IsExternal and (MDecl.ExternalName <> '') then
      EmitLine(Format('  call $%s(%s)', [MDecl.ExternalName, ArgLine]))
    else
      EmitLine(Format('  call $%s(%s)', [QBEMangle(ACall.Name), ArgLine]));
    Exit;
  end;

  { Built-in }
  UCaseName := UpperCase(ACall.Name);
  if UCaseName = 'WRITELN' then
    EmitWrite(ACall, True)
  else if UCaseName = 'WRITE' then
    EmitWrite(ACall, False)
  else if UCaseName = 'FREEMEM' then
  begin
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[0]));
    EmitLine(Format('  call $free(l %s)', [ArgTemp]));
  end
  else if UCaseName = 'ZEROMEM' then
  begin
    ArgTemp  := EmitExpr(TASTExpr(ACall.Args.Items[0]));
    ArgTemp2 := EmitExpr(TASTExpr(ACall.Args.Items[1]));
    SizeTemp := AllocTemp;
    EmitLine(Format('  %s =l extsw %s', [SizeTemp, ArgTemp2]));
    EmitLine(Format('  call $memset(l %s, w 0, l %s)', [ArgTemp, SizeTemp]));
  end
  else if UCaseName = '_CLASSADDREF' then
  begin
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[0]));
    EmitLine(Format('  call $_ClassAddRef(l %s)', [ArgTemp]));
  end
  else if UCaseName = '_CLASSRELEASE' then
  begin
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[0]));
    EmitLine(Format('  call $_ClassRelease(l %s)', [ArgTemp]));
  end
  else if UCaseName = 'WRITEFILE' then
  begin
    ArgTemp  := EmitExpr(TASTExpr(ACall.Args.Items[0]));
    ArgTemp2 := EmitExpr(TASTExpr(ACall.Args.Items[1]));
    EmitLine(Format('  call $_WriteFile(l %s, l %s)', [ArgTemp, ArgTemp2]));
  end
  else if UCaseName = 'APPENDFILE' then
  begin
    ArgTemp  := EmitExpr(TASTExpr(ACall.Args.Items[0]));
    ArgTemp2 := EmitExpr(TASTExpr(ACall.Args.Items[1]));
    EmitLine(Format('  call $_AppendFile(l %s, l %s)', [ArgTemp, ArgTemp2]));
  end
  else if UCaseName = 'HALT' then
  begin
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[0]));
    EmitLine(Format('  call $exit(w %s)', [ArgTemp]));
  end
  else if (UCaseName = 'INC') or (UCaseName = 'DEC') then
  begin
    { Inc(x) / Inc(x, n) / Dec(x) / Dec(x, n) — in-place add/sub }
    ArgTemp  := EmitVarArgAddr(TIdentExpr(TASTExpr(ACall.Args.Items[0])));
    ArgTemp2 := AllocTemp;
    if (TASTExpr(ACall.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(ACall.Args.Items[0]).ResolvedType.Kind in [tyInt64, tyClass, tyPointer]) then
    begin
      EmitLine(Format('  %s =l loadl %s', [ArgTemp2, ArgTemp]));
      if ACall.Args.Count >= 2 then
        SizeTemp := EmitExpr(TASTExpr(ACall.Args.Items[1]))
      else
        SizeTemp := '1';
      ArgLine := AllocTemp;
      if UCaseName = 'INC' then
        EmitLine(Format('  %s =l add %s, %s', [ArgLine, ArgTemp2, SizeTemp]))
      else
        EmitLine(Format('  %s =l sub %s, %s', [ArgLine, ArgTemp2, SizeTemp]));
      EmitLine(Format('  storel %s, %s', [ArgLine, ArgTemp]));
    end
    else
    begin
      EmitLine(Format('  %s =w loadw %s', [ArgTemp2, ArgTemp]));
      if ACall.Args.Count >= 2 then
        SizeTemp := EmitExpr(TASTExpr(ACall.Args.Items[1]))
      else
        SizeTemp := '1';
      ArgLine := AllocTemp;
      if UCaseName = 'INC' then
        EmitLine(Format('  %s =w add %s, %s', [ArgLine, ArgTemp2, SizeTemp]))
      else
        EmitLine(Format('  %s =w sub %s, %s', [ArgLine, ArgTemp2, SizeTemp]));
      EmitLine(Format('  storew %s, %s', [ArgLine, ArgTemp]));
    end;
  end
  else if UCaseName = 'INCLUDE' then
  begin
    { Include(S, elem): S := S or (1 shl ord(elem)) }
    ArgTemp  := EmitVarArgAddr(TIdentExpr(TASTExpr(ACall.Args.Items[0])));
    ArgTemp2 := AllocTemp;
    EmitLine(Format('  %s =w loadw %s', [ArgTemp2, ArgTemp]));
    SizeTemp := EmitExpr(TASTExpr(ACall.Args.Items[1]));  { enum ordinal }
    ArgLine  := AllocTemp;
    EmitLine(Format('  %s =w shl 1, %s', [ArgLine, SizeTemp]));
    SizeTemp := AllocTemp;
    EmitLine(Format('  %s =w or %s, %s', [SizeTemp, ArgTemp2, ArgLine]));
    EmitLine(Format('  storew %s, %s', [SizeTemp, ArgTemp]));
  end
  else if UCaseName = 'EXCLUDE' then
  begin
    { Exclude(S, elem): S := S and (not (1 shl ord(elem))) }
    ArgTemp  := EmitVarArgAddr(TIdentExpr(TASTExpr(ACall.Args.Items[0])));
    ArgTemp2 := AllocTemp;
    EmitLine(Format('  %s =w loadw %s', [ArgTemp2, ArgTemp]));
    SizeTemp := EmitExpr(TASTExpr(ACall.Args.Items[1]));  { enum ordinal }
    ArgLine  := AllocTemp;
    EmitLine(Format('  %s =w shl 1, %s', [ArgLine, SizeTemp]));
    SizeTemp := AllocTemp;
    EmitLine(Format('  %s =w xor %s, -1', [SizeTemp, ArgLine]));
    ArgLine  := AllocTemp;
    EmitLine(Format('  %s =w and %s, %s', [ArgLine, ArgTemp2, SizeTemp]));
    EmitLine(Format('  storew %s, %s', [ArgLine, ArgTemp]));
  end
  else if UCaseName = 'DELETEFILE' then
  begin
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[0]));
    EmitLine(Format('  call $_DeleteFile(l %s)', [ArgTemp]));
  end
  else if UCaseName = 'PROCESSSETEXE' then
  begin
    ArgTemp  := EmitExpr(TASTExpr(ACall.Args.Items[0]));
    ArgTemp2 := EmitExpr(TASTExpr(ACall.Args.Items[1]));
    EmitLine(Format('  call $_ProcessSetExe(l %s, l %s)', [ArgTemp, ArgTemp2]));
  end
  else if UCaseName = 'PROCESSADDARG' then
  begin
    ArgTemp  := EmitExpr(TASTExpr(ACall.Args.Items[0]));
    ArgTemp2 := EmitExpr(TASTExpr(ACall.Args.Items[1]));
    EmitLine(Format('  call $_ProcessAddArg(l %s, l %s)', [ArgTemp, ArgTemp2]));
  end
  else if UCaseName = 'PROCESSEXECUTE' then
  begin
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[0]));
    EmitLine(Format('  call $_ProcessExecute(l %s)', [ArgTemp]));
  end
  else if UCaseName = 'PROCESSWAITONEXIT' then
  begin
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[0]));
    EmitLine(Format('  call $_ProcessWaitOnExit(l %s)', [ArgTemp]));
  end
  else if UCaseName = 'PROCESSFREE' then
  begin
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[0]));
    EmitLine(Format('  call $_ProcessFree(l %s)', [ArgTemp]));
  end
  else
    raise ECodeGenError.Create(Format(
      'Unknown procedure ''%s'' at line %d', [ACall.Name, ACall.Line]));
end;

procedure TCodeGenQBE.EmitPointerWrite(AStmt: TPointerWriteStmt);
var
  PtrTemp:    string;
  ValTemp:    string;
  OldTemp:    string;
  QType:      string;
  StoreInstr: string;
begin
  PtrTemp := EmitExpr(AStmt.PtrExpr);
  { ARC: string stored through a typed pointer needs retain/release }
  if (AStmt.BaseTy <> nil) and AStmt.BaseTy.IsString then
  begin
    OldTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', [OldTemp, PtrTemp]));
    ValTemp := EmitExpr(AStmt.ValExpr);
    EmitLine(Format('  call $_StringAddRef(l %s)', [ValTemp]));
    EmitLine(Format('  call $_StringRelease(l %s)', [OldTemp]));
    EmitLine(Format('  storel %s, %s', [ValTemp, PtrTemp]));
    Exit;
  end;
  ValTemp := EmitExpr(AStmt.ValExpr);
  QType   := QbeTypeOf(AStmt.BaseTy);
  if QType = 'w' then StoreInstr := 'storew'
                 else StoreInstr := 'storel';
  EmitLine(Format('  %s %s, %s', [StoreInstr, ValTemp, PtrTemp]));
end;

procedure TCodeGenQBE.EmitWrite(ACall: TProcCall; ANewline: Boolean);
var
  ArgExpr:   TASTExpr;
  ArgTemp:   string;
  CharPtr:   string;
  IsString:  Boolean;
  I:         Integer;
  StartIdx:  Integer;
  ToStderr:  Boolean;
  StderrFd:  string;
begin
  if ACall.Args.Count = 0 then
  begin
    if ANewline then
      EmitLine('  call $printf(l $__fmt_nl)');
    Exit;
  end;

  { Detect WriteLn(StdErr, ...) — first arg is integer constant 2 (StdErr) }
  StartIdx := 0;
  ToStderr := False;
  ArgExpr := TASTExpr(ACall.Args.Items[0]);
  if (ArgExpr is TIdentExpr) and SameText(TIdentExpr(ArgExpr).Name, 'StdErr') then
  begin
    StartIdx := 1;
    ToStderr := True;
    { Load the libc stderr pointer from the FILE* global }
    StderrFd := AllocTemp;
    EmitLine(Format('  %s =l loadl $stderr', [StderrFd]));
  end;

  if (StartIdx >= ACall.Args.Count) then
  begin
    if ANewline then
    begin
      if ToStderr then
        EmitLine(Format('  call $fprintf(l %s, l $__fmt_nl)', [StderrFd]))
      else
        EmitLine('  call $printf(l $__fmt_nl)');
    end;
    Exit;
  end;

  { Emit one printf/fprintf call per argument. }
  for I := StartIdx to ACall.Args.Count - 1 do
  begin
    ArgExpr  := TASTExpr(ACall.Args.Items[I]);
    IsString := (ArgExpr.ResolvedType <> nil) and ArgExpr.ResolvedType.IsString;
    ArgTemp  := EmitExpr(ArgExpr);
    if ToStderr then
    begin
      if IsString then
      begin
        CharPtr := AllocTemp;
        EmitLine(Format('  %s =l add %s, 12', [CharPtr, ArgTemp]));
        EmitLine(Format('  call $fprintf(l %s, l $__fmt_s, ..., l %s)', [StderrFd, CharPtr]));
      end
      else
        EmitLine(Format('  call $fprintf(l %s, l $__fmt_d, ..., w %s)', [StderrFd, ArgTemp]));
    end
    else
    begin
      if IsString then
      begin
        { String pointer is the header pointer; char data starts at ptr+12. }
        CharPtr := AllocTemp;
        EmitLine(Format('  %s =l add %s, 12', [CharPtr, ArgTemp]));
        EmitLine(Format('  call $printf(l $__fmt_s, ..., l %s)', [CharPtr]));
      end
      else
        EmitLine(Format('  call $printf(l $__fmt_d, ..., w %s)', [ArgTemp]));
    end;
  end;

  if ANewline then
  begin
    if ToStderr then
      EmitLine(Format('  call $fprintf(l %s, l $__fmt_nl)', [StderrFd]))
    else
      EmitLine('  call $printf(l $__fmt_nl)');
  end;
end;

function TCodeGenQBE.EmitExpr(AExpr: TASTExpr): string;
var
  T, L, R:    string;
  Op:         string;
  BinExpr:    TBinaryExpr;
  FldAccess:  TFieldAccessExpr;
  MCallExpr:  TMethodCallExpr;
  Ptr:        string;
  QType:      string;
  LoadInstr:  string;
  SelfTemp:   string;
  ArgLine:    string;
  ArgTemp:    string;
  ArgTemp2:   string;
  Par:        TMethodParam;
  MDecl:      TMethodDecl;
  RT:         TRecordTypeDesc;
  FuncName:   string;
  I:          Integer;
  IntfDesc:     TInterfaceTypeDesc;
  VTblTemp:     string;
  FPtrTemp:     string;
  SlotOff:      Integer;
  FC:           TFuncCallExpr;
  NoArgCall:    TFuncCallExpr;
  ImplFld:      TFieldInfo;
  SelfT:        string;
  PtrT:         string;
  StrLabel:     string;
  SretBuf:      string;
  IdxTemp:      string;
  IdxQType:     string;
begin
  if AExpr is TFuncCallExpr then
  begin
    { Standalone function call expression }
    FC := TFuncCallExpr(AExpr);
    { SizeOf(TypeName) → integer literal = byte size of the type }
      if SameText(FC.Name,'SizeOf') then
      begin
        T := AllocTemp;
        EmitLine(Format('  %s =w copy %d',
          [T, TASTExpr(FC.Args.Items[0]).ResolvedType.ByteSize]));
        Result := T;
        Exit;
      end;

      { GetMem(N) → malloc(N) → pointer }
      if SameText(FC.Name,'GetMem') then
      begin
        ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        { Extend arg to l for malloc }
        L := AllocTemp;
        EmitLine(Format('  %s =l extsw %s', [L, ArgTemp]));
        EmitLine(Format('  %s =l call $malloc(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      { ReallocMem(P, N) → realloc(P, N) → pointer }
      if SameText(FC.Name,'ReallocMem') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        ArgTemp := AllocTemp;
        EmitLine(Format('  %s =l extsw %s', [ArgTemp, R]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $realloc(l %s, l %s)', [T, L, ArgTemp]));
        Result := T;
        Exit;
      end;

      { Open-array intrinsics }
      if SameText(FC.Name,'High') then
      begin
        T := AllocTemp;
        if TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyStaticArray then
          EmitLine(Format('  %s =w copy %d', [T,
            TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).HighBound]))
        else
        begin
          { Open-array: load the high-index slot and truncate to Integer (w) }
          L := TIdentExpr(FC.Args.Items[0]).Name;
          R := AllocTemp;
          EmitLine(Format('  %s =l loadl %%_var_%s_high', [R, L]));
          EmitLine(Format('  %s =w truncl %s', [T, R]));
        end;
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'Low') then
      begin
        T := AllocTemp;
        if TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyStaticArray then
          EmitLine(Format('  %s =w copy %d', [T,
            TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).LowBound]))
        else
          EmitLine(Format('  %s =w copy 0', [T]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'PChar') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
          tyPChar, tyPointer:
            Result := L;  { identity — raw pointer, no offset }
        else
          { PChar(str) — pointer to char data: str_ptr + 12 (past ARC header) }
          T := AllocTemp;
          EmitLine(Format('  %s =l add %s, 12', [T, L]));
          Result := T;
        end;
        Exit;
      end;

      if SameText(FC.Name,'string') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_StringFromPChar(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      { Built-in string operations — delegate to RTL functions }
      if SameText(FC.Name,'Length') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_StringLength(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'Pos') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_StringPos(l %s, l %s)', [T, L, R]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'Copy') then
      begin
        L       := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R       := EmitExpr(TASTExpr(FC.Args.Items[1]));
        ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[2]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_StringCopy(l %s, w %s, w %s)',
          [T, L, R, ArgTemp]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'UpperCase') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_StringUpperCase(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'LowerCase') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_StringLowerCase(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'Trim') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_StringTrim(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'SameText') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_StringSameText(l %s, l %s)', [T, L, R]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'IntToStr') then
      begin
        { Route to _Int64ToStr when the argument is Int64-typed, matching FPC's
          overloaded IntToStr resolution for Int64 values. }
        if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
           (QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType) = 'l') then
        begin
          L := EmitExpr(TASTExpr(FC.Args.Items[0]));
          T := AllocTemp;
          EmitLine(Format('  %s =l call $_Int64ToStr(l %s)', [T, L]));
        end
        else
        begin
          L := EmitExpr(TASTExpr(FC.Args.Items[0]));
          T := AllocTemp;
          EmitLine(Format('  %s =l call $_IntToStr(w %s)', [T, L]));
        end;
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'Int64ToStr') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_Int64ToStr(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'StrToInt') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_StrToInt(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'StrToInt64') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_StrToInt64(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      { Format(fmt, arg0, arg1, ...) → $_StringFormat(l fmt, ..., tag val, ...)
        Each arg is emitted as a (w tag, w/l value) pair after the variadic
        marker.  tag=0 for integer types, tag=1 for string/pointer types. }
      if SameText(FC.Name,'Format') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        { Build variadic arg pairs: "..., w tag, w/l val, ..." }
        ArgLine := Format('l %s, ...', [L]);
        { Support Pascal array-of-const notation: Format(str, [a, b, c]) }
        if (FC.Args.Count = 2) and (FC.Args.Items[1] is TArrayLiteralExpr) then
        begin
          for I := 0 to TArrayLiteralExpr(FC.Args.Items[1]).Elements.Count - 1 do
          begin
            ArgTemp := EmitExpr(TASTExpr(TArrayLiteralExpr(FC.Args.Items[1]).Elements.Items[I]));
            if TASTExpr(TArrayLiteralExpr(FC.Args.Items[1]).Elements.Items[I]).ResolvedType.Kind in
               [tyInteger, tyBoolean, tyByte, tyUInt32, tyInt64, tyEnum] then
              ArgLine := ArgLine + Format(', w 0, w %s', [ArgTemp])
            else
              ArgLine := ArgLine + Format(', w 1, l %s', [ArgTemp]);
          end;
        end
        else
          for I := 1 to FC.Args.Count - 1 do
          begin
            ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[I]));
            if TASTExpr(FC.Args.Items[I]).ResolvedType.Kind in
               [tyInteger, tyBoolean, tyByte, tyUInt32, tyInt64, tyEnum] then
              ArgLine := ArgLine + Format(', w 0, w %s', [ArgTemp])
            else
              ArgLine := ArgLine + Format(', w 1, l %s', [ArgTemp]);
          end;
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_StringFormat(%s)', [T, ArgLine]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'OrdAt') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_OrdAt(l %s, w %s)', [T, L, R]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'Ord') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        { String/char arg: get ordinal of first byte via OrdAt(str, 1) }
        { Enum/integer arg: already an integer — just copy }
        if TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyString then
          EmitLine(Format('  %s =w call $_OrdAt(l %s, w 1)', [T, L]))
        else
          EmitLine(Format('  %s =w copy %s', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'Chr') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_Chr(w %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'UpCase') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_UpCase(w %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'CompareStr') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_StringCompare(l %s, l %s)', [T, L, R]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'CompareText') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_StringCompareText(l %s, l %s)', [T, L, R]));
        Result := T;
        Exit;
      end;

      { CLI arguments }
      if SameText(FC.Name,'ParamCount') then
      begin
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_ParamCount()', [T]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'ParamStr') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_ParamStr(w %s)', [T, L]));
        Result := T;
        Exit;
      end;

      { File I/O functions }
      if SameText(FC.Name,'ReadFile') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_ReadFile(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'FileExists') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_FileExists(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      { Environment and process }
      if SameText(FC.Name,'GetEnvVar') or SameText(FC.Name,'GetEnvironmentVariable') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_GetEnvVar(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'CurrentExceptionMessage') then
      begin
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_CurrentExceptionMessage()', [T]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'Exec') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_Exec(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      { File path manipulation }
      if SameText(FC.Name,'ChangeFileExt') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_ChangeFileExt(l %s, l %s)',
          [T, L, EmitExpr(TASTExpr(FC.Args.Items[1]))]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'ExtractFileName') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_ExtractFileName(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'ExtractFilePath') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_ExtractFilePath(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'IncludeTrailingPathDelimiter') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_IncludeTrailingPathDelimiter(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      { Process management built-ins }
      if SameText(FC.Name,'ProcessCreate') then
      begin
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_ProcessCreate()', [T]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'ProcessRunning') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_ProcessRunning(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'ProcessReadOutput') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_ProcessReadOutput(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'ProcessExitCode') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_ProcessExitCode(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      { Type cast TypeName(Expr) — ResolvedDecl is nil; copy/extend to target QBE type }
      if FC.ResolvedDecl = nil then
      begin
        ArgTemp  := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T        := AllocTemp;
        QType    := QbeTypeOf(FC.ResolvedType);
        if QType = 'w' then
          EmitLine(Format('  %s =w copy %s', [T, ArgTemp]))
        else
        begin
          { Widening from w to l: sign-extend rather than copy (QBE rejects l copy w) }
          if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
             (QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType) = 'w') then
            EmitLine(Format('  %s =l extsw %s', [T, ArgTemp]))
          else
            EmitLine(Format('  %s =l copy %s', [T, ArgTemp]));
        end;
        Result := T;
        Exit;
      end;

      MDecl    := TMethodDecl(FC.ResolvedDecl);
      QType    := QbeTypeOf(MDecl.ResolvedReturnType);
      { sret: record-returning function — caller allocates a zero-init buffer
        and passes its address as the first (hidden) parameter. }
      if MDecl.ResolvedReturnType.Kind = tyRecord then
      begin
        RT      := TRecordTypeDesc(MDecl.ResolvedReturnType);
        SretBuf := AllocTemp;
        if RT.MaxAlign >= 8 then
          EmitLine(Format('  %s =l alloc8 %d', [SretBuf, RT.TotalSize]))
        else
          EmitLine(Format('  %s =l alloc4 %d', [SretBuf, RT.TotalSize]));
        if RT.TotalSize > 0 then
          EmitLine(Format('  call $memset(l %s, w 0, l %d)', [SretBuf, RT.TotalSize]));
        EmitRecordCallSret(AExpr, SretBuf);
        Result := SretBuf;
        Exit;
      end;
      if FC.IsImplicitSelfMethod then
      begin
        ArgTemp := AllocTemp;
        EmitLine(Format('  %s =l loadl %%_var_Self', [ArgTemp]));
        ArgLine  := Format('l %s', [ArgTemp]);
        FuncName := '$' + MDecl.OwnerTypeName + '_' + FC.Name;
        for I := 0 to FC.Args.Count - 1 do
        begin
          Par     := TMethodParam(MDecl.Params.Items[I]);
          ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[I]));
          ArgTemp := CoerceArg(ArgTemp, TASTExpr(FC.Args.Items[I]), QbeTypeOf(Par.ResolvedType));
          ArgLine := ArgLine + Format(', %s %s',
            [QbeTypeOf(Par.ResolvedType), ArgTemp]);
        end;
        T := AllocTemp;
        EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FuncName, ArgLine]));
        Result := T;
        Exit;
      end;
      if MDecl.IsExternal and (MDecl.ExternalName <> '') then
        FuncName := '$' + MDecl.ExternalName
      else
        FuncName := '$' + QBEMangle(FC.Name);
      ArgLine  := '';
      for I := 0 to FC.Args.Count - 1 do
      begin
        Par := TMethodParam(MDecl.Params.Items[I]);
        if ArgLine <> '' then ArgLine := ArgLine + ', ';
        if Par.IsOpenArray then
        begin
          if TASTExpr(FC.Args.Items[I]) is TArrayLiteralExpr then
          begin
            ArgTemp := EmitArrayLiteralExpr(TArrayLiteralExpr(TASTExpr(FC.Args.Items[I])));
            ArgLine := ArgLine + Format('l %s, l %d',
              [ArgTemp, TArrayLiteralExpr(TASTExpr(FC.Args.Items[I])).Elements.Count - 1]);
          end
          else
          begin
            { Forward an open-array param variable }
            ArgTemp  := EmitExpr(TASTExpr(FC.Args.Items[I]));
            ArgTemp2 := AllocTemp;
            EmitLine(Format('  %s =l loadl %%_var_%s_high',
              [ArgTemp2, TIdentExpr(TASTExpr(FC.Args.Items[I])).Name]));
            ArgLine := ArgLine + Format('l %s, l %s', [ArgTemp, ArgTemp2]);
          end;
        end
        else if Par.IsVarParam then
          ArgLine := ArgLine + Format('l %s',
            [EmitVarArgAddr(TIdentExpr(TASTExpr(FC.Args.Items[I])))])
        else
        begin
          ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[I]));
          ArgTemp := CoerceArg(ArgTemp, TASTExpr(FC.Args.Items[I]), QbeTypeOf(Par.ResolvedType));
          ArgLine := ArgLine + Format('%s %s', [QbeTypeOf(Par.ResolvedType), ArgTemp]);
        end;
      end;
      T := AllocTemp;
      EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FuncName, ArgLine]));
      Result := T;
    Exit;
  end;

  if AExpr is TMethodCallExpr then
  begin
    MCallExpr := TMethodCallExpr(AExpr);

    { Interface method call expression: dispatch through itab }
    if (MCallExpr.ResolvedClassType <> nil) and
       (MCallExpr.ResolvedClassType.Kind = tyInterface) then
    begin
      IntfDesc := TInterfaceTypeDesc(MCallExpr.ResolvedClassType);
      SelfTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s_obj',
        [SelfTemp, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)]));
      VTblTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s_itab',
        [VTblTemp, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)]));
      SlotOff := IntfDesc.MethodIndex(MCallExpr.Name) * 8;
      FPtrTemp := AllocTemp;
      if SlotOff = 0 then
        EmitLine(Format('  %s =l loadl %s', [FPtrTemp, VTblTemp]))
      else
      begin
        ArgTemp := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', [ArgTemp, VTblTemp, SlotOff]));
        EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
      end;
      { Evaluate arguments before the call }
      ArgLine := Format('l %s', [SelfTemp]);
      for I := 0 to MCallExpr.Args.Count - 1 do
      begin
        ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Items[I]));
        ArgLine := ArgLine + Format(', w %s', [ArgTemp]);
      end;
      T := AllocTemp;
      EmitLine(Format('  %s =w call %s(%s)', [T, FPtrTemp, ArgLine]));
      Result := T;
      Exit;
    end;

    RT := TRecordTypeDesc(MCallExpr.ResolvedClassType);

    { Constructor call with args: TypeName.Create(args) }
    if MCallExpr.IsConstructorCall then
    begin
      SelfTemp := AllocTemp;
      EmitLine(Format('  %s =l call $_ClassAlloc(l %d, l $_FieldCleanup_%s)',
        [SelfTemp, RT.TotalSize, RT.Name]));
      if RT.HasVTable then
        EmitLine(Format('  storel $vtable_%s, %s',
          [QBEMangle(RT.Name), SelfTemp]));
      EmitLine(Format('  call $_ClassAddRef(l %s)', [SelfTemp]));
      { If there's a user-defined Create method, call it }
      if MCallExpr.ResolvedMethod <> nil then
      begin
        MDecl   := TMethodDecl(MCallExpr.ResolvedMethod);
        ArgLine := Format('l %s', [SelfTemp]);
        for I := 0 to MCallExpr.Args.Count - 1 do
        begin
          Par     := TMethodParam(MDecl.Params.Items[I]);
          ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Items[I]));
          ArgLine := ArgLine + Format(', %s %s', [QbeTypeOf(Par.ResolvedType), ArgTemp]);
        end;
        if MDecl.OwnerTypeName <> '' then
          FuncName := '$' + MDecl.OwnerTypeName + '_' + MCallExpr.Name
        else
          FuncName := '$' + RT.Name + '_' + MCallExpr.Name;
        EmitLine(Format('  call %s(%s)', [FuncName, ArgLine]));
      end;
      Result := SelfTemp;
      Exit;
    end;

    MDecl     := TMethodDecl(MCallExpr.ResolvedMethod);
    if MDecl.OwnerTypeName <> '' then
      FuncName := '$' + MDecl.OwnerTypeName + '_' + MCallExpr.Name
    else
      FuncName := '$' + RT.Name + '_' + MCallExpr.Name;
    QType     := QbeTypeOf(MDecl.ResolvedReturnType);
    { sret: record-returning method }
    if MDecl.ResolvedReturnType.Kind = tyRecord then
    begin
      RT      := TRecordTypeDesc(MDecl.ResolvedReturnType);
      SretBuf := AllocTemp;
      if RT.MaxAlign >= 8 then
        EmitLine(Format('  %s =l alloc8 %d', [SretBuf, RT.TotalSize]))
      else
        EmitLine(Format('  %s =l alloc4 %d', [SretBuf, RT.TotalSize]));
      if RT.TotalSize > 0 then
        EmitLine(Format('  call $memset(l %s, w 0, l %d)', [SretBuf, RT.TotalSize]));
      EmitRecordCallSret(AExpr, SretBuf);
      Result := SretBuf;
      Exit;
    end;

    { Load the object pointer (Self): either from a named variable or from
      evaluating the receiver expression (e.g. a typecast). }
    if MCallExpr.ObjExpr <> nil then
      SelfTemp := EmitExpr(MCallExpr.ObjExpr)
    else if MCallExpr.IsVarParam then
    begin
      { Var/out param: local slot holds caller's address — dereference twice }
      SelfTemp := AllocTemp;
      FPtrTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [FPtrTemp, MCallExpr.ObjectName]));
      EmitLine(Format('  %s =l loadl %s', [SelfTemp, FPtrTemp]));
    end
    else
    begin
      SelfTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [SelfTemp, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)]));
    end;

    { Build argument string }
    ArgLine := Format('l %s', [SelfTemp]);
    for I := 0 to MCallExpr.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Items[I]);
      if Par.IsVarParam then
        ArgLine := ArgLine + Format(', l %s',
          [EmitVarArgAddr(TIdentExpr(TASTExpr(MCallExpr.Args.Items[I])))])
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Items[I]));
        ArgLine := ArgLine + Format(', %s %s', [QbeTypeOf(Par.ResolvedType), ArgTemp]);
      end;
    end;

    T := AllocTemp;
    if MDecl.VTableSlot >= 0 then
    begin
      { Virtual dispatch: load vptr then function pointer from vtable }
      VTblTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [VTblTemp, SelfTemp]));
      FPtrTemp := AllocTemp;
      SlotOff  := (MDecl.VTableSlot + 1) * 8;
      ArgTemp  := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', [ArgTemp, VTblTemp, SlotOff]));
      EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
      EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FPtrTemp, ArgLine]));
    end
    else
      EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FuncName, ArgLine]));
    Result := T;
    Exit;
  end;

  if AExpr is TNilLiteral then
  begin
    T := AllocTemp;
    EmitLine(Format('  %s =l copy 0', [T]));
    Result := T;
    Exit;
  end;

  if AExpr is TIntLiteral then
  begin
    T := AllocTemp;
    EmitLine(Format('  %s =w copy %s', [T, IntToStr(TIntLiteral(AExpr).Value)]));
    Result := T;
  end
  else if AExpr is TStringLiteral then
  begin
    if TStringLiteral(AExpr).IsCharCoerce then
    begin
      T := AllocTemp;
      EmitLine(Format('  %s =w copy %d', [T, TStringLiteral(AExpr).CharOrdValue]));
      Result := T;
    end
    else
      Result := EmitStrLit(TStringLiteral(AExpr).Value);
  end
  else if AExpr is TStringSubscriptExpr then
  begin
    Result := EmitStringSubscriptExpr(TStringSubscriptExpr(AExpr));
  end
  else if AExpr is TArrayLiteralExpr then
  begin
    Result := EmitArrayLiteralExpr(TArrayLiteralExpr(AExpr));
  end
  else if AExpr is TFieldAccessExpr then
  begin
    FldAccess := TFieldAccessExpr(AExpr);
    { Chained access: compute base storage pointer, then load the field from
      (base_ptr + offset) using the field's QBE type. }
    if FldAccess.Base <> nil then
    begin
      if FldAccess.IsMethodCall then
      begin
        { Zero-arg method on chained base }
        L     := EmitInstancePtr(FldAccess.Base);
        MDecl := TMethodDecl(FldAccess.ResolvedMethod);
        if MDecl.ResolvedReturnType.Kind = tyRecord then
        begin
          RT      := TRecordTypeDesc(MDecl.ResolvedReturnType);
          SretBuf := AllocTemp;
          if RT.MaxAlign >= 8 then
            EmitLine(Format('  %s =l alloc8 %d', [SretBuf, RT.TotalSize]))
          else
            EmitLine(Format('  %s =l alloc4 %d', [SretBuf, RT.TotalSize]));
          if RT.TotalSize > 0 then
            EmitLine(Format('  call $memset(l %s, w 0, l %d)', [SretBuf, RT.TotalSize]));
          EmitLine(Format('  call $%s_%s(l %s, l %s)',
            [MDecl.OwnerTypeName, FldAccess.FieldName, SretBuf, L]));
          Result := SretBuf;
        end
        else
        begin
          QType := QbeTypeOf(MDecl.ResolvedReturnType);
          T := AllocTemp;
          EmitLine(Format('  %s =%s call $%s_%s(l %s)',
            [T, QType, MDecl.OwnerTypeName, FldAccess.FieldName, L]));
          Result := T;
        end;
        Exit;
      end;
      L := EmitInstancePtr(FldAccess.Base);
      { Method-backed property read (indexed or non-indexed) }
      if FldAccess.PropRead <> nil then
      begin
        QType := QbeTypeOf(FldAccess.PropRead.TypeDesc);
        T := AllocTemp;
        if FldAccess.PropIndexExpr <> nil then
        begin
          IdxTemp  := EmitExpr(FldAccess.PropIndexExpr);
          IdxQType := QbeTypeOf(FldAccess.PropRead.IndexTypeDesc);
          EmitLine(Format('  %s =%s call $%s_%s(l %s, %s %s)',
            [T, QType, FldAccess.PropOwnerType, FldAccess.PropRead.ReadMethod,
             L, IdxQType, IdxTemp]));
        end
        else
          EmitLine(Format('  %s =%s call $%s_%s(l %s)',
            [T, QType, FldAccess.PropOwnerType, FldAccess.PropRead.ReadMethod, L]));
        Result := T;
        Exit;
      end;
      if FldAccess.FieldInfo = nil then
        raise ECodeGenError.Create(Format(
          'Chained field ''%s'' has no resolved field info', [FldAccess.FieldName]));
      if FldAccess.FieldInfo.Offset > 0 then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d',
          [Ptr, L, FldAccess.FieldInfo.Offset]));
      end
      else
        Ptr := L;
      QType := QbeTypeOf(FldAccess.FieldInfo.TypeDesc);
      T     := AllocTemp;
      if QType = 'w' then LoadInstr := 'loadw'
                     else LoadInstr := 'loadl';
      EmitLine(Format('  %s =%s %s %s', [T, QType, LoadInstr, Ptr]));
      Result := T;
      Exit;
    end;
    if FldAccess.IsImplicitSelf then
    begin
      { Implicit Self.Base.Field — Base is a field of Self }
      L := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_Self', [L]));
      if FldAccess.ImplicitBaseInfo.Offset > 0 then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d',
          [Ptr, L, FldAccess.ImplicitBaseInfo.Offset]));
        L := Ptr;
      end;
      if FldAccess.IsClassAccess then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l loadl %s', [Ptr, L]));
        L := Ptr;
      end;
      if FldAccess.IsMethodCall then
      begin
        { Zero-arg method on implicit-Self field: emit call(L) }
        MDecl := TMethodDecl(FldAccess.ResolvedMethod);
        if MDecl.ResolvedReturnType.Kind = tyRecord then
        begin
          RT      := TRecordTypeDesc(MDecl.ResolvedReturnType);
          SretBuf := AllocTemp;
          if RT.MaxAlign >= 8 then
            EmitLine(Format('  %s =l alloc8 %d', [SretBuf, RT.TotalSize]))
          else
            EmitLine(Format('  %s =l alloc4 %d', [SretBuf, RT.TotalSize]));
          if RT.TotalSize > 0 then
            EmitLine(Format('  call $memset(l %s, w 0, l %d)', [SretBuf, RT.TotalSize]));
          EmitLine(Format('  call $%s_%s(l %s, l %s)',
            [MDecl.OwnerTypeName, FldAccess.FieldName, SretBuf, L]));
          Result := SretBuf;
        end
        else
        begin
          QType := QbeTypeOf(MDecl.ResolvedReturnType);
          T := AllocTemp;
          EmitLine(Format('  %s =%s call $%s_%s(l %s)',
            [T, QType, MDecl.OwnerTypeName, FldAccess.FieldName, L]));
          Result := T;
        end;
        Exit;
      end;
      if FldAccess.PropRead <> nil then
      begin
        { Method-backed property read via implicit-Self field }
        T     := AllocTemp;
        QType := QbeTypeOf(FldAccess.PropRead.TypeDesc);
        if FldAccess.PropIndexExpr <> nil then
        begin
          IdxTemp  := EmitExpr(FldAccess.PropIndexExpr);
          IdxQType := QbeTypeOf(FldAccess.PropRead.IndexTypeDesc);
          EmitLine(Format('  %s =%s call $%s_%s(l %s, %s %s)',
            [T, QType, QBEMangle(FldAccess.PropOwnerType),
             FldAccess.PropRead.ReadMethod, L, IdxQType, IdxTemp]));
        end
        else
          EmitLine(Format('  %s =%s call $%s_%s(l %s)',
            [T, QType, QBEMangle(FldAccess.PropOwnerType),
             FldAccess.PropRead.ReadMethod, L]));
        Result := T;
        Exit;
      end;
      if FldAccess.FieldInfo.Offset > 0 then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d',
          [Ptr, L, FldAccess.FieldInfo.Offset]));
      end
      else
        Ptr := L;
      QType := QbeTypeOf(FldAccess.FieldInfo.TypeDesc);
      T     := AllocTemp;
      if QType = 'w' then LoadInstr := 'loadw'
                     else LoadInstr := 'loadl';
      EmitLine(Format('  %s =%s %s %s', [T, QType, LoadInstr, Ptr]));
      Result := T;
    end
    else if FldAccess.IsMethodCall then
    begin
      { Zero-arg method call on a variable: Obj.Method }
      MDecl := TMethodDecl(FldAccess.ResolvedMethod);
      if MDecl.ResolvedReturnType.Kind = tyRecord then
      begin
        RT      := TRecordTypeDesc(MDecl.ResolvedReturnType);
        SretBuf := AllocTemp;
        if RT.MaxAlign >= 8 then
          EmitLine(Format('  %s =l alloc8 %d', [SretBuf, RT.TotalSize]))
        else
          EmitLine(Format('  %s =l alloc4 %d', [SretBuf, RT.TotalSize]));
        if RT.TotalSize > 0 then
          EmitLine(Format('  call $memset(l %s, w 0, l %d)', [SretBuf, RT.TotalSize]));
        EmitRecordCallSret(AExpr, SretBuf);
        Result := SretBuf;
      end
      else
      begin
        L := AllocTemp;
        EmitLine(Format('  %s =l loadl %s',
          [L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
        QType := QbeTypeOf(MDecl.ResolvedReturnType);
        T := AllocTemp;
        EmitLine(Format('  %s =%s call $%s_%s(l %s)',
          [T, QType, MDecl.OwnerTypeName, FldAccess.FieldName, L]));
        Result := T;
      end;
    end
    else if FldAccess.IsConstant then
    begin
      { Class-level constant: TypeName.ConstName — emit as an integer or string literal }
      if FldAccess.ResolvedType.Kind = tyString then
      begin
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_StringRetain(l $%s)',
          [T, EmitStrLit(FldAccess.ConstString)]));
        Result := T;
      end
      else
      begin
        T := AllocTemp;
        EmitLine(Format('  %s =w copy %d', [T, FldAccess.ConstValue]));
        Result := T;
      end;
    end
    else if FldAccess.IsConstructorCall then
    begin
      { TypeName.Create — allocate zeroed instance on heap.  _ClassAlloc
        prefixes a 16-byte header (refcount + field-cleanup fn pointer)
        before the returned pointer (see blaise_arc.c).  The user pointer
        still points at the vptr, so field offsets are unchanged.  The
        cleanup fn is invoked by _ClassRelease before free() when the
        refcount reaches zero and is responsible for releasing any
        ARC-managed fields. }
      T := AllocTemp;
      EmitLine(Format('  %s =l call $_ClassAlloc(l %d, l $_FieldCleanup_%s)',
        [T, TRecordTypeDesc(FldAccess.ResolvedType).TotalSize,
         QBEMangle(FldAccess.ResolvedType.Name)]));
      { Store vtable pointer at offset 0 if this class has virtual methods }
      if TRecordTypeDesc(FldAccess.ResolvedType).HasVTable then
        EmitLine(Format('  storel $vtable_%s, %s',
          [QBEMangle(FldAccess.ResolvedType.Name), T]));
      { Call user-defined Create body if one exists }
      if FldAccess.ResolvedMethod <> nil then
      begin
        MDecl := TMethodDecl(FldAccess.ResolvedMethod);
        if MDecl.OwnerTypeName <> '' then
          FuncName := '$' + MDecl.OwnerTypeName + '_' + FldAccess.FieldName
        else
          FuncName := '$' + QBEMangle(FldAccess.ResolvedType.Name) + '_' + FldAccess.FieldName;
        EmitLine(Format('  call %s(l %s)', [FuncName, T]));
      end;
      Result := T;
    end
    else if FldAccess.PropRead <> nil then
    begin
      { Method-backed property read: load Self pointer and call getter }
      L := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
      T     := AllocTemp;
      QType := QbeTypeOf(FldAccess.PropRead.TypeDesc);
      if FldAccess.PropIndexExpr <> nil then
      begin
        IdxTemp  := EmitExpr(FldAccess.PropIndexExpr);
        IdxQType := QbeTypeOf(FldAccess.PropRead.IndexTypeDesc);
        EmitLine(Format('  %s =%s call $%s_%s(l %s, %s %s)',
          [T, QType, QBEMangle(FldAccess.PropOwnerType),
           FldAccess.PropRead.ReadMethod, L, IdxQType, IdxTemp]));
      end
      else
        EmitLine(Format('  %s =%s call $%s_%s(l %s)',
          [T, QType, QBEMangle(FldAccess.PropOwnerType),
           FldAccess.PropRead.ReadMethod, L]));
      Result := T;
    end
    else if FldAccess.IsClassAccess then
    begin
      { Load heap pointer, then load field }
      L := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
      if FldAccess.FieldInfo.Offset > 0 then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', [Ptr, L, FldAccess.FieldInfo.Offset]));
      end
      else
        Ptr := L;
      QType := QbeTypeOf(FldAccess.FieldInfo.TypeDesc);
      T     := AllocTemp;
      if QType = 'w' then LoadInstr := 'loadw'
                     else LoadInstr := 'loadl';
      EmitLine(Format('  %s =%s %s %s', [T, QType, LoadInstr, Ptr]));
      Result := T;
    end
    else
    begin
      { Record field access }
      if FldAccess.FieldInfo = nil then
        raise ECodeGenError.Create(Format(
          'Field access ''%s.%s'' has no resolved field info',
          [FldAccess.RecordName, FldAccess.FieldName]));
      Ptr   := FieldPtr(FldAccess.RecordName, FldAccess.FieldInfo.Offset);
      QType := QbeTypeOf(FldAccess.FieldInfo.TypeDesc);
      T     := AllocTemp;
      if QType = 'w' then LoadInstr := 'loadw'
                     else LoadInstr := 'loadl';
      EmitLine(Format('  %s =%s %s %s', [T, QType, LoadInstr, Ptr]));
      Result := T;
    end;
  end
  else if AExpr is TIdentExpr then
  begin
    T := AllocTemp;
    if TIdentExpr(AExpr).IsImplicitSelf then
    begin
      { Bare field name — equivalent to Self.FieldName: load Self, add offset }
      ImplFld := TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo);
      SelfT   := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_Self', [SelfT]));
      { Record-typed field: return the field's storage address, not a loaded value }
      if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyRecord) then
      begin
        if ImplFld.Offset > 0 then
        begin
          PtrT := AllocTemp;
          EmitLine(Format('  %s =l add %s, %d', [PtrT, SelfT, ImplFld.Offset]));
          Result := PtrT;
        end
        else
          Result := SelfT;
        Exit;
      end;
      T := AllocTemp;
      QType := QbeTypeOf(AExpr.ResolvedType);
      if ImplFld.Offset > 0 then
      begin
        PtrT := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', [PtrT, SelfT, ImplFld.Offset]));
        if QType = 'w' then
          EmitLine(Format('  %s =w loadw %s', [T, PtrT]))
        else
          EmitLine(Format('  %s =l loadl %s', [T, PtrT]));
      end
      else
      begin
        if QType = 'w' then
          EmitLine(Format('  %s =w loadw %s', [T, SelfT]))
        else
          EmitLine(Format('  %s =l loadl %s', [T, SelfT]));
      end;
      Result := T;
      Exit;
    end;

    if TIdentExpr(AExpr).IsImplicitSelfMethod then
    begin
      { Bare zero-arg method call on Self — emit direct call }
      NoArgCall := TFuncCallExpr.Create;
      try
        NoArgCall.Name                 := TIdentExpr(AExpr).Name;
        NoArgCall.ResolvedType         := AExpr.ResolvedType;
        NoArgCall.ResolvedDecl         := TIdentExpr(AExpr).ImplicitMethodDecl;
        NoArgCall.IsImplicitSelfMethod := True;
        Result := EmitExpr(NoArgCall);
      finally
        NoArgCall.Free;
      end;
      Exit;
    end
    else if TIdentExpr(AExpr).IsNoArgFuncCall then
    begin
      { Bare identifier resolving to a zero-arg function (no parens in source).
        Synthesise a temporary TFuncCallExpr so existing builtin dispatch
        handles it without duplicating logic. }
      NoArgCall := TFuncCallExpr.Create;
      try
        NoArgCall.Name         := TIdentExpr(AExpr).Name;
        NoArgCall.ResolvedType := AExpr.ResolvedType;
        NoArgCall.ResolvedDecl := TIdentExpr(AExpr).NoArgFuncDecl;
        Result := EmitExpr(NoArgCall);
      finally
        NoArgCall.Free;
      end;
      Exit;
    end
    else if TIdentExpr(AExpr).IsConstant then
    begin
      if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyString) then
      begin
        { String constant — emit as a string literal data label (l-typed pointer) }
        StrLabel := EmitStrLit(TIdentExpr(AExpr).ConstString);
        EmitLine(Format('  %s =l copy %s', [T, StrLabel]));
      end
      else if (AExpr.ResolvedType <> nil) and
              (QbeTypeOf(AExpr.ResolvedType) = 'l') then
        EmitLine(Format('  %s =l copy %s', [T, IntToStr(TIdentExpr(AExpr).ConstValue)]))
      else
        EmitLine(Format('  %s =w copy %d', [T, TIdentExpr(AExpr).ConstValue]));
    end
    else if TIdentExpr(AExpr).IsVarParam then
    begin
      { Var param: load pointer, then dereference }
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [Ptr, TIdentExpr(AExpr).Name]));
      QType := QbeTypeOf(AExpr.ResolvedType);
      if QType = 'l' then
        EmitLine(Format('  %s =l loadl %s', [T, Ptr]))
      else
        EmitLine(Format('  %s =w loadw %s', [T, Ptr]));
    end
    else if (AExpr.ResolvedType <> nil) and
            (AExpr.ResolvedType.Kind in [tyRecord, tyStaticArray]) then
    begin
      { Aggregate variable — return its storage address directly (no load). }
      Result := VarRef(TIdentExpr(AExpr).Name, TIdentExpr(AExpr).IsGlobal);
      Exit;
    end
    else if TIdentExpr(AExpr).IsGlobal then
    begin
      { Global program-level variable: address is $Name in data section }
      if (AExpr.ResolvedType <> nil) and (QbeTypeOf(AExpr.ResolvedType) = 'w') then
        EmitLine(Format('  %s =w loadw $%s', [T, TIdentExpr(AExpr).Name]))
      else
        EmitLine(Format('  %s =l loadl $%s', [T, TIdentExpr(AExpr).Name]));
    end
    else if (AExpr.ResolvedType <> nil) and (QbeTypeOf(AExpr.ResolvedType) = 'l') then
    begin
      EmitLine(Format('  %s =l loadl %%_var_%s', [T, TIdentExpr(AExpr).Name]));
    end
    else
    begin
      EmitLine(Format('  %s =w loadw %%_var_%s', [T, TIdentExpr(AExpr).Name]));
    end;
    Result := T;
  end
  else if AExpr is TBinaryExpr then
  begin
    BinExpr := TBinaryExpr(AExpr);
    { Bitwise and/or for integer operands (not Boolean short-circuit) }
    if ((BinExpr.Op = boAnd) or (BinExpr.Op = boOr)) and
       (BinExpr.ResolvedType <> nil) and BinExpr.ResolvedType.IsNumeric then
    begin
      L := EmitExpr(BinExpr.Left);
      R := EmitExpr(BinExpr.Right);
      T := AllocTemp;
      if BinExpr.ResolvedType.Kind = tyInt64 then
      begin
        if BinExpr.Op = boAnd then
          EmitLine(Format('  %s =l and %s, %s', [T, L, R]))
        else
          EmitLine(Format('  %s =l or %s, %s', [T, L, R]));
      end
      else
      begin
        if BinExpr.Op = boAnd then
          EmitLine(Format('  %s =w and %s, %s', [T, L, R]))
        else
          EmitLine(Format('  %s =w or %s, %s', [T, L, R]));
      end;
      Result := T;
      Exit;
    end;
    { Short-circuit boolean and/or: evaluate LHS, then skip RHS when the
      result is already determined.  FPC and Delphi use short-circuit by
      default, and the compiler source relies on it for guarded nil-checks
      like "(P <> nil) and P.IsX". }
    if (BinExpr.Op = boAnd) or (BinExpr.Op = boOr) then
    begin
      SelfTemp := AllocTemp;   { slot holding the boolean result }
      EmitLine(Format('  %s =l alloc4 1', [SelfTemp]));
      L := EmitExpr(BinExpr.Left);
      EmitLine(Format('  storew %s, %s', [L, SelfTemp]));
      FuncName := AllocLabel('sc_rhs');   { reuse local; acts as RHS label }
      ArgLine  := AllocLabel('sc_end');   { reuse local; acts as end label }
      if BinExpr.Op = boAnd then
        EmitLine(Format('  jnz %s, @%s, @%s', [L, FuncName, ArgLine]))
      else
        EmitLine(Format('  jnz %s, @%s, @%s', [L, ArgLine, FuncName]));
      EmitLine('@' + FuncName);
      R := EmitExpr(BinExpr.Right);
      EmitLine(Format('  storew %s, %s', [R, SelfTemp]));
      EmitLine(Format('  jmp @%s', [ArgLine]));
      EmitLine('@' + ArgLine);
      T := AllocTemp;
      EmitLine(Format('  %s =w loadw %s', [T, SelfTemp]));
      Result := T;
      Exit;
    end;
    L := EmitExpr(BinExpr.Left);
    R := EmitExpr(BinExpr.Right);
    T := AllocTemp;
    { String concatenation: delegate to RTL }
    if (BinExpr.Op = boAdd) and
       (BinExpr.Left.ResolvedType <> nil) and
       BinExpr.Left.ResolvedType.IsString then
    begin
      { Temporarily own any unowned intermediate string temps so they can be
        properly freed after the concat copies their bytes into the result. }
      if BinExpr.Left is TBinaryExpr then
        EmitLine(Format('  call $_StringAddRef(l %s)', [L]));
      if (BinExpr.Right is TBinaryExpr) or
         (BinExpr.Right is TFuncCallExpr) or
         (BinExpr.Right is TMethodCallExpr) then
        EmitLine(Format('  call $_StringAddRef(l %s)', [R]));
      EmitLine(Format('  %s =l call $_StringConcat(l %s, l %s)', [T, L, R]));
      if BinExpr.Left is TBinaryExpr then
        EmitLine(Format('  call $_StringRelease(l %s)', [L]));
      if (BinExpr.Right is TBinaryExpr) or
         (BinExpr.Right is TFuncCallExpr) or
         (BinExpr.Right is TMethodCallExpr) then
        EmitLine(Format('  call $_StringRelease(l %s)', [R]));
      Result := T;
      Exit;
    end;
    { Pointer arithmetic: Pointer/PChar +/- Integer — result is same pointer type }
    if (BinExpr.Op in [boAdd, boSub]) and
       (BinExpr.Left.ResolvedType <> nil) and
       (BinExpr.Left.ResolvedType.Kind in [tyPointer, tyPChar]) then
    begin
      ArgTemp := AllocTemp;
      EmitLine(Format('  %s =l extsw %s', [ArgTemp, R]));
      if BinExpr.Op = boAdd then
        EmitLine(Format('  %s =l add %s, %s', [T, L, ArgTemp]))
      else
        EmitLine(Format('  %s =l sub %s, %s', [T, L, ArgTemp]));
      Result := T;
      Exit;
    end;
    { String equality/inequality: content comparison via RTL helper }
    if (BinExpr.Left.ResolvedType <> nil) and
       BinExpr.Left.ResolvedType.IsString and
       (BinExpr.Op in [boEQ, boNE]) then
    begin
      EmitLine(Format('  %s =w call $_StringEquals(l %s, l %s)', [T, L, R]));
      if BinExpr.Op = boNE then
      begin
        ArgTemp := AllocTemp;
        EmitLine(Format('  %s =w ceqw %s, 0', [ArgTemp, T]));
        T := ArgTemp;
      end;
      Result := T;
      Exit;
    end;
    { Set membership: elem in SetVar — (set >> ord(elem)) & 1 }
    if BinExpr.Op = boIn then
    begin
      ArgTemp := AllocTemp;
      EmitLine(Format('  %s =w shr %s, %s', [ArgTemp, R, L]));
      EmitLine(Format('  %s =w and %s, 1', [T, ArgTemp]));
      Result := T;
      Exit;
    end;

    { Set arithmetic: union, difference, intersection }
    if (BinExpr.Left.ResolvedType <> nil) and
       (BinExpr.Left.ResolvedType.Kind = tySet) then
    begin
      case BinExpr.Op of
        boAdd:  { union: or }
          EmitLine(Format('  %s =w or %s, %s', [T, L, R]));
        boSub:  { difference: L and (not R) }
        begin
          ArgTemp := AllocTemp;
          EmitLine(Format('  %s =w xor %s, -1', [ArgTemp, R]));
          EmitLine(Format('  %s =w and %s, %s', [T, L, ArgTemp]));
        end;
        boMul:  { intersection: and }
          EmitLine(Format('  %s =w and %s, %s', [T, L, R]));
        boEQ:
          EmitLine(Format('  %s =w ceqw %s, %s', [T, L, R]));
        boNE:
          EmitLine(Format('  %s =w cnew %s, %s', [T, L, R]));
      else
        raise ECodeGenError.Create(Format(
          'Operator not supported for set types at line %d', [BinExpr.Line]));
      end;
      Result := T;
      Exit;
    end;

    { Use long (pointer) comparison instructions when operands are class/nil }
    if (BinExpr.Left.ResolvedType <> nil) and
       (BinExpr.Left.ResolvedType.Kind in [tyClass, tyNil]) then
    begin
      case BinExpr.Op of
        boEQ: Op := 'ceql';
        boNE: Op := 'cnel';
      else
        Op := 'ceql';
      end;
      EmitLine(Format('  %s =w %s %s, %s', [T, Op, L, R]));
    end
    // Int64 arithmetic: use l-typed instructions; extend w operands to l as needed.
    else if (BinExpr.ResolvedType <> nil) and (BinExpr.ResolvedType.Kind = tyInt64) then
    begin
      if (BinExpr.Left.ResolvedType = nil) or (BinExpr.Left.ResolvedType.Kind <> tyInt64) then
      begin
        ArgTemp := AllocTemp;
        EmitLine(Format('  %s =l extsw %s', [ArgTemp, L]));
        L := ArgTemp;
      end;
      // For shift ops, the shift count stays w (QBE accepts w shift count for l shifts).
      // For arithmetic ops, extend the right operand to l too.
      if not (BinExpr.Op in [boShl, boShr]) then
      begin
        if (BinExpr.Right.ResolvedType = nil) or (BinExpr.Right.ResolvedType.Kind <> tyInt64) then
        begin
          ArgTemp := AllocTemp;
          EmitLine(Format('  %s =l extsw %s', [ArgTemp, R]));
          R := ArgTemp;
        end;
      end;
      case BinExpr.Op of
        boAdd: Op := 'add';
        boSub: Op := 'sub';
        boMul: Op := 'mul';
        boDiv: Op := 'div';
        boMod: Op := 'rem';
        boAnd: Op := 'and';
        boOr:  Op := 'or';
        boShl: Op := 'shl';
        boShr: Op := 'shr';
      else
        Op := 'add';
      end;
      EmitLine(Format('  %s =l %s %s, %s', [T, Op, L, R]));
    end
    else
    begin
      case BinExpr.Op of
        boAdd: Op := 'add';
        boSub: Op := 'sub';
        boMul: Op := 'mul';
        boDiv: Op := 'div';
        boMod: Op := 'rem';
        boEQ:  Op := 'ceqw';
        boNE:  Op := 'cnew';
        boLT:  Op := 'csltw';
        boGT:  Op := 'csgtw';
        boLE:  Op := 'cslew';
        boGE:  Op := 'csgew';
        boAnd: Op := 'and';
        boOr:  Op := 'or';
        boShl: Op := 'shl';
        boShr: Op := 'shr';
      else
        Op := 'add';
      end;
      EmitLine(Format('  %s =w %s %s, %s', [T, Op, L, R]));
    end;
    Result := T;
  end
  else if AExpr is TNotExpr then
  begin
    { Logical not on Boolean (0/1): xor with 1 flips the low bit. }
    L := EmitExpr(TNotExpr(AExpr).Expr);
    T := AllocTemp;
    EmitLine(Format('  %s =w xor %s, 1', [T, L]));
    Result := T;
  end
  else if AExpr is TDerefExpr then
  begin
    { P^ — load the value at the pointer address }
    T     := EmitExpr(TDerefExpr(AExpr).Expr);
    QType := QbeTypeOf(AExpr.ResolvedType);
    L     := AllocTemp;
    if QType = 'w' then
      EmitLine(Format('  %s =w loadw %s', [L, T]))
    else
      EmitLine(Format('  %s =l loadl %s', [L, T]));
    Result := L;
  end
  else if AExpr is TAddrOfExpr then
    Result := EmitAddrOfExpr(TAddrOfExpr(AExpr))
  else if AExpr is TIsExpr then
    Result := EmitIsExpr(TIsExpr(AExpr))
  else if AExpr is TAsExpr then
    Result := EmitAsExpr(TAsExpr(AExpr))
  else
    raise ECodeGenError.Create('Unknown expression node type');
end;

function TCodeGenQBE.EmitIsExpr(AExpr: TIsExpr): string;
var
  ObjTemp: string;
  ResTemp: string;
begin
  ObjTemp := EmitExpr(AExpr.Obj);
  ResTemp := AllocTemp;
  if (AExpr.ResolvedTargetType <> nil) and
     (AExpr.ResolvedTargetType.Kind = tyInterface) then
    EmitLine(Format('  %s =w call $_ImplementsInterface(l %s, l $typeinfo_%s)',
      [ResTemp, ObjTemp, AExpr.TypeName]))
  else
    EmitLine(Format('  %s =w call $_IsInstance(l %s, l $typeinfo_%s)',
      [ResTemp, ObjTemp, AExpr.TypeName]));
  Result := ResTemp;
end;

function TCodeGenQBE.EmitAsExpr(AExpr: TAsExpr): string;
var
  ObjTemp:  string;
  OkTemp:   string;
  SlotTemp: string;
  ResTemp:  string;
  LblOk:    string;
  LblFail:  string;
  LblEnd:   string;
begin
  ObjTemp  := EmitExpr(AExpr.Obj);
  SlotTemp := AllocTemp;
  EmitLine(Format('  %s =l alloc8 1', [SlotTemp]));

  OkTemp  := AllocTemp;
  LblOk   := AllocLabel('as_ok');
  LblFail := AllocLabel('as_fail');
  LblEnd  := AllocLabel('as_end');

  EmitLine(Format('  %s =w call $_IsInstance(l %s, l $typeinfo_%s)',
    [OkTemp, ObjTemp, AExpr.TypeName]));
  EmitLine(Format('  jnz %s, @%s, @%s', [OkTemp, LblOk, LblFail]));

  EmitLine('@' + LblFail);
  EmitLine('  call $_Raise_InvalidCast()');
  EmitLine(Format('  storel 0, %s', [SlotTemp]));  { unreachable; satisfies SSA }
  EmitLine(Format('  jmp @%s', [LblEnd]));

  EmitLine('@' + LblOk);
  EmitLine(Format('  storel %s, %s', [ObjTemp, SlotTemp]));
  EmitLine(Format('  jmp @%s', [LblEnd]));

  EmitLine('@' + LblEnd);
  ResTemp := AllocTemp;
  EmitLine(Format('  %s =l loadl %s', [ResTemp, SlotTemp]));
  Result := ResTemp;
end;

function TCodeGenQBE.QBEMangle(const AName: string): string;
var
  I: Integer;
  C: Integer;
begin
  Result := '';
  for I := 1 to Length(AName) do
  begin
    C := Ord(AName[I]);
    case C of
      60: Result := Result + '_';    { '<' }
      62: ;                          { '>' — skip }
      44: Result := Result + '_';    { ',' }
    else
      Result := Result + Chr(C);
    end;
  end;
end;

function TCodeGenQBE.QbeEscapeString(const AStr: string): string;
var
  I:    Integer;
  C:    Integer;
  Hi:   Integer;
  Lo:   Integer;
begin
  Result := '';
  for I := 1 to Length(AStr) do
  begin
    C := Ord(AStr[I]);  { FPC: Ord(Char); Blaise: AStr[I] already Integer }
    case C of
      34:  Result := Result + '\"';   { '"' }
      92:  Result := Result + '\\';   { '\' }
      10:  Result := Result + '\n';
      13:  Result := Result + '\r';
      9:   Result := Result + '\t';
      else if (C < 32) or (C > 126) then
      begin
        Hi := C shr 4;
        Lo := C and 15;
        if Hi < 10 then Hi := 48 + Hi else Hi := 55 + Hi;
        if Lo < 10 then Lo := 48 + Lo else Lo := 55 + Lo;
        Result := Result + '\' + Chr(Hi) + Chr(Lo)
      end
      else
        Result := Result + Chr(C);
    end;
  end;
end;

procedure TCodeGenQBE.Generate(AProg: TProgram);
var
  Body:        TStringList;
  SavedOutput: TStringList;
begin
  FOutput.Clear;
  FStrLits.Clear;
  FStrLitsEmitted := 0;
  FTempCount  := 0;
  FLabelCount := 0;

  Body := TStringList.Create;
  try
    SavedOutput := FOutput;
    FOutput := Body;
    try
      EmitFieldCleanupDefs(AProg);
      EmitMethodDefs(AProg);
      EmitStandaloneDefs(AProg);
      FExitLabel := 'main_exit';
      EmitMainHeader;
      EmitBlock(AProg.Block);
      EmitMainFooter;
      FExitLabel := '';
    finally
      FOutput := SavedOutput;
    end;

    EmitLine('# Generated by Blaise Compiler');
    EmitLine('# Source: ' + AProg.Name);
    EmitLine('');
    EmitDataSection;
    EmitGlobalVarData(AProg.Block);
    EmitInterfaceDefs(AProg);
    EmitTypeInfoDefs(AProg);
    EmitVTableDefs(AProg);
    FOutput.AddStrings(Body);
  finally
    Body.Free;
  end;
end;

procedure TCodeGenQBE.GenerateUnit(AUnit: TUnit);
var
  I:         Integer;
  ImplDecl:  TMethodDecl;
  IntfNames: TStringList;
  Body:      TStringList;
  SavedOut:  TStringList;
begin
  FOutput.Clear;
  FStrLits.Clear;
  FStrLitsEmitted := 0;
  FTempCount  := 0;
  FLabelCount := 0;

  IntfNames := TStringList.Create;
  try
    IntfNames.CaseSensitive := False;
    for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
      IntfNames.Add(TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]).Name);

    Body := TStringList.Create;
    try
      SavedOut := FOutput;
      FOutput  := Body;
      try
        for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
        begin
          ImplDecl := TMethodDecl(AUnit.ImplBlock.ProcDecls.Items[I]);
          EmitFuncDef(ImplDecl, IntfNames.IndexOf(ImplDecl.Name) >= 0);
        end;
      finally
        FOutput := SavedOut;
      end;

      EmitLine('# Generated by Blaise Compiler');
      EmitLine('# Unit: ' + AUnit.Name);
      EmitLine('');
      EmitDataSection;
      FOutput.AddStrings(Body);
    finally
      Body.Free;
    end;
  finally
    IntfNames.Free;
  end;
end;

procedure TCodeGenQBE.SetSymbolTable(ASymTable: TSymbolTable);
begin
  FSymTable := ASymTable;
end;

procedure TCodeGenQBE.AppendUnit(AUnit: TUnit);
var
  I, J, K, S:  Integer;
  ImplDecl:     TMethodDecl;
  IntfNames:    TStringList;
  Body:         TStringList;
  SavedOut:     TStringList;
  TD:           TTypeDecl;
  CD:           TClassTypeDef;
  MDecl:        TMethodDecl;
  TDesc:        TTypeDesc;
  RT:           TRecordTypeDesc;
  ClassRT:      TRecordTypeDesc;
  IntfDesc:     TInterfaceTypeDesc;
  ParentStr:    string;
  ImplStr:      string;
  ItabLine:     string;
  ImplLine:     string;
  MethName:     string;
  IntfMangle:   string;
  VLine:        string;
  E:            TVTableEntry;
begin
  { No clears — output and string literal table accumulate across calls.
    Counter resets are safe: QBE temps and block labels are function-scoped. }
  FTempCount  := 0;
  FLabelCount := 0;

  IntfNames := TStringList.Create;
  try
    IntfNames.CaseSensitive := False;
    for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
      IntfNames.Add(TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]).Name);

    Body := TStringList.Create;
    try
      SavedOut := FOutput;
      FOutput  := Body;
      try
        { Standalone functions from impl block.
          Skip class method stubs (OwnerTypeName <> ''): after LinkClassMethodImpls
          their bodies were transferred to the class definition and their
          parameter types are not resolved — EmitFuncDef would crash on nil ResolvedType. }
        for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
        begin
          ImplDecl := TMethodDecl(AUnit.ImplBlock.ProcDecls.Items[I]);
          if ImplDecl.OwnerTypeName <> '' then Continue;
          EmitFuncDef(ImplDecl, IntfNames.IndexOf(ImplDecl.Name) >= 0);
        end;

        { Class method bodies from interface type declarations.
          After LinkClassMethodImpls the class definition's TMethodDecl nodes
          hold the bodies and parameter types are resolved by AnalyseMethodBodies. }
        for I := 0 to AUnit.IntfBlock.TypeDecls.Count - 1 do
        begin
          TD := TTypeDecl(AUnit.IntfBlock.TypeDecls.Items[I]);
          if not (TD.Def is TClassTypeDef) then Continue;
          CD := TClassTypeDef(TD.Def);
          for J := 0 to CD.Methods.Count - 1 do
          begin
            MDecl := TMethodDecl(CD.Methods.Items[J]);
            if MDecl.Body <> nil then
              EmitMethodDef(TD.Name, MDecl);
          end;
        end;

        { Field cleanup functions — emitted here (inside redirect) because they
          are function bodies, not data.  Requires FSymTable to look up TRecordTypeDesc. }
        if FSymTable <> nil then
          for I := 0 to AUnit.IntfBlock.TypeDecls.Count - 1 do
          begin
            TD := TTypeDecl(AUnit.IntfBlock.TypeDecls.Items[I]);
            if not (TD.Def is TClassTypeDef) then Continue;
            TDesc := FSymTable.FindType(TD.Name);
            if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
            RT := TRecordTypeDesc(TDesc);
            EmitFieldCleanupFn(TD.Name, RT);
          end;
      finally
        FOutput := SavedOut;
      end;

      EmitLine('# Unit: ' + AUnit.Name);
      EmitLine('');
      EmitPendingStrLits;

      { Per-class data sections: typeinfo, vtables, interface tables.
        All require FSymTable to look up resolved TRecordTypeDesc. }
      if FSymTable <> nil then
      begin
        { Interface typeinfo blocks }
        for I := 0 to AUnit.IntfBlock.TypeDecls.Count - 1 do
        begin
          TD := TTypeDecl(AUnit.IntfBlock.TypeDecls.Items[I]);
          if TD.Def is TInterfaceTypeDef then
            EmitLine('data $typeinfo_' + TD.Name + ' = { l 0 }');
        end;

        { Class typeinfo blocks }
        for I := 0 to AUnit.IntfBlock.TypeDecls.Count - 1 do
        begin
          TD := TTypeDecl(AUnit.IntfBlock.TypeDecls.Items[I]);
          if not (TD.Def is TClassTypeDef) then Continue;
          TDesc := FSymTable.FindType(TD.Name);
          if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
          RT := TRecordTypeDesc(TDesc);
          if RT.Parent <> nil then
            ParentStr := '$typeinfo_' + RT.Parent.Name
          else
            ParentStr := '0';
          if RT.ImplementsCount > 0 then
            ImplStr := '$impllist_' + TD.Name
          else
            ImplStr := '0';
          EmitLine('data $typeinfo_' + TD.Name +
                   ' = { l ' + ParentStr + ', l ' + ImplStr + ' }');
        end;

        { Vtable data }
        for I := 0 to AUnit.IntfBlock.TypeDecls.Count - 1 do
        begin
          TD := TTypeDecl(AUnit.IntfBlock.TypeDecls.Items[I]);
          if not (TD.Def is TClassTypeDef) then Continue;
          TDesc := FSymTable.FindType(TD.Name);
          if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
          RT := TRecordTypeDesc(TDesc);
          if not RT.HasVTable then Continue;
          VLine := 'data $vtable_' + TD.Name + ' = { l $typeinfo_' + TD.Name;
          for S := 0 to RT.VTableCount - 1 do
          begin
            E := RT.VTableEntryAt(S);
            VLine := VLine + ', l ' + E.ImplName;
          end;
          VLine := VLine + ' }';
          EmitLine(VLine);
        end;

        { Interface itab and impllist blocks for implementing classes }
        for I := 0 to AUnit.IntfBlock.TypeDecls.Count - 1 do
        begin
          TD := TTypeDecl(AUnit.IntfBlock.TypeDecls.Items[I]);
          if not (TD.Def is TClassTypeDef) then Continue;
          TDesc := FSymTable.FindType(TD.Name);
          if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
          ClassRT := TRecordTypeDesc(TDesc);
          if ClassRT.ImplementsCount = 0 then Continue;
          for J := 0 to ClassRT.ImplementsCount - 1 do
          begin
            IntfDesc   := ClassRT.ImplementsIntfAt(J);
            IntfMangle := QBEMangle(IntfDesc.Name);
            ItabLine   := 'data $itab_' + TD.Name + '_' + IntfMangle + ' = {';
            for K := 0 to IntfDesc.MethodCount - 1 do
            begin
              MethName := IntfDesc.MethodName(K);
              if K = 0 then
                ItabLine := ItabLine + ' l $' + TD.Name + '_' + MethName
              else
                ItabLine := ItabLine + ', l $' + TD.Name + '_' + MethName;
            end;
            ItabLine := ItabLine + ' }';
            EmitLine(ItabLine);
          end;
          ImplLine := 'data $impllist_' + TD.Name + ' = {';
          for J := 0 to ClassRT.ImplementsCount - 1 do
          begin
            IntfDesc   := ClassRT.ImplementsIntfAt(J);
            IntfMangle := QBEMangle(IntfDesc.Name);
            if J = 0 then
              ImplLine := ImplLine + ' l $typeinfo_' + IntfMangle +
                                     ', l $itab_' + TD.Name + '_' + IntfMangle
            else
              ImplLine := ImplLine + ', l $typeinfo_' + IntfMangle +
                                     ', l $itab_' + TD.Name + '_' + IntfMangle;
          end;
          ImplLine := ImplLine + ', l 0 }';
          EmitLine(ImplLine);
        end;
      end;

      { Global variables from impl section (IsGlobal set by semantic analyser) }
      EmitGlobalVarData(AUnit.ImplBlock);

      FOutput.AddStrings(Body);
    finally
      Body.Free;
    end;
  finally
    IntfNames.Free;
  end;
end;

procedure TCodeGenQBE.AppendProgram(AProg: TProgram);
var
  Body:        TStringList;
  SavedOutput: TStringList;
begin
  { No clears — accumulates after AppendUnit calls. }
  FTempCount  := 0;
  FLabelCount := 0;

  Body := TStringList.Create;
  try
    SavedOutput := FOutput;
    FOutput := Body;
    try
      EmitFieldCleanupDefs(AProg);
      EmitMethodDefs(AProg);
      EmitStandaloneDefs(AProg);
      FExitLabel := 'main_exit';
      EmitMainHeader;
      EmitBlock(AProg.Block);
      EmitMainFooter;
      FExitLabel := '';
    finally
      FOutput := SavedOutput;
    end;

    EmitLine('# Generated by Blaise Compiler');
    EmitLine('# Source: ' + AProg.Name);
    EmitLine('');
    EmitDataSection;  { emits remaining string literals + $__fmt_* (once) }
    EmitGlobalVarData(AProg.Block);
    EmitInterfaceDefs(AProg);
    EmitTypeInfoDefs(AProg);
    EmitVTableDefs(AProg);
    FOutput.AddStrings(Body);
  finally
    Body.Free;
  end;
end;

function TCodeGenQBE.GetOutput: string;
begin
  Result := FOutput.Text;
end;

function TCodeGenQBE.EmitStringSubscriptExpr(AExpr: TStringSubscriptExpr): string;
var
  StrPtr, IdxW, IdxL, Offset, BytePtr, ByteVal: string;
  ElemType:  TOpenArrayTypeDesc;
  ElemSize:  Integer;
  QLoad:     string;
  QType:     string;
  ElemPtr:   string;
  SAT:       TStaticArrayTypeDesc;
  LowBnd:    Integer;
  Adj:       string;
begin
  { Indexed property read: Obj.Items[I] — delegate to EmitExpr(StrExpr) }
  if (AExpr.StrExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr.StrExpr).PropRead <> nil) then
  begin
    Result := EmitExpr(AExpr.StrExpr);
    Exit;
  end;
  { Static array element read: A[I] where A: array[L..H] of T }
  if AExpr.StrExpr.ResolvedType.Kind = tyStaticArray then
  begin
    SAT      := TStaticArrayTypeDesc(AExpr.StrExpr.ResolvedType);
    ElemSize := SAT.ElementType.RawSize;
    LowBnd   := SAT.LowBound;
    case SAT.ElementType.Kind of
      tyByte, tyBoolean: QLoad := 'loadub';
      tyInteger, tyUInt32, tyEnum: QLoad := 'loadw';
      tyInt64, tyString, tyClass, tyPointer: QLoad := 'loadl';
    else
      QLoad := 'loadl';
    end;
    QType   := QbeTypeOf(SAT.ElementType);
    StrPtr  := EmitExpr(AExpr.StrExpr);
    IdxW    := EmitExpr(AExpr.IndexExpr);
    IdxL    := AllocTemp;
    Offset  := AllocTemp;
    ElemPtr := AllocTemp;
    ByteVal := AllocTemp;
    EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
    if LowBnd <> 0 then
    begin
      Adj := AllocTemp;
      EmitLine(Format('  %s =l sub %s, %d', [Adj, IdxL, LowBnd]));
      EmitLine(Format('  %s =l mul %s, %d', [Offset, Adj, ElemSize]));
    end
    else
      EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
    EmitLine(Format('  %s =l add %s, %s', [ElemPtr, StrPtr, Offset]));
    EmitLine(Format('  %s =%s %s %s', [ByteVal, QType, QLoad, ElemPtr]));
    Result := ByteVal;
    Exit;
  end;

  { Open-array element access: A[I] where A: array of T }
  if AExpr.StrExpr.ResolvedType.Kind = tyOpenArray then
  begin
    ElemType := TOpenArrayTypeDesc(AExpr.StrExpr.ResolvedType);
    ElemSize := ElemType.ElementType.ByteSize;
    case ElemType.ElementType.Kind of
      tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum: QLoad := 'loadw';
      tyInt64, tyString, tyClass, tyPointer:          QLoad := 'loadl';
    else
      QLoad := 'loadl';
    end;
    QType   := QbeTypeOf(ElemType.ElementType);
    StrPtr  := EmitExpr(AExpr.StrExpr);
    IdxW    := EmitExpr(AExpr.IndexExpr);
    IdxL    := AllocTemp;
    Offset  := AllocTemp;
    ElemPtr := AllocTemp;
    ByteVal := AllocTemp;
    EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
    EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
    EmitLine(Format('  %s =l add %s, %s', [ElemPtr, StrPtr, Offset]));
    EmitLine(Format('  %s =%s %s %s', [ByteVal, QType, QLoad, ElemPtr]));
    Result := ByteVal;
    Exit;
  end;

  { PChar byte access: P[I] (0-based) — loadub at ptr + I }
  if AExpr.StrExpr.ResolvedType.Kind = tyPChar then
  begin
    StrPtr  := EmitExpr(AExpr.StrExpr);
    IdxW    := EmitExpr(AExpr.IndexExpr);
    IdxL    := AllocTemp;
    BytePtr := AllocTemp;
    ByteVal := AllocTemp;
    EmitLine(Format('  %s =l extuw %s', [IdxL, IdxW]));
    EmitLine(Format('  %s =l add %s, %s', [BytePtr, StrPtr, IdxL]));
    EmitLine(Format('  %s =w loadub %s', [ByteVal, BytePtr]));
    Result := ByteVal;
    Exit;
  end;

  { String byte access: S[N] (1-based).
    String layout: [refcount(4)][length(4)][capacity(4)][chars...][0]
    S[N] = byte at ptr + 12 + (N - 1) = ptr + N + 11 }
  StrPtr  := EmitExpr(AExpr.StrExpr);    { pointer to string header (l) }
  IdxW    := EmitExpr(AExpr.IndexExpr);  { 1-based index (w) }
  IdxL    := AllocTemp;
  Offset  := AllocTemp;
  BytePtr := AllocTemp;
  ByteVal := AllocTemp;
  EmitLine(Format('  %s =l extuw %s', [IdxL, IdxW]));
  EmitLine(Format('  %s =l add %s, 11', [Offset, IdxL]));  { 12 + (N-1) = N+11 }
  EmitLine(Format('  %s =l add %s, %s', [BytePtr, StrPtr, Offset]));
  EmitLine(Format('  %s =w loadub %s', [ByteVal, BytePtr]));
  Result := ByteVal;
end;

function TCodeGenQBE.EmitAddrOfExpr(AExpr: TAddrOfExpr): string;
var
  Sub:     TStringSubscriptExpr;
  SAT:     TStaticArrayTypeDesc;
  OAT:     TOpenArrayTypeDesc;
  ElemSize: Integer;
  LowBnd:  Integer;
  StrPtr:  string;
  IdxW:    string;
  IdxL:    string;
  Adj:     string;
  Offset:  string;
  ElemPtr: string;
begin
  if AExpr.Expr is TStringSubscriptExpr then
  begin
    Sub := TStringSubscriptExpr(AExpr.Expr);
    if Sub.StrExpr.ResolvedType.Kind = tyStaticArray then
    begin
      SAT      := TStaticArrayTypeDesc(Sub.StrExpr.ResolvedType);
      ElemSize := SAT.ElementType.RawSize;
      LowBnd   := SAT.LowBound;
      StrPtr   := EmitExpr(Sub.StrExpr);
      IdxW     := EmitExpr(Sub.IndexExpr);
      IdxL     := AllocTemp;
      Offset   := AllocTemp;
      ElemPtr  := AllocTemp;
      EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
      if LowBnd <> 0 then
      begin
        Adj := AllocTemp;
        EmitLine(Format('  %s =l sub %s, %d', [Adj, IdxL, LowBnd]));
        EmitLine(Format('  %s =l mul %s, %d', [Offset, Adj, ElemSize]));
      end
      else
        EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
      EmitLine(Format('  %s =l add %s, %s', [ElemPtr, StrPtr, Offset]));
      Result := ElemPtr;
      Exit;
    end;
    if Sub.StrExpr.ResolvedType.Kind = tyOpenArray then
    begin
      OAT      := TOpenArrayTypeDesc(Sub.StrExpr.ResolvedType);
      ElemSize := OAT.ElementType.RawSize;
      StrPtr   := EmitExpr(Sub.StrExpr);
      IdxW     := EmitExpr(Sub.IndexExpr);
      IdxL     := AllocTemp;
      Offset   := AllocTemp;
      ElemPtr  := AllocTemp;
      EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
      EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
      EmitLine(Format('  %s =l add %s, %s', [ElemPtr, StrPtr, Offset]));
      Result := ElemPtr;
      Exit;
    end;
  end;
  if AExpr.Expr is TIdentExpr then
  begin
    Result := VarRef(TIdentExpr(AExpr.Expr).Name,
                     TIdentExpr(AExpr.Expr).IsGlobal);
    Exit;
  end;
  raise ECodeGenError.Create(
    'address-of (@) is only supported for array subscripts and local variables');
end;

procedure TCodeGenQBE.EmitStaticSubscriptAssign(AStmt: TStaticSubscriptAssign);
var
  SAT:        TStaticArrayTypeDesc;
  ElemType:   TTypeDesc;
  ElemSize:   Integer;
  LowBnd:     Integer;
  StoreInstr: string;
  IdxW:       string;
  IdxL:       string;
  Adj:        string;
  Offset:     string;
  ElemPtr:    string;
  ElemVal:    string;
  PCharBase:  string;
begin
  { PChar subscript write: P[I] := Integer — storeb at ptr + I }
  if AStmt.ResolvedArrayType.Kind = tyPChar then
  begin
    IdxW     := EmitExpr(AStmt.IndexExpr);
    IdxL     := AllocTemp;
    ElemPtr  := AllocTemp;
    ElemVal  := EmitExpr(AStmt.ValueExpr);
    PCharBase := AllocTemp;
    if AStmt.IsGlobal then
      EmitLine(Format('  %s =l loadl $%s', [PCharBase, AStmt.ArrayName]))
    else
      EmitLine(Format('  %s =l loadl %%_var_%s', [PCharBase, AStmt.ArrayName]));
    EmitLine(Format('  %s =l extuw %s', [IdxL, IdxW]));
    EmitLine(Format('  %s =l add %s, %s', [ElemPtr, PCharBase, IdxL]));
    EmitLine(Format('  storeb %s, %s', [ElemVal, ElemPtr]));
    Exit;
  end;
  SAT      := TStaticArrayTypeDesc(AStmt.ResolvedArrayType);
  ElemType := SAT.ElementType;
  ElemSize := ElemType.RawSize;
  LowBnd   := SAT.LowBound;
  case ElemType.Kind of
    tyByte, tyBoolean: StoreInstr := 'storeb';
    tyInteger, tyUInt32, tyEnum: StoreInstr := 'storew';
    tyInt64, tyString, tyClass, tyPointer: StoreInstr := 'storel';
  else
    StoreInstr := 'storew';
  end;
  { %_var_Name is already the base pointer to the stack buffer (from alloc) }
  IdxW    := EmitExpr(AStmt.IndexExpr);
  IdxL    := AllocTemp;
  Offset  := AllocTemp;
  ElemPtr := AllocTemp;
  ElemVal := EmitExpr(AStmt.ValueExpr);
  EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
  if LowBnd <> 0 then
  begin
    Adj := AllocTemp;
    EmitLine(Format('  %s =l sub %s, %d', [Adj, IdxL, LowBnd]));
    EmitLine(Format('  %s =l mul %s, %d', [Offset, Adj, ElemSize]));
  end
  else
    EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
  EmitLine(Format('  %s =l add %%_var_%s, %s', [ElemPtr, AStmt.ArrayName, Offset]));
  EmitLine(Format('  %s %s, %s', [StoreInstr, ElemVal, ElemPtr]));
end;

function TCodeGenQBE.EmitSetLiteralExpr(AExpr: TArrayLiteralExpr): string;
{ Compute a compile-time bitmask for a set literal [elem, ...].
  Each element must be a constant enum value; bit (1 shl ordinal) is set.
  Returns a QBE temp holding the 32-bit integer mask. }
var
  Mask:   Integer;
  I:      Integer;
  Elem:   TASTExpr;
  IdExpr: TIdentExpr;
  Tmp:    string;
begin
  Mask := 0;
  for I := 0 to AExpr.Elements.Count - 1 do
  begin
    Elem := TASTExpr(AExpr.Elements.Items[I]);
    if not (Elem is TIdentExpr) then
      raise ECodeGenError.Create('Set literal elements must be enum constant references');
    IdExpr := TIdentExpr(Elem);
    if not IdExpr.IsConstant then
      raise ECodeGenError.Create(Format(
        'Set literal element ''%s'' is not a constant', [IdExpr.Name]));
    Mask := Mask or (1 shl IdExpr.ConstValue);
  end;
  Tmp := AllocTemp;
  EmitLine(Format('  %s =w copy %d', [Tmp, Mask]));
  Result := Tmp;
end;

function TCodeGenQBE.EmitArrayLiteralExpr(AExpr: TArrayLiteralExpr): string;
var
  OAType:     TOpenArrayTypeDesc;
  ElemType:   TTypeDesc;
  ElemSize:   Integer;
  AllocInstr: string;
  StoreInstr: string;
  TotalBytes: Integer;
  BufPtr:     string;
  ElemVal:    string;
  ElemPtr:    string;
  Offset:     string;
  I:          Integer;
begin
  { Set literal: emit as bitmask constant rather than a memory buffer }
  if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tySet) then
  begin
    Result := EmitSetLiteralExpr(AExpr);
    Exit;
  end;

  OAType   := TOpenArrayTypeDesc(AExpr.ResolvedType);
  ElemType := OAType.ElementType;
  ElemSize := ElemType.ByteSize;
  TotalBytes := AExpr.Elements.Count * ElemSize;
  if TotalBytes < 1 then TotalBytes := 1;
  case ElemType.Kind of
    tyString, tyClass, tyPointer, tyInt64:
    begin
      AllocInstr := 'alloc8';
      StoreInstr := 'storel';
    end;
  else
    AllocInstr := 'alloc4';
    StoreInstr := 'storew';
  end;
  BufPtr := AllocTemp;
  EmitLine(Format('  %s =l %s %d', [BufPtr, AllocInstr, TotalBytes]));
  for I := 0 to AExpr.Elements.Count - 1 do
  begin
    ElemVal := EmitExpr(TASTExpr(AExpr.Elements.Items[I]));
    if I = 0 then
      EmitLine(Format('  %s %s, %s', [StoreInstr, ElemVal, BufPtr]))
    else
    begin
      Offset  := AllocTemp;
      ElemPtr := AllocTemp;
      EmitLine(Format('  %s =l copy %d', [Offset, I * ElemSize]));
      EmitLine(Format('  %s =l add %s, %s', [ElemPtr, BufPtr, Offset]));
      EmitLine(Format('  %s %s, %s', [StoreInstr, ElemVal, ElemPtr]));
    end;
  end;
  Result := BufPtr;
end;

end.
