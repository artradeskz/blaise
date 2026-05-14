{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uCodeGenQBE;

{ QBE IR emitter for Blaise.
  WriteLn/Write are built-ins emitted as calls to _SysWriteStr/_SysWriteInt/
  _SysWriteInt64/_SysWriteNewline (blaise_sys.pas / blaise_sys.c).
  Records are stack-allocated; field access uses pointer arithmetic. }

interface

uses
  SysUtils, StrUtils, Classes, uAST, uSymbolTable, uStrCompat;

// Raw byte copy used by TIRBuffer — maps to libc memcpy under both compilers.
// FPC: {$linklib c} ensures libc is linked; Blaise links blaise_rtl.a which
// already pulls in libc.
procedure _ir_memcpy(Dst, Src: Pointer; N: Int64); external name 'memcpy';

type
  ECodeGenError = class(Exception);

  { Growable byte buffer for QBE IR output.  Replaces TStringList + .Text:
    AppendLine writes bytes directly — no per-line string allocation.
    AppendBuffer bulk-copies another buffer in one memcpy.
    Swapping FOutput ↔ a local TIRBuffer works identically to the old
    TStringList swap pattern used by EmitFuncDef/AppendUnit/AppendProgram. }
  TIRBuffer = class
    FData:   PChar;   { heap-allocated byte array }
    FLen:    Integer; { bytes written so far }
    FCap:    Integer; { total allocated bytes }
    procedure Grow(ANeed: Integer);
    constructor Create;
    destructor  Destroy; override;
    procedure AppendLine(const ALine: string);
    procedure AppendBuffer(AOther: TIRBuffer);
    procedure Clear;
    function  Text: string;
    property  Len: Integer read FLen;
  end;

  TCodeGenQBE = class
  private
    FOutput:          TIRBuffer;
    FStrLits:         TStringList;  { index → raw value; label = $__s<index> }
    FStrLitsEmitted:  Integer;      { count of $__s<N> already written to output }
    FTempCount:       Integer;
    FLabelCount:      Integer;
    FCurrentBlock:      TBlock;      { block currently being emitted; set by EmitBlock }
    FCurrentBlockLabel: string;      { label of the current basic block; updated by EmitLine
                                       whenever a '@label' line is emitted; used by phi codegen }
    FExcFrameNext:  Integer;   { index of next pre-allocated exc frame slot to use }
    FExcDepth:      Integer;   { number of exc frames currently pushed in the try stack }
    FBreakLabels:    TStringList;  { stack of active loop-end labels; top = innermost }
    FContinueLabels: TStringList;  { stack of active loop-continue labels; top = innermost }
    FExitLabel:    string;       { label to jmp to for 'exit'; '' = main program }
    FSymTable:         TSymbolTable; { set via SetSymbolTable; used by AppendUnit for class data }
    FUnitInitNames:    TStringList;  { unit names that have initialization sections }
    { mem2reg: parallel lists tracking which locals are promoted SSA temps.
      FPromotedLocals[i] = var name; FPromotedTypes[i] = QBE type ('w','l','d','s').
      Cleared at the start of each function by EmitVarAllocs. }
    FPromotedLocals: TStringList;
    FPromotedTypes:  TStringList;

    function  AllocTemp: string;
    function  AllocLabel(const APrefix: string): string;
    function  CoerceArg(const AArgTemp: string; AArgExpr: TASTExpr; const AParamQType: string): string;
    function  EmitStrLit(const AValue: string): string;
    { Emit a class-name string literal as a data-section label expression.
      Returns '$__cn_ClassName + 12' which can be embedded in another data item. }
    function  EmitClassNameRef(const AClassName: string): string;
    procedure EmitLine(const ALine: string);
    procedure EmitPendingStrLits;
    procedure EmitDataSection;
    procedure EmitMainHeader;
    procedure EmitMainFooter;
    procedure EmitTypeInfoDefs(AProg: TProgram);
    procedure EmitVTableDefs(AProg: TProgram);
    procedure EmitMethodDefs(AProg: TProgram);
    procedure EmitInterfaceDefs(AProg: TProgram);
    function  IsAbstractClassMethod(ARec: TRecordTypeDesc;
                                    const AMethName: string): Boolean;
    procedure EmitFieldCleanupDefs(AProg: TProgram);
    procedure EmitFieldCleanupFn(const AMangledName: string;
                                 ARec: TRecordTypeDesc);
    procedure EmitMethodDef(const ATypeName: string; AMethod: TMethodDecl);
    procedure EmitStandaloneDefs(AProg: TProgram);
    procedure EmitStandaloneDef(ADecl: TMethodDecl);
    procedure EmitFuncDef(ADecl: TMethodDecl; AExported: Boolean);
    procedure EmitBlock(ABlock: TBlock);
    procedure EmitVarAllocs(ABlock: TBlock);
    { mem2reg helpers }
    { Returns True if AKind is a scalar type promotable to a QBE SSA temp. }
    function  IsPromotableKind(AKind: TTypeKind): Boolean;
    { Returns the QBE value type ('w','l','d','s') for a promotable kind. }
    function  PromotedQType(AKind: TTypeKind; AType: TTypeDesc): string;
    { Collect names of locals in ABlock whose address is taken (var-arg
      sites or @X expressions).  Result is caller-owned TStringList. }
    function  CollectAddressTaken(ABlock: TBlock): TStringList;
    { Returns True if ABlock contains any try/finally or try/except statement
      (recursively).  Promoted locals are unsafe across setjmp/longjmp. }
    function  BlockHasTry(ABlock: TBlock): Boolean;
    function  StmtHasTry(AStmt: TASTStmt): Boolean;
    { Walk a statement tree adding any address-taken local names to ASet. }
    procedure CollectAddressTakenStmt(AStmt: TASTStmt; ASet: TStringList);
    { Walk an expression adding any address-taken local names to ASet. }
    procedure CollectAddressTakenExpr(AExpr: TASTExpr; ASet: TStringList);
    { Returns True if AName is currently a promoted SSA temp. }
    function  IsPromoted(const AName: string): Boolean;
    { Returns the QBE type of a promoted local ('' if not promoted). }
    function  PromotedType(const AName: string): string;
    function  CountTryStmts(AStmt: TASTStmt): Integer;
    procedure EmitExcFrameAllocs(ABlock: TBlock);
    procedure EmitGlobalVarData(ABlock: TBlock);
    procedure EmitGlobalConstData(ABlock: TBlock);
    procedure EmitParamAllocs(AMethod: TMethodDecl; AClassType: TRecordTypeDesc);
    procedure EmitArcCleanup(ABlock: TBlock);
    procedure EmitExcPathArcCleanup(ABlock: TBlock);
    procedure EmitExcUnwind(ATargetDepth: Integer);
    procedure EmitStmt(AStmt: TASTStmt);
    procedure EmitIfStmt(AStmt: TIfStmt);
    procedure EmitWhileStmt(AStmt: TWhileStmt);
    procedure EmitRepeatStmt(AStmt: TRepeatStmt);
    procedure EmitForStmt(AStmt: TForStmt);
    procedure EmitForInStmt(AStmt: TForInStmt);
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
    { Helper for string-mutator built-ins (Delete, SetLength).
      ARtlName is the RTL function (e.g. '_StringDelete') and
      AExtraArgCount is the number of trailing Integer args after the
      string. Emits ARC-correct release-old/addref-new/store sequence. }
    procedure EmitStringMutator(ACall: TProcCall;
      const ARtlName: string; AExtraArgCount: Integer);
    procedure EmitDynArraySetLength(ACall: TProcCall);
    procedure EmitPointerWrite(AStmt: TPointerWriteStmt);
    procedure EmitStaticSubscriptAssign(AStmt: TStaticSubscriptAssign);
    procedure EmitWrite(ACall: TProcCall; ANewline: Boolean);
    function  EmitExpr(AExpr: TASTExpr): string;
    function  EmitIsExpr(AExpr: TIsExpr): string;
    function  EmitAsExpr(AExpr: TAsExpr): string;
    function  EmitSupportsExpr(AExpr: TSupportsExpr): string;
    function  EmitStringSubscriptExpr(AExpr: TStringSubscriptExpr): string;
    function  EmitAddrOfExpr(AExpr: TAddrOfExpr): string;
    function  EmitArrayLiteralExpr(AExpr: TArrayLiteralExpr): string;
    function  EmitSetLiteralExpr(AExpr: TArrayLiteralExpr): string;
    { Returns a QBE temp holding a pointer to the storage of a record or class
      instance referenced by AExpr.  Used by chained field access to traverse
      base nodes without loading record aggregates as scalars. }
    function  EmitInstancePtr(AExpr: TASTExpr): string;
    function  FieldPtr(const ARecordVar: string; AOffset: Integer; AIsGlobal: Boolean = False): string;
    { Returns the QBE address token for a variable: '$Name' for globals,
      '%_var_Name' for locals. }
    function  VarRef(const AName: string; AIsGlobal: Boolean): string;
    { Returns a QBE temp (or address token) that holds the address to pass as a
      var-param actual argument.  When the actual argument is itself a var param
      its local slot contains a pointer — emit loadl to obtain the original
      caller's address.  For plain locals/globals VarRef suffices. }
    function  EmitVarArgAddr(AIdent: TIdentExpr): string;
    { Generalised L-value address: handles TIdentExpr (delegates to
      EmitVarArgAddr), TDerefExpr (P^ — yields the pointer value as the
      address), and TFieldAccessExpr (R.F or P^.F — base address +
      field offset).  Used for var-argument passing. }
    function  EmitLValueAddr(AExpr: TASTExpr): string;
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
    { Builds the QBE symbol name for a class method call.  Uses the
      decl's pre-computed ResolvedQbeName when set (overloaded methods
      and any decl that has been through semantic mangling); falls back
      to the legacy '<Owner>_<Name>' form for callers that haven't been
      migrated.  ATypeName/AMethodName are the fallback components. }
    function  MethodEmitName(AMDecl: TMethodDecl;
      const ATypeName, AMethodName: string): string;
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

{ -----------------------------------------------------------------------
  TIRBuffer
  ----------------------------------------------------------------------- }

const
  IR_INIT_CAP = 65536;  { 64 KB initial allocation — avoids early reallocs }
  IR_NL = #10;

procedure BufCopy(Dst, Src: Pointer; N: Integer);
begin
  _ir_memcpy(Dst, Src, N);
end;

constructor TIRBuffer.Create;
begin
  inherited Create;
  FCap  := IR_INIT_CAP;
  FLen  := 0;
  FData := GetMem(FCap);
end;

destructor TIRBuffer.Destroy;
begin
  FreeMem(FData);
  inherited Destroy;
end;

procedure TIRBuffer.Grow(ANeed: Integer);
var
  NewCap: Integer;
  NewData: PChar;
begin
  NewCap := FCap;
  while NewCap < FLen + ANeed do
    NewCap := NewCap * 2;
  NewData := GetMem(NewCap);
  if FLen > 0 then
    BufCopy(NewData, FData, FLen);
  FreeMem(FData);
  FData := NewData;
  FCap  := NewCap;
end;

procedure TIRBuffer.AppendLine(const ALine: string);
var
  SLen: Integer;
  NL:   string;
begin
  SLen := Length(ALine);
  if FLen + SLen + 1 > FCap then
    Grow(SLen + 1);
  if SLen > 0 then
  begin
    BufCopy(FData + FLen, PChar(ALine), SLen);
    FLen := FLen + SLen;
  end;
  NL := IR_NL;
  BufCopy(FData + FLen, PChar(NL), 1);
  FLen := FLen + 1;
end;

procedure TIRBuffer.AppendBuffer(AOther: TIRBuffer);
begin
  if AOther.FLen = 0 then Exit;
  if FLen + AOther.FLen > FCap then
    Grow(AOther.FLen);
  BufCopy(FData + FLen, AOther.FData, AOther.FLen);
  FLen := FLen + AOther.FLen;
end;

procedure TIRBuffer.Clear;
begin
  FLen := 0;
end;

function TIRBuffer.Text: string;
begin
  SetLength(Result, FLen);
  if FLen > 0 then
    BufCopy(PChar(Result), FData, FLen);
end;

constructor TCodeGenQBE.Create;
begin
  inherited Create;
  FOutput          := TIRBuffer.Create;
  FStrLits         := TStringList.Create;
  FStrLits.CaseSensitive := True;
  FBreakLabels     := TStringList.Create;
  FContinueLabels  := TStringList.Create;
  FUnitInitNames   := TStringList.Create;
  FPromotedLocals  := TStringList.Create;
  FPromotedLocals.CaseSensitive := True;
  FPromotedTypes   := TStringList.Create;
  FTempCount       := 0;
  FStrLitsEmitted  := 0;
end;

destructor TCodeGenQBE.Destroy;
begin
  FBreakLabels.Free;
  FContinueLabels.Free;
  FUnitInitNames.Free;
  FPromotedLocals.Free;
  FPromotedTypes.Free;
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
  ArgQ:    string;
  ArgT:    TTypeDesc;
begin
  Result := AArgTemp;
  if (AArgExpr = nil) or (AArgExpr.ResolvedType = nil) then Exit;
  ArgT := AArgExpr.ResolvedType;
  ArgQ := QbeTypeOf(ArgT);
  if ArgQ = AParamQType then Exit;
  { Integer widening: w → l. }
  if (AParamQType = 'l') and (ArgQ = 'w') then
  begin
    ExtTemp := AllocTemp;
    EmitLine(Format('  %s =l extsw %s', [ExtTemp, AArgTemp]));
    Result := ExtTemp;
    Exit;
  end;
  { Integer/Single → Double. }
  if AParamQType = 'd' then
  begin
    ExtTemp := AllocTemp;
    if ArgQ = 'w' then
      EmitLine(Format('  %s =d swtof %s', [ExtTemp, AArgTemp]))
    else if ArgQ = 'l' then
      EmitLine(Format('  %s =d sltof %s', [ExtTemp, AArgTemp]))
    else if ArgQ = 's' then
      EmitLine(Format('  %s =d exts %s', [ExtTemp, AArgTemp]))
    else
      Exit;  { unsupported conversion — leave as-is; QBE will reject if invalid }
    Result := ExtTemp;
    Exit;
  end;
  { Integer → Single. }
  if AParamQType = 's' then
  begin
    ExtTemp := AllocTemp;
    if ArgQ = 'w' then
      EmitLine(Format('  %s =s swtof %s', [ExtTemp, AArgTemp]))
    else if ArgQ = 'l' then
      EmitLine(Format('  %s =s sltof %s', [ExtTemp, AArgTemp]))
    else
      Exit;
    Result := ExtTemp;
  end;
end;

function TCodeGenQBE.EmitStrLit(const AValue: string): string;
var
  Idx: Integer;
  T:   string;
begin
  Idx := FStrLits.IndexOf(AValue);
  if Idx < 0 then
    Idx := FStrLits.Add(AValue);
  { Data-pointer convention: $__s<N> labels the 12-byte header.
    Add 12 to get the data pointer that string variable slots hold. }
  T := AllocTemp;
  EmitLine(Format('  %s =l add $__s%d, 12', [T, Idx]));
  Result := T;
end;

function TCodeGenQBE.EmitClassNameRef(const AClassName: string): string;
{ Emit a dedicated immortal string data item for the class name and return
  a QBE data-section expression '$__cn_Name + 12' that resolves to the
  Blaise string data pointer.  QBE supports label+offset relocations in the
  data section so this can be inlined into another data item. }
var
  Mangled: string;
begin
  Mangled := QBEMangle(AClassName);
  { immortal ARC string: refcnt=-1, length, capacity, data, NUL }
  EmitLine(Format('data $__cn_%s = { w -1, w %d, w %d, b "%s", b 0 }',
    [Mangled, Length(AClassName), Length(AClassName), AClassName]));
  Result := '$__cn_' + Mangled + ' + 12';
end;

procedure TCodeGenQBE.EmitLine(const ALine: string);
begin
  FOutput.AppendLine(ALine);
  { Track the current basic block label — needed by short-circuit phi codegen
    to record which predecessor block each incoming value comes from. }
  if (Length(ALine) > 0) and (StrAt(ALine, 0) = Ord('@')) then
    FCurrentBlockLabel := StrCopyTail(ALine, 1);
end;

procedure TCodeGenQBE.EmitPendingStrLits;
var
  I:      Integer;
  StrLen: Integer;
begin
  { Emit only the string literals not yet written.  Each literal carries a
    12-byte ARC header: refcnt=-1 (immortal), length, capacity.
    $__s<N> labels the header; EmitStrLit emits 'add $__s<N>, 12' to produce
    the data pointer stored in string variable slots. }
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
  EmitLine('');
end;

procedure TCodeGenQBE.EmitMainHeader;
var
  I: Integer;
begin
  EmitLine('export function w $main(w %argc, l %argv) {');
  EmitLine('@start');
  EmitLine('  call $_SetArgs(w %argc, l %argv)');
  { Call initialization sections of imported units in order }
  for I := 0 to FUnitInitNames.Count - 1 do
    EmitLine('  call $' + FUnitInitNames.Strings[I] + '_init()');
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
    tyProcedural:                           Result := 'l';  { function code pointer }
    tyDouble:                               Result := 'd';  { 64-bit float }
    tySingle:                               Result := 's';  { 32-bit float }
    tyMetaClass:                            Result := 'l';  { typeinfo pointer }
    tyDynArray:                             Result := 'l';  { heap data pointer }
  else
    Result := 'w';
  end;
end;


function TCodeGenQBE.CountTryStmts(AStmt: TASTStmt): Integer;
var
  I, J: Integer;
  Cmp:  TCompoundStmt;
  IfS:  TIfStmt;
  WhS:  TWhileStmt;
  ForS: TForStmt;
  FiS:  TForInStmt;
  RepS: TRepeatStmt;
  TFS:  TTryFinallyStmt;
  TES:  TTryExceptStmt;
  CsS:  TCaseStmt;
  Br:   TCaseBranch;
  H:    TExceptHandlerClause;
begin
  Result := 0;
  if AStmt = nil then Exit;
  if AStmt is TTryFinallyStmt then
  begin
    TFS := TTryFinallyStmt(AStmt);
    Result := 1;
    for I := 0 to TFS.TryBody.Stmts.Count - 1 do
      Result := Result + CountTryStmts(TASTStmt(TFS.TryBody.Stmts.Items[I]));
    for I := 0 to TFS.FinallyBody.Stmts.Count - 1 do
      Result := Result + CountTryStmts(TASTStmt(TFS.FinallyBody.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TTryExceptStmt then
  begin
    TES := TTryExceptStmt(AStmt);
    Result := 1;
    for I := 0 to TES.TryBody.Stmts.Count - 1 do
      Result := Result + CountTryStmts(TASTStmt(TES.TryBody.Stmts.Items[I]));
    for I := 0 to TES.Handlers.Count - 1 do
    begin
      H := TExceptHandlerClause(TES.Handlers.Items[I]);
      Result := Result + CountTryStmts(H.Body);
    end;
    if TES.ElseBody <> nil then
      for I := 0 to TES.ElseBody.Stmts.Count - 1 do
        Result := Result + CountTryStmts(TASTStmt(TES.ElseBody.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TCompoundStmt then
  begin
    Cmp := TCompoundStmt(AStmt);
    for I := 0 to Cmp.Stmts.Count - 1 do
      Result := Result + CountTryStmts(TASTStmt(Cmp.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TIfStmt then
  begin
    IfS := TIfStmt(AStmt);
    Result := CountTryStmts(IfS.ThenStmt) + CountTryStmts(IfS.ElseStmt);
    Exit;
  end;
  if AStmt is TWhileStmt then
  begin
    WhS := TWhileStmt(AStmt);
    Result := CountTryStmts(WhS.Body);
    Exit;
  end;
  if AStmt is TForStmt then
  begin
    ForS := TForStmt(AStmt);
    Result := CountTryStmts(ForS.Body);
    Exit;
  end;
  if AStmt is TForInStmt then
  begin
    FiS := TForInStmt(AStmt);
    Result := CountTryStmts(FiS.Body);
    Exit;
  end;
  if AStmt is TRepeatStmt then
  begin
    RepS := TRepeatStmt(AStmt);
    for I := 0 to RepS.Body.Stmts.Count - 1 do
      Result := Result + CountTryStmts(TASTStmt(RepS.Body.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TCaseStmt then
  begin
    CsS := TCaseStmt(AStmt);
    for I := 0 to CsS.Branches.Count - 1 do
    begin
      Br := TCaseBranch(CsS.Branches.Items[I]);
      Result := Result + CountTryStmts(Br.Stmt);
    end;
    Result := Result + CountTryStmts(CsS.ElseStmt);
    Exit;
  end;
end;

{ Pre-allocate exception frame slots at @start so that try/finally and
  try/except blocks (including those inside loops) use static stack slots
  rather than dynamic sub-%rsp allocations.  Dynamic alloc16 512 in loop
  bodies grows the stack by 512 bytes per iteration and eventually
  corrupts parent exception frame prev-pointers. }
procedure TCodeGenQBE.EmitExcFrameAllocs(ABlock: TBlock);
var
  I, Total: Integer;
begin
  Total := 0;
  for I := 0 to ABlock.Stmts.Count - 1 do
    Total := Total + CountTryStmts(TASTStmt(ABlock.Stmts.Items[I]));
  FExcFrameNext := 0;
  FExcDepth := 0;
  for I := 0 to Total - 1 do
    EmitLine(Format('  %%_exc_frame_%d =l alloc16 512', [I]));
end;

{ -----------------------------------------------------------------------
  mem2reg helpers
  ----------------------------------------------------------------------- }

function TCodeGenQBE.IsPromotableKind(AKind: TTypeKind): Boolean;
begin
  { Only promote pure scalar types that are never used as receivers for
    method calls or ARC operations that load the slot address.
    tyClass, tyString, tyPointer, tyPChar, tyMetaClass are excluded because
    many codegen paths emit 'loadl %_var_X' to get the heap pointer from the
    local slot — those paths are not all promotion-aware yet. }
  Result := AKind in [
    tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum,
    tyInt64,
    tyDouble, tySingle,
    tySet
  ];
end;

function TCodeGenQBE.PromotedQType(AKind: TTypeKind; AType: TTypeDesc): string;
begin
  case AKind of
    tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum: Result := 'w';
    tyInt64, tyString, tyClass, tyPointer, tyPChar, tyMetaClass: Result := 'l';
    tyDouble: Result := 'd';
    tySingle: Result := 's';
    tySet:
      if TSetTypeDesc(AType).BitCount <= 32 then Result := 'w'
      else Result := 'l';
  else
    Result := 'l';
  end;
end;

function TCodeGenQBE.IsPromoted(const AName: string): Boolean;
begin
  Result := FPromotedLocals.IndexOf(AName) >= 0;
end;

function TCodeGenQBE.PromotedType(const AName: string): string;
var
  Idx: Integer;
begin
  Idx := FPromotedLocals.IndexOf(AName);
  if Idx >= 0 then
    Result := FPromotedTypes.Strings[Idx]
  else
    Result := '';
end;

procedure TCodeGenQBE.CollectAddressTakenExpr(AExpr: TASTExpr; ASet: TStringList);
var
  I: Integer;
  FC: TFuncCallExpr;
  MC: TMethodCallExpr;
  FA: TFieldAccessExpr;
  Param: TMethodParam;
  Arg: TASTExpr;
begin
  if AExpr = nil then Exit;

  { @X — explicit address-of }
  if AExpr is TAddrOfExpr then
  begin
    if TAddrOfExpr(AExpr).Expr is TIdentExpr then
      ASet.Add(TIdentExpr(TAddrOfExpr(AExpr).Expr).Name);
    CollectAddressTakenExpr(TAddrOfExpr(AExpr).Expr, ASet);
    Exit;
  end;

  { Function call: var params take the address of their actual argument }
  if AExpr is TFuncCallExpr then
  begin
    FC := TFuncCallExpr(AExpr);
    if FC.ResolvedDecl <> nil then
    begin
      for I := 0 to FC.Args.Count - 1 do
      begin
        Arg := TASTExpr(FC.Args.Items[I]);
        if I < TMethodDecl(FC.ResolvedDecl).Params.Count then
        begin
          Param := TMethodParam(TMethodDecl(FC.ResolvedDecl).Params.Items[I]);
          if Param.IsVarParam and (Arg is TIdentExpr) and not TIdentExpr(Arg).IsGlobal then
            ASet.Add(TIdentExpr(Arg).Name);
        end;
        CollectAddressTakenExpr(Arg, ASet);
      end;
    end
    else
      for I := 0 to FC.Args.Count - 1 do
        CollectAddressTakenExpr(TASTExpr(FC.Args.Items[I]), ASet);
    Exit;
  end;

  { Method call: same var-param check }
  if AExpr is TMethodCallExpr then
  begin
    MC := TMethodCallExpr(AExpr);
    CollectAddressTakenExpr(MC.ObjExpr, ASet);
    if MC.ResolvedMethod <> nil then
    begin
      for I := 0 to MC.Args.Count - 1 do
      begin
        Arg := TASTExpr(MC.Args.Items[I]);
        if I < TMethodDecl(MC.ResolvedMethod).Params.Count then
        begin
          Param := TMethodParam(TMethodDecl(MC.ResolvedMethod).Params.Items[I]);
          if Param.IsVarParam and (Arg is TIdentExpr) and not TIdentExpr(Arg).IsGlobal then
            ASet.Add(TIdentExpr(Arg).Name);
        end;
        CollectAddressTakenExpr(Arg, ASet);
      end;
    end
    else
      for I := 0 to MC.Args.Count - 1 do
        CollectAddressTakenExpr(TASTExpr(MC.Args.Items[I]), ASet);
    Exit;
  end;

  { Recurse into common composite expressions }
  if AExpr is TBinaryExpr then
  begin
    CollectAddressTakenExpr(TBinaryExpr(AExpr).Left, ASet);
    CollectAddressTakenExpr(TBinaryExpr(AExpr).Right, ASet);
  end
  else if AExpr is TNotExpr then
    CollectAddressTakenExpr(TNotExpr(AExpr).Expr, ASet)
  else if AExpr is TFieldAccessExpr then
  begin
    FA := TFieldAccessExpr(AExpr);
    CollectAddressTakenExpr(FA.Base, ASet);
    if FA.PropIndexExpr <> nil then
      CollectAddressTakenExpr(FA.PropIndexExpr, ASet);
  end
  else if AExpr is TDerefExpr then
    CollectAddressTakenExpr(TDerefExpr(AExpr).Expr, ASet)
  else if AExpr is TStringSubscriptExpr then
  begin
    CollectAddressTakenExpr(TStringSubscriptExpr(AExpr).StrExpr, ASet);
    CollectAddressTakenExpr(TStringSubscriptExpr(AExpr).IndexExpr, ASet);
  end
  else if AExpr is TIsExpr then
    CollectAddressTakenExpr(TIsExpr(AExpr).Obj, ASet)
  else if AExpr is TAsExpr then
    CollectAddressTakenExpr(TAsExpr(AExpr).Obj, ASet)
  else if AExpr is TSupportsExpr then
    CollectAddressTakenExpr(TSupportsExpr(AExpr).Obj, ASet)
  else if AExpr is TArrayLiteralExpr then
    for I := 0 to TArrayLiteralExpr(AExpr).Elements.Count - 1 do
      CollectAddressTakenExpr(TASTExpr(TArrayLiteralExpr(AExpr).Elements.Items[I]), ASet);
end;

procedure TCodeGenQBE.CollectAddressTakenStmt(AStmt: TASTStmt; ASet: TStringList);
var
  I:      Integer;
  TryE:   TTryExceptStmt;
  TryF:   TTryFinallyStmt;
  RaiseS: TRaiseStmt;
  CaseS:  TCaseStmt;
  PWrite: TPointerWriteStmt;
  SSubA:  TStaticSubscriptAssign;
  PCall:  TProcCall;
  MCall:  TMethodCallStmt;
  ICall:  TInheritedCallStmt;
  ForS:   TForStmt;
begin
  if AStmt = nil then Exit;

  if AStmt is TCompoundStmt then
  begin
    for I := 0 to TCompoundStmt(AStmt).Stmts.Count - 1 do
      CollectAddressTakenStmt(TASTStmt(TCompoundStmt(AStmt).Stmts.Items[I]), ASet);
  end
  else if AStmt is TIfStmt then
  begin
    CollectAddressTakenExpr(TIfStmt(AStmt).Condition, ASet);
    CollectAddressTakenStmt(TIfStmt(AStmt).ThenStmt, ASet);
    CollectAddressTakenStmt(TIfStmt(AStmt).ElseStmt, ASet);
  end
  else if AStmt is TWhileStmt then
  begin
    CollectAddressTakenExpr(TWhileStmt(AStmt).Condition, ASet);
    CollectAddressTakenStmt(TWhileStmt(AStmt).Body, ASet);
  end
  else if AStmt is TRepeatStmt then
  begin
    CollectAddressTakenExpr(TRepeatStmt(AStmt).Condition, ASet);
    CollectAddressTakenStmt(TRepeatStmt(AStmt).Body, ASet);
  end
  else if AStmt is TForStmt then
  begin
    ForS := TForStmt(AStmt);
    CollectAddressTakenExpr(ForS.StartExpr, ASet);
    CollectAddressTakenExpr(ForS.EndExpr, ASet);
    CollectAddressTakenStmt(ForS.Body, ASet);
  end
  else if AStmt is TForInStmt then
  begin
    CollectAddressTakenExpr(TForInStmt(AStmt).CollExpr, ASet);
    CollectAddressTakenStmt(TForInStmt(AStmt).Body, ASet);
  end
  else if AStmt is TAssignment then
    CollectAddressTakenExpr(TAssignment(AStmt).Expr, ASet)
  else if AStmt is TFieldAssignment then
    CollectAddressTakenExpr(TFieldAssignment(AStmt).Expr, ASet)
  else if AStmt is TMethodCallStmt then
  begin
    MCall := TMethodCallStmt(AStmt);
    CollectAddressTakenExpr(MCall.ObjExpr, ASet);
    if MCall.ResolvedMethod <> nil then
      for I := 0 to MCall.Args.Count - 1 do
      begin
        if I < TMethodDecl(MCall.ResolvedMethod).Params.Count then
          if TMethodParam(TMethodDecl(MCall.ResolvedMethod).Params.Items[I]).IsVarParam and
             (TASTExpr(MCall.Args.Items[I]) is TIdentExpr) and
             not TIdentExpr(TASTExpr(MCall.Args.Items[I])).IsGlobal then
            ASet.Add(TIdentExpr(TASTExpr(MCall.Args.Items[I])).Name);
        CollectAddressTakenExpr(TASTExpr(MCall.Args.Items[I]), ASet);
      end
    else
      for I := 0 to MCall.Args.Count - 1 do
        CollectAddressTakenExpr(TASTExpr(MCall.Args.Items[I]), ASet);
  end
  else if AStmt is TProcCall then
  begin
    PCall := TProcCall(AStmt);
    if PCall.ResolvedDecl <> nil then
      for I := 0 to PCall.Args.Count - 1 do
      begin
        if I < TMethodDecl(PCall.ResolvedDecl).Params.Count then
          if TMethodParam(TMethodDecl(PCall.ResolvedDecl).Params.Items[I]).IsVarParam and
             (TASTExpr(PCall.Args.Items[I]) is TIdentExpr) and
             not TIdentExpr(TASTExpr(PCall.Args.Items[I])).IsGlobal then
            ASet.Add(TIdentExpr(TASTExpr(PCall.Args.Items[I])).Name);
        CollectAddressTakenExpr(TASTExpr(PCall.Args.Items[I]), ASet);
      end
    else
      for I := 0 to PCall.Args.Count - 1 do
        CollectAddressTakenExpr(TASTExpr(PCall.Args.Items[I]), ASet);
  end
  else if AStmt is TInheritedCallStmt then
  begin
    ICall := TInheritedCallStmt(AStmt);
    if ICall.ResolvedMethod <> nil then
      for I := 0 to ICall.Args.Count - 1 do
      begin
        if I < TMethodDecl(ICall.ResolvedMethod).Params.Count then
          if TMethodParam(TMethodDecl(ICall.ResolvedMethod).Params.Items[I]).IsVarParam and
             (TASTExpr(ICall.Args.Items[I]) is TIdentExpr) and
             not TIdentExpr(TASTExpr(ICall.Args.Items[I])).IsGlobal then
            ASet.Add(TIdentExpr(TASTExpr(ICall.Args.Items[I])).Name);
        CollectAddressTakenExpr(TASTExpr(ICall.Args.Items[I]), ASet);
      end
    else
      for I := 0 to ICall.Args.Count - 1 do
        CollectAddressTakenExpr(TASTExpr(ICall.Args.Items[I]), ASet);
  end
  else if AStmt is TTryFinallyStmt then
  begin
    TryF := TTryFinallyStmt(AStmt);
    CollectAddressTakenStmt(TryF.TryBody, ASet);
    CollectAddressTakenStmt(TryF.FinallyBody, ASet);
  end
  else if AStmt is TTryExceptStmt then
  begin
    TryE := TTryExceptStmt(AStmt);
    CollectAddressTakenStmt(TryE.TryBody, ASet);
    for I := 0 to TryE.Handlers.Count - 1 do
      CollectAddressTakenStmt(TExceptHandlerClause(TryE.Handlers.Items[I]).Body, ASet);
    CollectAddressTakenStmt(TryE.ElseBody, ASet);
    CollectAddressTakenStmt(TryE.ExceptBody, ASet);
  end
  else if AStmt is TRaiseStmt then
  begin
    RaiseS := TRaiseStmt(AStmt);
    CollectAddressTakenExpr(RaiseS.Expr, ASet);
  end
  else if AStmt is TCaseStmt then
  begin
    CaseS := TCaseStmt(AStmt);
    CollectAddressTakenExpr(CaseS.Selector, ASet);
    for I := 0 to CaseS.Branches.Count - 1 do
      CollectAddressTakenStmt(TCaseBranch(CaseS.Branches.Items[I]).Stmt, ASet);
    CollectAddressTakenStmt(CaseS.ElseStmt, ASet);
  end
  else if AStmt is TPointerWriteStmt then
  begin
    PWrite := TPointerWriteStmt(AStmt);
    CollectAddressTakenExpr(PWrite.PtrExpr, ASet);
    CollectAddressTakenExpr(PWrite.ValExpr, ASet);
  end
  else if AStmt is TStaticSubscriptAssign then
  begin
    SSubA := TStaticSubscriptAssign(AStmt);
    CollectAddressTakenExpr(SSubA.IndexExpr, ASet);
    CollectAddressTakenExpr(SSubA.ValueExpr, ASet);
  end;
  { TExitStmt, TBreakStmt, TContinueStmt — no expressions to walk }
end;

function TCodeGenQBE.StmtHasTry(AStmt: TASTStmt): Boolean;
var
  I: Integer;
begin
  Result := False;
  if AStmt = nil then Exit;
  if (AStmt is TTryFinallyStmt) or (AStmt is TTryExceptStmt) then
  begin
    Result := True;
    Exit;
  end;
  if AStmt is TCompoundStmt then
    for I := 0 to TCompoundStmt(AStmt).Stmts.Count - 1 do
      if StmtHasTry(TASTStmt(TCompoundStmt(AStmt).Stmts.Items[I])) then
      begin
        Result := True;
        Exit;
      end;
  if AStmt is TIfStmt then
  begin
    if StmtHasTry(TIfStmt(AStmt).ThenStmt) or StmtHasTry(TIfStmt(AStmt).ElseStmt) then
    begin
      Result := True;
      Exit;
    end;
  end;
  if AStmt is TWhileStmt then
    Result := StmtHasTry(TWhileStmt(AStmt).Body)
  else if AStmt is TRepeatStmt then
    Result := StmtHasTry(TRepeatStmt(AStmt).Body)
  else if AStmt is TForStmt then
    Result := StmtHasTry(TForStmt(AStmt).Body)
  else if AStmt is TForInStmt then
    Result := StmtHasTry(TForInStmt(AStmt).Body)
  else if AStmt is TCaseStmt then
    for I := 0 to TCaseStmt(AStmt).Branches.Count - 1 do
      if StmtHasTry(TCaseBranch(TCaseStmt(AStmt).Branches.Items[I]).Stmt) then
      begin
        Result := True;
        Exit;
      end;
end;

function TCodeGenQBE.BlockHasTry(ABlock: TBlock): Boolean;
var
  I: Integer;
begin
  Result := False;
  if ABlock = nil then Exit;
  for I := 0 to ABlock.Stmts.Count - 1 do
    if StmtHasTry(TASTStmt(ABlock.Stmts.Items[I])) then
    begin
      Result := True;
      Exit;
    end;
end;

function TCodeGenQBE.CollectAddressTaken(ABlock: TBlock): TStringList;
var
  I: Integer;
begin
  Result := TStringList.Create;
  Result.CaseSensitive := True;
  Result.Duplicates    := dupIgnore;
  Result.Sorted        := True;
  if ABlock = nil then Exit;
  for I := 0 to ABlock.Stmts.Count - 1 do
    CollectAddressTakenStmt(TASTStmt(ABlock.Stmts.Items[I]), Result);
end;

procedure TCodeGenQBE.EmitVarAllocs(ABlock: TBlock);
var
  I, J:        Integer;
  Decl:        TVarDecl;
  VarName:     string;
  RT:          TRecordTypeDesc;
  RecSize:     Integer;
  RecAlign:    Integer;
  SAT:         TStaticArrayTypeDesc;
  ArrSize:     Integer;
  ArrAlign:    Integer;
  AddrTaken:   TStringList;
  QT:          string;
  IsMethodPtr: Boolean;
begin
  { mem2reg pre-pass: find which locals have their address taken so we
    know which ones must remain as stack slots.
    Also skip promotion entirely when the block contains try/except or
    try/finally — promoted SSA temps live in registers and don't survive
    the setjmp/longjmp used by the exception frame. }
  FPromotedLocals.Clear;
  FPromotedTypes.Clear;
  if not BlockHasTry(ABlock) then
  begin
    AddrTaken := CollectAddressTaken(ABlock);
    try
      for I := 0 to ABlock.Decls.Count - 1 do
      begin
        Decl := TVarDecl(ABlock.Decls.Items[I]);
        if Decl.ResolvedType = nil then Continue;
        if Decl.IsGlobal then Continue;
        for J := 0 to Decl.Names.Count - 1 do
        begin
          VarName := Decl.Names.Strings[J];
          if IsPromotableKind(Decl.ResolvedType.Kind) and
             (AddrTaken.IndexOf(VarName) < 0) then
          begin
            { tyProcedural method-pointers are two-slot aggregates — not promotable }
            IsMethodPtr := (Decl.ResolvedType.Kind = tyProcedural) and
                           TProceduralTypeDesc(Decl.ResolvedType).IsMethodPtr;
            if not IsMethodPtr then
            begin
              FPromotedLocals.Add(VarName);
              FPromotedTypes.Add(PromotedQType(Decl.ResolvedType.Kind, Decl.ResolvedType));
            end;
          end;
        end;
      end;
    finally
      AddrTaken.Free;
    end;
  end;

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

      { Promoted locals: emit a zero initialisation as a direct copy into
        the temp.  QBE re-uses the same name across assignments (non-SSA
        mode — QBE inserts phi nodes itself). }
      if IsPromoted(VarName) then
      begin
        QT := PromotedType(VarName);
        case QT of
          'w': EmitLine(Format('  %%_var_%s =w copy 0', [VarName]));
          'l': EmitLine(Format('  %%_var_%s =l copy 0', [VarName]));
          'd': EmitLine(Format('  %%_var_%s =d copy d_0', [VarName]));
          's': EmitLine(Format('  %%_var_%s =s copy s_0', [VarName]));
        end;
        Continue;
      end;

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
            if RecSize > 0 then
              EmitLine(Format('  call $memset(l %%_var_%s, w 0, l %d)',
                [VarName, RecSize]));
          end;

        tyClass:
          begin
            EmitLine(Format('  %%_var_%s =l alloc8 1', [VarName]));
            EmitLine(Format('  storel 0, %%_var_%s', [VarName]));
          end;

        tyPointer, tyProcedural, tyMetaClass:
          begin
            if (Decl.ResolvedType.Kind = tyProcedural) and
               TProceduralTypeDesc(Decl.ResolvedType).IsMethodPtr then
            begin
              EmitLine(Format('  %%_var_%s =l alloc8 16', [VarName]));
              EmitLine(Format('  call $memset(l %%_var_%s, w 0, l 16)', [VarName]));
            end
            else
            begin
              EmitLine(Format('  %%_var_%s =l alloc8 1', [VarName]));
              EmitLine(Format('  storel 0, %%_var_%s', [VarName]));
            end;
          end;

        tyPChar:
          begin
            EmitLine(Format('  %%_var_%s =l alloc8 1', [VarName]));
            EmitLine(Format('  storel 0, %%_var_%s', [VarName]));
          end;

        tyDouble:
          begin
            EmitLine(Format('  %%_var_%s =l alloc8 1', [VarName]));
            EmitLine(Format('  stored d_0, %%_var_%s', [VarName]));
          end;

        tySingle:
          begin
            EmitLine(Format('  %%_var_%s =l alloc4 1', [VarName]));
            EmitLine(Format('  stores s_0, %%_var_%s', [VarName]));
          end;

        tySet:
          begin
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

        tyDynArray:
          begin
            { Dynamic array variable is a pointer slot (nil = empty). }
            EmitLine(Format('  %%_var_%s =l alloc8 8', [VarName]));
            EmitLine(Format('  storel 0, %%_var_%s', [VarName]));
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
          EmitLine(Format('export data $%s = { w 0 }', [VarName]));
        tySet:
          if TSetTypeDesc(Decl.ResolvedType).BitCount <= 32 then
            EmitLine(Format('export data $%s = { w 0 }', [VarName]))
          else
            EmitLine(Format('export data $%s = { l 0 }', [VarName]));
        tyInt64:
          EmitLine(Format('export data $%s = { l 0 }', [VarName]));
        tyString, tyClass, tyPointer, tyMetaClass:
          EmitLine(Format('export data $%s = { l 0 }', [VarName]));
        tyProcedural:
          if TProceduralTypeDesc(Decl.ResolvedType).IsMethodPtr then
            { Method-pointer global: 16-byte zero block (Code at +0, Data at +8). }
            EmitLine(Format('export data $%s = { z 16 }', [VarName]))
          else
            EmitLine(Format('export data $%s = { l 0 }', [VarName]));
        tyDouble:
          EmitLine(Format('export data $%s = { d 0 }', [VarName]));
        tySingle:
          EmitLine(Format('export data $%s = { s 0 }', [VarName]));
        tyInterface:
          begin
            EmitLine(Format('export data $%s_obj  = { l 0 }', [VarName]));
            EmitLine(Format('export data $%s_itab = { l 0 }', [VarName]));
          end;
        tyRecord:
          begin
            RT := TRecordTypeDesc(Decl.ResolvedType);
            if RT.TotalSize > 0 then
              EmitLine(Format('export data $%s = { z %d }', [VarName, RT.TotalSize]))
            else
              EmitLine(Format('export data $%s = { l 0 }', [VarName]));
          end;
        tyStaticArray:
          begin
            if TStaticArrayTypeDesc(Decl.ResolvedType).ByteSize > 0 then
              EmitLine(Format('export data $%s = { z %d }',
                [VarName, TStaticArrayTypeDesc(Decl.ResolvedType).ByteSize]))
            else
              EmitLine(Format('export data $%s = { l 0 }', [VarName]));
          end;
      else
        EmitLine(Format('export data $%s = { l 0 }', [VarName]));
      end;
    end;
  end;
end;

procedure TCodeGenQBE.EmitGlobalConstData(ABlock: TBlock);
{ Emit QBE data-section entries for array-typed constants.
  Each array const is emitted as a labelled data object whose elements are
  either pointer-sized string references ($__sN + 12) or word-sized integers.
  String literals are pre-registered in FStrLits so EmitPendingStrLits writes
  their headers before the referencing data object. }
var
  I, J:       Integer;
  CD:         TConstDecl;
  ElemVal:    string;
  Parts:      string;
  StrIdx:     Integer;
  IsStrArray: Boolean;
begin
  for I := 0 to ABlock.ConstDecls.Count - 1 do
  begin
    CD := TConstDecl(ABlock.ConstDecls.Items[I]);
    if not CD.IsArrayConst then Continue;
    if (CD.ArrayElements = nil) or (CD.ArrayElements.Count = 0) then Continue;
    IsStrArray := SameText(CD.ArrayElemType, 'string');
    { Pre-register string literals so their data labels exist before the array }
    if IsStrArray then
    begin
      for J := 0 to CD.ArrayElements.Count - 1 do
        if FStrLits.IndexOf(CD.ArrayElements[J]) < 0 then
          FStrLits.Add(CD.ArrayElements[J]);
      EmitPendingStrLits;
    end;
    { Build the data initialiser }
    Parts := '';
    for J := 0 to CD.ArrayElements.Count - 1 do
    begin
      ElemVal := CD.ArrayElements[J];
      if J > 0 then Parts := Parts + ', ';
      if IsStrArray then
      begin
        StrIdx := FStrLits.IndexOf(ElemVal);
        Parts := Parts + Format('l $__s%d + 12', [StrIdx]);
      end
      else
        Parts := Parts + Format('w %s', [ElemVal]);
    end;
    EmitLine(Format('export data $%s = { %s }', [CD.Name, Parts]));
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
      else if not Decl.IsGlobal and IsPromoted(VarName) then
        EmitLine(Format('  %s =l copy %%_var_%s', [ValTemp, VarName]))
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
  EmitExcFrameAllocs(ABlock);
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

procedure TCodeGenQBE.EmitExcUnwind(ATargetDepth: Integer);
var
  I: Integer;
begin
  for I := FExcDepth downto ATargetDepth + 1 do
    EmitLine('  call $_PopExcFrame()');
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
  else if AStmt is TForInStmt then
    EmitForInStmt(TForInStmt(AStmt))
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
    EmitExcUnwind(0);
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
    EmitExcUnwind(PtrUInt(FBreakLabels.Objects[FBreakLabels.Count - 1]));
    EmitLine(Format('  jmp @%s',
      [FBreakLabels.Strings[FBreakLabels.Count - 1]]));
    DeadLbl := AllocLabel('after_break');
    EmitLine('@' + DeadLbl);
  end
  else if AStmt is TContinueStmt then
  begin
    if FContinueLabels.Count = 0 then
      raise ECodeGenError.Create('continue outside loop');
    EmitExcUnwind(PtrUInt(FContinueLabels.Objects[FContinueLabels.Count - 1]));
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

  { Use a pre-allocated exception frame slot from @start (see EmitExcFrameAllocs).
    Pre-allocation ensures the frame lives in the function's static stack frame
    rather than being allocated dynamically on every execution of this block.
    Dynamic alloc16 inside loops would grow the stack by 512 bytes per iteration
    and eventually corrupt parent exception frame prev-pointers. }
  FrameTemp := Format('%%_exc_frame_%d', [FExcFrameNext]);
  FExcFrameNext := FExcFrameNext + 1;
  EmitLine(Format('  call $_PushExcFrame(l %s)', [FrameTemp]));
  Inc(FExcDepth);

  SjrTemp := AllocTemp;
  EmitLine(Format('  %s =w call $setjmp(l %s)', [SjrTemp, FrameTemp]));
  EmitLine(Format('  jnz %s, @%s, @%s', [SjrTemp, LblFinExc, LblTry]));

  { Normal path: run try body, pop frame, run finally body }
  EmitLine('@' + LblTry);
  for I := 0 to AStmt.TryBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.TryBody.Stmts.Items[I]));
  EmitLine('  call $_PopExcFrame()');
  Dec(FExcDepth);
  for I := 0 to AStmt.FinallyBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.FinallyBody.Stmts.Items[I]));
  EmitLine(Format('  jmp @%s', [LblEnd]));

  { Exception path: capture exception, pop frame, run finally body, release
    in-scope ARC vars (prevent leaks on unwind), then re-raise }
  EmitLine('@' + LblFinExc);
  ExcTemp := AllocTemp;
  EmitLine(Format('  %s =l call $_CurrentException()', [ExcTemp]));
  EmitLine('  call $_PopExcFrame()');
  Dec(FExcDepth);
  for I := 0 to AStmt.FinallyBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.FinallyBody.Stmts.Items[I]));
  EmitExcPathArcCleanup(FCurrentBlock);
  EmitLine(Format('  call $_Reraise(l %s)', [ExcTemp]));
  EmitLine(Format('  jmp @%s', [LblEnd]));  { unreachable — satisfies QBE block exit }

  EmitLine('@' + LblEnd);
end;

procedure TCodeGenQBE.EmitTryExceptStmt(AStmt: TTryExceptStmt);
var
  LblTry:     string;
  LblExcept:  string;
  LblEnd:     string;
  FrameTemp:  string;
  SjrTemp:    string;
  ExcTemp:    string;
  MatchTemp:  string;
  LblBody:    string;
  LblNext:    string;
  I, J:       Integer;
  H:          TExceptHandlerClause;
begin
  LblTry    := AllocLabel('try_body');
  LblExcept := AllocLabel('except_handler');
  LblEnd    := AllocLabel('except_end');

  { Use a pre-allocated exception frame slot from @start (see EmitExcFrameAllocs).
    Matches the size contract in blaise_exc.c — must hold jmp_buf (200 B on
    Linux x86_64, ~312 B on macOS ARM64) plus two pointer fields. }
  FrameTemp := Format('%%_exc_frame_%d', [FExcFrameNext]);
  FExcFrameNext := FExcFrameNext + 1;
  EmitLine(Format('  call $_PushExcFrame(l %s)', [FrameTemp]));
  Inc(FExcDepth);

  SjrTemp := AllocTemp;
  EmitLine(Format('  %s =w call $setjmp(l %s)', [SjrTemp, FrameTemp]));
  EmitLine(Format('  jnz %s, @%s, @%s', [SjrTemp, LblExcept, LblTry]));

  { Normal path: run try body, pop frame on clean exit }
  EmitLine('@' + LblTry);
  for I := 0 to AStmt.TryBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.TryBody.Stmts.Items[I]));
  EmitLine('  call $_PopExcFrame()');
  Dec(FExcDepth);
  EmitLine(Format('  jmp @%s', [LblEnd]));

  { Exception path: capture exception before popping frame, then pop }
  EmitLine('@' + LblExcept);

  if AStmt.Handlers.Count > 0 then
  begin
    { Capture current exception while frame is still on the stack (g_exc_top
      points to our frame, so _CurrentException returns its exception field). }
    ExcTemp := AllocTemp;
    EmitLine(Format('  %s =l call $_CurrentException()', [ExcTemp]));
    EmitLine('  call $_PopExcFrame()');
    Dec(FExcDepth);

    for I := 0 to AStmt.Handlers.Count - 1 do
    begin
      H := TExceptHandlerClause(AStmt.Handlers[I]);
      LblBody := AllocLabel('exc_handler_body');
      LblNext := AllocLabel('exc_handler_next');

      MatchTemp := AllocTemp;
      EmitLine(Format('  %s =w call $_IsInstance(l %s, l $typeinfo_%s)',
        [MatchTemp, ExcTemp, H.TypeName]));
      EmitLine(Format('  jnz %s, @%s, @%s', [MatchTemp, LblBody, LblNext]));

      EmitLine('@' + LblBody);
      if H.VarName <> '' then
        EmitLine(Format('  storel %s, %%_var_%s', [ExcTemp, H.VarName]));
      for J := 0 to H.Body.Stmts.Count - 1 do
        EmitStmt(TASTStmt(H.Body.Stmts.Items[J]));
      EmitLine(Format('  jmp @%s', [LblEnd]));

      EmitLine('@' + LblNext);
    end;

    { No handler matched: run else body (if any), otherwise re-raise }
    if AStmt.ElseBody <> nil then
    begin
      for J := 0 to AStmt.ElseBody.Stmts.Count - 1 do
        EmitStmt(TASTStmt(AStmt.ElseBody.Stmts.Items[J]));
      EmitLine(Format('  jmp @%s', [LblEnd]));
    end
    else
    begin
      { No else: re-raise the unhandled exception }
      EmitLine(Format('  call $_Reraise(l %s)', [ExcTemp]));
      EmitLine(Format('  jmp @%s', [LblEnd]));  { unreachable; satisfies QBE SSA }
    end;
  end
  else
  begin
    { Plain catch-all body }
    EmitLine('  call $_PopExcFrame()');
    Dec(FExcDepth);
    for I := 0 to AStmt.ExceptBody.Stmts.Count - 1 do
      EmitStmt(TASTStmt(AStmt.ExceptBody.Stmts.Items[I]));
    EmitLine(Format('  jmp @%s', [LblEnd]));
  end;

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
  begin
    { Bare re-raise: retrieve the current exception, then call _Reraise.
      _Raise(0) would incorrectly clear g_current_exception to null. }
    ObjTemp := AllocTemp;
    EmitLine(Format('  %s =l call $_CurrentException()', [ObjTemp]));
    EmitLine(Format('  call $_Reraise(l %s)', [ObjTemp]));
  end;
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
  if not AStmt.IsGlobal and IsPromoted(AStmt.VarName) then
    EmitLine(Format('  %%_var_%s =w copy %s', [AStmt.VarName, StartT]))
  else
    EmitLine(Format('  storew %s, %s', [StartT, VarRef(AStmt.VarName, AStmt.IsGlobal)]));

  { Evaluate end value once into a temp }
  EndT := EmitExpr(AStmt.EndExpr);

  { Jump to condition (terminates current block) }
  EmitLine(Format('  jmp @%s', [LblCond]));

  { Condition block: test loop variable against end value }
  EmitLine('@' + LblCond);
  CurT := AllocTemp;
  if not AStmt.IsGlobal and IsPromoted(AStmt.VarName) then
    EmitLine(Format('  %s =w copy %%_var_%s', [CurT, AStmt.VarName]))
  else
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
  FBreakLabels.AddObject(LblEnd, TObject(PtrUInt(FExcDepth)));
  FContinueLabels.AddObject(LblNext, TObject(PtrUInt(FExcDepth)));
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
  if not AStmt.IsGlobal and IsPromoted(AStmt.VarName) then
    EmitLine(Format('  %s =w copy %%_var_%s', [CurT, AStmt.VarName]))
  else
    EmitLine(Format('  %s =w loadw %s', [CurT, VarRef(AStmt.VarName, AStmt.IsGlobal)]));
  if AStmt.IsDownTo then
    StepOp := 'sub'
  else
    StepOp := 'add';
  EmitLine(Format('  %s =w %s %s, 1', [StepT, StepOp, CurT]));
  if not AStmt.IsGlobal and IsPromoted(AStmt.VarName) then
    EmitLine(Format('  %%_var_%s =w copy %s', [AStmt.VarName, StepT]))
  else
    EmitLine(Format('  storew %s, %s', [StepT, VarRef(AStmt.VarName, AStmt.IsGlobal)]));
  EmitLine(Format('  jmp @%s', [LblCond]));

  { Continuation block }
  EmitLine('@' + LblEnd);
end;

procedure TCodeGenQBE.EmitForInStmt(AStmt: TForInStmt);
{ Implements for..in for two collection kinds:
    - IsArrayIter=True:  static array, index-based iteration
    - IsArrayIter=False: class enumerator (GetEnumerator / MoveNext / Current) }
var
  LblCond:    string;
  LblBody:    string;
  LblEnd:     string;
  EnumSlot:   string;
  SelfT:      string;
  EnumT:      string;
  OldT:       string;
  OkT:        string;
  CurT:       string;
  OldVarT:    string;
  GetEDecl:   TMethodDecl;
  MNDecl:     TMethodDecl;
  CurDecl:    TMethodDecl;
  QType:      string;
  FuncName:   string;
  VTblT:      string;
  FPtrT:      string;
  SlotOff:    Integer;
  StoreInstr: string;
  { Array iteration locals }
  IdxSlot:    string;
  IdxW:       string;
  IdxL:       string;
  CmpT:       string;
  BasePtr:    string;
  SAT:        TStaticArrayTypeDesc;
  ElemSize:   Integer;
  AdjL:       string;
  OffL:       string;
  ElemPtr:    string;
  QLoad:      string;
  NxtW:       string;
  { Set iteration locals }
  MaskSlot:   string;
  MaskT:      string;
  BitT:       string;
  OrdT:       string;
  LblNext:    string;
begin
  if AStmt.IsArrayIter then
  begin
    { ---- Static array iteration ---- }
    SAT      := TStaticArrayTypeDesc(AStmt.CollExpr.ResolvedType);
    ElemSize := SAT.ElementType.RawSize;
    case SAT.ElementType.Kind of
      tyByte, tyBoolean:            QLoad := 'loadub';
      tyInteger, tyUInt32, tyEnum:  QLoad := 'loadw';
    else
      QLoad := 'loadl';
    end;
    QType   := QbeTypeOf(SAT.ElementType);
    IdxSlot := '%_var_' + AStmt.IdxVarName;
    LblCond := AllocLabel('forin_cond');
    LblBody := AllocLabel('forin_body');
    LblEnd  := AllocLabel('forin_end');

    { Initialise index to ArrayLow }
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %s =w copy %d', [IdxSlot, AStmt.ArrayLow]))
    else
      EmitLine(Format('  storew %d, %s', [AStmt.ArrayLow, IdxSlot]));
    EmitLine(Format('  jmp @%s', [LblCond]));

    { Condition: idx <= ArrayHigh }
    EmitLine('@' + LblCond);
    IdxW := AllocTemp;
    CmpT := AllocTemp;
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %s =w copy %s', [IdxW, IdxSlot]))
    else
      EmitLine(Format('  %s =w loadw %s', [IdxW, IdxSlot]));
    EmitLine(Format('  %s =w cslew %s, %d', [CmpT, IdxW, AStmt.ArrayHigh]));
    EmitLine(Format('  jnz %s, @%s, @%s', [CmpT, LblBody, LblEnd]));

    { Body: load element, assign to loop var, then user body }
    EmitLine('@' + LblBody);
    FBreakLabels.AddObject(LblEnd, TObject(PtrUInt(FExcDepth)));
    FContinueLabels.AddObject(LblCond, TObject(PtrUInt(FExcDepth)));
    try
      BasePtr := EmitExpr(AStmt.CollExpr);
      IdxW    := AllocTemp;
      IdxL    := AllocTemp;
      if IsPromoted(AStmt.IdxVarName) then
        EmitLine(Format('  %s =w copy %s', [IdxW, IdxSlot]))
      else
        EmitLine(Format('  %s =w loadw %s', [IdxW, IdxSlot]));
      EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
      if AStmt.ArrayLow <> 0 then
      begin
        AdjL := AllocTemp;
        EmitLine(Format('  %s =l sub %s, %d', [AdjL, IdxL, AStmt.ArrayLow]));
        OffL := AllocTemp;
        EmitLine(Format('  %s =l mul %s, %d', [OffL, AdjL, ElemSize]));
      end
      else
      begin
        OffL := AllocTemp;
        EmitLine(Format('  %s =l mul %s, %d', [OffL, IdxL, ElemSize]));
      end;
      ElemPtr := AllocTemp;
      CurT    := AllocTemp;
      EmitLine(Format('  %s =l add %s, %s', [ElemPtr, BasePtr, OffL]));
      EmitLine(Format('  %s =%s %s %s', [CurT, QType, QLoad, ElemPtr]));

      { Assign element to loop variable }
      if AStmt.ResolvedVarType.IsString then
      begin
        OldVarT := AllocTemp;
        EmitLine(Format('  %s =l loadl %s',
          [OldVarT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));
        EmitLine(Format('  call $_StringAddRef(l %s)', [CurT]));
        EmitLine(Format('  call $_StringRelease(l %s)', [OldVarT]));
        EmitLine(Format('  storel %s, %s',
          [CurT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));
      end
      else if AStmt.ResolvedVarType.Kind = tyClass then
      begin
        OldVarT := AllocTemp;
        EmitLine(Format('  %s =l loadl %s',
          [OldVarT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));
        EmitLine(Format('  call $_ClassAddRef(l %s)', [CurT]));
        EmitLine(Format('  call $_ClassRelease(l %s)', [OldVarT]));
        EmitLine(Format('  storel %s, %s',
          [CurT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));
      end
      else if QType = 'w' then
      begin
        if not AStmt.VarIsGlobal and IsPromoted(AStmt.VarName) then
          EmitLine(Format('  %%_var_%s =w copy %s', [AStmt.VarName, CurT]))
        else
          EmitLine(Format('  storew %s, %s',
            [CurT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));
      end
      else
        EmitLine(Format('  storel %s, %s',
          [CurT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));

      EmitStmt(AStmt.Body);
    finally
      FBreakLabels.Delete(FBreakLabels.Count - 1);
      FContinueLabels.Delete(FContinueLabels.Count - 1);
    end;

    { Increment index }
    IdxW := AllocTemp;
    NxtW := AllocTemp;
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %s =w copy %s', [IdxW, IdxSlot]))
    else
      EmitLine(Format('  %s =w loadw %s', [IdxW, IdxSlot]));
    EmitLine(Format('  %s =w add %s, 1', [NxtW, IdxW]));
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %s =w copy %s', [IdxSlot, NxtW]))
    else
      EmitLine(Format('  storew %s, %s', [NxtW, IdxSlot]));
    EmitLine(Format('  jmp @%s', [LblCond]));

    EmitLine('@' + LblEnd);
    Exit;
  end;

  if AStmt.IsStringIter then
  begin
    { ---- String byte-iteration ----
      String layout: [refcount(4)][length(4)][capacity(4)][data...]
      0-based index: element = loadub(strptr + 12 + idx)
      Condition:     idx < loadw(strptr + 4)
      CollExpr is re-evaluated each iteration (cheap — just a loadl for a variable). }
    IdxSlot := '%_var_' + AStmt.IdxVarName;
    LblCond := AllocLabel('forin_cond');
    LblBody := AllocLabel('forin_body');
    LblEnd  := AllocLabel('forin_end');

    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %s =w copy 0', [IdxSlot]))
    else
      EmitLine(Format('  storew 0, %s', [IdxSlot]));
    EmitLine(Format('  jmp @%s', [LblCond]));

    { Condition: idx < string length
      Data-pointer convention: length at data_ptr − 8 }
    EmitLine('@' + LblCond);
    SelfT := EmitExpr(AStmt.CollExpr);  { string data pointer }
    OldT  := AllocTemp;
    OkT   := AllocTemp;
    IdxW  := AllocTemp;
    CmpT  := AllocTemp;
    EmitLine(Format('  %s =l add %s, -8', [OldT, SelfT]));  { data_ptr − 8 = length }
    EmitLine(Format('  %s =w loadw %s',   [OkT, OldT]));
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %s =w copy %s',  [IdxW, IdxSlot]))
    else
      EmitLine(Format('  %s =w loadw %s', [IdxW, IdxSlot]));
    EmitLine(Format('  %s =w csltw %s, %s', [CmpT, IdxW, OkT]));
    EmitLine(Format('  jnz %s, @%s, @%s', [CmpT, LblBody, LblEnd]));

    { Body: load byte at index — data IS the pointer, no skip needed }
    EmitLine('@' + LblBody);
    FBreakLabels.AddObject(LblEnd, TObject(PtrUInt(FExcDepth)));
    FContinueLabels.AddObject(LblCond, TObject(PtrUInt(FExcDepth)));
    try
      SelfT   := EmitExpr(AStmt.CollExpr);
      IdxW    := AllocTemp;
      IdxL    := AllocTemp;
      ElemPtr := AllocTemp;
      CurT    := AllocTemp;
      if IsPromoted(AStmt.IdxVarName) then
        EmitLine(Format('  %s =w copy %s',  [IdxW, IdxSlot]))
      else
        EmitLine(Format('  %s =w loadw %s', [IdxW, IdxSlot]));
      EmitLine(Format('  %s =l extuw %s',   [IdxL, IdxW]));
      EmitLine(Format('  %s =l add %s, %s', [ElemPtr, SelfT, IdxL]));  { data_ptr + idx }
      EmitLine(Format('  %s =w loadub %s',  [CurT, ElemPtr]));
      if not AStmt.VarIsGlobal and IsPromoted(AStmt.VarName) then
        EmitLine(Format('  %%_var_%s =w copy %s', [AStmt.VarName, CurT]))
      else
        EmitLine(Format('  storew %s, %s',
          [CurT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));

      EmitStmt(AStmt.Body);
    finally
      FBreakLabels.Delete(FBreakLabels.Count - 1);
      FContinueLabels.Delete(FContinueLabels.Count - 1);
    end;

    { Increment index }
    IdxW := AllocTemp;
    NxtW := AllocTemp;
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %s =w copy %s', [IdxW, IdxSlot]))
    else
      EmitLine(Format('  %s =w loadw %s', [IdxW, IdxSlot]));
    EmitLine(Format('  %s =w add %s, 1', [NxtW, IdxW]));
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %s =w copy %s', [IdxSlot, NxtW]))
    else
      EmitLine(Format('  storew %s, %s', [NxtW, IdxSlot]));
    EmitLine(Format('  jmp @%s', [LblCond]));

    EmitLine('@' + LblEnd);
    Exit;
  end;

  if AStmt.IsSetIter then
  begin
    { ---- Set iteration ----
      Evaluates the set expression once into a mask slot, then iterates
      bit positions 0..BitCount-1.  For each set bit, assigns the
      corresponding enum ordinal to the loop variable and runs the body.

      Desugaring:
        __setmask := <SetExpr>
        __idx := 0
        @forin_cond:
          if __idx >= BitCount then goto forin_end
        @forin_body:
          bit := (__setmask shr __idx) and 1
          if bit = 0 then goto forin_next
          LoopVar := TEnum(__idx)
          Body
        @forin_next:
          __idx := __idx + 1
          goto forin_cond
        @forin_end: }
    MaskSlot := '%_var_' + AStmt.SetMaskVarName;
    IdxSlot  := '%_var_' + AStmt.IdxVarName;
    LblCond  := AllocLabel('forin_cond');
    LblBody  := AllocLabel('forin_body');
    LblNext  := AllocLabel('forin_next');
    LblEnd   := AllocLabel('forin_end');

    { Evaluate the set expression once and store in mask slot }
    MaskT := EmitExpr(AStmt.CollExpr);
    if IsPromoted(AStmt.SetMaskVarName) then
      EmitLine(Format('  %%_var_%s =w copy %s', [AStmt.SetMaskVarName, MaskT]))
    else
      EmitLine(Format('  storew %s, %s', [MaskT, MaskSlot]));

    { Initialise index to 0 }
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %%_var_%s =w copy 0', [AStmt.IdxVarName]))
    else
      EmitLine(Format('  storew 0, %s', [IdxSlot]));
    EmitLine(Format('  jmp @%s', [LblCond]));

    { Condition: idx < BitCount }
    EmitLine('@' + LblCond);
    IdxW := AllocTemp;
    CmpT := AllocTemp;
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %s =w copy %s', [IdxW, IdxSlot]))
    else
      EmitLine(Format('  %s =w loadw %s', [IdxW, IdxSlot]));
    EmitLine(Format('  %s =w csltw %s, %d', [CmpT, IdxW, AStmt.SetBitCount]));
    EmitLine(Format('  jnz %s, @%s, @%s', [CmpT, LblBody, LblEnd]));

    { Body block: test bit, skip if clear }
    EmitLine('@' + LblBody);
    MaskT := AllocTemp;
    BitT  := AllocTemp;
    if IsPromoted(AStmt.SetMaskVarName) then
      EmitLine(Format('  %s =w copy %%_var_%s', [MaskT, AStmt.SetMaskVarName]))
    else
      EmitLine(Format('  %s =w loadw %s', [MaskT, MaskSlot]));
    IdxW := AllocTemp;
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %s =w copy %s', [IdxW, IdxSlot]))
    else
      EmitLine(Format('  %s =w loadw %s', [IdxW, IdxSlot]));
    EmitLine(Format('  %s =w shr %s, %s', [BitT, MaskT, IdxW]));
    CmpT := AllocTemp;
    EmitLine(Format('  %s =w and %s, 1', [CmpT, BitT]));
    { If bit is 0 skip body, go directly to forin_next }
    EmitLine(Format('  jnz %s, @%s_yes, @%s', [CmpT, LblBody, LblNext]));
    EmitLine('@' + LblBody + '_yes');

    FBreakLabels.AddObject(LblEnd, TObject(PtrUInt(FExcDepth)));
    FContinueLabels.AddObject(LblNext, TObject(PtrUInt(FExcDepth)));
    try
      { Assign ordinal (idx) to loop variable as enum }
      OrdT := AllocTemp;
      IdxW := AllocTemp;
      if IsPromoted(AStmt.IdxVarName) then
        EmitLine(Format('  %s =w copy %s', [IdxW, IdxSlot]))
      else
        EmitLine(Format('  %s =w loadw %s', [IdxW, IdxSlot]));
      EmitLine(Format('  %s =w copy %s', [OrdT, IdxW]));
      if not AStmt.VarIsGlobal and IsPromoted(AStmt.VarName) then
        EmitLine(Format('  %%_var_%s =w copy %s', [AStmt.VarName, OrdT]))
      else
        EmitLine(Format('  storew %s, %s',
          [OrdT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));

      EmitStmt(AStmt.Body);
    finally
      FBreakLabels.Delete(FBreakLabels.Count - 1);
      FContinueLabels.Delete(FContinueLabels.Count - 1);
    end;

    { Increment index }
    EmitLine('@' + LblNext);
    IdxW := AllocTemp;
    NxtW := AllocTemp;
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %s =w copy %s', [IdxW, IdxSlot]))
    else
      EmitLine(Format('  %s =w loadw %s', [IdxW, IdxSlot]));
    EmitLine(Format('  %s =w add %s, 1', [NxtW, IdxW]));
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %%_var_%s =w copy %s', [AStmt.IdxVarName, NxtW]))
    else
      EmitLine(Format('  storew %s, %s', [NxtW, IdxSlot]));
    EmitLine(Format('  jmp @%s', [LblCond]));

    EmitLine('@' + LblEnd);
    Exit;
  end;

  { ---- Class enumerator protocol ---- }
  LblCond := AllocLabel('forin_cond');
  LblBody := AllocLabel('forin_body');
  LblEnd  := AllocLabel('forin_end');

  GetEDecl := TMethodDecl(AStmt.GetEnumDecl);
  MNDecl   := TMethodDecl(AStmt.MoveNextDecl);
  CurDecl  := TMethodDecl(AStmt.CurrentDecl);
  EnumSlot := '%_var_' + AStmt.EnumVarName;

  { --- Call GetEnumerator on the collection --- }
  SelfT := EmitExpr(AStmt.CollExpr);
  EnumT := AllocTemp;
  FuncName := '$' + QBEMangle(GetEDecl.OwnerTypeName + '_' + GetEDecl.Name);
  if GetEDecl.VTableSlot >= 0 then
  begin
    VTblT   := AllocTemp;
    FPtrT   := AllocTemp;
    SlotOff := (GetEDecl.VTableSlot + 1) * 8;
    EmitLine(Format('  %s =l loadl %s', [VTblT, SelfT]));
    if SlotOff = 0 then
      EmitLine(Format('  %s =l loadl %s', [FPtrT, VTblT]))
    else
    begin
      OldT := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', [OldT, VTblT, SlotOff]));
      EmitLine(Format('  %s =l loadl %s', [FPtrT, OldT]));
    end;
    EmitLine(Format('  %s =l call %s(l %s)', [EnumT, FPtrT, SelfT]));
  end
  else
    EmitLine(Format('  %s =l call %s(l %s)', [EnumT, FuncName, SelfT]));

  { ARC-assign the enumerator into the synthetic slot }
  OldT := AllocTemp;
  EmitLine(Format('  %s =l loadl %s', [OldT, EnumSlot]));
  EmitLine(Format('  call $_ClassAddRef(l %s)', [EnumT]));
  EmitLine(Format('  call $_ClassRelease(l %s)', [OldT]));
  EmitLine(Format('  storel %s, %s', [EnumT, EnumSlot]));

  EmitLine(Format('  jmp @%s', [LblCond]));

  { --- Condition: call MoveNext --- }
  EmitLine('@' + LblCond);
  SelfT    := AllocTemp;
  EmitLine(Format('  %s =l loadl %s', [SelfT, EnumSlot]));
  OkT      := AllocTemp;
  FuncName := '$' + QBEMangle(MNDecl.OwnerTypeName + '_' + MNDecl.Name);
  if MNDecl.VTableSlot >= 0 then
  begin
    VTblT   := AllocTemp;
    FPtrT   := AllocTemp;
    SlotOff := (MNDecl.VTableSlot + 1) * 8;
    EmitLine(Format('  %s =l loadl %s', [VTblT, SelfT]));
    if SlotOff = 0 then
      EmitLine(Format('  %s =l loadl %s', [FPtrT, VTblT]))
    else
    begin
      OldT := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', [OldT, VTblT, SlotOff]));
      EmitLine(Format('  %s =l loadl %s', [FPtrT, OldT]));
    end;
    EmitLine(Format('  %s =w call %s(l %s)', [OkT, FPtrT, SelfT]));
  end
  else
    EmitLine(Format('  %s =w call %s(l %s)', [OkT, FuncName, SelfT]));
  EmitLine(Format('  jnz %s, @%s, @%s', [OkT, LblBody, LblEnd]));

  { --- Body: read Current, assign to loop var, then user body --- }
  EmitLine('@' + LblBody);
  FBreakLabels.AddObject(LblEnd, TObject(PtrUInt(FExcDepth)));
  FContinueLabels.AddObject(LblCond, TObject(PtrUInt(FExcDepth)));
  try
    SelfT    := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', [SelfT, EnumSlot]));
    QType    := QbeTypeOf(CurDecl.ResolvedReturnType);
    FuncName := '$' + QBEMangle(CurDecl.OwnerTypeName + '_' + CurDecl.Name);
    CurT     := AllocTemp;
    if CurDecl.VTableSlot >= 0 then
    begin
      VTblT   := AllocTemp;
      FPtrT   := AllocTemp;
      SlotOff := (CurDecl.VTableSlot + 1) * 8;
      EmitLine(Format('  %s =l loadl %s', [VTblT, SelfT]));
      if SlotOff = 0 then
        EmitLine(Format('  %s =l loadl %s', [FPtrT, VTblT]))
      else
      begin
        OldT := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', [OldT, VTblT, SlotOff]));
        EmitLine(Format('  %s =l loadl %s', [FPtrT, OldT]));
      end;
      EmitLine(Format('  %s =%s call %s(l %s)', [CurT, QType, FPtrT, SelfT]));
    end
    else
      EmitLine(Format('  %s =%s call %s(l %s)', [CurT, QType, FuncName, SelfT]));

    { Assign Current result to the loop variable }
    if AStmt.ResolvedVarType.IsString then
    begin
      OldVarT := AllocTemp;
      EmitLine(Format('  %s =l loadl %s',
        [OldVarT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));
      EmitLine(Format('  call $_StringAddRef(l %s)', [CurT]));
      EmitLine(Format('  call $_StringRelease(l %s)', [OldVarT]));
      EmitLine(Format('  storel %s, %s',
        [CurT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));
    end
    else if AStmt.ResolvedVarType.Kind = tyClass then
    begin
      OldVarT := AllocTemp;
      EmitLine(Format('  %s =l loadl %s',
        [OldVarT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));
      EmitLine(Format('  call $_ClassAddRef(l %s)', [CurT]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [OldVarT]));
      EmitLine(Format('  storel %s, %s',
        [CurT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));
    end
    else if QType = 'w' then
      EmitLine(Format('  storew %s, %s',
        [CurT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]))
    else
      EmitLine(Format('  storel %s, %s',
        [CurT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));

    EmitStmt(AStmt.Body);
  finally
    FBreakLabels.Delete(FBreakLabels.Count - 1);
    FContinueLabels.Delete(FContinueLabels.Count - 1);
  end;
  EmitLine(Format('  jmp @%s', [LblCond]));

  { --- End label --- }
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
  FBreakLabels.AddObject(LblEnd, TObject(PtrUInt(FExcDepth)));
  FContinueLabels.AddObject(LblCond, TObject(PtrUInt(FExcDepth)));
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
  FBreakLabels.AddObject(LblEnd, TObject(PtrUInt(FExcDepth)));
  FContinueLabels.AddObject(LblCond, TObject(PtrUInt(FExcDepth)));
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
    ItabName := '$itab_' + QBEMangle(ClassRT.Name) + '_' + QBEMangle(IntfDesc.Name);
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
    PtrTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_%s', [PtrTemp, AAssign.Name]));
    if AAssign.Expr.ResolvedType.IsString then
    begin
      OldTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [OldTemp, PtrTemp]));
      ValTemp := EmitExpr(AAssign.Expr);
      EmitLine(Format('  call $_StringAddRef(l %s)', [ValTemp]));
      EmitLine(Format('  call $_StringRelease(l %s)', [OldTemp]));
      EmitLine(Format('  storel %s, %s', [ValTemp, PtrTemp]));
    end
    else if AAssign.Expr.ResolvedType.Kind = tyClass then
    begin
      OldTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [OldTemp, PtrTemp]));
      ValTemp := EmitExpr(AAssign.Expr);
      EmitLine(Format('  call $_ClassAddRef(l %s)', [ValTemp]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
      EmitLine(Format('  storel %s, %s', [ValTemp, PtrTemp]));
    end
    else
    begin
      QType   := QbeTypeOf(AAssign.Expr.ResolvedType);
      ValTemp := EmitExpr(AAssign.Expr);
      if QType = 'w' then StoreInstr := 'storew'
                     else StoreInstr := 'storel';
      EmitLine(Format('  %s %s, %s', [StoreInstr, ValTemp, PtrTemp]));
    end;
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
  else if (AAssign.ResolvedLhsType <> nil) and
          (AAssign.ResolvedLhsType.Kind = tyProcedural) and
          TProceduralTypeDesc(AAssign.ResolvedLhsType).IsMethodPtr then
  begin
    { Method-pointer assignment: 16-byte block copy (Code at +0, Data at +8).
      The RHS evaluates to the address of a 16-byte source block — either
      another method-pointer var or a TMethod record (same layout). }
    ValTemp := EmitExpr(AAssign.Expr);
    EmitLine(Format('  call $memcpy(l %s, l %s, l 16)',
      [VarRef(AAssign.Name, AAssign.IsGlobal), ValTemp]));
  end
  else if AAssign.Expr.ResolvedType.IsString then
  begin
    { ARC: load old, compute new, retain new, release old, store new }
    OldTemp := AllocTemp;
    if not AAssign.IsGlobal and IsPromoted(AAssign.Name) then
      EmitLine(Format('  %s =l copy %%_var_%s', [OldTemp, AAssign.Name]))
    else
      EmitLine(Format('  %s =l loadl %s', [OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    ValTemp := EmitExpr(AAssign.Expr);
    EmitLine(Format('  call $_StringAddRef(l %s)', [ValTemp]));
    EmitLine(Format('  call $_StringRelease(l %s)', [OldTemp]));
    if not AAssign.IsGlobal and IsPromoted(AAssign.Name) then
      EmitLine(Format('  %%_var_%s =l copy %s', [AAssign.Name, ValTemp]))
    else
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
    if not AAssign.IsGlobal and IsPromoted(AAssign.Name) then
      EmitLine(Format('  %s =l copy %%_var_%s', [OldTemp, AAssign.Name]))
    else
      EmitLine(Format('  %s =l loadl %s', [OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    ValTemp := EmitExpr(AAssign.Expr);
    EmitLine(Format('  call $_ClassAddRef(l %s)', [ValTemp]));
    EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
    if not AAssign.IsGlobal and IsPromoted(AAssign.Name) then
      EmitLine(Format('  %%_var_%s =l copy %s', [AAssign.Name, ValTemp]))
    else
      EmitLine(Format('  storel %s, %s', [ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
  end
  else
  begin
    { Use LHS type (if known) for the store instruction, so that assigning a
      small int to an Int64 or Double variable uses the correct instruction. }
    if (AAssign.ResolvedLhsType <> nil) and
       (AAssign.ResolvedLhsType.Kind = tyDouble) then
    begin
      { Double := integer/single — promote rhs to double }
      ValTemp := EmitExpr(AAssign.Expr);
      if (AAssign.Expr.ResolvedType <> nil) and
         (QbeTypeOf(AAssign.Expr.ResolvedType) = 'w') then
      begin
        ExtTemp := AllocTemp;
        EmitLine(Format('  %s =d swtof %s', [ExtTemp, ValTemp]));
        ValTemp := ExtTemp;
      end
      else if (AAssign.Expr.ResolvedType <> nil) and
              (AAssign.Expr.ResolvedType.Kind = tySingle) then
      begin
        ExtTemp := AllocTemp;
        EmitLine(Format('  %s =d exts %s', [ExtTemp, ValTemp]));
        ValTemp := ExtTemp;
      end;
      if not AAssign.IsGlobal and IsPromoted(AAssign.Name) then
        EmitLine(Format('  %%_var_%s =d copy %s', [AAssign.Name, ValTemp]))
      else
        EmitLine(Format('  stored %s, %s', [ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    end
    else if (AAssign.ResolvedLhsType <> nil) and
            (QbeTypeOf(AAssign.ResolvedLhsType) = 'l') then
    begin
      ValTemp := EmitExpr(AAssign.Expr);
      if QbeTypeOf(AAssign.Expr.ResolvedType) = 'w' then
      begin
        ExtTemp := AllocTemp;
        EmitLine(Format('  %s =l extsw %s', [ExtTemp, ValTemp]));
        ValTemp := ExtTemp;
      end;
      if not AAssign.IsGlobal and IsPromoted(AAssign.Name) then
        EmitLine(Format('  %%_var_%s =l copy %s', [AAssign.Name, ValTemp]))
      else
        EmitLine(Format('  storel %s, %s', [ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    end
    else
    begin
      QType   := QbeTypeOf(AAssign.Expr.ResolvedType);
      ValTemp := EmitExpr(AAssign.Expr);
      if not AAssign.IsGlobal and IsPromoted(AAssign.Name) then
      begin
        EmitLine(Format('  %%_var_%s =%s copy %s', [AAssign.Name, QType, ValTemp]));
      end
      else
      begin
        case QType of
          'w': StoreInstr := 'storew';
          'd': StoreInstr := 'stored';
          's': StoreInstr := 'stores';
        else   StoreInstr := 'storel';
        end;
        EmitLine(Format('  %s %s, %s', [StoreInstr, ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
      end;
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
    else if Id.IsVarParam then
    begin
      { Var-record param: dereference the param slot to get the actual record
        address. }
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
    { Property-backed access: the result is already a pointer — delegate to EmitExpr }
    if Fld.PropRead <> nil then
    begin
      Result := EmitExpr(Fld);
      Exit;
    end;
    if Fld.Base <> nil then
      Base := EmitInstancePtr(Fld.Base)
    else if Fld.IsImplicitSelf then
    begin
      { Leaf: RecordName is a field of Self — load through %_var_Self. }
      SelfT := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_Self', [SelfT]));
      if Fld.ImplicitBaseInfo.Offset > 0 then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', [Ptr, SelfT, Fld.ImplicitBaseInfo.Offset]));
        SelfT := Ptr;
      end;
      Loaded := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [Loaded, SelfT]));
      Base := Loaded;
    end
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
      else if Fld.IsVarParam then
      begin
        { Var-record param leaf: dereference the param slot. }
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

function TCodeGenQBE.FieldPtr(const ARecordVar: string; AOffset: Integer; AIsGlobal: Boolean = False): string;
var
  PtrTemp: string;
  Base:    string;
begin
  Base := VarRef(ARecordVar, AIsGlobal);
  if AOffset = 0 then
    Result := Base
  else
  begin
    PtrTemp := AllocTemp;
    EmitLine(Format('  %s =l add %s, %d', [PtrTemp, Base, AOffset]));
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

function TCodeGenQBE.EmitLValueAddr(AExpr: TASTExpr): string;
var
  Deref:    TDerefExpr;
  FldAcc:   TFieldAccessExpr;
  BaseAddr: string;
  RT:       TRecordTypeDesc;
  FldInfo:  TFieldInfo;
  T:        string;
begin
  if AExpr is TIdentExpr then
  begin
    Result := EmitVarArgAddr(TIdentExpr(AExpr));
    Exit;
  end;
  if AExpr is TDerefExpr then
  begin
    { P^ as L-value: the pointer's value IS the address. }
    Deref := TDerefExpr(AExpr);
    Result := EmitExpr(Deref.Expr);
    Exit;
  end;
  if AExpr is TFieldAccessExpr then
  begin
    FldAcc := TFieldAccessExpr(AExpr);
    if FldAcc.Base <> nil then
      BaseAddr := EmitInstancePtr(FldAcc.Base)
    else if FldAcc.IsVarParam then
    begin
      { Var-record param leaf: dereference the param slot. }
      T := AllocTemp;
      EmitLine(Format('  %s =l loadl %s',
        [T, VarRef(FldAcc.RecordName, FldAcc.IsGlobal)]));
      BaseAddr := T;
    end
    else
      BaseAddr := VarRef(FldAcc.RecordName, FldAcc.IsGlobal);
    if (FldAcc.ResolvedType <> nil) and
       (FldAcc.FieldInfo <> nil) and (FldAcc.FieldInfo.Offset > 0) then
    begin
      RT := nil;
      FldInfo := FldAcc.FieldInfo;
      T := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d',
        [T, BaseAddr, FldInfo.Offset]));
      Result := T;
    end
    else
      Result := BaseAddr;
    Exit;
  end;
  raise ECodeGenError.Create('Unsupported L-value form for var argument');
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
      FuncName := '$' + MethodEmitName(MDecl, MDecl.OwnerTypeName, FCallExpr.Name);
      ArgLine  := Format('l %s, l %s', [ASretAddr, SelfTemp]);
    end
    else
    begin
      if (MDecl <> nil) and (MDecl.ResolvedQbeName <> '') then
        FuncName := '$' + QBEMangle(MDecl.ResolvedQbeName)
      else
        FuncName := '$' + QBEMangle(FCallExpr.Name);
      ArgLine  := Format('l %s', [ASretAddr]);
    end;
    for I := 0 to FCallExpr.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Items[I]);
      if Par.IsVarParam then
        ArgLine := ArgLine + Format(', l %s',
          [EmitLValueAddr(TASTExpr(FCallExpr.Args.Items[I]))])
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(FCallExpr.Args.Items[I]));
        ArgTemp := CoerceArg(ArgTemp, TASTExpr(FCallExpr.Args.Items[I]),
          QbeTypeOf(Par.ResolvedType));
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
    FuncName := '$' + MethodEmitName(MDecl, MDecl.OwnerTypeName, MCallExpr.Name);
    ArgLine  := Format('l %s, l %s', [ASretAddr, SelfTemp]);
    for I := 0 to MCallExpr.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Items[I]);
      if Par.IsVarParam then
        ArgLine := ArgLine + Format(', l %s',
          [EmitLValueAddr(TASTExpr(MCallExpr.Args.Items[I]))])
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Items[I]));
        ArgTemp := CoerceArg(ArgTemp, TASTExpr(MCallExpr.Args.Items[I]),
          QbeTypeOf(Par.ResolvedType));
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
    FuncName := '$' + MethodEmitName(MDecl, MDecl.OwnerTypeName, FldAccess.FieldName);
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
    { Receiver is an arbitrary expression — get its storage address.
      For class-typed bases (heap object) EmitInstancePtr loads the heap pointer.
      For record-typed bases (inline storage) EmitInstancePtr returns the address
      of the record in memory — EmitExpr would incorrectly load the contents. }
    PtrTemp := EmitInstancePtr(AAssign.ObjExpr);
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
  else if AAssign.IsVarParam then
  begin
    { Var-record param: dereference the param slot to get the actual record
      address, then add field offset. }
    PtrTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s',
      [PtrTemp, VarRef(AAssign.RecordName, AAssign.IsGlobal)]));
    if AAssign.FieldInfo.Offset > 0 then
    begin
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d',
        [Ptr, PtrTemp, AAssign.FieldInfo.Offset]));
    end
    else
      Ptr := PtrTemp;
  end
  else
    Ptr := FieldPtr(AAssign.RecordName, AAssign.FieldInfo.Offset, AAssign.IsGlobal);

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
    { Emit args: no concrete param info at interface-dispatch site, so use
      the resolved type of each argument expression to pick the QBE type.
      Pointer-typed args (var params written as TAddrOfExpr or already resolved
      as pointer/class) use 'l'; all other scalar args use 'w'. }
    ArgLine := Format('l %s', [SelfTemp]);
    for I := 0 to ACall.Args.Count - 1 do
    begin
      ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
      if (TASTExpr(ACall.Args.Items[I]).ResolvedType <> nil) and
         (TASTExpr(ACall.Args.Items[I]).ResolvedType.Kind in
           [tyPointer, tyClass, tyInterface, tyPChar, tyString]) then
        ArgLine := ArgLine + Format(', l %s', [ArgTemp])
      else
        ArgLine := ArgLine + Format(', w %s', [ArgTemp]);
    end;
    EmitLine(Format('  call %s(%s)', [FPtrTemp, ArgLine]));
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
          [EmitLValueAddr(TASTExpr(ACall.Args.Items[I]))])
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
        QType   := QbeTypeOf(Par.ResolvedType);
        ArgTemp := CoerceArg(ArgTemp, TASTExpr(ACall.Args.Items[I]), QType);
        ArgLine := ArgLine + Format(', %s %s', [QType, ArgTemp]);
      end;
    end;
    { Virtual methods on an arbitrary receiver expression must dispatch
      through the vtable — the static-class type seen here may be an
      abstract base whose direct method symbol does not exist (the slot
      points at $_AbstractMethodError).  Mirror the same vtable-load
      sequence used below for the IsImplicitSelf / ObjectName paths. }
    if (MDecl <> nil) and (MDecl.VTableSlot >= 0) then
    begin
      VTblTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [VTblTemp, SelfTemp]));
      FPtrTemp := AllocTemp;
      SlotOff  := (MDecl.VTableSlot + 1) * 8;
      ArgTemp  := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', [ArgTemp, VTblTemp, SlotOff]));
      EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
      EmitLine(Format('  call %s(%s)', [FPtrTemp, ArgLine]));
      Exit;
    end;
    if MDecl.OwnerTypeName <> '' then
      FuncName := '$' + MethodEmitName(MDecl, MDecl.OwnerTypeName, ACall.Name)
    else
      FuncName := '$' + MethodEmitName(MDecl, RT.Name, ACall.Name);
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
  begin
    EmitLine(Format('  %s =l loadl %s', [SelfTemp, VarRef(ACall.ObjectName, ACall.IsGlobal)]));
    EmitLine(Format('  call $_CheckNil(l %s)', [SelfTemp]));
  end;

  { Build argument string: l Self, then each explicit arg }
  ArgLine := Format('l %s', [SelfTemp]);
  for I := 0 to ACall.Args.Count - 1 do
  begin
    Par := TMethodParam(MDecl.Params.Items[I]);
    if Par.IsVarParam then
      ArgLine := ArgLine + Format(', l %s',
        [EmitLValueAddr(TASTExpr(ACall.Args.Items[I]))])
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
      FuncName := '$' + MethodEmitName(MDecl, MDecl.OwnerTypeName, ACall.Name)
    else
      FuncName := '$' + MethodEmitName(MDecl, RT.Name, ACall.Name);
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
      on no match fall through to next branch test or else.
      String-typed selector lowers each label test to a call to
      _StringEquals (returns 1 on equal, 0 otherwise) so jnz works
      against the result directly. }
    for I := 0 to AStmt.Branches.Count - 1 do
    begin
      Branch    := TCaseBranch(AStmt.Branches.Items[I]);
      BranchLbl := BranchLabels.Strings[I];
      for J := 0 to Branch.Values.Count - 1 do
      begin
        ValTemp := EmitExpr(TASTExpr(Branch.Values.Items[J]));
        CmpTemp := AllocTemp;
        NextLbl := AllocLabel('case_next');
        if AStmt.IsStringCase then
          EmitLine(Format('  %s =w call $_StringEquals(l %s, l %s)',
            [CmpTemp, SelTemp, ValTemp]))
        else
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
    ArgTemp := CoerceArg(ArgTemp, TASTExpr(ACall.Args.Items[I]), QType);
    ArgLine := ArgLine + Format(', %s %s', [QType, ArgTemp]);
  end;

  { Always a direct (static) call — inherited bypasses vtable dispatch.
    If the parent method returns a value, store it into %_var_Result so that
    "inherited F;" as a statement sets Result in the overriding function. }
  if (MDecl.ResolvedReturnType <> nil) and
     (MDecl.ResolvedReturnType.Kind <> tyVoid) then
  begin
    QType   := QbeTypeOf(MDecl.ResolvedReturnType);
    ArgTemp := AllocTemp;
    EmitLine(Format('  %s =%s call $%s(%s)',
      [ArgTemp, QType, MethodEmitName(MDecl, MDecl.OwnerTypeName, ACall.Name), ArgLine]));
    if QType = 'w' then
      EmitLine(Format('  storew %s, %%_var_Result', [ArgTemp]))
    else
      EmitLine(Format('  storel %s, %%_var_Result', [ArgTemp]));
  end
  else
    EmitLine(Format('  call $%s(%s)',
      [MethodEmitName(MDecl, MDecl.OwnerTypeName, ACall.Name), ArgLine]));
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
      tyInt64, tyString, tyClass, tyMetaClass:
        begin
          EmitLine(Format('  %%_var_%s =l alloc8 1', [Par.ParamName]));
          EmitLine(Format('  storel %%_par_%s, %%_var_%s',
            [Par.ParamName, Par.ParamName]));
        end;
      tyDouble:
        begin
          EmitLine(Format('  %%_var_%s =l alloc8 1', [Par.ParamName]));
          EmitLine(Format('  stored %%_par_%s, %%_var_%s',
            [Par.ParamName, Par.ParamName]));
        end;
      tySingle:
        begin
          EmitLine(Format('  %%_var_%s =l alloc4 1', [Par.ParamName]));
          EmitLine(Format('  stores %%_par_%s, %%_var_%s',
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
  if AMethod.ResolvedQbeName <> '' then
    FuncName := '$' + QBEMangle(AMethod.ResolvedQbeName)
  else
    FuncName := '$' + QBEMangle(ATypeName + '_' + AMethod.Name);
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

  { ARC: addref string and class value params on entry — balances the
    release pass at method exit. }
  for I := 0 to AMethod.Params.Count - 1 do
  begin
    Par := TMethodParam(AMethod.Params.Items[I]);
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
    else if RetQType = 'd' then
    begin
      EmitLine('  %_var_Result =l alloc8 1');
      EmitLine('  stored d_0, %_var_Result');
    end
    else if RetQType = 's' then
    begin
      EmitLine('  %_var_Result =l alloc4 1');
      EmitLine('  stores s_0, %_var_Result');
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

  { ARC: release string and class value params on exit. }
  for I := 0 to AMethod.Params.Count - 1 do
  begin
    Par := TMethodParam(AMethod.Params.Items[I]);
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
    if AMethod.ResolvedReturnType.Kind = tyRecord then
      EmitLine('  ret')  { sret: caller's buffer already holds result }
    else
    begin
      RetTemp := AllocTemp;
      if IsPromoted('Result') then
        EmitLine(Format('  %s =%s copy %%_var_Result', [RetTemp, RetQType]))
      else if RetQType = 'w' then
        EmitLine(Format('  %s =w loadw %%_var_Result', [RetTemp]))
      else if RetQType = 'd' then
        EmitLine(Format('  %s =d loadd %%_var_Result', [RetTemp]))
      else if RetQType = 's' then
        EmitLine(Format('  %s =s loads %%_var_Result', [RetTemp]))
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
{ Emit one $typeinfo_T data item per class type.  Each typeinfo data
  block has 7 l-slots, in order:

    Slot 0 (offset  0): parent typeinfo pointer (0 = root)
    Slot 1 (offset  8): impllist pointer (0 = no interfaces)
    Slot 2 (offset 16): pointer to class name string literal
    Slot 3 (offset 24): pointer to published-method table (0 = none)
                        Table holds count followed by (name, code) pairs.
                        TObject.MethodAddress walks vtable[0] -> typeinfo
                        -> slot 3, then climbs the parent chain.
    Slot 4 (offset 32): total instance size in bytes (vptr + fields)
    Slot 5 (offset 40): pointer to $_FieldCleanup_<T> for this class
    Slot 6 (offset 48): pointer to $vtable_<T> for this class

  Slots 4-6 are read by _ClassCreate(TInfo) to allocate, install the
  vtable, and arrange for ARC field cleanup on release — the runtime
  equivalent of the inline lowering EmitConstructorCall produces for
  the static 'TFoo.Create' form.

  TObject is the built-in root class; any user class with an explicit
  class(TObject, IFoo) parent list resolves Parent to TObject's
  TRecordTypeDesc, so we emit a typeinfo stub for TObject unconditionally
  to satisfy the linker.  Its parent slot is nil and its impllist slot
  is nil because TObject implements no interfaces.  TObject also gets
  a vtable stub and an empty field-cleanup function so its typeinfo
  can name them. }
var
  I, J, PubCount:  Integer;
  TD:              TTypeDecl;
  TDesc:           TTypeDesc;
  RT:              TRecordTypeDesc;
  GI:              TGenericInstance;
  CD:              TClassTypeDef;
  MD:              TMethodDecl;
  ParentStr:       string;
  ImplStr:         string;
  MethStr:         string;
  MName:           string;
  MethLine:        string;
begin
  EmitLine('data $typeinfo_TObject = { l 0, l 0, l ' +
           EmitClassNameRef('TObject') + ', l 0' +
           ', l 8, l $_FieldCleanup_TObject, l $vtable_TObject }');

  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    CD := TClassTypeDef(TD.Def);

    if RT.Parent <> nil then
      ParentStr := '$typeinfo_' + RT.Parent.Name
    else
      ParentStr := '0';
    if RT.ImplementsCount > 0 then
      ImplStr := '$impllist_' + TD.Name
    else
      ImplStr := '0';

    { Emit the published-method table if any methods are flagged.
      Each entry: l name-string-data-ptr, l method-code-ptr. }
    PubCount := 0;
    for J := 0 to CD.Methods.Count - 1 do
      if TMethodDecl(CD.Methods.Items[J]).IsPublished then
        Inc(PubCount);
    if PubCount > 0 then
    begin
      MethLine := 'data $methods_' + TD.Name + ' = { l ' + IntToStr(PubCount);
      for J := 0 to CD.Methods.Count - 1 do
      begin
        MD := TMethodDecl(CD.Methods.Items[J]);
        if not MD.IsPublished then Continue;
        MethLine := MethLine +
                    ', l ' + EmitClassNameRef(MD.Name) +
                    ', l $' + MethodEmitName(MD, TD.Name, MD.Name);
      end;
      MethLine := MethLine + ' }';
      EmitLine(MethLine);
      MethStr := '$methods_' + TD.Name;
    end
    else
      MethStr := '0';

    EmitLine('data $typeinfo_' + TD.Name +
             ' = { l ' + ParentStr + ', l ' + ImplStr +
             ', l ' + EmitClassNameRef(TD.Name) +
             ', l ' + MethStr +
             ', l ' + IntToStr(RT.TotalSize) +
             ', l $_FieldCleanup_' + TD.Name +
             ', l $vtable_' + TD.Name + ' }');
  end;

  { Generic instances — no published-method table emission yet (the
    type-name mangling makes deduplicating across instantiations
    finicky; revisit if a use case appears). }
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI    := TGenericInstance(AProg.GenericInstances.Items[I]);
    RT    := TRecordTypeDesc(GI.TypeDesc);
    MName := QBEMangle(GI.TypeName);
    if RT.Parent <> nil then
      ParentStr := '$typeinfo_' + QBEMangle(RT.Parent.Name)
    else
      ParentStr := '0';
    if RT.ImplementsCount > 0 then
      ImplStr := '$impllist_' + MName
    else
      ImplStr := '0';
    EmitLine('data $typeinfo_' + MName + ' = { l ' + ParentStr + ', l ' + ImplStr +
             ', l ' + EmitClassNameRef(GI.TypeName) + ', l 0' +
             ', l ' + IntToStr(RT.TotalSize) +
             ', l $_FieldCleanup_' + MName +
             ', l $vtable_' + MName + ' }');
  end;

  EmitLine('');
end;

procedure TCodeGenQBE.EmitVTableDefs(AProg: TProgram);
{ Vtable layout: slot 0 = $typeinfo_T pointer, slots 1..N = virtual method ptrs.
  Dispatch uses (VTableSlot + 1) * 8 to skip the typeinfo slot.
  TObject's vtable carries Destroy and ToString — referenced by every
  user class through inheritance and by the typeinfo's vtable slot.
  Abstract vtable slots point to $_AbstractMethodError (defined in the C
  RTL — blaise_arc_class.c — so program and unit IR can both reference it
  without duplicate-symbol conflicts at link time). }
var
  I, S:         Integer;
  TD:           TTypeDecl;
  TDesc:        TTypeDesc;
  RT:           TRecordTypeDesc;
  GI:           TGenericInstance;
  E:            TVTableEntry;
  Line:         string;
  MName:        string;
  ERef:         string;
begin
  EmitLine('data $vtable_TObject = { l $typeinfo_TObject' +
           ', l $TObject_Destroy, l $TObject_ToString }');
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
      E := RT.VTableEntryAt(S);
      if E.IsAbstract then
        ERef := ', l $_AbstractMethodError'
      else if (Length(E.ImplName) > 0) and (StrAt(E.ImplName, 0) = Ord('$')) then
        ERef := ', l $' + QBEMangle(StrCopyTail(E.ImplName, 1))
      else
        ERef := ', l ' + QBEMangle(E.ImplName);
      Line := Line + ERef;
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
      E := RT.VTableEntryAt(S);
      if E.IsAbstract then
        ERef := ', l $_AbstractMethodError'
      else if (Length(E.ImplName) > 0) and (StrAt(E.ImplName, 0) = Ord('$')) then
        ERef := ', l $' + QBEMangle(StrCopyTail(E.ImplName, 1))
      else
        ERef := ', l ' + QBEMangle(E.ImplName);
      Line := Line + ERef;
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
  MethRef:     string;
  IntfMangle:  string;
  GII:         TGenericInterfaceInstance;
  GI:          TGenericInstance;
  MName:       string;
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

    { One itab per interface — when a class's vtable slot for a given
      interface method is abstract (e.g. the class is an abstract base that
      declares the interface but defers implementation to subclasses), the
      itab entry must point at $_AbstractMethodError instead of the would-be
      symbol, which does not exist. }
    for J := 0 to ClassRT.ImplementsCount - 1 do
    begin
      IntfDesc   := ClassRT.ImplementsIntfAt(J);
      IntfMangle := QBEMangle(IntfDesc.Name);
      ItabLine   := 'data $itab_' + TD.Name + '_' + IntfMangle + ' = {';
      for K := 0 to IntfDesc.MethodCount - 1 do
      begin
        MethName := IntfDesc.MethodName(K);
        if IsAbstractClassMethod(ClassRT, MethName) then
          MethRef := '$_AbstractMethodError'
        else
          MethRef := '$' + TD.Name + '_' + MethName;
        if K = 0 then
          ItabLine := ItabLine + ' l ' + MethRef
        else
          ItabLine := ItabLine + ', l ' + MethRef;
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

  { Itab and impllist for generic class instances that implement interfaces }
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI      := TGenericInstance(AProg.GenericInstances.Items[I]);
    ClassRT := TRecordTypeDesc(GI.TypeDesc);
    if ClassRT.ImplementsCount = 0 then Continue;
    MName := QBEMangle(GI.TypeName);

    { One itab per interface }
    for J := 0 to ClassRT.ImplementsCount - 1 do
    begin
      IntfDesc   := ClassRT.ImplementsIntfAt(J);
      IntfMangle := QBEMangle(IntfDesc.Name);
      ItabLine   := 'data $itab_' + MName + '_' + IntfMangle + ' = {';
      for K := 0 to IntfDesc.MethodCount - 1 do
      begin
        MethName := IntfDesc.MethodName(K);
        if IsAbstractClassMethod(ClassRT, MethName) then
          MethRef := '$_AbstractMethodError'
        else
          MethRef := '$' + MName + '_' + MethName;
        if K = 0 then
          ItabLine := ItabLine + ' l ' + MethRef
        else
          ItabLine := ItabLine + ', l ' + MethRef;
      end;
      ItabLine := ItabLine + ' }';
      EmitLine(ItabLine);
    end;

    { One impllist per generic class instance }
    ImplLine := 'data $impllist_' + MName + ' = {';
    for J := 0 to ClassRT.ImplementsCount - 1 do
    begin
      IntfDesc   := ClassRT.ImplementsIntfAt(J);
      IntfMangle := QBEMangle(IntfDesc.Name);
      if J = 0 then
        ImplLine := ImplLine + ' l $typeinfo_' + IntfMangle +
                               ', l $itab_' + MName + '_' + IntfMangle
      else
        ImplLine := ImplLine + ', l $typeinfo_' + IntfMangle +
                               ', l $itab_' + MName + '_' + IntfMangle;
    end;
    ImplLine := ImplLine + ', l 0 }';
    EmitLine(ImplLine);
  end;

  EmitLine('');
end;

function TCodeGenQBE.IsAbstractClassMethod(ARec: TRecordTypeDesc;
                                           const AMethName: string): Boolean;
{ An interface method maps to one of ARec's vtable slots.  If that slot is
  flagged abstract (no concrete implementation on this class), itab/vtable
  emission must point at $_AbstractMethodError so linking succeeds.  The
  abstract class itself can never be instantiated, so the stub is
  statically unreachable; it exists purely to satisfy the linker. }
var
  Slot: Integer;
begin
  Slot := ARec.FindVTableSlot(AMethName);
  if Slot < 0 then
    Result := False
  else
    Result := ARec.VTableEntryAt(Slot).IsAbstract;
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
  functions by name; see the _ClassAlloc call in EmitExpr.
  TObject also gets a no-op stub so the typeinfo's fieldcleanup slot
  can name a real symbol — needed by _ClassCreate's runtime path. }
var
  I:     Integer;
  TD:    TTypeDecl;
  TDesc: TTypeDesc;
  RT:    TRecordTypeDesc;
  GI:    TGenericInstance;
begin
  EmitLine('function $_FieldCleanup_TObject(l %self) {');
  EmitLine('@start');
  EmitLine('  ret');
  EmitLine('}');
  EmitLine('');
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
  if ADecl.Body = nil then Exit;  { forward declaration — impl appears elsewhere }
  if ADecl.ResolvedQbeName <> '' then
    FuncName := '$' + QBEMangle(ADecl.ResolvedQbeName)
  else
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
        tyDouble:
          begin
            EmitLine(Format('  %%_var_%s =l alloc8 1', [Par.ParamName]));
            EmitLine(Format('  stored %%_par_%s, %%_var_%s',
              [Par.ParamName, Par.ParamName]));
          end;
        tySingle:
          begin
            EmitLine(Format('  %%_var_%s =l alloc4 1', [Par.ParamName]));
            EmitLine(Format('  stores %%_par_%s, %%_var_%s',
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
    else if RetQType = 'd' then
    begin
      EmitLine('  %_var_Result =l alloc8 1');
      EmitLine('  stored d_0, %_var_Result');
    end
    else if RetQType = 's' then
    begin
      EmitLine('  %_var_Result =l alloc4 1');
      EmitLine('  stores s_0, %_var_Result');
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
      if IsPromoted('Result') then
        EmitLine(Format('  %s =%s copy %%_var_Result', [RetTemp, RetQType]))
      else if RetQType = 'w' then
        EmitLine(Format('  %s =w loadw %%_var_Result', [RetTemp]))
      else if RetQType = 'd' then
        EmitLine(Format('  %s =d loadd %%_var_Result', [RetTemp]))
      else if RetQType = 's' then
        EmitLine(Format('  %s =s loads %%_var_Result', [RetTemp]))
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
  EmitFuncDef(ADecl, True);
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
  FPtrTemp:  string;
  I:         Integer;
begin
  { Indirect call through a procedural-typed variable: load the function
    pointer from the variable and call through it.  For 'of object' types
    the variable's slot is a 16-byte (Code, Data) block; load both halves
    and pass Data as the implicit first argument so the callee sees it as
    Self. }
  if ACall.IsIndirectCall then
  begin
    if TProceduralTypeDesc(ACall.ResolvedProcType).IsMethodPtr then
    begin
      { Method-pointer dispatch: Code at slot+0, Data at slot+8. }
      FPtrTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s',
        [FPtrTemp, VarRef(ACall.Name, ACall.IndirectCallIsGlobal)]));
      ArgTemp := AllocTemp;
      EmitLine(Format('  %s =l add %s, 8',
        [ArgTemp, VarRef(ACall.Name, ACall.IndirectCallIsGlobal)]));
      ArgTemp2 := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [ArgTemp2, ArgTemp]));
      ArgLine := Format('l %s', [ArgTemp2]);
    end
    else
    begin
      FPtrTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s',
        [FPtrTemp, VarRef(ACall.Name, ACall.IndirectCallIsGlobal)]));
      ArgLine := '';
    end;
    for I := 0 to ACall.Args.Count - 1 do
    begin
      if ArgLine <> '' then ArgLine := ArgLine + ', ';
      ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
      ArgTemp := CoerceArg(ArgTemp, TASTExpr(ACall.Args.Items[I]),
        QbeTypeOf(TProcParamInfo(
          TProceduralTypeDesc(ACall.ResolvedProcType).Params.Items[I]).TypeDesc));
      ArgLine := ArgLine + Format('%s %s',
        [QbeTypeOf(TProcParamInfo(
          TProceduralTypeDesc(ACall.ResolvedProcType).Params.Items[I]).TypeDesc),
         ArgTemp]);
    end;
    EmitLine(Format('  call %s(%s)', [FPtrTemp, ArgLine]));
    Exit;
  end;

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
        Par := TMethodParam(MDecl.Params.Items[I]);
        if Par.IsOpenArray then
        begin
          if TASTExpr(ACall.Args.Items[I]) is TArrayLiteralExpr then
          begin
            ArgTemp := EmitArrayLiteralExpr(TArrayLiteralExpr(TASTExpr(ACall.Args.Items[I])));
            ArgLine := ArgLine + Format(', l %s, l %d',
              [ArgTemp, TArrayLiteralExpr(TASTExpr(ACall.Args.Items[I])).Elements.Count - 1]);
          end
          else if TASTExpr(ACall.Args.Items[I]).ResolvedType.Kind = tyStaticArray then
          begin
            { Static array coerced to open-array: pass base ptr + compile-time high }
            ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
            ArgLine := ArgLine + Format(', l %s, l %d', [ArgTemp,
              TStaticArrayTypeDesc(TASTExpr(ACall.Args.Items[I]).ResolvedType).HighBound -
              TStaticArrayTypeDesc(TASTExpr(ACall.Args.Items[I]).ResolvedType).LowBound]);
          end
          else
          begin
            ArgTemp  := EmitExpr(TASTExpr(ACall.Args.Items[I]));
            ArgTemp2 := AllocTemp;
            EmitLine(Format('  %s =l loadl %%_var_%s_high',
              [ArgTemp2, TIdentExpr(TASTExpr(ACall.Args.Items[I])).Name]));
            ArgLine := ArgLine + Format(', l %s, l %s', [ArgTemp, ArgTemp2]);
          end;
        end
        else if Par.IsVarParam then
          ArgLine := ArgLine + Format(', l %s',
            [EmitLValueAddr(TASTExpr(ACall.Args.Items[I]))])
        else
        begin
          ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
          ArgTemp := CoerceArg(ArgTemp, TASTExpr(ACall.Args.Items[I]), QbeTypeOf(Par.ResolvedType));
          ArgLine := ArgLine + Format(', %s %s',
            [QbeTypeOf(Par.ResolvedType), ArgTemp]);
        end;
      end;
      EmitLine(Format('  call $%s(%s)',
        [MethodEmitName(MDecl, MDecl.OwnerTypeName, ACall.Name), ArgLine]));
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
        else if TASTExpr(ACall.Args.Items[I]).ResolvedType.Kind = tyStaticArray then
        begin
          { Static array coerced to open-array: pass base ptr + compile-time high }
          ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
          ArgLine := ArgLine + Format('l %s, l %d', [ArgTemp,
            TStaticArrayTypeDesc(TASTExpr(ACall.Args.Items[I]).ResolvedType).HighBound -
            TStaticArrayTypeDesc(TASTExpr(ACall.Args.Items[I]).ResolvedType).LowBound]);
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
          [EmitLValueAddr(TASTExpr(ACall.Args.Items[I]))])
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
        ArgTemp := CoerceArg(ArgTemp, TASTExpr(ACall.Args.Items[I]), QbeTypeOf(Par.ResolvedType));
        ArgLine := ArgLine + Format('%s %s', [QbeTypeOf(Par.ResolvedType), ArgTemp]);
      end;
    end;
    if MDecl.IsExternal and (MDecl.ExternalName <> '') then
      EmitLine(Format('  call $%s(%s)', [MDecl.ExternalName, ArgLine]))
    else if MDecl.ResolvedQbeName <> '' then
      EmitLine(Format('  call $%s(%s)', [QBEMangle(MDecl.ResolvedQbeName), ArgLine]))
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
    { Inc(x) / Inc(x, n) / Dec(x) / Dec(x, n) — in-place add/sub.
      For promoted locals the variable is an SSA temp (no memory address);
      use copy/add/sub instead of load/store. }
    if (TASTExpr(ACall.Args.Items[0]) is TIdentExpr) and
       not TIdentExpr(TASTExpr(ACall.Args.Items[0])).IsGlobal and
       IsPromoted(TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name) then
    begin
      { Promoted scalar local: read directly, compute, write directly }
      ArgTemp  := TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name;
      ArgTemp2 := AllocTemp;
      if (TASTExpr(ACall.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(ACall.Args.Items[0]).ResolvedType.Kind in [tyInt64, tyClass, tyPointer]) then
      begin
        EmitLine(Format('  %s =l copy %%_var_%s', [ArgTemp2, ArgTemp]));
        if ACall.Args.Count >= 2 then
          SizeTemp := EmitExpr(TASTExpr(ACall.Args.Items[1]))
        else
          SizeTemp := '1';
        ArgLine := AllocTemp;
        if UCaseName = 'INC' then
          EmitLine(Format('  %s =l add %s, %s', [ArgLine, ArgTemp2, SizeTemp]))
        else
          EmitLine(Format('  %s =l sub %s, %s', [ArgLine, ArgTemp2, SizeTemp]));
        EmitLine(Format('  %%_var_%s =l copy %s', [ArgTemp, ArgLine]));
      end
      else
      begin
        EmitLine(Format('  %s =w copy %%_var_%s', [ArgTemp2, ArgTemp]));
        if ACall.Args.Count >= 2 then
          SizeTemp := EmitExpr(TASTExpr(ACall.Args.Items[1]))
        else
          SizeTemp := '1';
        ArgLine := AllocTemp;
        if UCaseName = 'INC' then
          EmitLine(Format('  %s =w add %s, %s', [ArgLine, ArgTemp2, SizeTemp]))
        else
          EmitLine(Format('  %s =w sub %s, %s', [ArgLine, ArgTemp2, SizeTemp]));
        EmitLine(Format('  %%_var_%s =w copy %s', [ArgTemp, ArgLine]));
      end;
    end
    else
    begin
      { Stack-slot local or global: use address-based load/store }
      ArgTemp  := EmitLValueAddr(TASTExpr(ACall.Args.Items[0]));
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
    end;
  end
  else if UCaseName = 'INCLUDE' then
  begin
    { Include(S, elem): S := S or (1 shl ord(elem)) }
    ArgTemp  := EmitLValueAddr(TASTExpr(ACall.Args.Items[0]));
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
    ArgTemp  := EmitLValueAddr(TASTExpr(ACall.Args.Items[0]));
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
  else if UCaseName = 'REMOVEDIR' then
  begin
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[0]));
    EmitLine(Format('  call $_RemoveDir(l %s)', [ArgTemp]));
  end
  else if UCaseName = 'FORCEDIRECTORIES' then
  begin
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[0]));
    EmitLine(Format('  call $_ForceDirectories(l %s)', [ArgTemp]));
  end
  else if UCaseName = 'SLEEP' then
  begin
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[0]));
    EmitLine(Format('  call $_Sleep(w %s)', [ArgTemp]));
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
  else if UCaseName = 'DELETE' then
  begin
    { Delete(var S; Idx, Count) — string mutator. Emits:
        new := _StringDelete(loadl(addr), idx, count);
        addref new; release old; store new. }
    EmitStringMutator(ACall, '_StringDelete', 2);
  end
  else if UCaseName = 'SETLENGTH' then
  begin
    { SetLength(var S; N) — string or dynamic array resize. }
    if TASTExpr(ACall.Args.Items[0]).ResolvedType.Kind = tyDynArray then
      EmitDynArraySetLength(ACall)
    else
      EmitStringMutator(ACall, '_StringSetLength', 1);
  end
  else
    raise ECodeGenError.Create(Format(
      'Unknown procedure ''%s'' at line %d', [ACall.Name, ACall.Line]));
end;

procedure TCodeGenQBE.EmitStringMutator(ACall: TProcCall;
  const ARtlName: string; AExtraArgCount: Integer);
var
  Addr:     string;
  OldTemp:  string;
  NewTemp:  string;
  ArgLine:  string;
  Extra:    string;
  I:        Integer;
begin
  { Address of the string slot (works for plain idents, var params,
    implicit-Self fields).  Field-access targets (R.F or P^.F) are not
    supported here — semantic enforces the L-value forms we accept. }
  if TASTExpr(ACall.Args.Items[0]) is TIdentExpr then
    Addr := EmitVarArgAddr(TIdentExpr(TASTExpr(ACall.Args.Items[0])))
  else
    raise ECodeGenError.Create(
      'String mutator on non-ident receiver not yet supported');

  OldTemp := AllocTemp;
  EmitLine(Format('  %s =l loadl %s', [OldTemp, Addr]));

  ArgLine := Format('l %s', [OldTemp]);
  for I := 1 to AExtraArgCount do
  begin
    Extra := EmitExpr(TASTExpr(ACall.Args.Items[I]));
    ArgLine := ArgLine + Format(', w %s', [Extra]);
  end;

  NewTemp := AllocTemp;
  EmitLine(Format('  %s =l call $%s(%s)', [NewTemp, ARtlName, ArgLine]));
  EmitLine(Format('  call $_StringAddRef(l %s)', [NewTemp]));
  EmitLine(Format('  call $_StringRelease(l %s)', [OldTemp]));
  EmitLine(Format('  storel %s, %s', [NewTemp, Addr]));
end;

procedure TCodeGenQBE.EmitDynArraySetLength(ACall: TProcCall);
var
  Addr:    string;
  OldPtr:  string;
  NewPtr:  string;
  NTemp:   string;
  ElemSz:  Integer;
  DAT:     TDynArrayTypeDesc;
begin
  if not (TASTExpr(ACall.Args.Items[0]) is TIdentExpr) then
    raise ECodeGenError.Create(
      'SetLength on dynamic array: first argument must be a variable');
  Addr    := EmitVarArgAddr(TIdentExpr(TASTExpr(ACall.Args.Items[0])));
  OldPtr  := AllocTemp;
  EmitLine(Format('  %s =l loadl %s', [OldPtr, Addr]));
  NTemp   := EmitExpr(TASTExpr(ACall.Args.Items[1]));
  DAT     := TDynArrayTypeDesc(TASTExpr(ACall.Args.Items[0]).ResolvedType);
  ElemSz  := DAT.ElementType.RawSize;
  NewPtr  := AllocTemp;
  EmitLine(Format('  %s =l call $_DynArraySetLength(l %s, w %s, w %d)',
    [NewPtr, OldPtr, NTemp, ElemSz]));
  EmitLine(Format('  storel %s, %s', [NewPtr, Addr]));
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
  ArgExpr:  TASTExpr;
  ArgTemp:  string;
  IsString: Boolean;
  IsInt64:  Boolean;
  I:        Integer;
  StartIdx: Integer;
  FdLit:    string;
begin
  { bare WriteLn with no arguments — emit newline to stdout }
  if ACall.Args.Count = 0 then
  begin
    if ANewline then
      EmitLine('  call $_SysWriteNewline(w 1)');
    Exit;
  end;

  { Detect WriteLn(StdErr, ...) — first arg is the StdErr identifier (FD 2) }
  StartIdx := 0;
  FdLit    := '1';
  ArgExpr  := TASTExpr(ACall.Args.Items[0]);
  if (ArgExpr is TIdentExpr) and SameText(TIdentExpr(ArgExpr).Name, 'StdErr') then
  begin
    StartIdx := 1;
    FdLit    := '2';
  end;

  if StartIdx >= ACall.Args.Count then
  begin
    if ANewline then
      EmitLine(Format('  call $_SysWriteNewline(w %s)', [FdLit]));
    Exit;
  end;

  { Emit one _SysWrite* call per argument. }
  for I := StartIdx to ACall.Args.Count - 1 do
  begin
    ArgExpr  := TASTExpr(ACall.Args.Items[I]);
    IsString := (ArgExpr.ResolvedType <> nil) and ArgExpr.ResolvedType.IsString;
    ArgTemp  := EmitExpr(ArgExpr);
    if IsString then
      EmitLine(Format('  call $_SysWriteStr(w %s, l %s)', [FdLit, ArgTemp]))
    else
    begin
      IsInt64 := (ArgExpr.ResolvedType <> nil) and
                 (QbeTypeOf(ArgExpr.ResolvedType) = 'l');
      if IsInt64 then
        EmitLine(Format('  call $_SysWriteInt64(w %s, l %s)', [FdLit, ArgTemp]))
      else
        EmitLine(Format('  call $_SysWriteInt(w %s, w %s)', [FdLit, ArgTemp]));
    end;
  end;

  if ANewline then
    EmitLine(Format('  call $_SysWriteNewline(w %s)', [FdLit]));
end;

function TCodeGenQBE.EmitExpr(AExpr: TASTExpr): string;
var
  T, L, R, T2: string;
  Op:          string;
  BinExpr:     TBinaryExpr;
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
  Ptr2:         string;
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
        case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
          tyStaticArray:
            EmitLine(Format('  %s =w copy %d', [T,
              TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).HighBound]));
          tyString:
          begin
            { High(S) = Length(S) - 1; load length from ARC header at data_ptr-8 }
            L := EmitExpr(TASTExpr(FC.Args.Items[0]));
            R := AllocTemp;
            EmitLine(Format('  %s =l sub %s, 8', [R, L]));
            EmitLine(Format('  %s =w loadsw %s', [T, R]));
            R := AllocTemp;
            EmitLine(Format('  %s =w sub %s, 1', [R, T]));
            T := R;
          end;
        else
          begin
            { Open-array: load the high-index slot and truncate to Integer (w).
              QBE has no truncl; assigning an l value to a w temp implicitly truncates. }
            L := TIdentExpr(FC.Args.Items[0]).Name;
            R := AllocTemp;
            EmitLine(Format('  %s =l loadl %%_var_%s_high', [R, L]));
            EmitLine(Format('  %s =w copy %s', [T, R]));
          end;
        end;
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'Low') then
      begin
        T := AllocTemp;
        case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
          tyStaticArray:
            EmitLine(Format('  %s =w copy %d', [T,
              TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).LowBound]));
          tyString:
            EmitLine(Format('  %s =w copy 0', [T]));
        else
          EmitLine(Format('  %s =w copy 0', [T]));
        end;
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
          { PChar(str) — data-pointer convention: str_ptr IS the char data }
          Result := L;
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

      { Built-in string/array length }
      if SameText(FC.Name,'Length') then
      begin
        T := AllocTemp;
        case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
          tyStaticArray:
          begin
            { Compile-time constant: HighBound - LowBound + 1 }
            EmitLine(Format('  %s =w copy %d', [T,
              TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).HighBound -
              TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).LowBound + 1]));
          end;
          tyOpenArray:
          begin
            { Length = High + 1: load the _high slot then add 1 }
            L := TIdentExpr(FC.Args.Items[0]).Name;
            R := AllocTemp;
            EmitLine(Format('  %s =l loadl %%_var_%s_high', [R, L]));
            EmitLine(Format('  %s =w add %s, 1', [T, R]));
          end;
          tyDynArray:
          begin
            { Length stored at data_ptr − 4; nil ptr → length 0 }
            L := EmitExpr(TASTExpr(FC.Args.Items[0]));
            R := AllocTemp;
            EmitLine(Format('  %s =w call $_DynArrayLength(l %s)', [R, L]));
            EmitLine(Format('  %s =w copy %s', [T, R]));
          end;
        else
          { tyString: delegate to RTL }
          L := EmitExpr(TASTExpr(FC.Args.Items[0]));
          EmitLine(Format('  %s =w call $_StringLength(l %s)', [T, L]));
        end;
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

      if SameText(FC.Name,'PosEx') then
      begin
        L       := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R       := EmitExpr(TASTExpr(FC.Args.Items[1]));
        ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[2]));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_StringPosEx(l %s, l %s, w %s)',
          [T, L, R, ArgTemp]));
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

      if SameText(FC.Name,'Assigned') then
      begin
        { Assigned(P) ≡ P <> nil — emit a pointer comparison. }
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =w cnel %s, 0', [T, L]));
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

      if SameText(FC.Name,'DoubleToStr') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_DoubleToStr(d %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'SingleToStr') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_SingleToStr(s %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'StrToDouble') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =d call $_StrToDouble(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'Abs') then
      begin
        L   := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T   := AllocTemp;
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        case QType of
          'w': EmitLine(Format('  %s =w call $_AbsInt(w %s)',   [T, L]));
          'l': EmitLine(Format('  %s =l call $_AbsInt64(l %s)', [T, L]));
          'd': EmitLine(Format('  %s =d call $fabs(d %s)',      [T, L]));
          's': EmitLine(Format('  %s =s call $fabsf(s %s)',     [T, L]));
        else   EmitLine(Format('  %s =w call $_AbsInt(w %s)',   [T, L]));
        end;
        Result := T;
        Exit;
      end;

      { Math builtins — Sqrt, Ceil, Floor, Round, Trunc, Ln, Log2, Log10,
        Power, Sin, Cos, Tan, ArcTan, ArcTan2, IsNaN, IsInfinite.
        These are compiler builtins so that:
          - Ceil/Floor/Round/Trunc can emit dtosi (double→int) directly.
          - Sin/Cos/Tan/ArcTan dispatch to *f variants for Single args.
        Min/Max/Sign/DivMod/InRange/EnsureRange live in math.pas RTL. }

      if SameText(FC.Name, 'Sqrt') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $sqrtf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $sqrt(d %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name, 'Ceil') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        R := AllocTemp;
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
        begin
          EmitLine(Format('  %s =s call $ceilf(s %s)', [T, L]));
          EmitLine(Format('  %s =w stosi %s', [R, T]));
        end
        else
        begin
          EmitLine(Format('  %s =d call $ceil(d %s)', [T, L]));
          EmitLine(Format('  %s =w dtosi %s', [R, T]));
        end;
        Result := R;
        Exit;
      end;

      if SameText(FC.Name, 'Floor') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        R := AllocTemp;
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
        begin
          EmitLine(Format('  %s =s call $floorf(s %s)', [T, L]));
          EmitLine(Format('  %s =w stosi %s', [R, T]));
        end
        else
        begin
          EmitLine(Format('  %s =d call $floor(d %s)', [T, L]));
          EmitLine(Format('  %s =w dtosi %s', [R, T]));
        end;
        Result := R;
        Exit;
      end;

      if SameText(FC.Name, 'Trunc') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =w stosi %s', [T, L]))
        else
          EmitLine(Format('  %s =w dtosi %s', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name, 'Round') then
      begin
        { Round half-away from zero: C99 round() rounds .5 away from zero,
          matching the behaviour of Delphi/FPC Round(). }
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        R := AllocTemp;
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
        begin
          EmitLine(Format('  %s =s call $roundf(s %s)', [T, L]));
          EmitLine(Format('  %s =w stosi %s', [R, T]));
        end
        else
        begin
          EmitLine(Format('  %s =d call $round(d %s)', [T, L]));
          EmitLine(Format('  %s =w dtosi %s', [R, T]));
        end;
        Result := R;
        Exit;
      end;

      if SameText(FC.Name, 'Ln') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $logf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $log(d %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name, 'Log2') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $log2f(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $log2(d %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name, 'Log10') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $log10f(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $log10(d %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name, 'Power') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp;
        EmitLine(Format('  %s =d call $pow(d %s, d %s)', [T, L, R]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name, 'Sin') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $sinf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $sin(d %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name, 'Cos') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $cosf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $cos(d %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name, 'Tan') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $tanf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $tan(d %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name, 'ArcTan') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $atanf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $atan(d %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name, 'ArcTan2') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp;
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $atan2f(s %s, s %s)', [T, L, R]))
        else
          EmitLine(Format('  %s =d call $atan2(d %s, d %s)', [T, L, R]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name, 'IsNaN') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =w call $__isnanf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =w call $__isnan(d %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name, 'IsInfinite') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =w call $__isinff(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =w call $__isinf(d %s)', [T, L]));
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

      if SameText(FC.Name,'MethodAddress') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_MethodAddress(l %s, l %s)', [T, L, R]));
        Result := T;
        Exit;
      end;

      { ClassCreate(Cls, ...args): runtime equivalent of TFoo.Create(args).
        Allocates via _ClassCreate (which reads totalsize/fieldcleanup/vtable
        from Cls's typeinfo), then calls $<BaseClass>_Create statically with
        the new pointer and the supplied args.  Returns the new pointer. }
      if SameText(FC.Name,'ClassCreate') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));   { metaclass = typeinfo ptr }
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_ClassCreate(l %s)', [T, L]));
        if FC.ResolvedDecl <> nil then
        begin
          MDecl := TMethodDecl(FC.ResolvedDecl);
          ArgLine := Format('l %s', [T]);
          for I := 1 to FC.Args.Count - 1 do
          begin
            Par     := TMethodParam(MDecl.Params.Items[I - 1]);
            ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[I]));
            ArgTemp := CoerceArg(ArgTemp, TASTExpr(FC.Args.Items[I]),
              QbeTypeOf(Par.ResolvedType));
            ArgLine := ArgLine + Format(', %s %s',
              [QbeTypeOf(Par.ResolvedType), ArgTemp]);
          end;
          EmitLine(Format('  call $%s(%s)',
            [MethodEmitName(MDecl, MDecl.OwnerTypeName, 'Create'), ArgLine]));
        end;
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
        { String/char arg: get ordinal of first byte via OrdAt(str, 0) }
        { Enum/integer arg: already an integer — just copy }
        if TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyString then
          EmitLine(Format('  %s =w call $_OrdAt(l %s, w 0)', [T, L]))
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
        if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
           TASTExpr(FC.Args.Items[0]).ResolvedType.IsString then
        begin
          T := AllocTemp;
          EmitLine(Format('  %s =w call $_OrdAt(l %s, w 0)', [T, L]));
          L := T;
        end;
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

      if SameText(FC.Name,'GetProcessID') then
      begin
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_GetProcessID()', [T]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'GetTempDir') then
      begin
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_GetTempDir()', [T]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'GetCurrentDir') then
      begin
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_GetCurrentDir()', [T]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'GetTempFileName') then
      begin
        L       := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R       := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_GetTempFileName(l %s, l %s)', [T, L, R]));
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

      if SameText(FC.Name,'DirectoryExists') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_DirectoryExists(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'ForceDirectories') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_ForceDirectories(l %s)', [T, L]));
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

      if SameText(FC.Name,'ExtractFileDir') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_ExtractFileDir(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'ExtractFileExt') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_ExtractFileExt(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'ExcludeTrailingPathDelimiter') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $_ExcludeTrailingPathDelimiter(l %s)', [T, L]));
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

      if SameText(FC.Name,'RenameFile') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_RenameFile(l %s, l %s)',
          [T, L, EmitExpr(TASTExpr(FC.Args.Items[1]))]));
        Result := T;
        Exit;
      end;

      if SameText(FC.Name,'SetCurrentDir') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp;
        EmitLine(Format('  %s =w call $_SetCurrentDir(l %s)', [T, L]));
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

      { Indirect call through a procedural-typed variable: F() / F(args)
        where F is declared 'var F: TProcType'.  Load the function pointer
        from F and call through it.  Must precede the ResolvedDecl=nil
        type-cast branch below — indirect calls also have ResolvedDecl=nil. }
      if FC.IsIndirectCall then
      begin
        if TProceduralTypeDesc(FC.ResolvedProcType).IsMethodPtr then
        begin
          { Method-pointer dispatch: 16-byte slot.  Code at +0, Data at +8;
            pass Data as the implicit first arg. }
          FPtrTemp := AllocTemp;
          EmitLine(Format('  %s =l loadl %s',
            [FPtrTemp, VarRef(FC.Name, FC.IndirectCallIsGlobal)]));
          ArgTemp := AllocTemp;
          EmitLine(Format('  %s =l add %s, 8',
            [ArgTemp, VarRef(FC.Name, FC.IndirectCallIsGlobal)]));
          T := AllocTemp;
          EmitLine(Format('  %s =l loadl %s', [T, ArgTemp]));
          ArgLine := Format('l %s', [T]);
        end
        else
        begin
          FPtrTemp := AllocTemp;
          EmitLine(Format('  %s =l loadl %s',
            [FPtrTemp, VarRef(FC.Name, FC.IndirectCallIsGlobal)]));
          ArgLine := '';
        end;
        for I := 0 to FC.Args.Count - 1 do
        begin
          if ArgLine <> '' then ArgLine := ArgLine + ', ';
          ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[I]));
          ArgTemp := CoerceArg(ArgTemp, TASTExpr(FC.Args.Items[I]),
            QbeTypeOf(TProcParamInfo(
              TProceduralTypeDesc(FC.ResolvedProcType).Params.Items[I]).TypeDesc));
          ArgLine := ArgLine + Format('%s %s',
            [QbeTypeOf(TProcParamInfo(
              TProceduralTypeDesc(FC.ResolvedProcType).Params.Items[I]).TypeDesc),
             ArgTemp]);
        end;
        if TProceduralTypeDesc(FC.ResolvedProcType).ReturnType = nil then
        begin
          { procedure call — no result temp }
          EmitLine(Format('  call %s(%s)', [FPtrTemp, ArgLine]));
          Result := '';
        end
        else
        begin
          QType  := QbeTypeOf(TProceduralTypeDesc(FC.ResolvedProcType).ReturnType);
          T      := AllocTemp;
          EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FPtrTemp, ArgLine]));
          Result := T;
        end;
        Exit;
      end;

      { Type cast TypeName(Expr) — ResolvedDecl is nil; copy/extend/truncate to target QBE type }
      if FC.ResolvedDecl = nil then
      begin
        ArgTemp  := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T        := AllocTemp;
        QType    := QbeTypeOf(FC.ResolvedType);
        if FC.ResolvedType.Kind = tyByte then
          { Byte(X): truncate to 8 bits — mask to [0..255] }
          EmitLine(Format('  %s =w and %s, 255', [T, ArgTemp]))
        else if QType = 'w' then
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
        FuncName := '$' + MethodEmitName(MDecl, MDecl.OwnerTypeName, FC.Name);
        for I := 0 to FC.Args.Count - 1 do
        begin
          Par := TMethodParam(MDecl.Params.Items[I]);
          if Par.IsOpenArray then
          begin
            if TASTExpr(FC.Args.Items[I]) is TArrayLiteralExpr then
            begin
              ArgTemp := EmitArrayLiteralExpr(TArrayLiteralExpr(TASTExpr(FC.Args.Items[I])));
              ArgLine := ArgLine + Format(', l %s, l %d',
                [ArgTemp, TArrayLiteralExpr(TASTExpr(FC.Args.Items[I])).Elements.Count - 1]);
            end
            else if TASTExpr(FC.Args.Items[I]).ResolvedType.Kind = tyStaticArray then
            begin
              { Static array coerced to open-array: pass base ptr + compile-time high }
              ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[I]));
              ArgLine := ArgLine + Format(', l %s, l %d', [ArgTemp,
                TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[I]).ResolvedType).HighBound -
                TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[I]).ResolvedType).LowBound]);
            end
            else
            begin
              ArgTemp  := EmitExpr(TASTExpr(FC.Args.Items[I]));
              ArgTemp2 := AllocTemp;
              EmitLine(Format('  %s =l loadl %%_var_%s_high',
                [ArgTemp2, TIdentExpr(TASTExpr(FC.Args.Items[I])).Name]));
              ArgLine := ArgLine + Format(', l %s, l %s', [ArgTemp, ArgTemp2]);
            end;
          end
          else if Par.IsVarParam then
            ArgLine := ArgLine + Format(', l %s',
              [EmitLValueAddr(TASTExpr(FC.Args.Items[I]))])
          else
          begin
            ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[I]));
            ArgTemp := CoerceArg(ArgTemp, TASTExpr(FC.Args.Items[I]), QbeTypeOf(Par.ResolvedType));
            ArgLine := ArgLine + Format(', %s %s',
              [QbeTypeOf(Par.ResolvedType), ArgTemp]);
          end;
        end;
        T := AllocTemp;
        EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FuncName, ArgLine]));
        Result := T;
        Exit;
      end;
      if MDecl.IsExternal and (MDecl.ExternalName <> '') then
        FuncName := '$' + MDecl.ExternalName
      else if MDecl.ResolvedQbeName <> '' then
        FuncName := '$' + QBEMangle(MDecl.ResolvedQbeName)
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
          else if TASTExpr(FC.Args.Items[I]).ResolvedType.Kind = tyStaticArray then
          begin
            { Static array coerced to open-array: pass base ptr + compile-time high }
            ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[I]));
            ArgLine := ArgLine + Format('l %s, l %d', [ArgTemp,
              TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[I]).ResolvedType).HighBound -
              TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[I]).ResolvedType).LowBound]);
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
            [EmitLValueAddr(TASTExpr(FC.Args.Items[I]))])
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
      { Evaluate arguments: use var-param flags stored on the interface desc }
      ArgLine := Format('l %s', [SelfTemp]);
      for I := 0 to MCallExpr.Args.Count - 1 do
      begin
        if IntfDesc.MethodParamIsVar(IntfDesc.MethodIndex(MCallExpr.Name), I) then
          ArgLine := ArgLine + Format(', l %s',
            [EmitLValueAddr(TASTExpr(MCallExpr.Args.Items[I]))])
        else
        begin
          ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Items[I]));
          if (TASTExpr(MCallExpr.Args.Items[I]).ResolvedType <> nil) and
             (TASTExpr(MCallExpr.Args.Items[I]).ResolvedType.Kind in
               [tyPointer, tyClass, tyInterface, tyPChar, tyString]) then
            ArgLine := ArgLine + Format(', l %s', [ArgTemp])
          else
            ArgLine := ArgLine + Format(', w %s', [ArgTemp]);
        end;
      end;
      QType := QbeTypeOf(MCallExpr.ResolvedType);
      if QType = '' then QType := 'w';
      T := AllocTemp;
      EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FPtrTemp, ArgLine]));
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
          ArgTemp := CoerceArg(ArgTemp, TASTExpr(MCallExpr.Args.Items[I]),
            QbeTypeOf(Par.ResolvedType));
          ArgLine := ArgLine + Format(', %s %s', [QbeTypeOf(Par.ResolvedType), ArgTemp]);
        end;
        if MDecl.OwnerTypeName <> '' then
          FuncName := '$' + MethodEmitName(MDecl, MDecl.OwnerTypeName, MCallExpr.Name)
        else
          FuncName := '$' + MethodEmitName(MDecl, RT.Name, MCallExpr.Name);
        EmitLine(Format('  call %s(%s)', [FuncName, ArgLine]));
      end;
      Result := SelfTemp;
      Exit;
    end;

    { Built-in InheritsFrom: calls $_InheritsFrom(child_ti, parent_ti).
      Receiver is a typeinfo pointer (Pointer/metaclass var, or class instance);
      argument is any expression that produces a typeinfo pointer. }
    if MCallExpr.IsBuiltinInheritsFrom then
    begin
      { Load the receiver typeinfo pointer }
      if MCallExpr.ObjExpr <> nil then
        SelfTemp := EmitExpr(MCallExpr.ObjExpr)  { already a typeinfo ptr }
      else if MCallExpr.IsVarParam then
      begin
        FPtrTemp := AllocTemp;
        SelfTemp := AllocTemp;
        EmitLine(Format('  %s =l loadl %%_var_%s', [FPtrTemp, MCallExpr.ObjectName]));
        EmitLine(Format('  %s =l loadl %s', [SelfTemp, FPtrTemp]));
      end
      else
      begin
        SelfTemp := AllocTemp;
        EmitLine(Format('  %s =l loadl %s',
          [SelfTemp, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)]));
      end;
      { For a class instance receiver, load typeinfo from vtable[0] }
      if (MCallExpr.ResolvedClassType <> nil) and
         (MCallExpr.ResolvedClassType.Kind = tyClass) then
      begin
        VTblTemp := AllocTemp;
        Ptr      := AllocTemp;
        EmitLine(Format('  %s =l loadl %s', [VTblTemp, SelfTemp]));
        EmitLine(Format('  %s =l loadl %s', [Ptr, VTblTemp]));
        SelfTemp := Ptr;
      end;
      { Evaluate the argument — a class ref or Pointer variable }
      ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Items[0]));
      T := AllocTemp;
      EmitLine(Format('  %s =w call $_InheritsFrom(l %s, l %s)',
        [T, SelfTemp, ArgTemp]));
      Result := T;
      Exit;
    end;

    { Built-in TObject.ToString: virtual dispatch through vtable slot 1.
      Loads the object pointer, reads its vtable, reads slot 1 (ToString),
      calls through it with just Self, returns a string (QBE type l). }
    if MCallExpr.IsBuiltinToString then
    begin
      if MCallExpr.ObjExpr <> nil then
        SelfTemp := EmitExpr(MCallExpr.ObjExpr)
      else if MCallExpr.IsVarParam then
      begin
        FPtrTemp := AllocTemp;
        SelfTemp := AllocTemp;
        EmitLine(Format('  %s =l loadl %%_var_%s', [FPtrTemp, MCallExpr.ObjectName]));
        EmitLine(Format('  %s =l loadl %s', [SelfTemp, FPtrTemp]));
      end
      else
      begin
        SelfTemp := AllocTemp;
        EmitLine(Format('  %s =l loadl %s',
          [SelfTemp, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)]));
      end;
      VTblTemp := AllocTemp;
      FPtrTemp := AllocTemp;
      ArgTemp  := AllocTemp;
      T        := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [VTblTemp, SelfTemp]));
      EmitLine(Format('  %s =l add %s, 16', [ArgTemp, VTblTemp]));
      EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
      EmitLine(Format('  %s =l call %s(l %s)', [T, FPtrTemp, SelfTemp]));
      Result := T;
      Exit;
    end;

    MDecl     := TMethodDecl(MCallExpr.ResolvedMethod);
    if MDecl.OwnerTypeName <> '' then
      FuncName := '$' + MethodEmitName(MDecl, MDecl.OwnerTypeName, MCallExpr.Name)
    else
      FuncName := '$' + MethodEmitName(MDecl, RT.Name, MCallExpr.Name);
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
          [EmitLValueAddr(TASTExpr(MCallExpr.Args.Items[I]))])
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Items[I]));
        ArgTemp := CoerceArg(ArgTemp, TASTExpr(MCallExpr.Args.Items[I]),
          QbeTypeOf(Par.ResolvedType));
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
    if (TIntLiteral(AExpr).Value < -2147483648) or (TIntLiteral(AExpr).Value > 2147483647) then
      EmitLine(Format('  %s =l copy %s', [T, IntToStr(TIntLiteral(AExpr).Value)]))
    else
      EmitLine(Format('  %s =w copy %s', [T, IntToStr(TIntLiteral(AExpr).Value)]));
    Result := T;
  end
  else if AExpr is TFloatLiteral then
  begin
    T := AllocTemp;
    { QBE float literal syntax: d_3.14 for double, s_3.14 for single.
      The type is always Double for unadorned float literals. }
    EmitLine(Format('  %s =d copy d_%s', [T, TFloatLiteral(AExpr).Value]));
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

    { Built-in: Obj.ClassName — load vtable ptr → typeinfo ptr → name slot (offset 16) }
    if FldAccess.IsClassNameAccess then
    begin
      { Step 1: load the class instance pointer }
      if FldAccess.Base <> nil then
        L := EmitExpr(FldAccess.Base)
      else
        begin
          T := AllocTemp;
          EmitLine(Format('  %s =l loadl %s',
            [T, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
          L := T;
        end;
      { Step 2: load vtable pointer from instance[0] }
      T := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [T, L]));
      { Step 3: load typeinfo from vtable[0] }
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [Ptr, T]));
      { Step 4: load nameptr from typeinfo[16] (third slot) }
      T := AllocTemp;
      EmitLine(Format('  %s =l add %s, 16', [T, Ptr]));
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [Ptr, T]));
      Result := Ptr;
      Exit;
    end;

    { Built-in: Obj.ClassType — returns the typeinfo pointer (the value
      stored at vtable[0]).  Two indirections: instance → vtable → typeinfo. }
    if FldAccess.IsClassTypeAccess then
    begin
      if FldAccess.Base <> nil then
        L := EmitExpr(FldAccess.Base)
      else
      begin
        T := AllocTemp;
        EmitLine(Format('  %s =l loadl %s',
          [T, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
        L := T;
      end;
      { vtable pointer at instance[0] }
      T := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [T, L]));
      { typeinfo pointer at vtable[0] }
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [Ptr, T]));
      Result := Ptr;
      Exit;
    end;

    { Built-in: Obj.ToString — virtual dispatch via vtable slot 1.
      vtable[0]=typeinfo, vtable[1]=Destroy, vtable[2]=ToString → offset 16. }
    if FldAccess.IsBuiltinToString then
    begin
      if FldAccess.Base <> nil then
        L := EmitExpr(FldAccess.Base)
      else
      begin
        T := AllocTemp;
        EmitLine(Format('  %s =l loadl %s',
          [T, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
        L := T;
      end;
      VTblTemp := AllocTemp;
      FPtrTemp := AllocTemp;
      ArgTemp  := AllocTemp;
      T        := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [VTblTemp, L]));
      EmitLine(Format('  %s =l add %s, 16', [ArgTemp, VTblTemp]));
      EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
      EmitLine(Format('  %s =l call %s(l %s)', [T, FPtrTemp, L]));
      Result := T;
      Exit;
    end;

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
          EmitLine(Format('  call $%s(l %s, l %s)',
            [MethodEmitName(MDecl, MDecl.OwnerTypeName, FldAccess.FieldName),
             SretBuf, L]));
          Result := SretBuf;
        end
        else
        begin
          QType := QbeTypeOf(MDecl.ResolvedReturnType);
          T := AllocTemp;
          EmitLine(Format('  %s =%s call $%s(l %s)',
            [T, QType,
             MethodEmitName(MDecl, MDecl.OwnerTypeName, FldAccess.FieldName), L]));
          Result := T;
        end;
        Exit;
      end;
      L := EmitInstancePtr(FldAccess.Base);
      { Method-backed property read (indexed or non-indexed).
        When FieldInfo is also non-nil, load the field value first — the getter
        runs on the field's object, not the chained base. }
      if FldAccess.PropRead <> nil then
      begin
        if FldAccess.FieldInfo <> nil then
        begin
          Ptr := AllocTemp;
          if FldAccess.FieldInfo.Offset > 0 then
            EmitLine(Format('  %s =l add %s, %d', [Ptr, L, FldAccess.FieldInfo.Offset]))
          else
            Ptr := L;
          L := AllocTemp;
          EmitLine(Format('  %s =l loadl %s', [L, Ptr]));
        end;
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
          EmitLine(Format('  call $%s(l %s, l %s)',
            [MethodEmitName(MDecl, MDecl.OwnerTypeName, FldAccess.FieldName),
             SretBuf, L]));
          Result := SretBuf;
        end
        else
        begin
          QType := QbeTypeOf(MDecl.ResolvedReturnType);
          T := AllocTemp;
          EmitLine(Format('  %s =%s call $%s(l %s)',
            [T, QType,
             MethodEmitName(MDecl, MDecl.OwnerTypeName, FldAccess.FieldName), L]));
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
        if MDecl.VTableSlot >= 0 then
        begin
          { Virtual dispatch: load vptr, then load function pointer from
            vtable[(VTableSlot+1)*8] (slot 0 is reserved for typeinfo). }
          VTblTemp := AllocTemp;
          FPtrTemp := AllocTemp;
          SlotOff  := (MDecl.VTableSlot + 1) * 8;
          ArgTemp  := AllocTemp;
          EmitLine(Format('  %s =l loadl %s', [VTblTemp, L]));
          EmitLine(Format('  %s =l add %s, %d', [ArgTemp, VTblTemp, SlotOff]));
          EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
          EmitLine(Format('  %s =%s call %s(l %s)', [T, QType, FPtrTemp, L]));
        end
        else
          EmitLine(Format('  %s =%s call $%s_%s(l %s)',
            [T, QType, MDecl.OwnerTypeName, FldAccess.FieldName, L]));
        Result := T;
      end;
    end
    else if FldAccess.IsInterfaceCall then
    begin
      { Zero-arg method call through interface itab: M.GetCount where M: IFoo }
      IntfDesc := TInterfaceTypeDesc(FldAccess.ResolvedClassType);
      SelfTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s_obj',
        [SelfTemp, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
      VTblTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s_itab',
        [VTblTemp, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
      SlotOff  := IntfDesc.MethodIndex(FldAccess.FieldName) * 8;
      FPtrTemp := AllocTemp;
      if SlotOff = 0 then
        EmitLine(Format('  %s =l loadl %s', [FPtrTemp, VTblTemp]))
      else
      begin
        ArgTemp := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', [ArgTemp, VTblTemp, SlotOff]));
        EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
      end;
      QType := QbeTypeOf(FldAccess.ResolvedType);
      T := AllocTemp;
      EmitLine(Format('  %s =%s call %s(l %s)', [T, QType, FPtrTemp, SelfTemp]));
      Result := T;
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
        { Int64-safe: see comment at TIdentExpr ConstValue emission. }
        EmitLine(Format('  %s =w copy %s', [T, IntToStr(FldAccess.ConstValue)]));
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
    else if FldAccess.IsCharAccess then
    begin
      { String field subscript: Rec.Field[N] (1-based) — load field, then read byte at N-1. }
      L := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
      if FldAccess.FieldInfo.Offset > 0 then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', [Ptr, L, FldAccess.FieldInfo.Offset]));
        L := Ptr;
      end;
      { Load the string pointer (the field value) }
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [Ptr, L]));
      { Compute 0-based byte offset: idx - 1 }
      T := EmitExpr(FldAccess.PropIndexExpr);
      IdxTemp := AllocTemp;
      EmitLine(Format('  %s =l extsw %s', [IdxTemp, T]));
      Ptr2    := AllocTemp;
      EmitLine(Format('  %s =l sub %s, 1', [Ptr2, IdxTemp]));
      IdxTemp := AllocTemp;
      EmitLine(Format('  %s =l add %s, %s', [IdxTemp, Ptr, Ptr2]));
      T := AllocTemp;
      EmitLine(Format('  %s =w loadub %s', [T, IdxTemp]));
      Result := T;
    end
    else if FldAccess.PropRead <> nil then
    begin
      { Method-backed property read: load Self pointer and call getter.
        When FieldInfo is also non-nil, the getter is on a field of the record
        (e.g. Rec.Field[I]) — load the field first, then use that as Self. }
      L := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
      if FldAccess.FieldInfo <> nil then
      begin
        { Load the field value to get the actual object the getter is called on }
        Ptr := AllocTemp;
        if FldAccess.FieldInfo.Offset > 0 then
          EmitLine(Format('  %s =l add %s, %d', [Ptr, L, FldAccess.FieldInfo.Offset]))
        else
          Ptr := L;
        L := AllocTemp;
        EmitLine(Format('  %s =l loadl %s', [L, Ptr]));
      end;
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
      if FldAccess.IsVarParam then
      begin
        { Var-record param: dereference the param slot to get the actual record
          address, then add field offset. }
        L := AllocTemp;
        EmitLine(Format('  %s =l loadl %s',
          [L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
        if FldAccess.FieldInfo.Offset > 0 then
        begin
          Ptr := AllocTemp;
          EmitLine(Format('  %s =l add %s, %d',
            [Ptr, L, FldAccess.FieldInfo.Offset]));
        end
        else
          Ptr := L;
      end
      else
        Ptr := FieldPtr(FldAccess.RecordName, FldAccess.FieldInfo.Offset, FldAccess.IsGlobal);
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
    else if TIdentExpr(AExpr).IsMetaclassRef then
    begin
      { Bare class type identifier used as a value: emit the typeinfo address.
        This is the same pointer that vtable[0] holds at runtime, so
        identity comparisons against Obj.ClassType return true for instances
        of that exact class.  See language-rationale.adoc § Metaclass refs. }
      EmitLine(Format('  %s =l copy $typeinfo_%s',
        [T, QBEMangle(TIdentExpr(AExpr).Name)]));
    end
    else if TIdentExpr(AExpr).IsConstant and
            ((AExpr.ResolvedType = nil) or
             (AExpr.ResolvedType.Kind <> tyStaticArray)) then
    begin
      if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyString) then
      begin
        { String constant — emit as a string literal data label (l-typed pointer) }
        StrLabel := EmitStrLit(TIdentExpr(AExpr).ConstString);
        EmitLine(Format('  %s =l copy %s', [T, StrLabel]));
      end
      else if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyDouble) then
        { Float constant stored as text in ConstString }
        EmitLine(Format('  %s =d copy d_%s', [T, TIdentExpr(AExpr).ConstString]))
      else if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tySingle) then
        EmitLine(Format('  %s =s copy s_%s', [T, TIdentExpr(AExpr).ConstString]))
      else if (AExpr.ResolvedType <> nil) and
              (QbeTypeOf(AExpr.ResolvedType) = 'l') then
        EmitLine(Format('  %s =l copy %s', [T, IntToStr(TIdentExpr(AExpr).ConstValue)]))
      else
        { Use IntToStr (Int64-aware) instead of %d to avoid the
          self-hosted Format runtime truncating Int64 args to int32. }
        EmitLine(Format('  %s =w copy %s', [T, IntToStr(TIdentExpr(AExpr).ConstValue)]));
    end
    else if TIdentExpr(AExpr).IsVarParam and
            (AExpr.ResolvedType <> nil) and
            (AExpr.ResolvedType.Kind in [tyRecord, tyStaticArray]) then
    begin
      { Var param of aggregate type: the param slot already holds the address
        of the caller's storage — load and return that as the storage address. }
      EmitLine(Format('  %s =l loadl %%_var_%s', [T, TIdentExpr(AExpr).Name]));
      Result := T;
      Exit;
    end
    else if TIdentExpr(AExpr).IsVarParam then
    begin
      { Var param of scalar type: load pointer, then dereference to get value }
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
    else if not TIdentExpr(AExpr).IsGlobal and
            IsPromoted(TIdentExpr(AExpr).Name) then
    begin
      { mem2reg: promoted local — the temp already holds the value; just copy. }
      QType := PromotedType(TIdentExpr(AExpr).Name);
      EmitLine(Format('  %s =%s copy %%_var_%s', [T, QType, TIdentExpr(AExpr).Name]));
    end
    else
    begin
      QType := QbeTypeOf(AExpr.ResolvedType);
      case QType of
        'w': EmitLine(Format('  %s =w loadw %s',
               [T, VarRef(TIdentExpr(AExpr).Name, TIdentExpr(AExpr).IsGlobal)]));
        'd': EmitLine(Format('  %s =d loadd %s',
               [T, VarRef(TIdentExpr(AExpr).Name, TIdentExpr(AExpr).IsGlobal)]));
        's': EmitLine(Format('  %s =s loads %s',
               [T, VarRef(TIdentExpr(AExpr).Name, TIdentExpr(AExpr).IsGlobal)]));
      else
        EmitLine(Format('  %s =l loadl %s',
          [T, VarRef(TIdentExpr(AExpr).Name, TIdentExpr(AExpr).IsGlobal)]));
      end;
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
        { Extend w operands to l before the l-typed instruction. }
        if (BinExpr.Left.ResolvedType = nil) or (BinExpr.Left.ResolvedType.Kind <> tyInt64) then
        begin
          ArgTemp := AllocTemp;
          EmitLine(Format('  %s =l extsw %s', [ArgTemp, L]));
          L := ArgTemp;
        end;
        if (BinExpr.Right.ResolvedType = nil) or (BinExpr.Right.ResolvedType.Kind <> tyInt64) then
        begin
          ArgTemp := AllocTemp;
          EmitLine(Format('  %s =l extsw %s', [ArgTemp, R]));
          R := ArgTemp;
        end;
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
      like "(P <> nil) and P.IsX".
      We use a QBE phi node at the join block so that no alloc4/storew/loadw
      memory slot is needed.  alloc4 inside loop bodies caused the stack
      pointer to drift on every iteration (QBE emits a dynamic sub %rsp per
      non-@start alloc), eventually overwriting parent exception frames. }
    if (BinExpr.Op = boAnd) or (BinExpr.Op = boOr) then
    begin
      FuncName := AllocLabel('sc_rhs');
      ArgLine  := AllocLabel('sc_end');
      L := EmitExpr(BinExpr.Left);
      { Record the label of the block from which LHS falls through to @sc_end
        (used by the phi).  We need the label of the CURRENT block — the last
        @label emitted is our predecessor.  FCurrentBlockLabel tracks this. }
      ArgTemp  := FCurrentBlockLabel;   { predecessor label for phi's LHS arm }
      if BinExpr.Op = boAnd then
        EmitLine(Format('  jnz %s, @%s, @%s', [L, FuncName, ArgLine]))
      else
        EmitLine(Format('  jnz %s, @%s, @%s', [L, ArgLine, FuncName]));
      EmitLine('@' + FuncName);
      R := EmitExpr(BinExpr.Right);
      SelfTemp := FCurrentBlockLabel;   { predecessor label for phi's RHS arm }
      EmitLine(Format('  jmp @%s', [ArgLine]));
      EmitLine('@' + ArgLine);
      T := AllocTemp;
      EmitLine(Format('  %s =w phi @%s %s, @%s %s',
        [T, ArgTemp, L, SelfTemp, R]));
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

    { Use long (pointer) comparison instructions when either operand is
      pointer-shaped (class/nil/pointer/metaclass).  Identity check only;
      ordering ops on pointers are not supported. }
    if ((BinExpr.Left.ResolvedType <> nil) and
        (BinExpr.Left.ResolvedType.Kind in [tyClass, tyNil, tyPointer, tyMetaClass])) or
       ((BinExpr.Right.ResolvedType <> nil) and
        (BinExpr.Right.ResolvedType.Kind in [tyClass, tyNil, tyPointer, tyMetaClass])) then
    begin
      case BinExpr.Op of
        boEQ: Op := 'ceql';
        boNE: Op := 'cnel';
      else
        Op := 'ceql';
      end;
      EmitLine(Format('  %s =w %s %s, %s', [T, Op, L, R]));
    end
    { Int64 comparison: result is Boolean (w) but operands must be compared as l }
    else if (BinExpr.Op in [boEQ, boNE, boLT, boGT, boLE, boGE]) and
            (((BinExpr.Left.ResolvedType <> nil) and
              (BinExpr.Left.ResolvedType.Kind = tyInt64)) or
             ((BinExpr.Right.ResolvedType <> nil) and
              (BinExpr.Right.ResolvedType.Kind = tyInt64))) then
    begin
      if (BinExpr.Left.ResolvedType = nil) or (BinExpr.Left.ResolvedType.Kind <> tyInt64) then
      begin
        ArgTemp := AllocTemp;
        EmitLine(Format('  %s =l extsw %s', [ArgTemp, L]));
        L := ArgTemp;
      end;
      if (BinExpr.Right.ResolvedType = nil) or (BinExpr.Right.ResolvedType.Kind <> tyInt64) then
      begin
        ArgTemp := AllocTemp;
        EmitLine(Format('  %s =l extsw %s', [ArgTemp, R]));
        R := ArgTemp;
      end;
      case BinExpr.Op of
        boEQ: Op := 'ceql';
        boNE: Op := 'cnel';
        boLT: Op := 'csltl';
        boGT: Op := 'csgtl';
        boLE: Op := 'cslel';
        boGE: Op := 'csgel';
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
        boXor: Op := 'xor';
        boShl: Op := 'shl';
        boShr: Op := 'shr';
      else
        Op := 'add';
      end;
      EmitLine(Format('  %s =l %s %s, %s', [T, Op, L, R]));
    end
    { Float arithmetic/comparison: QBE uses d/s typed instructions.
      Integer operands mixed with float are promoted via exts/extd. }
    else if (BinExpr.ResolvedType <> nil) and BinExpr.ResolvedType.IsFloat then
    begin
      { Promote integer operands to double if needed }
      if (BinExpr.Left.ResolvedType <> nil) and
         not BinExpr.Left.ResolvedType.IsFloat then
      begin
        ArgTemp := AllocTemp;
        EmitLine(Format('  %s =d swtof %s', [ArgTemp, L]));
        L := ArgTemp;
      end;
      if (BinExpr.Right.ResolvedType <> nil) and
         not BinExpr.Right.ResolvedType.IsFloat then
      begin
        ArgTemp := AllocTemp;
        EmitLine(Format('  %s =d swtof %s', [ArgTemp, R]));
        R := ArgTemp;
      end;
      case BinExpr.Op of
        boAdd: Op := 'add';
        boSub: Op := 'sub';
        boMul: Op := 'mul';
        boDiv: Op := 'div';
      else    Op := 'add';
      end;
      EmitLine(Format('  %s =d %s %s, %s', [T, Op, L, R]));
    end
    else if BinExpr.ResolvedType.Kind = tyBoolean then
    begin
      { Float comparison — at least one operand is float }
      if (BinExpr.Left.ResolvedType <> nil) and BinExpr.Left.ResolvedType.IsFloat then
      begin
        { Both already evaluated; coerce integer side if needed }
        if (BinExpr.Right.ResolvedType <> nil) and
           not BinExpr.Right.ResolvedType.IsFloat then
        begin
          ArgTemp := AllocTemp;
          EmitLine(Format('  %s =d swtof %s', [ArgTemp, R]));
          R := ArgTemp;
        end;
        case BinExpr.Op of
          boEQ: Op := 'ceqd';
          boNE: Op := 'cned';
          boLT: Op := 'cltd';
          boGT: Op := 'cgtd';
          boLE: Op := 'cled';
          boGE: Op := 'cged';
        else    Op := 'ceqd';
        end;
        EmitLine(Format('  %s =w %s %s, %s', [T, Op, L, R]));
      end
      else
      begin
        case BinExpr.Op of
          boEQ:  Op := 'ceqw';
          boNE:  Op := 'cnew';
          boLT:  Op := 'csltw';
          boGT:  Op := 'csgtw';
          boLE:  Op := 'cslew';
          boGE:  Op := 'csgew';
        else     Op := 'ceqw';
        end;
        EmitLine(Format('  %s =w %s %s, %s', [T, Op, L, R]));
      end;
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
        boXor: Op := 'xor';
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
    { P^ — T is the pointer value stored in the pointer variable.
      For record/array types, T IS the storage address — return it directly.
      For scalar types, load through T to get the actual value. }
    T := EmitExpr(TDerefExpr(AExpr).Expr);
    if (AExpr.ResolvedType <> nil) and
       (AExpr.ResolvedType.Kind in [tyRecord, tyStaticArray]) then
    begin
      { P : ^TRecord — T is already the record's address; no further load }
      Result := T;
    end
    else
    begin
      QType := QbeTypeOf(AExpr.ResolvedType);
      L     := AllocTemp;
      case QType of
        'w': EmitLine(Format('  %s =w loadw %s', [L, T]));
        'd': EmitLine(Format('  %s =d loadd %s', [L, T]));
        's': EmitLine(Format('  %s =s loads %s', [L, T]));
      else   EmitLine(Format('  %s =l loadl %s', [L, T]));
      end;
      Result := L;
    end;
  end
  else if AExpr is TAddrOfExpr then
    Result := EmitAddrOfExpr(TAddrOfExpr(AExpr))
  else if AExpr is TIsExpr then
    Result := EmitIsExpr(TIsExpr(AExpr))
  else if AExpr is TAsExpr then
    Result := EmitAsExpr(TAsExpr(AExpr))
  else if AExpr is TSupportsExpr then
    Result := EmitSupportsExpr(TSupportsExpr(AExpr))
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

function TCodeGenQBE.EmitSupportsExpr(AExpr: TSupportsExpr): string;
var
  ObjTemp:   string;
  OkTemp:    string;
  OldTemp:   string;
  ResSlot:   string;
  ResTemp:   string;
  ItabTemp:  string;
  LblYes:    string;
  LblNo:     string;
  LblEnd:    string;
  OutRef:    string;
begin
  ObjTemp := EmitExpr(AExpr.Obj);
  OkTemp  := AllocTemp;
  EmitLine(Format('  %s =w call $_ImplementsInterface(l %s, l $typeinfo_%s)',
    [OkTemp, ObjTemp, AExpr.IntfTypeName]));

  if AExpr.OutVarName = '' then
  begin
    { 2-arg form — just return the Boolean result }
    Result := OkTemp;
    Exit;
  end;

  { 3-arg form — on success populate the out-var's fat pointer }
  ResSlot := AllocTemp;
  EmitLine(Format('  %s =l alloc4 1', [ResSlot]));
  LblYes := AllocLabel('supports_yes');
  LblNo  := AllocLabel('supports_no');
  LblEnd := AllocLabel('supports_end');

  EmitLine(Format('  jnz %s, @%s, @%s', [OkTemp, LblYes, LblNo]));

  EmitLine('@' + LblYes);
  OutRef   := VarRef(AExpr.OutVarName, AExpr.OutVarIsGlobal);
  ItabTemp := AllocTemp;
  EmitLine(Format('  %s =l call $_GetItab(l %s, l $typeinfo_%s)',
    [ItabTemp, ObjTemp, AExpr.IntfTypeName]));
  { ARC: retain new obj, release old obj slot of out-var }
  OldTemp := AllocTemp;
  EmitLine(Format('  %s =l loadl %s_obj', [OldTemp, OutRef]));
  EmitLine(Format('  call $_ClassAddRef(l %s)',  [ObjTemp]));
  EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
  EmitLine(Format('  storel %s, %s_obj',  [ObjTemp, OutRef]));
  EmitLine(Format('  storel %s, %s_itab', [ItabTemp, OutRef]));
  EmitLine(Format('  storew 1, %s', [ResSlot]));
  EmitLine(Format('  jmp @%s', [LblEnd]));

  EmitLine('@' + LblNo);
  EmitLine(Format('  storew 0, %s', [ResSlot]));
  EmitLine(Format('  jmp @%s', [LblEnd]));

  EmitLine('@' + LblEnd);
  ResTemp := AllocTemp;
  EmitLine(Format('  %s =w loadw %s', [ResTemp, ResSlot]));
  Result := ResTemp;
end;

function TCodeGenQBE.QBEMangle(const AName: string): string;
var
  I: Integer;
  C: Integer;
begin
  Result := '';
  for I := 0 to Length(AName) - 1 do
  begin
    C := StrAt(AName, I);
    case C of
      60:  Result := Result + '_';    { '<' }
      62:  ;                          { '>' — skip }
      44:  Result := Result + '_';    { ',' }
      36:  Result := Result + '_D_';  { '$' — overload delimiter }
      64:  Result := Result + '_V_';  { '@' — var-param prefix }
      94:  Result := Result + '_P_';  { '^' — pointer prefix }
    else
      Result := Result + Chr(C);
    end;
  end;
end;

function TCodeGenQBE.MethodEmitName(AMDecl: TMethodDecl;
  const ATypeName, AMethodName: string): string;
begin
  if (AMDecl <> nil) and (AMDecl.ResolvedQbeName <> '') then
    Result := QBEMangle(AMDecl.ResolvedQbeName)
  else
    Result := QBEMangle(ATypeName + '_' + AMethodName);
end;

function TCodeGenQBE.QbeEscapeString(const AStr: string): string;
var
  I:    Integer;
  C:    Integer;
  Hi:   Integer;
  Lo:   Integer;
begin
  Result := '';
  for I := 0 to Length(AStr) - 1 do
  begin
    C := StrAt(AStr, I);
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
  Body:        TIRBuffer;
  SavedOutput: TIRBuffer;
begin
  FOutput.Clear;
  FStrLits.Clear;
  FStrLitsEmitted := 0;
  FTempCount  := 0;
  FLabelCount := 0;

  Body := TIRBuffer.Create;
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
    EmitGlobalConstData(AProg.Block);
    EmitInterfaceDefs(AProg);
    EmitTypeInfoDefs(AProg);
    EmitVTableDefs(AProg);
    FOutput.AppendBuffer(Body);
  finally
    Body.Free;
  end;
end;

procedure TCodeGenQBE.GenerateUnit(AUnit: TUnit);
var
  I:         Integer;
  ImplDecl:  TMethodDecl;
  IntfNames: TStringList;
  Body:      TIRBuffer;
  SavedOut:  TIRBuffer;
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

    Body := TIRBuffer.Create;
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
      FOutput.AppendBuffer(Body);
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
  PubCount:    Integer;
  ImplDecl:     TMethodDecl;
  IntfNames:    TStringList;
  Body:         TIRBuffer;
  SavedOut:     TIRBuffer;
  TD:           TTypeDecl;
  CD:           TClassTypeDef;
  MDecl:        TMethodDecl;
  TDesc:        TTypeDesc;
  RT:           TRecordTypeDesc;
  ClassRT:      TRecordTypeDesc;
  IntfDesc:     TInterfaceTypeDesc;
  ParentStr:    string;
  ImplStr:      string;
  MethStr:      string;
  MethLine:     string;
  ItabLine:     string;
  ItabRef:      string;
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

    Body := TIRBuffer.Create;
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

        { Class typeinfo blocks — full 7-slot layout matching EmitTypeInfoDefs }
        for I := 0 to AUnit.IntfBlock.TypeDecls.Count - 1 do
        begin
          TD := TTypeDecl(AUnit.IntfBlock.TypeDecls.Items[I]);
          if not (TD.Def is TClassTypeDef) then Continue;
          CD := TClassTypeDef(TD.Def);
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

          PubCount := 0;
          for J := 0 to CD.Methods.Count - 1 do
            if TMethodDecl(CD.Methods.Items[J]).IsPublished then
              Inc(PubCount);
          if PubCount > 0 then
          begin
            MethLine := 'data $methods_' + TD.Name + ' = { l ' + IntToStr(PubCount);
            for J := 0 to CD.Methods.Count - 1 do
            begin
              MDecl := TMethodDecl(CD.Methods.Items[J]);
              if not MDecl.IsPublished then Continue;
              MethLine := MethLine +
                          ', l ' + EmitClassNameRef(MDecl.Name) +
                          ', l $' + MethodEmitName(MDecl, TD.Name, MDecl.Name);
            end;
            MethLine := MethLine + ' }';
            EmitLine(MethLine);
            MethStr := '$methods_' + TD.Name;
          end
          else
            MethStr := '0';

          EmitLine('data $typeinfo_' + TD.Name +
                   ' = { l ' + ParentStr + ', l ' + ImplStr +
                   ', l ' + EmitClassNameRef(TD.Name) +
                   ', l ' + MethStr +
                   ', l ' + IntToStr(RT.TotalSize) +
                   ', l $_FieldCleanup_' + TD.Name +
                   ', l $vtable_' + TD.Name + ' }');
        end;

        { Vtable data — abstract slots point at $__abstract_method_error
          so the abstract class's vtable links even when no subclass
          overrides the method.  Matches EmitVTableDefs behaviour for
          program-level classes. }
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
            if E.IsAbstract then
              VLine := VLine + ', l $_AbstractMethodError'
            else if (Length(E.ImplName) > 0) and (StrAt(E.ImplName, 0) = Ord('$')) then
              VLine := VLine + ', l $' + QBEMangle(StrCopyTail(E.ImplName, 1))
            else
              VLine := VLine + ', l ' + QBEMangle(E.ImplName);
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
              if (ClassRT.FindVTableSlot(MethName) >= 0) and
                 ClassRT.VTableEntryAt(ClassRT.FindVTableSlot(MethName)).IsAbstract then
                ItabRef := '$_AbstractMethodError'
              else
                ItabRef := '$' + TD.Name + '_' + MethName;
              if K = 0 then
                ItabLine := ItabLine + ' l ' + ItabRef
              else
                ItabLine := ItabLine + ', l ' + ItabRef;
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

      { Global variables from interface and impl sections }
      EmitGlobalVarData(AUnit.IntfBlock);
      EmitGlobalVarData(AUnit.ImplBlock);
      EmitGlobalConstData(AUnit.IntfBlock);
      EmitGlobalConstData(AUnit.ImplBlock);

      FOutput.AppendBuffer(Body);

      { Initialization section: emit as export function $<Unit>_init() }
      if (AUnit.InitStmts <> nil) and (AUnit.InitStmts.Count > 0) then
      begin
        FUnitInitNames.Add(AUnit.Name);
        EmitLine('');
        EmitLine('export function w $' + AUnit.Name + '_init() {');
        EmitLine('@start');
        FTempCount  := 0;
        FLabelCount := 0;
        for I := 0 to AUnit.InitStmts.Count - 1 do
          EmitStmt(TASTStmt(AUnit.InitStmts.Items[I]));
        EmitLine('  ret 0');
        EmitLine('}');
        EmitPendingStrLits;
      end;

      { Finalization section: emit as export function $<Unit>_fini() }
      if (AUnit.FinalStmts <> nil) and (AUnit.FinalStmts.Count > 0) then
      begin
        EmitLine('');
        EmitLine('export function w $' + AUnit.Name + '_fini() {');
        EmitLine('@start');
        FTempCount  := 0;
        FLabelCount := 0;
        for I := 0 to AUnit.FinalStmts.Count - 1 do
          EmitStmt(TASTStmt(AUnit.FinalStmts.Items[I]));
        EmitLine('  ret 0');
        EmitLine('}');
        EmitPendingStrLits;
      end;
    finally
      Body.Free;
    end;
  finally
    IntfNames.Free;
  end;
end;

procedure TCodeGenQBE.AppendProgram(AProg: TProgram);
var
  Body:        TIRBuffer;
  SavedOutput: TIRBuffer;
begin
  { No clears — accumulates after AppendUnit calls. }
  FTempCount  := 0;
  FLabelCount := 0;

  Body := TIRBuffer.Create;
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
    EmitGlobalConstData(AProg.Block);
    EmitInterfaceDefs(AProg);
    EmitTypeInfoDefs(AProg);
    EmitVTableDefs(AProg);
    FOutput.AppendBuffer(Body);
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
    StrPtr  := EmitExpr(AExpr.StrExpr);
    IdxW    := EmitExpr(AExpr.IndexExpr);
    IdxL    := AllocTemp;
    Offset  := AllocTemp;
    ElemPtr := AllocTemp;
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
    { Record elements: return address directly — records are by-value via pointer }
    if SAT.ElementType.Kind = tyRecord then
    begin
      Result := ElemPtr;
      Exit;
    end;
    case SAT.ElementType.Kind of
      tyByte, tyBoolean: QLoad := 'loadub';
      tyInteger, tyUInt32, tyEnum: QLoad := 'loadw';
      tyInt64, tyString, tyClass, tyPointer, tyMetaClass: QLoad := 'loadl';
    else
      QLoad := 'loadl';
    end;
    QType   := QbeTypeOf(SAT.ElementType);
    ByteVal := AllocTemp;
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
      tyInt64, tyString, tyClass, tyPointer, tyMetaClass: QLoad := 'loadl';
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

  { Dynamic array element read: A[I] — data_ptr + I * ElemSize }
  if AExpr.StrExpr.ResolvedType.Kind = tyDynArray then
  begin
    ElemSize := TDynArrayTypeDesc(AExpr.StrExpr.ResolvedType).ElementType.RawSize;
    case TDynArrayTypeDesc(AExpr.StrExpr.ResolvedType).ElementType.Kind of
      tyByte, tyBoolean:   QLoad := 'loadub';
      tyInteger, tyUInt32, tyEnum: QLoad := 'loadw';
      tyInt64, tyString, tyClass, tyPointer, tyMetaClass: QLoad := 'loadl';
    else
      QLoad := 'loadl';
    end;
    QType   := QbeTypeOf(TDynArrayTypeDesc(AExpr.StrExpr.ResolvedType).ElementType);
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

  { String byte access: S[N] (0-based).
    Data-pointer convention: str_ptr IS the char data.
    S[N] = byte at str_ptr + N }
  StrPtr  := EmitExpr(AExpr.StrExpr);    { data pointer (l) }
  IdxW    := EmitExpr(AExpr.IndexExpr);  { 0-based index (w) }
  IdxL    := AllocTemp;
  BytePtr := AllocTemp;
  ByteVal := AllocTemp;
  EmitLine(Format('  %s =l extuw %s', [IdxL, IdxW]));
  EmitLine(Format('  %s =l add %s, %s', [BytePtr, StrPtr, IdxL]));
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
  MBlock:  string;
  DataSlot: string;
  ObjPtr:  string;
  MD:      TMethodDecl;
  FldExpr: TFieldAccessExpr;
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
    { @FuncName: semantic recorded a tyProcedural ResolvedType when the
      identifier names a standalone function or procedure.  In that case
      the address is the function's QBE label, not a stack-variable ref. }
    if (TIdentExpr(AExpr.Expr).ResolvedType <> nil) and
       (TIdentExpr(AExpr.Expr).ResolvedType.Kind = tyProcedural) then
    begin
      Result := '$' + TIdentExpr(AExpr.Expr).Name;
      Exit;
    end;
    { @VarParam: the address is the dereferenced param slot value, not the
      local slot itself.  Without this, @ARun on a var-record param yields
      the local 8-byte slot's address instead of the caller's record. }
    if TIdentExpr(AExpr.Expr).IsVarParam then
    begin
      StrPtr := AllocTemp;
      EmitLine(Format('  %s =l loadl %s',
        [StrPtr, VarRef(TIdentExpr(AExpr.Expr).Name,
                        TIdentExpr(AExpr.Expr).IsGlobal)]));
      Result := StrPtr;
      Exit;
    end;
    Result := VarRef(TIdentExpr(AExpr.Expr).Name,
                     TIdentExpr(AExpr.Expr).IsGlobal);
    Exit;
  end;
  { @Obj.MethodName — method-pointer construction.  The semantic pass set
    IsMethodPtr on the TFieldAccessExpr's ResolvedType when it detected this
    pattern.  Allocate a 16-byte block [code_ptr, data_ptr] on the stack,
    store the static method address and the object pointer, return the block. }
  if (AExpr.Expr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr.Expr).ResolvedType <> nil) and
     (TFieldAccessExpr(AExpr.Expr).ResolvedType.Kind = tyProcedural) and
     TProceduralTypeDesc(TFieldAccessExpr(AExpr.Expr).ResolvedType).IsMethodPtr then
  begin
    FldExpr  := TFieldAccessExpr(AExpr.Expr);
    MD       := TMethodDecl(FldExpr.ResolvedMethod);
    MBlock   := AllocTemp;
    EmitLine(Format('  %s =l alloc8 16', [MBlock]));
    DataSlot := AllocTemp;
    EmitLine(Format('  %s =l add %s, 8', [DataSlot, MBlock]));
    { Store code pointer at offset 0 }
    EmitLine(Format('  storel $%s, %s',
      [MethodEmitName(MD, MD.OwnerTypeName, FldExpr.FieldName), MBlock]));
    { Load and store the object pointer at offset 8.
      Simple form: @VarName.Method — FldExpr.Base is nil; load via RecordName.
      Chained form: @Expr.Method — FldExpr.Base is set; use EmitInstancePtr. }
    if FldExpr.Base <> nil then
      ObjPtr := EmitInstancePtr(FldExpr.Base)
    else
    begin
      ObjPtr := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [ObjPtr, VarRef(FldExpr.RecordName, FldExpr.IsGlobal)]));
    end;
    EmitLine(Format('  storel %s, %s', [ObjPtr, DataSlot]));
    Result := MBlock;
    Exit;
  end;
  { Fallthrough: field access, pointer deref, etc. — delegate to EmitLValueAddr
    which already handles TFieldAccessExpr, TDerefExpr, and TIdentExpr. }
  Result := EmitLValueAddr(AExpr.Expr);
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
  { Dynamic array subscript write: A[I] := V — data_ptr + I * ElemSize }
  if AStmt.ResolvedArrayType.Kind = tyDynArray then
  begin
    ElemType  := TDynArrayTypeDesc(AStmt.ResolvedArrayType).ElementType;
    ElemSize  := ElemType.RawSize;
    PCharBase := AllocTemp;
    { load the data pointer from the variable slot }
    if AStmt.IsGlobal then
      EmitLine(Format('  %s =l loadl $%s', [PCharBase, AStmt.ArrayName]))
    else
      EmitLine(Format('  %s =l loadl %%_var_%s', [PCharBase, AStmt.ArrayName]));
    IdxW    := EmitExpr(AStmt.IndexExpr);
    IdxL    := AllocTemp;
    Offset  := AllocTemp;
    ElemPtr := AllocTemp;
    ElemVal := EmitExpr(AStmt.ValueExpr);
    EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
    EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
    EmitLine(Format('  %s =l add %s, %s', [ElemPtr, PCharBase, Offset]));
    case ElemType.Kind of
      tyByte, tyBoolean:           StoreInstr := 'storeb';
      tyInteger, tyUInt32, tyEnum: StoreInstr := 'storew';
    else
      begin
        StoreInstr := 'storel';
        { Sign-extend w-typed value to l if needed (e.g. integer literals into Int64 slots) }
        if (ElemVal <> '') and (ElemType.Kind = tyInt64) and
           (AStmt.ValueExpr.ResolvedType <> nil) and
           (AStmt.ValueExpr.ResolvedType.Kind <> tyInt64) then
        begin
          Adj := AllocTemp;
          EmitLine(Format('  %s =l extsw %s', [Adj, ElemVal]));
          ElemVal := Adj;
        end;
      end;
    end;
    EmitLine(Format('  %s %s, %s', [StoreInstr, ElemVal, ElemPtr]));
    Exit;
  end;

  SAT      := TStaticArrayTypeDesc(AStmt.ResolvedArrayType);
  ElemType := SAT.ElementType;
  ElemSize := ElemType.RawSize;
  LowBnd   := SAT.LowBound;
  IdxW    := EmitExpr(AStmt.IndexExpr);
  IdxL    := AllocTemp;
  Offset  := AllocTemp;
  ElemPtr := AllocTemp;
  EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
  if LowBnd <> 0 then
  begin
    Adj := AllocTemp;
    EmitLine(Format('  %s =l sub %s, %d', [Adj, IdxL, LowBnd]));
    EmitLine(Format('  %s =l mul %s, %d', [Offset, Adj, ElemSize]));
  end
  else
    EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
  EmitLine(Format('  %s =l add %s, %s',
    [ElemPtr, VarRef(AStmt.ArrayName, AStmt.IsGlobal), Offset]));
  if ElemType.Kind = tyRecord then
  begin
    ElemVal := EmitExpr(AStmt.ValueExpr);
    EmitRecordCopy(TRecordTypeDesc(ElemType), ElemPtr, ElemVal);
    Exit;
  end;
  ElemVal := EmitExpr(AStmt.ValueExpr);
  case ElemType.Kind of
    tyByte, tyBoolean: StoreInstr := 'storeb';
    tyInteger, tyUInt32, tyEnum: StoreInstr := 'storew';
    tyInt64, tyString, tyClass, tyPointer, tyMetaClass: StoreInstr := 'storel';
  else
    StoreInstr := 'storew';
  end;
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
    tyString, tyClass, tyPointer, tyInt64, tyMetaClass:
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
