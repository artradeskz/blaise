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
  _SysWriteInt64/_SysWriteBool/_SysWriteNewline (rtl.platform.posix.pas).
  Records are stack-allocated; field access uses pointer arithmetic. }

interface

uses
  SysUtils, StrUtils, Classes, uAST, uSymbolTable, uStrCompat, uCodeGen;

// Raw byte copy used by TIRBuffer — maps to libc memcpy.
// Blaise links blaise_rtl.a which already pulls in libc.
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

  TCodeGenQBE = class(TObject, ICodeGen)
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
    FFinallyStack:  TObjectList; { active try-block FinallyBody (TCompoundStmt, not
                                   owned), index 0 = outermost; aligned 1:1 with the
                                   FExcDepth exception frames.  A non-local exit
                                   (Exit/Break/Continue) crossing a try/finally must
                                   run its finally body; try/except pushes nil so the
                                   indices stay aligned with FExcDepth. }
    FBreakLabels:    TStringList;  { stack of active loop-end labels; top = innermost }
    FContinueLabels: TStringList;  { stack of active loop-continue labels; top = innermost }
    FExitLabel:    string;       { label to jmp to for 'exit'; '' = main program }
    FSymTable:         TSymbolTable; { set via SetSymbolTable; used by AppendUnit for class data }
    FSystemDefsEmitted: Boolean;    { Phase 1 reservation: a stage-1
                                       binary built from this commit
                                       carries the field but never
                                       reads or writes it.  Phase 2
                                       (follow-up) wires AppendUnit to
                                       emit System-unit (TObject /
                                       TCustomAttribute) typeinfo +
                                       vtable + FieldCleanup *and*
                                       gates the existing
                                       EmitTypeInfoDefs / EmitVTableDefs
                                       / EmitFieldCleanupDefs on this
                                       flag.  Splitting the work in two
                                       phases avoids the bootstrap
                                       chicken-and-egg where a partial
                                       state's binary emits duplicate
                                       System defs and can't compile
                                       its own next iteration. }
    FThreadVarNames:   TStringList;  { global names declared as threadvar }
    FUnitInitNames:    TStringList;  { unit names that have initialization sections }
    { mem2reg: parallel lists tracking which locals are promoted SSA temps.
      FPromotedLocals[i] = var name; FPromotedTypes[i] = QBE type ('w','l','d','s').
      Cleared at the start of each function by EmitVarAllocs. }
    FPromotedLocals: TStringList;
    FPromotedTypes:  TStringList;

    { Nested-proc capture: when emitting a nested function, this holds the
      names of variables captured from the enclosing scope.  Each captured
      variable is received as an implicit leading pointer parameter named
      %_cap_<VarName>, and reads/writes are transparently redirected through
      that pointer.  Nil when not inside a nested function. }
    FCapturedVars: TStringList;

    { Nil-slot ARC tracking: set of local variable names whose class/string
      slot has already been written in the current function.  EmitVarAllocs
      zeroes all class/string slots at function entry, so the *first* store
      to a slot is provably writing into a nil location and does not need
      to call _ClassRelease/_StringRelease on the prior content.  Subsequent
      stores to the same slot do need the release.

      Tracking is conservative: any branch (if/while/case) or call that
      could have written to the slot through aliasing must invalidate the
      "still nil" claim.  To stay simple, the set is cleared whenever we
      leave the linear entry-prelude region of a function — see SeenArcStore. }
    FArcSlotWritten: TStringList;

    { Record types referenced by a record-by-value FFI (cdecl external) call
      parameter.  Each entry is a record name; Objects[] holds the
      TRecordTypeDesc.  At end of Generate/GenerateUnit/AppendUnit/
      AppendProgram, EmitFFIRecordTypeDecls writes a QBE `type :_ffi_<Name>`
      declaration for each entry not already in FFFIRecordEmitted, lets QBE
      classify the aggregate per SysV (or Win64) ABI at the call site, then
      moves the entry to FFFIRecordEmitted so chained AppendUnit/Program
      calls don't re-emit duplicates. }
    FFFIRecordTypes:   TStringList;
    FFFIRecordEmitted: TStringList;

    { Inlining: stack of active inline contexts.
      When non-empty, the topmost context maps parameter names of the
      callee (currently being emitted inline) to caller-side temps,
      and supplies a result-temp and end-label for Exit/Result handling.
      Each entry encodes one frame as 'PN1=T1\0PN2=T2\0...|ResultTemp|EndLabel|ResultQType'
      via parallel lists for simplicity.  See docs/inlining-design.adoc. }
    FInlineParamNames:   TStringList;  { CSV per frame: 'P1,P2,...' }
    FInlineParamTemps:   TStringList;  { CSV per frame: 'T1,T2,...' }
    FInlineResultTemps:  TStringList;  { one temp per frame }
    FInlineEndLabels:    TStringList;  { one label per frame }
    FInlineResultQTypes: TStringList;  { one QBE type per frame }
    FInlineDepth:        Integer;      { active inline depth; cap to prevent runaway }

    function  ExportPrefix(): string;
    function  AllocTemp(): string;
    function  AllocLabel(const APrefix: string): string;
    function  CoerceArg(const AArgTemp: string; AArgExpr: TASTExpr; const AParamQType: string): string;
    function  EmitByteRhs(AExpr: TASTExpr): string;
    function  EmitStrLit(const AValue: string): string;
    { Emit a class-name string literal as a data-section label expression.
      Returns '$__cn_ClassName + 12' which can be embedded in another data item. }
    function  EmitClassNameRef(const AClassName: string): string;
    { Emit a method-name string literal scoped to its containing class so two
      published methods of the same name in different classes don't collide.
      Returns '$__mn_<unit>_<class>_<method> + 12'. }
    function  EmitMethodNameRef(const AClassName, AMethodName: string): string;
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
    function  IsCaptured(const AName: string): Boolean;
    function  IsPromoted(const AName: string): Boolean;
    { Returns True if the named local class/string slot is still provably nil
      at the current emit position.  Used to elide _ClassRelease/_StringRelease
      on the slot's first write within the function entry block. }
    function  ArcSlotIsNil(const AName: string): Boolean;
    { Mark the named local's ARC slot as having been written.  Subsequent
      assignments to the same slot will emit release as normal. }
    procedure MarkArcSlotWritten(const AName: string);

    { Inline helpers: top-of-stack lookups and frame push/pop. }
    function  InlineParamTemp(const AName: string; out ATemp: string): Boolean;
    function  InlineResultTemp(): string;
    function  InlineEndLabel(): string;
    function  InlineResultQType(): string;
    procedure PushInlineFrame(const AParamCsv, ATempCsv, AResultTemp,
                              AEndLabel, AResultQType: string);
    procedure PopInlineFrame;
    function  InsideInlineFrame(): Boolean;
    { Try to inline the call at AExpr.  Returns True (and sets ATemp) when the
      call was emitted inline; False means the caller should emit a regular call. }
    function  TryEmitInlineCall(AExpr: TFuncCallExpr; out ATemp: string): Boolean;
    { Returns the QBE type of a promoted local ('' if not promoted). }
    function  PromotedType(const AName: string): string;
    function  CountTryStmts(AStmt: TASTStmt): Integer;
    procedure EmitExcFrameAllocs(ABlock: TBlock);
    procedure CollectThreadVarNames(ABlock: TBlock);
    procedure EmitGlobalVarData(ABlock: TBlock);
    procedure EmitArrayConstData(CD: TConstDecl; const APrefix: string);
    procedure EmitClassConstData(AClassDef: TClassTypeDef; const AClassName: string);
    procedure EmitGlobalConstData(ABlock: TBlock);
    procedure EmitLocalArrayConstsInBlock(ABlock: TBlock);
    procedure EmitLocalArrayConstsInTypeDecls(ABlock: TBlock);
    procedure EmitLocalArrayConstsInProgram(AProg: TProgram);
    procedure EmitLocalArrayConstsInUnit(AUnit: TUnit);
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
    { After a call, release any value-argument temporaries that carried a
      +1-owned reference (function/property/method returns passed directly).
      The callee took ownership via its parameter-entry AddRef and releases
      at scope exit, so the caller's temporary would otherwise leak.
      AArgs and AArgTemps are parallel: AArgTemps.Strings[i] is the temp for
      AArgs.Items[i], or '' if that arg was not a value temp (e.g. var param). }
    procedure EmitOwnedArgReleases(AArgs: TObjectList; AArgTemps: TStringList;
      AParams: TObjectList);
    { Caller-side retain/release for a const-string param.  A const param skips
      the callee-side _StringAddRef/_StringRelease pair (see 5a5b5d4), so a
      fresh transient (rc=0 from _StringConcat or a function returning string)
      would be unowned for the duration of the call.  Variables/fields/literals
      already have a live owner — the AddRef/Release pair nets to zero on them. }
    procedure EnsureConstStringRef(const AArgTemp: string; APar: TMethodParam);
    procedure ReleaseConstStringArgs(AArgs: TObjectList;
      AArgTemps: TStringList; AParams: TObjectList);
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
    procedure EmitInterfaceExprPair(AExpr: TASTExpr;
      out AObjTemp, AItabTemp: string);
    { Emit AExpr as an interface argument and return the ', l %obj, l %itab'
      call-argument fragment.  Wraps EmitInterfaceExprPair so the method-call
      arg loops can pass an interface param as the two-slot fat pointer the
      callee now expects, without each site declaring extra temps. }
    function  InterfaceArgFragment(AExpr: TASTExpr): string;
    { Assign the interface value produced by AExpr into the two memory slots
      pointed to by AObjSlotPtr (obj) and AItabSlotPtr (itab).  Handles ARC
      for strong interface fields (addref new obj, release old obj). }
    procedure EmitInterfaceToFieldSlots(AExpr: TASTExpr;
      const AObjSlotPtr, AItabSlotPtr: string; AIntfType: TTypeDesc);
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
    function  QbeParamTypeOf(AType: TTypeDesc): string;
    function  LoadInstrFor(AType: TTypeDesc): string;
    function  StoreInstrFor(AType: TTypeDesc): string;
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
    { Normalise the result of an external (cdecl) call to its declared
      width.  C calling conventions leave the upper bits of %eax
      unspecified for sub-int returns (Byte/Boolean/Word/SmallInt), so
      callers that hold the value as a full word would otherwise see
      garbage in those bits — `if Foo() <> 0 then` mis-fires silently. }
    function  MaybeNormalizeExtReturn(const ASrcTemp: string;
      AMDecl: TMethodDecl): string;
    { Returns the QBE primitive letter ('b','h','w','l','s','d') for a
      scalar record-field type, or '' for non-scalar fields (nested
      records, static arrays, etc.).  An '' result tells the type-decl
      emitter to fall back to the opaque size form. }
    function  QbeAggFieldType(AType: TTypeDesc): string;
    { Registers ARec for FFI-aggregate type emission and returns the QBE
      type reference ':_ffi_<Name>' to splice into a call or declare. }
    function  FFIRecordTypeRef(ARec: TRecordTypeDesc): string;
    { Emit a QBE aggregate type decl per entry of FFFIRecordTypes that
      is not already in FFFIRecordEmitted, then mark each one emitted so
      chained AppendUnit/Program calls do not duplicate. }
    procedure EmitFFIRecordTypeDecls;
    { Returns 'unitname_' for AClassName when the owning unit is
      unit-prefix-mangled, '' otherwise.  Consults FSymTable.Lookup
      for the class's TSymbol.OwningUnit, then applies the same
      allowlist semantics as uSemantic.MangleUnitPrefix. }
    function  ClassUnitPrefix(const AClassName: string): string;
    { ClassUnitPrefix(AClassName) + AClassName — used as the
      identifying suffix of class data symbols: $typeinfo_<sym>,
      $vtable_<sym>, $__cn_<sym>, $_FieldCleanup_<sym>. }
    function  ClassSymName(const AClassName: string): string;
    { Suffix for $typeinfo_<X> of an interface.  Generic interface
      instances use QBEMangle(name) with no unit prefix (matching
      GII.InstName); plain interfaces use ClassSymName. }
    function  IntfTypeInfoName(const AIntfName: string): string;
    { Find a TMethodDecl by name in a TClassTypeDef.Methods list.
      Returns nil if not found. }
    function  FindMethodInClassDef(AClassDef: TClassTypeDef;
      const AName: string): TMethodDecl;
  public
    FDebugMode: Boolean;
    FExportAll: Boolean;
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
    procedure SetDebugMode(AEnabled: Boolean);
    procedure SetExportAll(AEnabled: Boolean);
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
  inherited Create();
  FCap  := IR_INIT_CAP;
  FLen  := 0;
  FData := GetMem(FCap);
end;

destructor TIRBuffer.Destroy;
begin
  FreeMem(FData);
  inherited Destroy();
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
  inherited Create();
  FOutput          := TIRBuffer.Create();
  FStrLits         := TStringList.Create();
  FStrLits.CaseSensitive := True;
  FBreakLabels     := TStringList.Create();
  FContinueLabels  := TStringList.Create();
  FFinallyStack    := TObjectList.Create(False);  { not owned — AST owns the blocks }
  FThreadVarNames  := TStringList.Create();
  FThreadVarNames.CaseSensitive := True;
  FUnitInitNames   := TStringList.Create();
  FPromotedLocals  := TStringList.Create();
  FPromotedLocals.CaseSensitive := True;
  FPromotedTypes   := TStringList.Create();
  FArcSlotWritten  := TStringList.Create();
  FArcSlotWritten.CaseSensitive := True;
  FFFIRecordTypes  := TStringList.Create();
  FFFIRecordTypes.CaseSensitive := True;
  FFFIRecordTypes.Sorted := True;
  FFFIRecordTypes.Duplicates := dupIgnore;
  FFFIRecordEmitted := TStringList.Create();
  FFFIRecordEmitted.CaseSensitive := True;
  FFFIRecordEmitted.Sorted := True;
  FFFIRecordEmitted.Duplicates := dupIgnore;
  FInlineParamNames   := TStringList.Create();
  FInlineParamTemps   := TStringList.Create();
  FInlineResultTemps  := TStringList.Create();
  FInlineEndLabels    := TStringList.Create();
  FInlineResultQTypes := TStringList.Create();
  FInlineDepth        := 0;
  FTempCount       := 0;
  FStrLitsEmitted  := 0;
  FSystemDefsEmitted := False;  { Phase 1 reservation (see field comment) }
end;

destructor TCodeGenQBE.Destroy;
begin
  FBreakLabels.Free();
  FContinueLabels.Free();
  FFinallyStack.Free();
  FThreadVarNames.Free();
  FUnitInitNames.Free();
  FPromotedLocals.Free();
  FPromotedTypes.Free();
  FArcSlotWritten.Free();
  FFFIRecordTypes.Free();
  FFFIRecordEmitted.Free();
  FCapturedVars.Free();
  FInlineParamNames.Free();
  FInlineParamTemps.Free();
  FInlineResultTemps.Free();
  FInlineEndLabels.Free();
  FInlineResultQTypes.Free();
  FOutput.Free();
  FStrLits.Free();
  inherited Destroy();
end;

function TCodeGenQBE.ExportPrefix(): string;
begin
  if FExportAll then
    Result := 'export '
  else
    Result := ''
end;

function TCodeGenQBE.AllocTemp(): string;
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
    ExtTemp := AllocTemp();
    EmitLine(Format('  %s =l extsw %s', [ExtTemp, AArgTemp]));
    Exit(ExtTemp);
  end;
  { Integer/Single → Double. }
  if AParamQType = 'd' then
  begin
    ExtTemp := AllocTemp();
    if ArgQ = 'w' then
      EmitLine(Format('  %s =d swtof %s', [ExtTemp, AArgTemp]))
    else if ArgQ = 'l' then
      EmitLine(Format('  %s =d sltof %s', [ExtTemp, AArgTemp]))
    else if ArgQ = 's' then
      EmitLine(Format('  %s =d exts %s', [ExtTemp, AArgTemp]))
    else
      Exit;  { unsupported conversion — leave as-is; QBE will reject if invalid }
    Exit(ExtTemp);
  end;
  { Integer → Single, or Double → Single via truncd.  Without the d→s
    narrowing, a double-typed literal or sub-expression passed to a
    Single-typed parameter reaches the assembler as `d` against an `s`
    slot — QBE rejects with "invalid type for first operand in arg",
    and the C `float`-by-value callee at the other end would see the
    low half of the double mantissa instead of the intended Single. }
  if AParamQType = 's' then
  begin
    ExtTemp := AllocTemp();
    if ArgQ = 'w' then
      EmitLine(Format('  %s =s swtof %s', [ExtTemp, AArgTemp]))
    else if ArgQ = 'l' then
      EmitLine(Format('  %s =s sltof %s', [ExtTemp, AArgTemp]))
    else if ArgQ = 'd' then
      EmitLine(Format('  %s =s truncd %s', [ExtTemp, AArgTemp]))
    else
      Exit;
    Result := ExtTemp;
  end;
end;

{ Emit the RHS of a byte-store (storeb) as a w-typed value.

  When the RHS is Chr(N), we must NOT lower it via the normal _Chr call,
  because Chr returns a heap string Pointer (tyString) and a downstream
  storeb would silently truncate to the low byte of that pointer — the
  source of the historical "P[I] := Chr(N)" garbage bug.  Instead, emit
  the argument N directly as a w temp.  Callers consume the result with
  a storeb / byte-typed store.

  The same trap applies to single-char string literals (#N or 'A'): the
  normal lowering emits a string-literal data item and returns its data
  pointer, whose low byte is then storeb'd — yielding the address byte,
  not the intended Ord.  Fold to the Ord value directly. }
function TCodeGenQBE.EmitByteRhs(AExpr: TASTExpr): string;
var
  FC: TFuncCallExpr;
  SL: TStringLiteral;
  T:  string;
begin
  if (AExpr is TFuncCallExpr) then
  begin
    FC := TFuncCallExpr(AExpr);
    if SameText(FC.Name, 'Chr') and (FC.Args.Count = 1) then
    begin
      Exit(EmitExpr(TASTExpr(FC.Args.Items[0])));
    end;
  end;
  if AExpr is TStringLiteral then
  begin
    SL := TStringLiteral(AExpr);
    if Length(SL.Value) = 1 then
    begin
      T := AllocTemp();
      EmitLine(Format('  %s =w copy %d', [T, StrAt(SL.Value, 0)]));
      Exit(T);
    end;
  end;
  Result := EmitExpr(AExpr);
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
  T := AllocTemp();
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
  Sym:     string;
begin
  Mangled := QBEMangle(AClassName);
  Sym := ClassUnitPrefix(AClassName) + Mangled;
  { immortal ARC string: refcnt=-1, length, capacity, data, NUL }
  EmitLine(Format('%sdata $__cn_%s = { w -1, w %d, w %d, b "%s", b 0 }',
    [ExportPrefix(), Sym, Length(AClassName), Length(AClassName), AClassName]));
  Result := '$__cn_' + Sym + ' + 12';
end;

function TCodeGenQBE.EmitMethodNameRef(const AClassName, AMethodName: string): string;
{ Like EmitClassNameRef but the data-symbol name is scoped to the containing
  class so two classes can publish methods of the same name without colliding
  at link time.  String content is just AMethodName — published-method
  reflection still sees the bare method name. }
var
  Sym: string;
begin
  Sym := ClassUnitPrefix(AClassName) + QBEMangle(AClassName) + '_' + QBEMangle(AMethodName);
  EmitLine(Format('%sdata $__mn_%s = { w -1, w %d, w %d, b "%s", b 0 }',
    [ExportPrefix(), Sym, Length(AMethodName), Length(AMethodName), AMethodName]));
  Result := '$__mn_' + Sym + ' + 12';
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
  EmitPendingStrLits();
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
  if FDebugMode then
    EmitLine('  call $_LeakTrackerEnable()');
end;

procedure TCodeGenQBE.EmitMainFooter;
begin
  EmitLine('  ret 0');
  EmitLine('}');
end;

function TCodeGenQBE.QbeTypeOf(AType: TTypeDesc): string;
begin
  case AType.Kind of
    tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum,
    tySmallInt, tyWord: Result := 'w';
    tySet: if TSetTypeDesc(AType).BitCount <= 32 then Result := 'w' else Result := 'l';
    tyInt64, tyUInt64, tyString:            Result := 'l';
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

{ Return the QBE load instruction for reading a memory-resident value of
  AType.  Byte-sized fields (tyByte, tyBoolean) must use loadub so that
  only the single occupying byte is read — using loadw would over-read
  into the adjacent field. }
function TCodeGenQBE.LoadInstrFor(AType: TTypeDesc): string;
begin
  case AType.Kind of
    tyByte, tyBoolean:                       Result := 'loadub';
    tySmallInt:                              Result := 'loadsh';
    tyWord:                                  Result := 'loaduh';
    tyInteger, tyUInt32, tyEnum:             Result := 'loadw';
    tySet: if TSetTypeDesc(AType).BitCount <= 32 then Result := 'loadw' else Result := 'loadl';
    tyDouble:                                Result := 'loadd';
    tySingle:                                Result := 'loads';
  else
    Result := 'loadl';
  end;
end;

{ Counterpart of LoadInstrFor for stores.  Byte-sized fields must use
  storeb to avoid overwriting adjacent fields. }
function TCodeGenQBE.StoreInstrFor(AType: TTypeDesc): string;
begin
  case AType.Kind of
    tyByte, tyBoolean:                       Result := 'storeb';
    tySmallInt, tyWord:                      Result := 'storeh';
    tyInteger, tyUInt32, tyEnum:             Result := 'storew';
    tySet: if TSetTypeDesc(AType).BitCount <= 32 then Result := 'storew' else Result := 'storel';
    tyDouble:                                Result := 'stored';
    tySingle:                                Result := 'stores';
  else
    Result := 'storel';
  end;
end;

{ For an external (cdecl) call returning a sub-int type, emit a mask
  (Byte/Boolean/Word) or low-16 sign-extend (SmallInt) to clear the
  ABI-undefined upper bits before the value enters the i32 SSA domain. }
function TCodeGenQBE.MaybeNormalizeExtReturn(const ASrcTemp: string;
  AMDecl: TMethodDecl): string;
var NewT: string;
begin
  Result := ASrcTemp;
  if (AMDecl = nil) or (not AMDecl.IsExternal) or
     (AMDecl.ResolvedReturnType = nil) then Exit;
  case AMDecl.ResolvedReturnType.Kind of
    tyByte, tyBoolean:
      begin
        NewT := AllocTemp();
        EmitLine(Format('  %s =w and %s, 255', [NewT, ASrcTemp]));
        Result := NewT;
      end;
    tyWord:
      begin
        NewT := AllocTemp();
        EmitLine(Format('  %s =w and %s, 65535', [NewT, ASrcTemp]));
        Result := NewT;
      end;
    tySmallInt:
      begin
        NewT := AllocTemp();
        EmitLine(Format('  %s =w shl %s, 16', [NewT, ASrcTemp]));
        EmitLine(Format('  %s =w sar %s, 16', [NewT, NewT]));
        Result := NewT;
      end;
  end;
end;

{ Returns the QBE parameter type for AType.  For tyRecord this is the
  `:_ffi_<Name>` aggregate type so QBE classifies the value per SysV /
  Win64 ABI (caller scatters fields into INTEGER / SSE eightbytes,
  callee receives a pointer to a gathered struct buffer).  For every
  other type it is just QbeTypeOf.  Used uniformly in param signatures
  and call-site arg lists — Pascal-to-Pascal calls and C-FFI calls go
  through the same ABI to keep callbacks consistent. }
function TCodeGenQBE.QbeParamTypeOf(AType: TTypeDesc): string;
begin
  if (AType <> nil) and (AType.Kind = tyRecord) then
    Result := FFIRecordTypeRef(TRecordTypeDesc(AType))
  else
    Result := QbeTypeOf(AType);
end;

{ Maps a scalar record-field type to its QBE aggregate-type letter.
  Aggregate type decls use 'b' (byte) / 'h' (half) / 'w' (word) /
  'l' (long) / 's' / 'd' rather than the load-suffix variants. }
function TCodeGenQBE.QbeAggFieldType(AType: TTypeDesc): string;
begin
  case AType.Kind of
    tyByte, tyBoolean:           Result := 'b';
    tySmallInt, tyWord:          Result := 'h';
    tyInteger, tyUInt32, tyEnum: Result := 'w';
    tyInt64, tyUInt64:           Result := 'l';
    tySingle:                    Result := 's';
    tyDouble:                    Result := 'd';
    tyPointer, tyClass, tyString, tyPChar, tyDynArray,
    tyProcedural, tyMetaClass:   Result := 'l';
  else
    Result := '';
  end;
end;

{ Registers ARec for `type :_ffi_<Name>` emission and returns the QBE
  type reference. }
function TCodeGenQBE.FFIRecordTypeRef(ARec: TRecordTypeDesc): string;
begin
  if FFFIRecordEmitted.IndexOf(ARec.Name) < 0 then
    FFFIRecordTypes.AddObject(ARec.Name, ARec);
  Result := ':_ffi_' + ARec.Name;
end;

procedure TCodeGenQBE.EmitFFIRecordTypeDecls;
var
  I, J:   Integer;
  R:      TRecordTypeDesc;
  F:      TFieldInfo;
  Letter: string;
  Frag:   string;
  AllOk:  Boolean;
begin
  for I := 0 to FFFIRecordTypes.Count - 1 do
  begin
    R := TRecordTypeDesc(FFFIRecordTypes.Objects[I]);
    if FFFIRecordEmitted.IndexOf(R.Name) >= 0 then Continue;
    Frag  := '';
    AllOk := True;
    for J := 0 to R.Fields.Count - 1 do
    begin
      F := TFieldInfo(R.Fields.Items[J]);
      Letter := QbeAggFieldType(F.TypeDesc);
      if Letter = '' then begin AllOk := False; Break; end;
      if Frag <> '' then Frag := Frag + ', ';
      Frag := Frag + Letter;
    end;
    if AllOk then
      EmitLine(Format('type :_ffi_%s = align %d { %s }',
        [R.Name, R.AllocAlign(), Frag]))
    else
      { Opaque-byte fallback: SysV will classify as INTEGER regardless of
        actual field types.  Acceptable for records with non-scalar fields
        — those are unlikely to round-trip through a stable C ABI anyway. }
      EmitLine(Format('type :_ffi_%s = align %d { %d }',
        [R.Name, R.AllocAlign(), R.TotalSize()]));
    FFFIRecordEmitted.Add(R.Name);
  end;
  FFFIRecordTypes.Clear();
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
    Exit(CountTryStmts(IfS.ThenStmt) + CountTryStmts(IfS.ElseStmt));
  end;
  if AStmt is TWhileStmt then
  begin
    WhS := TWhileStmt(AStmt);
    Exit(CountTryStmts(WhS.Body));
  end;
  if AStmt is TForStmt then
  begin
    ForS := TForStmt(AStmt);
    Exit(CountTryStmts(ForS.Body));
  end;
  if AStmt is TForInStmt then
  begin
    FiS := TForInStmt(AStmt);
    Exit(CountTryStmts(FiS.Body));
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
    Exit(Result + CountTryStmts(CsS.ElseStmt));
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
  FFinallyStack.Clear();  { defensive: each function starts with no active finallys }
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
    tyClass, tyString, tyMetaClass are excluded because many codegen
    paths emit 'loadl %_var_X' to get the heap pointer from the local
    slot — those paths are not all promotion-aware yet.
    tyPointer, tyPChar are promotion-aware (audited 2026-05-16). }
  Result := AKind in [
    tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum,
    tyInt64, tyUInt64,
    tySmallInt, tyWord,
    tyDouble, tySingle,
    tySet,
    tyPointer, tyPChar
  ];
end;

function TCodeGenQBE.PromotedQType(AKind: TTypeKind; AType: TTypeDesc): string;
begin
  case AKind of
    tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum,
    tySmallInt, tyWord: Result := 'w';
    tyInt64, tyUInt64, tyString, tyClass, tyPointer, tyPChar, tyMetaClass: Result := 'l';
    tyDouble: Result := 'd';
    tySingle: Result := 's';
    tySet:
      if TSetTypeDesc(AType).BitCount <= 32 then Result := 'w'
      else Result := 'l';
  else
    Result := 'l';
  end;
end;

function TCodeGenQBE.IsCaptured(const AName: string): Boolean;
begin
  Result := (FCapturedVars <> nil) and (FCapturedVars.IndexOf(AName) >= 0);
end;

function TCodeGenQBE.IsPromoted(const AName: string): Boolean;
begin
  Result := FPromotedLocals.IndexOf(AName) >= 0;
end;

function TCodeGenQBE.ArcSlotIsNil(const AName: string): Boolean;
begin
  { Slot is still nil only when:
    1. We are still in the function's entry block (@start) — once a branch
       starts a new label we conservatively give up, since the slot could
       have been written along a branch we are not currently emitting.
    2. The slot has not been written yet in the current function. }
  Result := (FCurrentBlockLabel = 'start') and
            (FArcSlotWritten.IndexOf(AName) < 0);
end;

procedure TCodeGenQBE.MarkArcSlotWritten(const AName: string);
begin
  if FArcSlotWritten.IndexOf(AName) < 0 then
    FArcSlotWritten.Add(AName);
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

{ ------------------------------------------------------------------ }
{ Inline frame helpers                                                 }
{ ------------------------------------------------------------------ }

function TCodeGenQBE.InsideInlineFrame(): Boolean;
begin
  Result := FInlineDepth > 0;
end;

function TCodeGenQBE.InlineResultTemp(): string;
begin
  if FInlineDepth = 0 then Result := ''
  else Result := FInlineResultTemps.Strings[FInlineDepth - 1];
end;

function TCodeGenQBE.InlineEndLabel(): string;
begin
  if FInlineDepth = 0 then Result := ''
  else Result := FInlineEndLabels.Strings[FInlineDepth - 1];
end;

function TCodeGenQBE.InlineResultQType(): string;
begin
  if FInlineDepth = 0 then Result := ''
  else Result := FInlineResultQTypes.Strings[FInlineDepth - 1];
end;

{ Parameter remap: search the topmost frame's name CSV for AName.
  Returns True (and the mapped temp via ATemp) when found. }
function TCodeGenQBE.InlineParamTemp(const AName: string;
                                      out ATemp: string): Boolean;
var
  Names, Temps: string;
  NL, TL:       TStringList;
  Idx:          Integer;
begin
  Result := False;
  ATemp  := '';
  if FInlineDepth = 0 then Exit;
  Names := FInlineParamNames.Strings[FInlineDepth - 1];
  Temps := FInlineParamTemps.Strings[FInlineDepth - 1];
  NL := TStringList.Create();
  TL := TStringList.Create();
  try
    NL.CommaText := Names;
    TL.CommaText := Temps;
    Idx := NL.IndexOf(AName);
    if Idx >= 0 then
    begin
      ATemp  := TL.Strings[Idx];
      Result := True;
    end;
  finally
    NL.Free();
    TL.Free();
  end;
end;

procedure TCodeGenQBE.PushInlineFrame(const AParamCsv, ATempCsv,
                                       AResultTemp, AEndLabel,
                                       AResultQType: string);
begin
  FInlineParamNames.Add(AParamCsv);
  FInlineParamTemps.Add(ATempCsv);
  FInlineResultTemps.Add(AResultTemp);
  FInlineEndLabels.Add(AEndLabel);
  FInlineResultQTypes.Add(AResultQType);
  Inc(FInlineDepth);
end;

procedure TCodeGenQBE.PopInlineFrame;
begin
  if FInlineDepth = 0 then Exit;
  FInlineParamNames.Delete(FInlineDepth - 1);
  FInlineParamTemps.Delete(FInlineDepth - 1);
  FInlineResultTemps.Delete(FInlineDepth - 1);
  FInlineEndLabels.Delete(FInlineDepth - 1);
  FInlineResultQTypes.Delete(FInlineDepth - 1);
  Dec(FInlineDepth);
end;

{ ------------------------------------------------------------------ }
{ Inline call emitter                                                  }
{ ------------------------------------------------------------------ }
{ Attempts to inline AExpr.  Returns True (and sets ATemp to the      }
{ result-temp) when successful.  False = caller should emit a regular }
{ call.                                                                }
{                                                                      }
{ Pre-conditions checked here (defence in depth — analyser should     }
{ have caught these):                                                  }
{   - ResolvedDecl exists and is_inline_candidate                     }
{   - argument count matches parameter count                           }
{   - we are not already deeply nested                                 }
{ ------------------------------------------------------------------ }
function TCodeGenQBE.TryEmitInlineCall(AExpr: TFuncCallExpr;
                                        out ATemp: string): Boolean;
const
  MAX_INLINE_DEPTH = 2;
var
  Callee:       TMethodDecl;
  ResultTemp:   string;
  EndLabel:     string;
  ResultQType:  string;
  ParamCsv:     string;
  TempCsv:      string;
  ArgTemp:      string;
  ParamQType:   string;
  I:            Integer;
  Par:          TMethodParam;
  ParamNames:   TStringList;
  ArgTemps:     TStringList;
  IsFunc:       Boolean;
begin
  Result := False;
  ATemp  := '';
  if AExpr = nil then Exit;
  if AExpr.ResolvedDecl = nil then Exit;
  Callee := TMethodDecl(AExpr.ResolvedDecl);
  if not Callee.IsInlineCandidate then Exit;
  if FInlineDepth >= MAX_INLINE_DEPTH then Exit;
  if AExpr.Args.Count <> Callee.Params.Count then Exit;
  { Refuse to inline inside loop bodies — the inline result slot is allocated
    via alloc4/alloc8 at the call site, and QBE materialises each non-@start
    alloc as a dynamic stack bump.  Inside a loop that runs N times the stack
    would grow by 8*N bytes per inline call, leading to stack overflow.
    Detect via the active break/continue label stack. }
  if (FBreakLabels.Count > 0) or (FContinueLabels.Count > 0) then Exit;

  IsFunc := Callee.ResolvedReturnType <> nil;

  { Evaluate arguments to fresh caller-side temps.  We rely on the
    analyser to have rejected by-ref/open-array/aggregate params, so
    every argument is a simple value expression. }
  ParamNames := TStringList.Create();
  ArgTemps   := TStringList.Create();
  try
    for I := 0 to Callee.Params.Count - 1 do
    begin
      Par := TMethodParam(Callee.Params.Items[I]);
      ParamQType := QbeTypeOf(Par.ResolvedType);
      ArgTemp := EmitExpr(TASTExpr(AExpr.Args.Items[I]));
      ArgTemp := CoerceArg(ArgTemp, TASTExpr(AExpr.Args.Items[I]), ParamQType);
      ParamNames.Add(Par.ParamName);
      ArgTemps.Add(ArgTemp);
    end;

    { Allocate the result slot.  Inlined bodies may contain control flow
      (early Exit, nested if branches) that would emit multiple writes to
      a single SSA temp — QBE rejects that pattern when the temp also
      participates in a downstream phi.  So we use a stack slot (alloc4/
      alloc8) instead, identical to how the regular function-call return
      lands in a temp via store-then-load.  The slot is read once at the
      inline end label to produce the call-expression's value. }
    if IsFunc then
    begin
      ResultQType := QbeTypeOf(Callee.ResolvedReturnType);
      ResultTemp  := '%_var_inline_r' + IntToStr(FInlineDepth) + '_' + IntToStr(FTempCount);
      Inc(FTempCount);
      case ResultQType of
        'w':
          begin
            EmitLine(Format('  %s =l alloc4 1', [ResultTemp]));
            EmitLine(Format('  storew 0, %s', [ResultTemp]));
          end;
        'l':
          begin
            EmitLine(Format('  %s =l alloc8 1', [ResultTemp]));
            EmitLine(Format('  storel 0, %s', [ResultTemp]));
          end;
        'd':
          begin
            EmitLine(Format('  %s =l alloc8 1', [ResultTemp]));
            EmitLine(Format('  stored d_0, %s', [ResultTemp]));
          end;
        's':
          begin
            EmitLine(Format('  %s =l alloc4 1', [ResultTemp]));
            EmitLine(Format('  stores s_0, %s', [ResultTemp]));
          end;
      else
        EmitLine(Format('  %s =l alloc8 1', [ResultTemp]));
        EmitLine(Format('  storel 0, %s', [ResultTemp]));
      end;
    end
    else
    begin
      ResultQType := '';
      ResultTemp  := '';
    end;
    EndLabel := AllocLabel('inline_end');

    ParamCsv := ParamNames.CommaText;
    TempCsv  := ArgTemps.CommaText;
  finally
    ParamNames.Free();
    ArgTemps.Free();
  end;

  PushInlineFrame(ParamCsv, TempCsv, ResultTemp, EndLabel, ResultQType);
  try
    { Emit the callee body's statements.  EmitStmt / EmitExpr consult the
      inline frame stack to remap parameter ident reads and to redirect
      Exit and Result assignments. }
    for I := 0 to Callee.Body.Stmts.Count - 1 do
      EmitStmt(TASTStmt(Callee.Body.Stmts.Items[I]));
  finally
    PopInlineFrame();
  end;

  EmitLine(Format('  jmp @%s', [EndLabel]));
  EmitLine('@' + EndLabel);

  { Load the result from the slot into a fresh temp so callers receive an
    SSA value, not a slot address. }
  if IsFunc then
  begin
    ATemp := AllocTemp();
    case ResultQType of
      'w': EmitLine(Format('  %s =w loadw %s', [ATemp, ResultTemp]));
      'l': EmitLine(Format('  %s =l loadl %s', [ATemp, ResultTemp]));
      'd': EmitLine(Format('  %s =d loadd %s', [ATemp, ResultTemp]));
      's': EmitLine(Format('  %s =s loads %s', [ATemp, ResultTemp]));
    else
      EmitLine(Format('  %s =l loadl %s', [ATemp, ResultTemp]));
    end;
  end
  else
    ATemp := '';
  Result := True;
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
  end
  else if (AStmt is TExitStmt) and (TExitStmt(AStmt).ResultAssign <> nil) then
    { Exit(X) carries a synthesised 'Result := X' — walk it. }
    CollectAddressTakenStmt(TExitStmt(AStmt).ResultAssign, ASet);
  { TBreakStmt, TContinueStmt, bare TExitStmt — no expressions to walk }
end;

function TCodeGenQBE.StmtHasTry(AStmt: TASTStmt): Boolean;
var
  I: Integer;
begin
  Result := False;
  if AStmt = nil then Exit;
  if (AStmt is TTryFinallyStmt) or (AStmt is TTryExceptStmt) then
  begin
    Exit(True);
  end;
  if AStmt is TCompoundStmt then
    for I := 0 to TCompoundStmt(AStmt).Stmts.Count - 1 do
      if StmtHasTry(TASTStmt(TCompoundStmt(AStmt).Stmts.Items[I])) then
      begin
        Exit(True);
      end;
  if AStmt is TIfStmt then
  begin
    if StmtHasTry(TIfStmt(AStmt).ThenStmt) or StmtHasTry(TIfStmt(AStmt).ElseStmt) then
    begin
      Exit(True);
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
        Exit(True);
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
      Exit(True);
    end;
end;

function TCodeGenQBE.CollectAddressTaken(ABlock: TBlock): TStringList;
var
  I: Integer;
begin
  Result := TStringList.Create();
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
  FPromotedLocals.Clear();
  FPromotedTypes.Clear();
  { Reset nil-slot tracking: every class/string slot starts zero because
    EmitVarAllocs below emits `storel 0, ...` for them. }
  FArcSlotWritten.Clear();
  if not BlockHasTry(ABlock) then
  begin
    AddrTaken := CollectAddressTaken(ABlock);
    { Vars captured by nested procs have their address passed to the nested
      function — treat them as address-taken so they get stack slots. }
    for I := 0 to ABlock.ProcDecls.Count - 1 do
      if TMethodDecl(ABlock.ProcDecls.Items[I]).CapturedVars <> nil then
        for J := 0 to TMethodDecl(ABlock.ProcDecls.Items[I]).CapturedVars.Count - 1 do
        begin
          VarName := TMethodDecl(ABlock.ProcDecls.Items[I]).CapturedVars.Strings[J];
          if AddrTaken.IndexOf(VarName) < 0 then
            AddrTaken.Add(VarName);
        end;
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
      AddrTaken.Free();
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
        tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum,
        tySmallInt, tyWord:
          begin
            EmitLine(Format('  %%_var_%s =l alloc4 1', [VarName]));
            EmitLine(Format('  storew 0, %%_var_%s', [VarName]));
          end;

        tyInt64, tyUInt64:
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
            RecSize  := RT.TotalSize();
            RecAlign := RT.MaxAlign();
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
            ArrSize  := SAT.ByteSize();
            ArrAlign := SAT.AllocAlign();
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

procedure TCodeGenQBE.CollectThreadVarNames(ABlock: TBlock);
var
  I, J: Integer;
  Decl: TVarDecl;
begin
  if ABlock = nil then Exit;
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(ABlock.Decls.Items[I]);
    if Decl.IsThreadVar then
      for J := 0 to Decl.Names.Count - 1 do
        FThreadVarNames.Add(Decl.Names.Strings[J]);
  end;
end;

procedure TCodeGenQBE.EmitGlobalVarData(ABlock: TBlock);
var
  I, J:    Integer;
  Decl:    TVarDecl;
  VarName: string;
  Pfx:     string;
  RT:      TRecordTypeDesc;
begin
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(ABlock.Decls.Items[I]);
    if not Decl.IsGlobal then Continue;
    if Decl.ResolvedType = nil then Continue;
    if Decl.IsThreadVar then
      Pfx := 'export thread data'
    else
      Pfx := 'export data';
    for J := 0 to Decl.Names.Count - 1 do
    begin
      VarName := Decl.Names.Strings[J];
      if Decl.IsThreadVar then
        FThreadVarNames.Add(VarName);
      case Decl.ResolvedType.Kind of
        tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum:
          EmitLine(Format('%s $%s = { w 0 }', [Pfx, VarName]));
        tySmallInt, tyWord:
          EmitLine(Format('%s $%s = { h 0 }', [Pfx, VarName]));
        tySet:
          if TSetTypeDesc(Decl.ResolvedType).BitCount <= 32 then
            EmitLine(Format('%s $%s = { w 0 }', [Pfx, VarName]))
          else
            EmitLine(Format('%s $%s = { l 0 }', [Pfx, VarName]));
        tyInt64, tyUInt64:
          EmitLine(Format('%s $%s = { l 0 }', [Pfx, VarName]));
        tyString, tyClass, tyPointer, tyPChar, tyMetaClass:
          EmitLine(Format('%s $%s = { l 0 }', [Pfx, VarName]));
        tyProcedural:
          if TProceduralTypeDesc(Decl.ResolvedType).IsMethodPtr then
            EmitLine(Format('%s $%s = { z 16 }', [Pfx, VarName]))
          else
            EmitLine(Format('%s $%s = { l 0 }', [Pfx, VarName]));
        tyDouble:
          EmitLine(Format('%s $%s = { d 0 }', [Pfx, VarName]));
        tySingle:
          EmitLine(Format('%s $%s = { s 0 }', [Pfx, VarName]));
        tyInterface:
          begin
            EmitLine(Format('%s $%s_obj  = { l 0 }', [Pfx, VarName]));
            EmitLine(Format('%s $%s_itab = { l 0 }', [Pfx, VarName]));
          end;
        tyRecord:
          begin
            RT := TRecordTypeDesc(Decl.ResolvedType);
            if RT.TotalSize() > 0 then
              EmitLine(Format('%s $%s = { z %d }', [Pfx, VarName, RT.TotalSize()]))
            else
              EmitLine(Format('%s $%s = { l 0 }', [Pfx, VarName]));
          end;
        tyStaticArray:
          begin
            if TStaticArrayTypeDesc(Decl.ResolvedType).ByteSize() > 0 then
              EmitLine(Format('%s $%s = { z %d }',
                [Pfx, VarName, TStaticArrayTypeDesc(Decl.ResolvedType).ByteSize()]))
            else
              EmitLine(Format('%s $%s = { l 0 }', [Pfx, VarName]));
          end;
      else
        EmitLine(Format('%s $%s = { l 0 }', [Pfx, VarName]));
      end;
    end;
  end;
end;

procedure TCodeGenQBE.EmitArrayConstData(CD: TConstDecl; const APrefix: string);
var
  J:          Integer;
  ElemVal:    string;
  Parts:      string;
  StrIdx:     Integer;
  IsStrArray: Boolean;
  Label_:     string;
begin
  if not CD.IsArrayConst then Exit;
  if (CD.ArrayElements = nil) or (CD.ArrayElements.Count = 0) then Exit;
  if APrefix <> '' then
    Label_ := APrefix + '_' + CD.Name
  else if CD.ResolvedQbeName <> '' then
    Label_ := CD.ResolvedQbeName
  else
    Label_ := CD.Name;
  IsStrArray := SameText(CD.ArrayElemType, 'string');
  if IsStrArray then
  begin
    for J := 0 to CD.ArrayElements.Count - 1 do
      if FStrLits.IndexOf(CD.ArrayElements[J]) < 0 then
        FStrLits.Add(CD.ArrayElements[J]);
    EmitPendingStrLits();
  end;
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
  { Class/record consts keep an exported, type-qualified label (referenced as
    TFoo.Const across the compilation).  Block-local and program/unit array
    consts use a mangled, file-local label: the mangled name is only unique
    within one compilation, so it must NOT be exported — otherwise two
    separately-compiled objects (e.g. the RTL and a user program) that each
    mint '__bac_1_X' would collide at link time. }
  if APrefix <> '' then
    EmitLine(Format('export data $%s = { %s }', [Label_, Parts]))
  else
    EmitLine(Format('data $%s = { %s }', [Label_, Parts]));
end;

procedure TCodeGenQBE.EmitClassConstData(AClassDef: TClassTypeDef; const AClassName: string);
var
  I: Integer;
begin
  for I := 0 to AClassDef.ConstDecls.Count - 1 do
    EmitArrayConstData(TConstDecl(AClassDef.ConstDecls.Items[I]), AClassName);
end;

procedure TCodeGenQBE.EmitGlobalConstData(ABlock: TBlock);
{ Emit QBE data-section entries for array-typed constants.
  Each array const is emitted as a labelled data object whose elements are
  either pointer-sized string references ($__sN + 12) or word-sized integers.
  String literals are pre-registered in FStrLits so EmitPendingStrLits writes
  their headers before the referencing data object. }
var
  I:          Integer;
  TD:         TTypeDecl;
begin
  for I := 0 to ABlock.ConstDecls.Count - 1 do
    EmitArrayConstData(TConstDecl(ABlock.ConstDecls.Items[I]), '');
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
    if TD.Def is TClassTypeDef then
      EmitClassConstData(TClassTypeDef(TD.Def), TD.Name);
  end;
end;

procedure TCodeGenQBE.EmitLocalArrayConstsInBlock(ABlock: TBlock);
{ Walk ABlock's standalone proc/func decls and emit any local typed array
  constants as top-level data items.  Local consts share the unprefixed
  global symbol namespace, which is fine in practice because block-scoped
  names are unique per program; if collisions ever arise a prefix mangling
  would go here. }
var
  I, J:    Integer;
  Decl:    TMethodDecl;
  CD:      TConstDecl;
begin
  if ABlock = nil then Exit;
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(ABlock.ProcDecls.Items[I]);
    if Decl.Body = nil then Continue;
    for J := 0 to Decl.Body.ConstDecls.Count - 1 do
    begin
      CD := TConstDecl(Decl.Body.ConstDecls.Items[J]);
      EmitArrayConstData(CD, '');
    end;
  end;
end;

procedure TCodeGenQBE.EmitLocalArrayConstsInTypeDecls(ABlock: TBlock);
{ Walk ABlock's type decls and emit local typed array constants found in
  class/record method bodies as top-level data items. }
var
  I, J, K: Integer;
  TD:      TTypeDecl;
  Methods: TObjectList;
  Decl:    TMethodDecl;
  CD:      TConstDecl;
begin
  if ABlock = nil then Exit;
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
    if TD.Def is TClassTypeDef then
      Methods := TClassTypeDef(TD.Def).Methods
    else if TD.Def is TRecordTypeDef then
      Methods := TRecordTypeDef(TD.Def).Methods
    else
      Continue;
    for J := 0 to Methods.Count - 1 do
    begin
      Decl := TMethodDecl(Methods.Items[J]);
      if Decl.Body = nil then Continue;
      for K := 0 to Decl.Body.ConstDecls.Count - 1 do
      begin
        CD := TConstDecl(Decl.Body.ConstDecls.Items[K]);
        EmitArrayConstData(CD, '');
      end;
    end;
  end;
end;

procedure TCodeGenQBE.EmitLocalArrayConstsInProgram(AProg: TProgram);
{ Emit local typed array constants from class/record method bodies and
  standalone procs in the program block as top-level data items.  Mirrors
  the EmitMethodDefs + EmitStandaloneDefs sweep but only looks at consts. }
begin
  EmitLocalArrayConstsInTypeDecls(AProg.Block);
  EmitLocalArrayConstsInBlock(AProg.Block);
end;

procedure TCodeGenQBE.EmitLocalArrayConstsInUnit(AUnit: TUnit);
begin
  if AUnit = nil then Exit;
  EmitLocalArrayConstsInTypeDecls(AUnit.IntfBlock);
  EmitLocalArrayConstsInTypeDecls(AUnit.ImplBlock);
  EmitLocalArrayConstsInBlock(AUnit.IntfBlock);
  EmitLocalArrayConstsInBlock(AUnit.ImplBlock);
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
    if Decl.ResolvedType.IsString() then
      RelFn := '$_StringRelease'
    else if Decl.ResolvedType.Kind = tyClass then
      RelFn := '$_ClassRelease'
    else if IsIntf then
      RelFn := '$_ClassRelease'  { obj slot release; itab is static }
    else if Decl.ResolvedType.Kind = tyDynArray then
      RelFn := '$_DynArrayRelease'
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
      ValTemp := AllocTemp();
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
    if Decl.ResolvedType.IsString() then
      RelFn := '$_StringRelease'
    else if Decl.ResolvedType.Kind = tyClass then
      RelFn := '$_ClassRelease'
    else if IsIntf then
      RelFn := '$_ClassRelease'
    else if Decl.ResolvedType.Kind = tyDynArray then
      RelFn := '$_DynArrayRelease'
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
      ValTemp := AllocTemp();
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
  I, J:    Integer;
  FinBody: TCompoundStmt;
begin
  { Unwind exception frames from innermost (FExcDepth) down to ATargetDepth+1.
    For a try/finally frame, its finally body must run as control leaves the
    try region via a non-local exit (Exit/Break/Continue) — pop the frame,
    then emit the finally body inline (mirroring the normal/exception paths in
    EmitTryFinallyStmt).  try/except frames have a nil FFinallyStack entry and
    only need the frame popped. }
  for I := FExcDepth downto ATargetDepth + 1 do
  begin
    EmitLine('  call $_PopExcFrame()');
    if I - 1 < FFinallyStack.Count then
    begin
      FinBody := TCompoundStmt(FFinallyStack.Items[I - 1]);
      if FinBody <> nil then
        for J := 0 to FinBody.Stmts.Count - 1 do
          EmitStmt(TASTStmt(FinBody.Stmts.Items[J]));
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
    { Exit(X) shorthand: emit the synthesised 'Result := X' (built by the
      semantic pass) before the return, so the value flows through the normal
      assignment path (widening, ARC for string/class returns, etc.). }
    if TExitStmt(AStmt).ResultAssign <> nil then
      EmitAssignment(TAssignment(TExitStmt(AStmt).ResultAssign));
    { Inline frame: Exit jumps to the per-call-site end label, not the
      caller's exit.  No exception unwinding needed because the analyser
      rejects bodies that contain try frames. }
    if InsideInlineFrame() then
      EmitLine(Format('  jmp @%s', [InlineEndLabel()]))
    else
    begin
      EmitExcUnwind(0);
      if FExitLabel <> '' then
        EmitLine(Format('  jmp @%s', [FExitLabel]))
      else
        EmitLine('  ret 0');
    end;
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
  { Register this finally body so a non-local exit (Exit/Break/Continue) inside
    the try body runs it on the way out.  Index aligns with FExcDepth-1. }
  FFinallyStack.Add(AStmt.FinallyBody);

  SjrTemp := AllocTemp();
  EmitLine(Format('  %s =w call $_blaise_setjmp(l %s)', [SjrTemp, FrameTemp]));
  EmitLine(Format('  jnz %s, @%s, @%s', [SjrTemp, LblFinExc, LblTry]));

  { Normal path: run try body, pop frame, run finally body.  Remove this
    frame's finally registration before emitting the normal-path finally so a
    non-local exit *inside* the finally body itself does not re-run it. }
  EmitLine('@' + LblTry);
  for I := 0 to AStmt.TryBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.TryBody.Stmts.Items[I]));
  EmitLine('  call $_PopExcFrame()');
  Dec(FExcDepth);
  FFinallyStack.Delete(FFinallyStack.Count - 1);
  for I := 0 to AStmt.FinallyBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.FinallyBody.Stmts.Items[I]));
  EmitLine(Format('  jmp @%s', [LblEnd]));

  { Exception path: capture exception, pop frame, run finally body, re-raise.
    ARC cleanup is NOT emitted here — the outer handler (or function exit)
    is responsible for releasing variables that are still in scope. Releasing
    them here would nil variables that the outer except handler still reads. }
  EmitLine('@' + LblFinExc);
  ExcTemp := AllocTemp();
  EmitLine(Format('  %s =l call $_CurrentException()', [ExcTemp]));
  EmitLine('  call $_PopExcFrame()');
  Dec(FExcDepth);
  for I := 0 to AStmt.FinallyBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.FinallyBody.Stmts.Items[I]));
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
    Matches the size contract in blaise_exc.pas — must hold jmp_buf (64 B on
    x86_64, larger on ARM64) plus two pointer fields. }
  FrameTemp := Format('%%_exc_frame_%d', [FExcFrameNext]);
  FExcFrameNext := FExcFrameNext + 1;
  EmitLine(Format('  call $_PushExcFrame(l %s)', [FrameTemp]));
  Inc(FExcDepth);
  { Push a nil finally entry so FFinallyStack stays index-aligned with
    FExcDepth.  A non-local exit crossing a try/except frame only pops it;
    there is no finally body to run. }
  FFinallyStack.Add(nil);

  SjrTemp := AllocTemp();
  EmitLine(Format('  %s =w call $_blaise_setjmp(l %s)', [SjrTemp, FrameTemp]));
  EmitLine(Format('  jnz %s, @%s, @%s', [SjrTemp, LblExcept, LblTry]));

  { Normal path: run try body, pop frame on clean exit }
  EmitLine('@' + LblTry);
  for I := 0 to AStmt.TryBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.TryBody.Stmts.Items[I]));
  EmitLine('  call $_PopExcFrame()');
  Dec(FExcDepth);
  FFinallyStack.Delete(FFinallyStack.Count - 1);
  EmitLine(Format('  jmp @%s', [LblEnd]));

  { Exception path: capture exception before popping frame, then pop }
  EmitLine('@' + LblExcept);

  if AStmt.Handlers.Count > 0 then
  begin
    { Capture current exception while frame is still on the stack (g_exc_top
      points to our frame, so _CurrentException returns its exception field). }
    ExcTemp := AllocTemp();
    EmitLine(Format('  %s =l call $_CurrentException()', [ExcTemp]));
    EmitLine('  call $_PopExcFrame()');
    Dec(FExcDepth);

    for I := 0 to AStmt.Handlers.Count - 1 do
    begin
      H := TExceptHandlerClause(AStmt.Handlers[I]);
      LblBody := AllocLabel('exc_handler_body');
      LblNext := AllocLabel('exc_handler_next');

      MatchTemp := AllocTemp();
      EmitLine(Format('  %s =w call $_IsInstance(l %s, l $typeinfo_%s)',
        [MatchTemp, ExcTemp, ClassSymName(H.TypeName)]));
      EmitLine(Format('  jnz %s, @%s, @%s', [MatchTemp, LblBody, LblNext]));

      EmitLine('@' + LblBody);
      if H.VarName <> '' then
      begin
        { Bind the caught exception to the handler variable.  The handler var
          is a regular class-typed local that EmitArcCleanup releases at scope
          exit, so retain the exception here to balance that release — without
          this AddRef the scope-exit release drives the exception's refcount
          negative (it is created at rc=0 by `raise EFoo.Create` and never
          otherwise retained). }
        EmitLine(Format('  call $_ClassAddRef(l %s)', [ExcTemp]));
        EmitLine(Format('  storel %s, %%_var_%s', [ExcTemp, H.VarName]));
      end;
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
    ObjTemp := AllocTemp();
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
  CurT := AllocTemp();
  if not AStmt.IsGlobal and IsPromoted(AStmt.VarName) then
    EmitLine(Format('  %s =w copy %%_var_%s', [CurT, AStmt.VarName]))
  else
    EmitLine(Format('  %s =w loadw %s', [CurT, VarRef(AStmt.VarName, AStmt.IsGlobal)]));
  CmpT := AllocTemp();
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
  CurT  := AllocTemp();
  StepT := AllocTemp();
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
  DAT:        TDynArrayTypeDesc;
  LenT:       string;
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
  SetMQT:     string;
  SetMLd:     string;
  SetMSt:     string;
begin
  if AStmt.IsArrayIter then
  begin
    { ---- Static array iteration ---- }
    SAT      := TStaticArrayTypeDesc(AStmt.CollExpr.ResolvedType);
    ElemSize := SAT.ElementType.RawSize();
    case SAT.ElementType.Kind of
      tyByte, tyBoolean:            QLoad := 'loadub';
      tySmallInt:                   QLoad := 'loadsh';
      tyWord:                       QLoad := 'loaduh';
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
    IdxW := AllocTemp();
    CmpT := AllocTemp();
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
      IdxW    := AllocTemp();
      IdxL    := AllocTemp();
      if IsPromoted(AStmt.IdxVarName) then
        EmitLine(Format('  %s =w copy %s', [IdxW, IdxSlot]))
      else
        EmitLine(Format('  %s =w loadw %s', [IdxW, IdxSlot]));
      EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
      if AStmt.ArrayLow <> 0 then
      begin
        AdjL := AllocTemp();
        EmitLine(Format('  %s =l sub %s, %d', [AdjL, IdxL, AStmt.ArrayLow]));
        OffL := AllocTemp();
        EmitLine(Format('  %s =l mul %s, %d', [OffL, AdjL, ElemSize]));
      end
      else
      begin
        OffL := AllocTemp();
        EmitLine(Format('  %s =l mul %s, %d', [OffL, IdxL, ElemSize]));
      end;
      ElemPtr := AllocTemp();
      CurT    := AllocTemp();
      EmitLine(Format('  %s =l add %s, %s', [ElemPtr, BasePtr, OffL]));
      EmitLine(Format('  %s =%s %s %s', [CurT, QType, QLoad, ElemPtr]));

      { Assign element to loop variable }
      if AStmt.ResolvedVarType.IsString() then
      begin
        OldVarT := AllocTemp();
        EmitLine(Format('  %s =l loadl %s',
          [OldVarT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));
        EmitLine(Format('  call $_StringAddRef(l %s)', [CurT]));
        EmitLine(Format('  call $_StringRelease(l %s)', [OldVarT]));
        EmitLine(Format('  storel %s, %s',
          [CurT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));
      end
      else if AStmt.ResolvedVarType.Kind = tyClass then
      begin
        OldVarT := AllocTemp();
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
    IdxW := AllocTemp();
    NxtW := AllocTemp();
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

  if AStmt.IsDynArrayIter then
  begin
    { ---- Dynamic array iteration ----
      idx runs 0 .. $_DynArrayLength(ptr)-1 (0-based).
      Condition: idx < length  (re-evaluated each iteration from the header).
      BasePtr = data pointer (the dyn-array variable value itself). }
    DAT      := TDynArrayTypeDesc(AStmt.CollExpr.ResolvedType);
    ElemSize := DAT.ElementType.RawSize();
    case DAT.ElementType.Kind of
      tyByte, tyBoolean:            QLoad := 'loadub';
      tySmallInt:                   QLoad := 'loadsh';
      tyWord:                       QLoad := 'loaduh';
      tyInteger, tyUInt32, tyEnum:  QLoad := 'loadw';
    else
      QLoad := 'loadl';
    end;
    QType   := QbeTypeOf(DAT.ElementType);
    IdxSlot := '%_var_' + AStmt.IdxVarName;
    LblCond := AllocLabel('forin_cond');
    LblBody := AllocLabel('forin_body');
    LblEnd  := AllocLabel('forin_end');

    { Initialise index to 0 }
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %s =w copy 0', [IdxSlot]))
    else
      EmitLine(Format('  storew 0, %s', [IdxSlot]));
    EmitLine(Format('  jmp @%s', [LblCond]));

    { Condition: idx < length }
    EmitLine('@' + LblCond);
    IdxW  := AllocTemp();
    BasePtr := EmitExpr(AStmt.CollExpr);
    CmpT  := AllocTemp();
    LenT := AllocTemp();
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %s =w copy %s', [IdxW, IdxSlot]))
    else
      EmitLine(Format('  %s =w loadw %s', [IdxW, IdxSlot]));
    EmitLine(Format('  %s =w call $_DynArrayLength(l %s)', [LenT, BasePtr]));
    EmitLine(Format('  %s =w csltw %s, %s', [CmpT, IdxW, LenT]));
    EmitLine(Format('  jnz %s, @%s, @%s', [CmpT, LblBody, LblEnd]));

    { Body: load element, assign to loop var, then user body }
    EmitLine('@' + LblBody);
    FBreakLabels.AddObject(LblEnd, TObject(PtrUInt(FExcDepth)));
    FContinueLabels.AddObject(LblCond, TObject(PtrUInt(FExcDepth)));
    try
      BasePtr := EmitExpr(AStmt.CollExpr);
      IdxW    := AllocTemp();
      IdxL    := AllocTemp();
      if IsPromoted(AStmt.IdxVarName) then
        EmitLine(Format('  %s =w copy %s', [IdxW, IdxSlot]))
      else
        EmitLine(Format('  %s =w loadw %s', [IdxW, IdxSlot]));
      EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
      OffL := AllocTemp();
      EmitLine(Format('  %s =l mul %s, %d', [OffL, IdxL, ElemSize]));
      ElemPtr := AllocTemp();
      CurT    := AllocTemp();
      EmitLine(Format('  %s =l add %s, %s', [ElemPtr, BasePtr, OffL]));
      EmitLine(Format('  %s =%s %s %s', [CurT, QType, QLoad, ElemPtr]));

      { Assign element to loop variable }
      if AStmt.ResolvedVarType.IsString() then
      begin
        OldVarT := AllocTemp();
        EmitLine(Format('  %s =l loadl %s',
          [OldVarT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));
        EmitLine(Format('  call $_StringAddRef(l %s)', [CurT]));
        EmitLine(Format('  call $_StringRelease(l %s)', [OldVarT]));
        EmitLine(Format('  storel %s, %s',
          [CurT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));
      end
      else if AStmt.ResolvedVarType.Kind = tyClass then
      begin
        OldVarT := AllocTemp();
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
    IdxW := AllocTemp();
    NxtW := AllocTemp();
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

  if AStmt.IsCodePointIter then
  begin
    { ---- String codepoint-iteration ----
      Calls _Utf8DecodeAt(strptr, byteIdx) which returns a packed Int64:
        low 21 bits = codepoint value, bits 32..33 = byte count (1-4).
      Loop advances by the decoded byte count each iteration. }
    IdxSlot := '%_var_' + AStmt.IdxVarName;
    LblCond := AllocLabel('forin_cond');
    LblBody := AllocLabel('forin_body');
    LblEnd  := AllocLabel('forin_end');

    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %s =w copy 0', [IdxSlot]))
    else
      EmitLine(Format('  storew 0, %s', [IdxSlot]));
    EmitLine(Format('  jmp @%s', [LblCond]));

    EmitLine('@' + LblCond);
    SelfT := EmitExpr(AStmt.CollExpr);
    OldT  := AllocTemp();
    OkT   := AllocTemp();
    IdxW  := AllocTemp();
    CmpT  := AllocTemp();
    EmitLine(Format('  %s =l add %s, -8', [OldT, SelfT]));
    EmitLine(Format('  %s =w loadw %s',   [OkT, OldT]));
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %s =w copy %s',  [IdxW, IdxSlot]))
    else
      EmitLine(Format('  %s =w loadw %s', [IdxW, IdxSlot]));
    EmitLine(Format('  %s =w csltw %s, %s', [CmpT, IdxW, OkT]));
    EmitLine(Format('  jnz %s, @%s, @%s', [CmpT, LblBody, LblEnd]));

    EmitLine('@' + LblBody);
    FBreakLabels.AddObject(LblEnd, TObject(PtrUInt(FExcDepth)));
    FContinueLabels.AddObject(LblCond, TObject(PtrUInt(FExcDepth)));
    try
      SelfT := EmitExpr(AStmt.CollExpr);
      IdxW  := AllocTemp();
      if IsPromoted(AStmt.IdxVarName) then
        EmitLine(Format('  %s =w copy %s',  [IdxW, IdxSlot]))
      else
        EmitLine(Format('  %s =w loadw %s', [IdxW, IdxSlot]));
      CurT := AllocTemp();
      EmitLine(Format('  %s =l call $_Utf8DecodeAt(l %s, w %s)', [CurT, SelfT, IdxW]));
      OkT := AllocTemp();
      EmitLine(Format('  %s =w copy %s', [OkT, CurT]));
      if not AStmt.VarIsGlobal and IsPromoted(AStmt.VarName) then
        EmitLine(Format('  %%_var_%s =w copy %s', [AStmt.VarName, OkT]))
      else
        EmitLine(Format('  storew %s, %s',
          [OkT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));
      OldT := AllocTemp();
      EmitLine(Format('  %s =l shr %s, 32', [OldT, CurT]));
      NxtW := AllocTemp();
      EmitLine(Format('  %s =w copy %s', [NxtW, OldT]));
      if IsPromoted(AStmt.AdvVarName) then
        EmitLine(Format('  %%_var_%s =w copy %s', [AStmt.AdvVarName, NxtW]))
      else
        EmitLine(Format('  storew %s, %s',
          [NxtW, VarRef(AStmt.AdvVarName, False)]));

      EmitStmt(AStmt.Body);
    finally
      FBreakLabels.Delete(FBreakLabels.Count - 1);
      FContinueLabels.Delete(FContinueLabels.Count - 1);
    end;

    IdxW := AllocTemp();
    NxtW := AllocTemp();
    OkT  := AllocTemp();
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %s =w copy %s', [IdxW, IdxSlot]))
    else
      EmitLine(Format('  %s =w loadw %s', [IdxW, IdxSlot]));
    if IsPromoted(AStmt.AdvVarName) then
      EmitLine(Format('  %s =w copy %%_var_%s', [OkT, AStmt.AdvVarName]))
    else
      EmitLine(Format('  %s =w loadw %s', [OkT, VarRef(AStmt.AdvVarName, False)]));
    EmitLine(Format('  %s =w add %s, %s', [NxtW, IdxW, OkT]));
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
    OldT  := AllocTemp();
    OkT   := AllocTemp();
    IdxW  := AllocTemp();
    CmpT  := AllocTemp();
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
      IdxW    := AllocTemp();
      IdxL    := AllocTemp();
      ElemPtr := AllocTemp();
      CurT    := AllocTemp();
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
    IdxW := AllocTemp();
    NxtW := AllocTemp();
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

    { Determine mask width from set type }
    SetMQT := QbeTypeOf(AStmt.CollExpr.ResolvedType);
    SetMLd := LoadInstrFor(AStmt.CollExpr.ResolvedType);
    SetMSt := StoreInstrFor(AStmt.CollExpr.ResolvedType);

    { Evaluate the set expression once and store in mask slot }
    MaskT := EmitExpr(AStmt.CollExpr);
    if IsPromoted(AStmt.SetMaskVarName) then
      EmitLine(Format('  %%_var_%s =%s copy %s', [AStmt.SetMaskVarName, SetMQT, MaskT]))
    else
      EmitLine(Format('  %s %s, %s', [SetMSt, MaskT, MaskSlot]));

    { Initialise index to 0 }
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %%_var_%s =w copy 0', [AStmt.IdxVarName]))
    else
      EmitLine(Format('  storew 0, %s', [IdxSlot]));
    EmitLine(Format('  jmp @%s', [LblCond]));

    { Condition: idx < BitCount }
    EmitLine('@' + LblCond);
    IdxW := AllocTemp();
    CmpT := AllocTemp();
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %s =w copy %s', [IdxW, IdxSlot]))
    else
      EmitLine(Format('  %s =w loadw %s', [IdxW, IdxSlot]));
    EmitLine(Format('  %s =w csltw %s, %d', [CmpT, IdxW, AStmt.SetBitCount]));
    EmitLine(Format('  jnz %s, @%s, @%s', [CmpT, LblBody, LblEnd]));

    { Body block: test bit, skip if clear }
    EmitLine('@' + LblBody);
    MaskT := AllocTemp();
    BitT  := AllocTemp();
    if IsPromoted(AStmt.SetMaskVarName) then
      EmitLine(Format('  %s =%s copy %%_var_%s', [MaskT, SetMQT, AStmt.SetMaskVarName]))
    else
      EmitLine(Format('  %s =%s %s %s', [MaskT, SetMQT, SetMLd, MaskSlot]));
    IdxW := AllocTemp();
    if IsPromoted(AStmt.IdxVarName) then
      EmitLine(Format('  %s =w copy %s', [IdxW, IdxSlot]))
    else
      EmitLine(Format('  %s =w loadw %s', [IdxW, IdxSlot]));
    EmitLine(Format('  %s =%s shr %s, %s', [BitT, SetMQT, MaskT, IdxW]));
    CmpT := AllocTemp();
    EmitLine(Format('  %s =w and %s, 1', [CmpT, BitT]));
    { If bit is 0 skip body, go directly to forin_next }
    EmitLine(Format('  jnz %s, @%s_yes, @%s', [CmpT, LblBody, LblNext]));
    EmitLine('@' + LblBody + '_yes');

    FBreakLabels.AddObject(LblEnd, TObject(PtrUInt(FExcDepth)));
    FContinueLabels.AddObject(LblNext, TObject(PtrUInt(FExcDepth)));
    try
      { Assign ordinal (idx) to loop variable as enum }
      OrdT := AllocTemp();
      IdxW := AllocTemp();
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
    IdxW := AllocTemp();
    NxtW := AllocTemp();
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
  EnumT := AllocTemp();
  FuncName := '$' + MethodEmitName(GetEDecl, GetEDecl.OwnerTypeName, GetEDecl.Name);
  if GetEDecl.VTableSlot >= 0 then
  begin
    VTblT   := AllocTemp();
    FPtrT   := AllocTemp();
    SlotOff := (GetEDecl.VTableSlot + 1) * 8;
    EmitLine(Format('  %s =l loadl %s', [VTblT, SelfT]));
    if SlotOff = 0 then
      EmitLine(Format('  %s =l loadl %s', [FPtrT, VTblT]))
    else
    begin
      OldT := AllocTemp();
      EmitLine(Format('  %s =l add %s, %d', [OldT, VTblT, SlotOff]));
      EmitLine(Format('  %s =l loadl %s', [FPtrT, OldT]));
    end;
    EmitLine(Format('  %s =l call %s(l %s)', [EnumT, FPtrT, SelfT]));
  end
  else
    EmitLine(Format('  %s =l call %s(l %s)', [EnumT, FuncName, SelfT]));

  { ARC-assign the enumerator into the synthetic slot }
  OldT := AllocTemp();
  EmitLine(Format('  %s =l loadl %s', [OldT, EnumSlot]));
  EmitLine(Format('  call $_ClassAddRef(l %s)', [EnumT]));
  EmitLine(Format('  call $_ClassRelease(l %s)', [OldT]));
  EmitLine(Format('  storel %s, %s', [EnumT, EnumSlot]));

  EmitLine(Format('  jmp @%s', [LblCond]));

  { --- Condition: call MoveNext --- }
  EmitLine('@' + LblCond);
  SelfT    := AllocTemp();
  EmitLine(Format('  %s =l loadl %s', [SelfT, EnumSlot]));
  OkT      := AllocTemp();
  FuncName := '$' + MethodEmitName(MNDecl, MNDecl.OwnerTypeName, MNDecl.Name);
  if MNDecl.VTableSlot >= 0 then
  begin
    VTblT   := AllocTemp();
    FPtrT   := AllocTemp();
    SlotOff := (MNDecl.VTableSlot + 1) * 8;
    EmitLine(Format('  %s =l loadl %s', [VTblT, SelfT]));
    if SlotOff = 0 then
      EmitLine(Format('  %s =l loadl %s', [FPtrT, VTblT]))
    else
    begin
      OldT := AllocTemp();
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
    SelfT    := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [SelfT, EnumSlot]));
    QType    := QbeTypeOf(CurDecl.ResolvedReturnType);
    FuncName := '$' + MethodEmitName(CurDecl, CurDecl.OwnerTypeName, CurDecl.Name);
    CurT     := AllocTemp();
    if CurDecl.VTableSlot >= 0 then
    begin
      VTblT   := AllocTemp();
      FPtrT   := AllocTemp();
      SlotOff := (CurDecl.VTableSlot + 1) * 8;
      EmitLine(Format('  %s =l loadl %s', [VTblT, SelfT]));
      if SlotOff = 0 then
        EmitLine(Format('  %s =l loadl %s', [FPtrT, VTblT]))
      else
      begin
        OldT := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d', [OldT, VTblT, SlotOff]));
        EmitLine(Format('  %s =l loadl %s', [FPtrT, OldT]));
      end;
      EmitLine(Format('  %s =%s call %s(l %s)', [CurT, QType, FPtrT, SelfT]));
    end
    else
      EmitLine(Format('  %s =%s call %s(l %s)', [CurT, QType, FuncName, SelfT]));

    { Assign Current result to the loop variable }
    if AStmt.ResolvedVarType.IsString() then
    begin
      OldVarT := AllocTemp();
      EmitLine(Format('  %s =l loadl %s',
        [OldVarT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));
      EmitLine(Format('  call $_StringAddRef(l %s)', [CurT]));
      EmitLine(Format('  call $_StringRelease(l %s)', [OldVarT]));
      EmitLine(Format('  storel %s, %s',
        [CurT, VarRef(AStmt.VarName, AStmt.VarIsGlobal)]));
    end
    else if AStmt.ResolvedVarType.Kind = tyClass then
    begin
      OldVarT := AllocTemp();
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

{ Returns True when AExpr already carries a +1 owned reference on return,
  meaning the assignment site must NOT emit an additional _ClassAddRef.

  Only function and method calls that return a class value qualify — because
  the callee's Result assignment already emitted _ClassAddRef, transferring
  ownership to the caller.  Constructors are excluded: the constructor EmitExpr
  path emits only _ClassAlloc (rc=0); the sole _ClassAddRef is emitted by the
  assignment site.

  Variable reads, field reads, type casts, and lookups do NOT own their result
  and always need the assignment-site AddRef. }
function ExprOwnsRef(AExpr: TASTExpr): Boolean;
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
    Without covering tyString/tyDynArray here the assignment branches below
    emit a spurious _StringAddRef/_DynArrayAddRef on the call result, which
    is never balanced and leaks one buffer per call. }
  if not (AExpr.ResolvedType.Kind in [tyClass, tyDynArray])
     and not AExpr.ResolvedType.IsString() then Exit;
  if AExpr is TIdentExpr then
  begin
    IE := TIdentExpr(AExpr);
    if IE.IsImplicitSelfMethod then
      Exit(True);
  end;
  { Constructor calls via TFieldAccessExpr (TFoo.Create) — do NOT own }
  if AExpr is TFieldAccessExpr then
  begin
    FA := TFieldAccessExpr(AExpr);
    if FA.IsConstructorCall then Exit;
    if FA.IsMethodCall then begin Result := True; Exit end;
    { Method-backed property read (read GetX): the getter returns +1.
      Field-backed reads (read FX) emit a plain load and do NOT own. }
    if (FA.PropRead <> nil) and (FA.PropRead.ReadMethod <> '') then
    begin
      Exit(True);
    end;
  end;
  { TMethodCallExpr: constructor calls do NOT own; all other method calls DO }
  if AExpr is TMethodCallExpr then
  begin
    MC := TMethodCallExpr(AExpr);
    if not MC.IsConstructorCall then Result := True;
    Exit;
  end;
  { Explicit function calls (free functions returning a class) — owns +1.
    Type casts (TClassName(expr)) are also TFuncCallExpr but have nil
    ResolvedDecl — they reinterpret the pointer without AddRef. }
  if AExpr is TFuncCallExpr then
  begin
    if (TFuncCallExpr(AExpr).ResolvedDecl <> nil) or
       TFuncCallExpr(AExpr).IsIndirectCall then
      Result := True;
    Exit;
  end;
end;

procedure TCodeGenQBE.EmitOwnedArgReleases(AArgs: TObjectList;
  AArgTemps: TStringList; AParams: TObjectList);
var
  I: Integer;
  Arg: TASTExpr;
  Par: TMethodParam;
begin
  for I := 0 to AArgs.Count - 1 do
  begin
    if I >= AArgTemps.Count then Break;
    if AArgTemps.Strings[I] = '' then Continue;
    Arg := TASTExpr(AArgs.Items[I]);
    if not ExprOwnsRef(Arg) then Continue;
    Par := nil;
    if (AParams <> nil) and (I < AParams.Count) then
      Par := TMethodParam(AParams.Items[I]);
    { The argument is a call result that already owns +1 and is passed by
      value; release that transient after the call.  Dispatch on the actual
      ARC kind — _ClassRelease/_StringRelease/_DynArrayRelease read the
      refcount at different header offsets (16/12/8 bytes), so releasing a
      String or dyn-array via _ClassRelease would corrupt the heap. }
    if Arg.ResolvedType = nil then
      EmitLine(Format('  call $_ClassRelease(l %s)', [AArgTemps.Strings[I]]))
    else if Arg.ResolvedType.IsString() then
    begin
      { Const-string params already balance the transient via
        EnsureConstStringRef (AddRef before) + ReleaseConstStringArgs
        (Release after).  Emitting another release here would release the
        same temporary twice and corrupt the heap, so skip it. }
      if not ((Par <> nil) and Par.IsConstParam) then
        EmitLine(Format('  call $_StringRelease(l %s)', [AArgTemps.Strings[I]]));
    end
    else if Arg.ResolvedType.Kind = tyDynArray then
      EmitLine(Format('  call $_DynArrayRelease(l %s)', [AArgTemps.Strings[I]]))
    else
      EmitLine(Format('  call $_ClassRelease(l %s)', [AArgTemps.Strings[I]]));
  end;
end;

{ call $_StringAddRef(l <ArgTemp>) }
procedure TCodeGenQBE.EnsureConstStringRef(const AArgTemp: string;
  APar: TMethodParam);
begin
  if (APar = nil) or (AArgTemp = '') then Exit;
  if APar.IsConstParam and (APar.ResolvedType <> nil) and
     (APar.ResolvedType.Kind = tyString) then
    EmitLine(Format('  call $_StringAddRef(l %s)', [AArgTemp]));
end;

{ call $_StringRelease(l <ArgTemps[I]>) for each const-string param. }
procedure TCodeGenQBE.ReleaseConstStringArgs(AArgs: TObjectList;
  AArgTemps: TStringList; AParams: TObjectList);
var
  I: Integer;
  Par: TMethodParam;
begin
  if (AArgs = nil) or (AArgTemps = nil) or (AParams = nil) then Exit;
  for I := 0 to AArgs.Count - 1 do
  begin
    if I >= AArgTemps.Count then Break;
    if AArgTemps.Strings[I] = '' then Continue;
    if I >= AParams.Count then Break;
    Par := TMethodParam(AParams.Items[I]);
    if Par.IsConstParam and (Par.ResolvedType <> nil) and
       (Par.ResolvedType.Kind = tyString) then
      EmitLine(Format('  call $_StringRelease(l %s)',
        [AArgTemps.Strings[I]]));
  end;
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

  { Inline frame: assignment to Result inside an inlined body stores into
    the per-call-site result slot, not the caller's Result. }
  if InsideInlineFrame() and SameText(AAssign.Name, 'Result') then
  begin
    ValTemp := EmitExpr(AAssign.Expr);
    QType   := InlineResultQType();
    ValTemp := CoerceArg(ValTemp, AAssign.Expr, QType);
    case QType of
      'w': EmitLine(Format('  storew %s, %s', [ValTemp, InlineResultTemp()]));
      'l': EmitLine(Format('  storel %s, %s', [ValTemp, InlineResultTemp()]));
      'd': EmitLine(Format('  stored %s, %s', [ValTemp, InlineResultTemp()]));
      's': EmitLine(Format('  stores %s, %s', [ValTemp, InlineResultTemp()]));
    else
      EmitLine(Format('  storel %s, %s', [ValTemp, InlineResultTemp()]));
    end;
    Exit;
  end;

  { Captured outer-scope variable: %_cap_Name IS the address of the var in
    the enclosing frame — store directly to that address. }
  if (AAssign.ImplicitSelfField = nil) and IsCaptured(AAssign.Name) then
  begin
    ValTemp := EmitExpr(AAssign.Expr);
    QType   := QbeTypeOf(AAssign.ResolvedLhsType);
    ValTemp := CoerceArg(ValTemp, AAssign.Expr, QType);
    case QType of
      'w': EmitLine(Format('  storew %s, %%_cap_%s', [ValTemp, AAssign.Name]));
      'l': EmitLine(Format('  storel %s, %%_cap_%s', [ValTemp, AAssign.Name]));
      'd': EmitLine(Format('  stored %s, %%_cap_%s', [ValTemp, AAssign.Name]));
      's': EmitLine(Format('  stores %s, %%_cap_%s', [ValTemp, AAssign.Name]));
    else
      EmitLine(Format('  storel %s, %%_cap_%s', [ValTemp, AAssign.Name]));
    end;
    Exit;
  end;

  { Implicit Self.Field assignment: bare field name like FPos := ... }
  if AAssign.ImplicitSelfField <> nil then
  begin
    ISFld   := TFieldInfo(AAssign.ImplicitSelfField);
    { Compute destination address = Self + field offset }
    ObjTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %%_var_Self', [ObjTemp]));
    if ISFld.Offset > 0 then
    begin
      ISAddrT := AllocTemp();
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
        EmitLine(Format('  call $memset(l %s, w 0, l %d)', [ObjTemp, ClassRT.TotalSize()]));
        EmitRecordCallSret(AAssign.Expr, ObjTemp);
      end
      else
      begin
        ValTemp := EmitExpr(AAssign.Expr);
        EmitRecordCopy(ClassRT, ObjTemp, ValTemp);
      end;
      Exit;
    end;
    { Interface field: fat-pointer stored as two consecutive 8-byte slots
      (obj at offset, itab at offset+8).  ObjTemp already points at the
      obj slot; the itab slot is 8 bytes further. }
    if ISFld.TypeDesc.Kind = tyInterface then
    begin
      ISAddrT := AllocTemp();
      EmitLine(Format('  %s =l add %s, 8', [ISAddrT, ObjTemp]));
      EmitInterfaceToFieldSlots(AAssign.Expr, ObjTemp, ISAddrT, ISFld.TypeDesc);
      Exit;
    end;
    ValTemp := EmitExpr(AAssign.Expr);
    QType := QbeTypeOf(ISFld.TypeDesc);
    if QType = 'w' then
      EmitLine(Format('  %s %s, %s', [StoreInstrFor(ISFld.TypeDesc), ValTemp, ObjTemp]))
    else
    begin
      if QbeTypeOf(AAssign.Expr.ResolvedType) = 'w' then
      begin
        ExtTemp := AllocTemp();
        EmitLine(Format('  %s =l extsw %s', [ExtTemp, ValTemp]));
        ValTemp := ExtTemp;
      end;
      { ARC for class/string field stored via implicit Self.Field }
      if ISFld.IsUnretained and (ISFld.TypeDesc.Kind = tyClass) then
      begin
        EmitLine(Format('  storel %s, %s', [ValTemp, ObjTemp]));
        if ExprOwnsRef(AAssign.Expr) then
          EmitLine(Format('  call $_ClassRelease(l %s)', [ValTemp]));
        Exit;
      end;
      if ISFld.IsWeak and (ISFld.TypeDesc.Kind = tyClass) then
      begin
        { Weak class field: route through _WeakAssign so the runtime can
          zero the slot if the target is freed.  No strong refcount change. }
        EmitLine(Format('  call $_WeakAssign(l %s, l %s)', [ObjTemp, ValTemp]));
        Exit;
      end;
      if ISFld.TypeDesc.IsString() then
      begin
        OldTemp := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [OldTemp, ObjTemp]));
        if not ExprOwnsRef(AAssign.Expr) then
          EmitLine(Format('  call $_StringAddRef(l %s)',  [ValTemp]));
        EmitLine(Format('  call $_StringRelease(l %s)', [OldTemp]));
      end
      else if ISFld.TypeDesc.Kind = tyClass then
      begin
        OldTemp := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [OldTemp, ObjTemp]));
        if not ExprOwnsRef(AAssign.Expr) then
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
    ItabTemp  := AllocTemp();
    EmitLine(Format('  %s =l call $_GetItab(l %s, l $typeinfo_%s)',
      [ItabTemp, ObjTemp, ClassSymName(AE.TypeName)]));
    CheckTemp := AllocTemp();
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
      OldTemp := AllocTemp();
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
    ItabName := '$itab_' + QBEMangle(ClassSymName(ClassRT.Name)) + '_' + QBEMangle(IntfDesc.Name);
    ValTemp  := EmitExpr(AAssign.Expr);
    if AAssign.IsWeakLhs then
      EmitLine(Format('  call $_WeakAssign(l %s_obj, l %s)',
        [VarRef(AAssign.Name, AAssign.IsGlobal), ValTemp]))
    else
    begin
      OldTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s_obj', [OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
      if not ExprOwnsRef(AAssign.Expr) then
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
    ObjTemp  := AllocTemp();
    ItabTemp := AllocTemp();
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
    OldTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s_obj', [OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    EmitLine(Format('  call $_ClassAddRef(l %s)',  [ObjTemp]));
    EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
    EmitLine(Format('  storel %s, %s_obj',  [ObjTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    EmitLine(Format('  storel %s, %s_itab', [ItabTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    Exit;
  end;

  { Interface := nil — clear the fat pointer (obj + itab slots).  Without
    this case a nil assignment falls through to the scalar store path, which
    emits a single-slot `storew ..., $Name` against a variable that has no
    `$Name` data definition (only `$Name_obj` / `$Name_itab`), producing an
    undefined-symbol link error for interface-typed globals.  For a strong
    reference the prior obj ref is released; weak references unregister via
    _WeakClear.  The itab slot is static rodata and is simply zeroed. }
  if (AAssign.ResolvedLhsType <> nil) and
     (AAssign.ResolvedLhsType.Kind = tyInterface) and
     (AAssign.Expr is TNilLiteral) then
  begin
    if AAssign.IsWeakLhs then
      EmitLine(Format('  call $_WeakClear(l %s_obj)',
        [VarRef(AAssign.Name, AAssign.IsGlobal)]))
    else
    begin
      OldTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s_obj', [OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
      EmitLine(Format('  storel 0, %s_obj', [VarRef(AAssign.Name, AAssign.IsGlobal)]));
    end;
    EmitLine(Format('  storel 0, %s_itab', [VarRef(AAssign.Name, AAssign.IsGlobal)]));
    Exit;
  end;

  if AAssign.IsVarParam then
  begin
    PtrTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %%_var_%s', [PtrTemp, AAssign.Name]));
    if AAssign.Expr.ResolvedType.IsString() then
    begin
      OldTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [OldTemp, PtrTemp]));
      ValTemp := EmitExpr(AAssign.Expr);
      if not ExprOwnsRef(AAssign.Expr) then
        EmitLine(Format('  call $_StringAddRef(l %s)', [ValTemp]));
      EmitLine(Format('  call $_StringRelease(l %s)', [OldTemp]));
      EmitLine(Format('  storel %s, %s', [ValTemp, PtrTemp]));
    end
    else if AAssign.Expr.ResolvedType.Kind = tyClass then
    begin
      OldTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [OldTemp, PtrTemp]));
      ValTemp := EmitExpr(AAssign.Expr);
      if not ExprOwnsRef(AAssign.Expr) then
        EmitLine(Format('  call $_ClassAddRef(l %s)', [ValTemp]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
      EmitLine(Format('  storel %s, %s', [ValTemp, PtrTemp]));
    end
    else if (AAssign.ResolvedLhsType <> nil) and
            (AAssign.ResolvedLhsType.Kind = tyRecord) then
    begin
      { Record through a var/out param: PtrTemp already holds the caller's
        record address (loaded from the pointer slot).  Copy into it as for a
        normal record LHS — sret for a record-returning call, else ARC-aware
        field copy.  Storing a single word here (the old default branch) would
        write only 8 bytes and corrupt the record. }
      ClassRT := TRecordTypeDesc(AAssign.ResolvedLhsType);
      if IsRecordCall(AAssign.Expr) then
      begin
        EmitRecordReleaseFields(ClassRT, PtrTemp);
        EmitLine(Format('  call $memset(l %s, w 0, l %d)',
          [PtrTemp, ClassRT.TotalSize()]));
        EmitRecordCallSret(AAssign.Expr, PtrTemp);
      end
      else
      begin
        ValTemp := EmitExpr(AAssign.Expr);
        EmitRecordCopy(ClassRT, PtrTemp, ValTemp);
      end;
    end
    else
    begin
      ValTemp    := EmitExpr(AAssign.Expr);
      StoreInstr := StoreInstrFor(AAssign.Expr.ResolvedType);
      EmitLine(Format('  %s %s, %s', [StoreInstr, ValTemp, PtrTemp]));
    end;
  end
  else if (AAssign.ResolvedLhsType <> nil) and
          (AAssign.ResolvedLhsType.Kind = tyRecord) then
  begin
    { Record assignment (non-var-param LHS — the var/out case is handled in the
      IsVarParam branch above): use sret (directly into dest) or field-by-field
      copy. }
    ClassRT := TRecordTypeDesc(AAssign.ResolvedLhsType);
    if IsRecordCall(AAssign.Expr) then
    begin
      { Release old ARC fields, zero the slot, then call function with dest as sret }
      EmitRecordReleaseFields(ClassRT, VarRef(AAssign.Name, AAssign.IsGlobal));
      EmitLine(Format('  call $memset(l %s, w 0, l %d)',
        [VarRef(AAssign.Name, AAssign.IsGlobal), ClassRT.TotalSize()]));
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
  else if AAssign.Expr.ResolvedType.IsString() then
  begin
    { ARC: load old, compute new, retain new, release old, store new }
    OldTemp := AllocTemp();
    if not AAssign.IsGlobal and IsPromoted(AAssign.Name) then
      EmitLine(Format('  %s =l copy %%_var_%s', [OldTemp, AAssign.Name]))
    else
      EmitLine(Format('  %s =l loadl %s', [OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    ValTemp := EmitExpr(AAssign.Expr);
    if not ExprOwnsRef(AAssign.Expr) then
      EmitLine(Format('  call $_StringAddRef(l %s)', [ValTemp]));
    EmitLine(Format('  call $_StringRelease(l %s)', [OldTemp]));
    if not AAssign.IsGlobal and IsPromoted(AAssign.Name) then
      EmitLine(Format('  %%_var_%s =l copy %s', [AAssign.Name, ValTemp]))
    else
      EmitLine(Format('  storel %s, %s', [ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
  end
  else if (AAssign.ResolvedLhsType <> nil) and
          (AAssign.ResolvedLhsType.Kind = tyDynArray) then
  begin
    { Dynamic-array variable assignment: same ARC shape as string. The dyn-array
      data pointer carries a refcount in its header, so b := a must retain the
      new buffer and release the old before overwriting the slot. }
    OldTemp := AllocTemp();
    if not AAssign.IsGlobal and IsPromoted(AAssign.Name) then
      EmitLine(Format('  %s =l copy %%_var_%s', [OldTemp, AAssign.Name]))
    else
      EmitLine(Format('  %s =l loadl %s', [OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    ValTemp := EmitExpr(AAssign.Expr);
    if not ExprOwnsRef(AAssign.Expr) then
      EmitLine(Format('  call $_DynArrayAddRef(l %s)', [ValTemp]));
    EmitLine(Format('  call $_DynArrayRelease(l %s)', [OldTemp]));
    if not AAssign.IsGlobal and IsPromoted(AAssign.Name) then
      EmitLine(Format('  %%_var_%s =l copy %s', [AAssign.Name, ValTemp]))
    else
      EmitLine(Format('  storel %s, %s', [ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
  end
  else if (AAssign.ResolvedLhsType <> nil) and
          (AAssign.ResolvedLhsType.Kind = tyClass) and
          (AAssign.Expr is TNilLiteral) then
  begin
    if AAssign.IsWeakLhs then
      EmitLine(Format('  call $_WeakClear(l %s)',
        [VarRef(AAssign.Name, AAssign.IsGlobal)]))
    else
    begin
      OldTemp := AllocTemp();
      if not AAssign.IsGlobal and IsPromoted(AAssign.Name) then
        EmitLine(Format('  %s =l copy %%_var_%s', [OldTemp, AAssign.Name]))
      else
        EmitLine(Format('  %s =l loadl %s', [OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
      if not AAssign.IsGlobal and IsPromoted(AAssign.Name) then
        EmitLine(Format('  %%_var_%s =l copy 0', [AAssign.Name]))
      else
        EmitLine(Format('  storel 0, %s', [VarRef(AAssign.Name, AAssign.IsGlobal)]));
    end;
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
    { ARC: retain new, release prior slot content, store new.

      When the LHS is a local non-promoted slot that has not been written
      yet within the function entry block, EmitVarAllocs has already
      zeroed it via `storel 0, %%_var_X`.  Releasing nil is a no-op at
      runtime but still pays a function-call/ret per assignment — so the
      nil-slot fast path elides the load+release entirely.

      Note: promoted locals (mem2reg SSA copies) live in registers and
      track value-history through copies, so they require their own
      old-value bookkeeping; we conservatively skip elision for them. }
    if not AAssign.IsGlobal and not IsPromoted(AAssign.Name) and
       ArcSlotIsNil(AAssign.Name) then
    begin
      ValTemp := EmitExpr(AAssign.Expr);
      if not ExprOwnsRef(AAssign.Expr) then
        EmitLine(Format('  call $_ClassAddRef(l %s)', [ValTemp]));
      EmitLine(Format('  storel %s, %s',
        [ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
      MarkArcSlotWritten(AAssign.Name);
    end
    else
    begin
      OldTemp := AllocTemp();
      if not AAssign.IsGlobal and IsPromoted(AAssign.Name) then
        EmitLine(Format('  %s =l copy %%_var_%s', [OldTemp, AAssign.Name]))
      else
        EmitLine(Format('  %s =l loadl %s', [OldTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
      ValTemp := EmitExpr(AAssign.Expr);
      if not ExprOwnsRef(AAssign.Expr) then
        EmitLine(Format('  call $_ClassAddRef(l %s)', [ValTemp]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
      if not AAssign.IsGlobal and IsPromoted(AAssign.Name) then
        EmitLine(Format('  %%_var_%s =l copy %s', [AAssign.Name, ValTemp]))
      else
        EmitLine(Format('  storel %s, %s', [ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
      MarkArcSlotWritten(AAssign.Name);
    end;
  end
  else if (AAssign.ResolvedLhsType <> nil) and
          (AAssign.ResolvedLhsType.Kind = tyClass) and
          (AAssign.Expr.ResolvedType.Kind = tyPointer) then
  begin
    { Pointer-to-class coercion: the RHS is Pointer-typed (e.g. from
      TStringList.Objects[]) but the LHS is a class-typed ARC-managed
      variable.  Without this branch the code falls through to the scalar
      store and no _ClassAddRef is emitted — the variable then receives a
      spurious _ClassRelease at scope exit, corrupting the refcount of the
      object that the Pointer holds.
      Treat as a normal class assignment: retain the incoming pointer value
      and release the old slot contents. }
    if not AAssign.IsGlobal and not IsPromoted(AAssign.Name) and
       ArcSlotIsNil(AAssign.Name) then
    begin
      ValTemp := EmitExpr(AAssign.Expr);
      EmitLine(Format('  call $_ClassAddRef(l %s)', [ValTemp]));
      EmitLine(Format('  storel %s, %s',
        [ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
      MarkArcSlotWritten(AAssign.Name);
    end
    else
    begin
      OldTemp := AllocTemp();
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
      MarkArcSlotWritten(AAssign.Name);
    end;
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
        ExtTemp := AllocTemp();
        EmitLine(Format('  %s =d swtof %s', [ExtTemp, ValTemp]));
        ValTemp := ExtTemp;
      end
      else if (AAssign.Expr.ResolvedType <> nil) and
              (QbeTypeOf(AAssign.Expr.ResolvedType) = 'l') and
              not AAssign.Expr.ResolvedType.IsFloat() then
      begin
        ExtTemp := AllocTemp();
        EmitLine(Format('  %s =d sltof %s', [ExtTemp, ValTemp]));
        ValTemp := ExtTemp;
      end
      else if (AAssign.Expr.ResolvedType <> nil) and
              (AAssign.Expr.ResolvedType.Kind = tySingle) then
      begin
        ExtTemp := AllocTemp();
        EmitLine(Format('  %s =d exts %s', [ExtTemp, ValTemp]));
        ValTemp := ExtTemp;
      end;
      if not AAssign.IsGlobal and IsPromoted(AAssign.Name) then
        EmitLine(Format('  %%_var_%s =d copy %s', [AAssign.Name, ValTemp]))
      else
        EmitLine(Format('  stored %s, %s', [ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    end
    else if (AAssign.ResolvedLhsType <> nil) and
            (AAssign.ResolvedLhsType.Kind = tySingle) then
    begin
      ValTemp := EmitExpr(AAssign.Expr);
      if (AAssign.Expr.ResolvedType <> nil) and
         (QbeTypeOf(AAssign.Expr.ResolvedType) = 'w') and
         not AAssign.Expr.ResolvedType.IsFloat() then
      begin
        ExtTemp := AllocTemp();
        EmitLine(Format('  %s =s swtof %s', [ExtTemp, ValTemp]));
        ValTemp := ExtTemp;
      end
      else if (AAssign.Expr.ResolvedType <> nil) and
              (QbeTypeOf(AAssign.Expr.ResolvedType) = 'l') and
              not AAssign.Expr.ResolvedType.IsFloat() then
      begin
        ExtTemp := AllocTemp();
        EmitLine(Format('  %s =s sltof %s', [ExtTemp, ValTemp]));
        ValTemp := ExtTemp;
      end
      else if (AAssign.Expr.ResolvedType <> nil) and
              (AAssign.Expr.ResolvedType.Kind = tyDouble) then
      begin
        ExtTemp := AllocTemp();
        EmitLine(Format('  %s =s truncd %s', [ExtTemp, ValTemp]));
        ValTemp := ExtTemp;
      end;
      if not AAssign.IsGlobal and IsPromoted(AAssign.Name) then
        EmitLine(Format('  %%_var_%s =s copy %s', [AAssign.Name, ValTemp]))
      else
        EmitLine(Format('  stores %s, %s', [ValTemp, VarRef(AAssign.Name, AAssign.IsGlobal)]));
    end
    else if (AAssign.ResolvedLhsType <> nil) and
            (QbeTypeOf(AAssign.ResolvedLhsType) = 'l') then
    begin
      ValTemp := EmitExpr(AAssign.Expr);
      if QbeTypeOf(AAssign.Expr.ResolvedType) = 'w' then
      begin
        ExtTemp := AllocTemp();
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
      SelfT   := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_Self', [SelfT]));
      if ImplFld.Offset > 0 then
      begin
        Ptr := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d', [Ptr, SelfT, ImplFld.Offset]));
        SelfT := Ptr;
      end;
      Loaded := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [Loaded, SelfT]));
      Exit(Loaded);
    end;
    if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyClass) then
    begin
      Loaded := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [Loaded, VarRef(Id.Name, Id.IsGlobal)]));
      Result := Loaded;
    end
    else if Id.IsVarParam then
    begin
      { Var-record param: dereference the param slot to get the actual record
        address. }
      Loaded := AllocTemp();
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
      Exit(EmitExpr(Fld));
    end;
    if Fld.Base <> nil then
      Base := EmitInstancePtr(Fld.Base)
    else if Fld.IsImplicitSelf then
    begin
      { Leaf: RecordName is a field of Self — load through %_var_Self. }
      SelfT := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_Self', [SelfT]));
      if Fld.ImplicitBaseInfo.Offset > 0 then
      begin
        Ptr := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d', [Ptr, SelfT, Fld.ImplicitBaseInfo.Offset]));
        SelfT := Ptr;
      end;
      Loaded := AllocTemp();
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
        Loaded := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [Loaded, VarRef(Fld.RecordName, Fld.IsGlobal)]));
        Base := Loaded;
      end
      else if Fld.IsVarParam then
      begin
        { Var-record param leaf: dereference the param slot. }
        Loaded := AllocTemp();
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
      Ptr := AllocTemp();
      EmitLine(Format('  %s =l add %s, %d',
        [Ptr, Base, Fld.FieldInfo.Offset]));
    end
    else
      Ptr := Base;
    { If this field is a class pointer, load it to get the heap object pointer.
      If it is an inline record, the pointer itself points to the storage. }
    if Fld.FieldInfo.TypeDesc.Kind = tyClass then
    begin
      Loaded := AllocTemp();
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
    Exit(EmitExpr(AExpr));
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
    PtrTemp := AllocTemp();
    EmitLine(Format('  %s =l add %s, %d', [PtrTemp, Base, AOffset]));
    Result := PtrTemp;
  end;
end;

function TCodeGenQBE.VarRef(const AName: string; AIsGlobal: Boolean): string;
begin
  if AIsGlobal then
  begin
    if FThreadVarNames.IndexOf(AName) >= 0 then
      Result := 'thread $' + AName
    else
      Result := '$' + AName;
  end
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
    Result := AllocTemp();
    EmitLine(Format('  %s =l loadl %%_var_%s', [Result, AIdent.Name]));
  end
  else if AIdent.IsImplicitSelf then
  begin
    // Field of Self — compute address as Self pointer + field offset.
    ImplFld := TFieldInfo(AIdent.ImplicitFieldInfo);
    SelfT := AllocTemp();
    EmitLine(Format('  %s =l loadl %%_var_Self', [SelfT]));
    if ImplFld.Offset > 0 then
    begin
      Result := AllocTemp();
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
    Exit(EmitVarArgAddr(TIdentExpr(AExpr)));
  end;
  if AExpr is TDerefExpr then
  begin
    { P^ as L-value: the pointer's value IS the address. }
    Deref := TDerefExpr(AExpr);
    Exit(EmitExpr(Deref.Expr));
  end;
  if AExpr is TFieldAccessExpr then
  begin
    FldAcc := TFieldAccessExpr(AExpr);
    if FldAcc.Base <> nil then
      BaseAddr := EmitInstancePtr(FldAcc.Base)
    else if FldAcc.IsClassAccess then
    begin
      { Class field leaf: the variable's slot holds a pointer to the heap
        object — load it so the offset addition reaches the field, not a
        location adjacent to the slot itself. }
      T := AllocTemp();
      EmitLine(Format('  %s =l loadl %s',
        [T, VarRef(FldAcc.RecordName, FldAcc.IsGlobal)]));
      BaseAddr := T;
    end
    else if FldAcc.IsImplicitSelf then
    begin
      T := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_Self', [T]));
      if (FldAcc.ImplicitBaseInfo <> nil) and (FldAcc.ImplicitBaseInfo.Offset > 0) then
      begin
        BaseAddr := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d',
          [BaseAddr, T, FldAcc.ImplicitBaseInfo.Offset]));
      end
      else
        BaseAddr := T;
      if FldAcc.IsClassAccess then
      begin
        T := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [T, BaseAddr]));
        BaseAddr := T;
      end;
    end
    else if FldAcc.IsVarParam then
    begin
      { Var-record param leaf: dereference the param slot. }
      T := AllocTemp();
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
      T := AllocTemp();
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
      SrcField := AllocTemp();
      EmitLine(Format('  %s =l add %s, %d', [SrcField, ASrcAddr, F.Offset]));
      DstField := AllocTemp();
      EmitLine(Format('  %s =l add %s, %d', [DstField, ADestAddr, F.Offset]));
    end
    else
    begin
      SrcField := ASrcAddr;
      DstField := ADestAddr;
    end;
    if F.TypeDesc.IsString() then
    begin
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [ValTemp, SrcField]));
      OldTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [OldTemp, DstField]));
      EmitLine(Format('  call $_StringAddRef(l %s)', [ValTemp]));
      EmitLine(Format('  call $_StringRelease(l %s)', [OldTemp]));
      EmitLine(Format('  storel %s, %s', [ValTemp, DstField]));
    end
    else if F.TypeDesc.Kind = tyClass then
    begin
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [ValTemp, SrcField]));
      OldTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [OldTemp, DstField]));
      EmitLine(Format('  call $_ClassAddRef(l %s)', [ValTemp]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
      EmitLine(Format('  storel %s, %s', [ValTemp, DstField]));
    end
    else if F.TypeDesc.Kind = tyDynArray then
    begin
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [ValTemp, SrcField]));
      OldTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [OldTemp, DstField]));
      EmitLine(Format('  call $_DynArrayAddRef(l %s)', [ValTemp]));
      EmitLine(Format('  call $_DynArrayRelease(l %s)', [OldTemp]));
      EmitLine(Format('  storel %s, %s', [ValTemp, DstField]));
    end
    else if F.TypeDesc.Kind = tyInterface then
    begin
      { Interface field: 16-byte fat pointer (obj at +0, itab at +8). Only the
        obj slot is refcounted; the itab slot is static rodata. }
      ValTemp := AllocTemp();              { src obj }
      EmitLine(Format('  %s =l loadl %s', [ValTemp, SrcField]));
      OldTemp := AllocTemp();              { dst obj (to release) }
      EmitLine(Format('  %s =l loadl %s', [OldTemp, DstField]));
      EmitLine(Format('  call $_ClassAddRef(l %s)',  [ValTemp]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
      EmitLine(Format('  storel %s, %s', [ValTemp, DstField]));
      { Copy itab slot (src+8 → dst+8). }
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l add %s, 8', [ValTemp, SrcField]));
      OldTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [OldTemp, ValTemp]));
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l add %s, 8', [ValTemp, DstField]));
      EmitLine(Format('  storel %s, %s', [OldTemp, ValTemp]));
    end
    else if F.TypeDesc.Kind = tyRecord then
      { Nested record field: recurse into sub-fields }
      Self.EmitRecordCopy(TRecordTypeDesc(F.TypeDesc), DstField, SrcField)
    else if QbeTypeOf(F.TypeDesc) = 'w' then
    begin
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =w loadw %s', [ValTemp, SrcField]));
      EmitLine(Format('  storew %s, %s', [ValTemp, DstField]));
    end
    else
    begin
      ValTemp := AllocTemp();
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
      SelfTemp := AllocTemp();
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
      else if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyInterface) then
        ArgLine := ArgLine + InterfaceArgFragment(TASTExpr(FCallExpr.Args.Items[I]))
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(FCallExpr.Args.Items[I]));
        ArgTemp := CoerceArg(ArgTemp, TASTExpr(FCallExpr.Args.Items[I]),
          QbeTypeOf(Par.ResolvedType));
        ArgLine := ArgLine + Format(', %s %s',
          [QbeParamTypeOf(Par.ResolvedType), ArgTemp]);
      end;
    end;
    EmitLine(Format('  call %s(%s)', [FuncName, ArgLine]));
  end
  else if AExpr is TMethodCallExpr then
  begin
    MCallExpr := TMethodCallExpr(AExpr);
    MDecl := TMethodDecl(MCallExpr.ResolvedMethod);
    if MCallExpr.ObjExpr <> nil then
      SelfTemp := EmitExpr(MCallExpr.ObjExpr)
    else if MDecl.IsRecordMethod and MCallExpr.IsVarParam then
    begin
      SelfTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s',
        [SelfTemp, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)]));
    end
    else if MDecl.IsRecordMethod then
      SelfTemp := VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)
    else
    begin
      SelfTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s',
        [SelfTemp, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)]));
    end;
    FuncName := '$' + MethodEmitName(MDecl, MDecl.OwnerTypeName, MCallExpr.Name);
    ArgLine  := Format('l %s, l %s', [ASretAddr, SelfTemp]);
    for I := 0 to MCallExpr.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Items[I]);
      if Par.IsVarParam then
        ArgLine := ArgLine + Format(', l %s',
          [EmitLValueAddr(TASTExpr(MCallExpr.Args.Items[I]))])
      else if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyInterface) then
        ArgLine := ArgLine + InterfaceArgFragment(TASTExpr(MCallExpr.Args.Items[I]))
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Items[I]));
        ArgTemp := CoerceArg(ArgTemp, TASTExpr(MCallExpr.Args.Items[I]),
          QbeTypeOf(Par.ResolvedType));
        ArgLine := ArgLine + Format(', %s %s',
          [QbeParamTypeOf(Par.ResolvedType), ArgTemp]);
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
      SelfTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_Self', [SelfTemp]));
      if FldAccess.ImplicitBaseInfo.Offset > 0 then
      begin
        Ptr := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d',
          [Ptr, SelfTemp, FldAccess.ImplicitBaseInfo.Offset]));
        SelfTemp := Ptr;
      end;
      if FldAccess.IsClassAccess then
      begin
        Ptr := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [Ptr, SelfTemp]));
        SelfTemp := Ptr;
      end;
    end
    else if MDecl.IsRecordMethod and FldAccess.IsVarParam then
    begin
      { Record var-param receiver (Self inside a record method, or a record
        passed via var): the slot holds the address — load it. }
      SelfTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s',
        [SelfTemp, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
    end
    else if MDecl.IsRecordMethod then
    begin
      { Regular record variable: VarRef IS the record address — pass directly. }
      SelfTemp := VarRef(FldAccess.RecordName, FldAccess.IsGlobal);
    end
    else
    begin
      { Class variable: load the heap pointer from the variable slot. }
      SelfTemp := AllocTemp();
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
    if F.TypeDesc.Kind = tyRecord then
    begin
      { Nested record field: recurse so its managed sub-fields are released.
        EmitRecordCopy already recurses on copy — without this, every nested
        managed sub-field leaks one ref per copy. }
      if F.Offset > 0 then
      begin
        FldAddr := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d', [FldAddr, AAddr, F.Offset]));
      end
      else
        FldAddr := AAddr;
      EmitRecordReleaseFields(TRecordTypeDesc(F.TypeDesc), FldAddr);
      Continue;
    end;
    if not (F.TypeDesc.IsString() or (F.TypeDesc.Kind = tyClass)
            or (F.TypeDesc.Kind = tyDynArray)
            or (F.TypeDesc.Kind = tyInterface)) then Continue;
    if F.Offset > 0 then
    begin
      FldAddr := AllocTemp();
      EmitLine(Format('  %s =l add %s, %d', [FldAddr, AAddr, F.Offset]));
    end
    else
      FldAddr := AAddr;
    ValT := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [ValT, FldAddr]));
    if F.TypeDesc.IsString() then
      EmitLine(Format('  call $_StringRelease(l %s)', [ValT]))
    else if F.TypeDesc.Kind = tyDynArray then
      EmitLine(Format('  call $_DynArrayRelease(l %s)', [ValT]))
    else
      { tyClass and tyInterface both release the obj slot via _ClassRelease.
        For an interface field the itab slot lives at +8 and is static rodata,
        so no extra release is needed. }
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
      SelfPtr := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_Self', [SelfPtr]));
      if AAssign.ImplicitBaseInfo.Offset > 0 then
      begin
        PtrTemp := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d',
          [PtrTemp, SelfPtr, AAssign.ImplicitBaseInfo.Offset]));
        SelfPtr := PtrTemp;
      end;
      if AAssign.IsClassAccess then
      begin
        PtrTemp := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [PtrTemp, SelfPtr]));
        SelfPtr := PtrTemp;
      end;
    end
    else
    begin
      SelfPtr := AllocTemp();
      EmitLine(Format('  %s =l loadl %s',
        [SelfPtr, VarRef(AAssign.RecordName, AAssign.IsGlobal)]));
    end;
    QType := QbeTypeOf(AAssign.PropWriteInfo.TypeDesc);
    if AAssign.PropIndexExpr <> nil then
    begin
      IdxTemp  := EmitExpr(AAssign.PropIndexExpr);
      IdxQType := QbeTypeOf(AAssign.PropWriteInfo.IndexTypeDesc);
      EmitLine(Format('  call $%s%s_%s(l %s, %s %s, %s %s)',
        [ClassUnitPrefix(AAssign.PropOwnerType),
         QBEMangle(AAssign.PropOwnerType), AAssign.PropWriteInfo.WriteMethod,
         SelfPtr, IdxQType, IdxTemp, QType, ValTemp]));
    end
    else
      EmitLine(Format('  call $%s%s_%s(l %s, %s %s)',
        [ClassUnitPrefix(AAssign.PropOwnerType),
         QBEMangle(AAssign.PropOwnerType), AAssign.PropWriteInfo.WriteMethod,
         SelfPtr, QType, ValTemp]));
    Exit;
  end;

  if AAssign.FieldInfo = nil then
    raise ECodeGenError.Create(Format(
      'Field assignment ''%s.%s'' has no resolved field info',
      [AAssign.RecordName, AAssign.FieldName]));

  { Interface-typed field: the RHS must be stored as a two-slot fat pointer
    (obj + itab), not a single value.  EmitInterfaceToFieldSlots evaluates the
    RHS itself, so the generic single-value EmitExpr below must be skipped for
    this case (re-evaluating would double any side effects). }
  if AAssign.FieldInfo.TypeDesc.Kind <> tyInterface then
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
      Ptr := AllocTemp();
      EmitLine(Format('  %s =l add %s, %d', [Ptr, PtrTemp, AAssign.FieldInfo.Offset]));
    end
    else
      Ptr := PtrTemp;
  end
  else if AAssign.IsImplicitSelf then
  begin
    { Implicit Self.Base.Field — Base is a field of Self }
    PtrTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %%_var_Self', [PtrTemp]));
    if AAssign.ImplicitBaseInfo.Offset > 0 then
    begin
      Ptr := AllocTemp();
      EmitLine(Format('  %s =l add %s, %d',
        [Ptr, PtrTemp, AAssign.ImplicitBaseInfo.Offset]));
      PtrTemp := Ptr;
    end;
    if AAssign.IsClassAccess then
    begin
      { Base field holds a class pointer; load it }
      Ptr := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [Ptr, PtrTemp]));
      PtrTemp := Ptr;
    end;
    if AAssign.FieldInfo.Offset > 0 then
    begin
      Ptr := AllocTemp();
      EmitLine(Format('  %s =l add %s, %d',
        [Ptr, PtrTemp, AAssign.FieldInfo.Offset]));
    end
    else
      Ptr := PtrTemp;
  end
  else if AAssign.IsClassAccess then
  begin
    { Load the heap pointer stored in the class variable }
    PtrTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [PtrTemp, VarRef(AAssign.RecordName, AAssign.IsGlobal)]));
    if AAssign.FieldInfo.Offset > 0 then
    begin
      Ptr := AllocTemp();
      EmitLine(Format('  %s =l add %s, %d', [Ptr, PtrTemp, AAssign.FieldInfo.Offset]));
    end
    else
      Ptr := PtrTemp;
  end
  else if AAssign.IsVarParam then
  begin
    { Var-record param: dereference the param slot to get the actual record
      address, then add field offset. }
    PtrTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s',
      [PtrTemp, VarRef(AAssign.RecordName, AAssign.IsGlobal)]));
    if AAssign.FieldInfo.Offset > 0 then
    begin
      Ptr := AllocTemp();
      EmitLine(Format('  %s =l add %s, %d',
        [Ptr, PtrTemp, AAssign.FieldInfo.Offset]));
    end
    else
      Ptr := PtrTemp;
  end
  else
    Ptr := FieldPtr(AAssign.RecordName, AAssign.FieldInfo.Offset, AAssign.IsGlobal);

  { Interface-typed field: store the fat pointer (obj at Ptr, itab at Ptr+8)
    with ARC on the obj slot.  EmitInterfaceToFieldSlots handles both an
    interface-typed RHS (copy obj+itab) and a class-typed RHS (obj + static
    itab via _GetItab), retaining the new obj and releasing the old. }
  if AAssign.FieldInfo.TypeDesc.Kind = tyInterface then
  begin
    PtrTemp := AllocTemp();
    EmitLine(Format('  %s =l add %s, 8', [PtrTemp, Ptr]));
    EmitInterfaceToFieldSlots(AAssign.Expr, Ptr, PtrTemp,
      AAssign.FieldInfo.TypeDesc);
    Exit;
  end;

  { Record-typed field: copy all subfields recursively (ValTemp is the source
    record address; Ptr is the destination field address inside the parent). }
  if AAssign.FieldInfo.TypeDesc.Kind = tyRecord then
  begin
    if IsRecordCall(AAssign.Expr) then
    begin
      EmitRecordCallSret(AAssign.Expr, Ptr);
    end
    else
      EmitRecordCopy(TRecordTypeDesc(AAssign.FieldInfo.TypeDesc), Ptr, ValTemp);
    Exit;
  end;

  { Method-pointer field: 16-byte inline TMethod (Code+Data).  ValTemp is the
    address of a 16-byte source block.  Mirrors the variable-assign path. }
  if (AAssign.FieldInfo.TypeDesc.Kind = tyProcedural) and
     TProceduralTypeDesc(AAssign.FieldInfo.TypeDesc).IsMethodPtr then
  begin
    EmitLine(Format('  call $memcpy(l %s, l %s, l 16)', [Ptr, ValTemp]));
    Exit;
  end;

  IsStr := AAssign.FieldInfo.TypeDesc.IsString();
  IsArc := IsStr or (AAssign.FieldInfo.TypeDesc.Kind = tyClass)
                 or (AAssign.FieldInfo.TypeDesc.Kind = tyDynArray);
  if AAssign.FieldInfo.IsUnretained and (AAssign.FieldInfo.TypeDesc.Kind = tyClass) then
  begin
    { Unretained class field: non-owning — store the pointer with no addref
      and no release of the old value.  If the RHS was a +1 temporary (e.g.
      function return), release it — the field borrows, so nobody keeps the +1. }
    EmitLine(Format('  storel %s, %s', [ValTemp, Ptr]));
    if ExprOwnsRef(AAssign.Expr) then
      EmitLine(Format('  call $_ClassRelease(l %s)', [ValTemp]));
  end
  else if AAssign.FieldInfo.IsWeak then
  begin
    { Weak class field: store through _WeakAssign so the runtime can zero
      the field slot if the target is freed while the weak ref is live. }
    EmitLine(Format('  call $_WeakAssign(l %s, l %s)', [Ptr, ValTemp]));
  end
  else if IsArc then
  begin
    { ARC for ARC-managed field storage: retain the new value and release the
      old field contents before overwriting, so neither reference leaks. }
    OldTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [OldTemp, Ptr]));
    { When the RHS already owns +1 (a function/method/property-getter call
      result), the field consumes that transferred reference and must NOT
      AddRef again — otherwise the buffer/object leaks one reference per
      store.  The old field contents are released unconditionally. }
    if IsStr then
    begin
      if not ExprOwnsRef(AAssign.Expr) then
        EmitLine(Format('  call $_StringAddRef(l %s)',  [ValTemp]));
      EmitLine(Format('  call $_StringRelease(l %s)', [OldTemp]));
    end
    else if AAssign.FieldInfo.TypeDesc.Kind = tyDynArray then
    begin
      if not ExprOwnsRef(AAssign.Expr) then
        EmitLine(Format('  call $_DynArrayAddRef(l %s)',  [ValTemp]));
      EmitLine(Format('  call $_DynArrayRelease(l %s)', [OldTemp]));
    end
    else
    begin
      { Class field keeps an unconditional retain.  ExprOwnsRef-guarding this
        is unsafe: some method calls return a borrowed class reference without
        an AddRef (ExprOwnsRef reports them as owning), so skipping the retain
        would release a reference the field never acquired — a heap-corrupting
        use-after-free that the self-hosting compiler hits in its own codegen.
        The transient-leak this leaves for genuine +1 class returns assigned to
        a field is the safe direction and matches long-standing behaviour. }
      EmitLine(Format('  call $_ClassAddRef(l %s)',   [ValTemp]));
      EmitLine(Format('  call $_ClassRelease(l %s)',  [OldTemp]));
    end;
    EmitLine(Format('  storel %s, %s', [ValTemp, Ptr]));
  end
  else
  begin
    QType      := QbeTypeOf(AAssign.FieldInfo.TypeDesc);
    StoreInstr := StoreInstrFor(AAssign.FieldInfo.TypeDesc);
    if QType <> 'w' then
    begin
      { Sign-extend if the value is word-typed but the field needs l }
      if QbeTypeOf(AAssign.Expr.ResolvedType) = 'w' then
      begin
        ExtTemp := AllocTemp();
        EmitLine(Format('  %s =l extsw %s', [ExtTemp, ValTemp]));
        ValTemp := ExtTemp;
      end;
    end;
    { Float-width coercion: real-typed literals and double sub-exprs land
      in the SSA as 'd' even when the destination field is a 32-bit
      'Single' ('s').  Without this, 'rec.s := 1.5' emits
      'stores d_1.5, ...' — a type mismatch the assembler rejects. }
    if (QType = 's') and (QbeTypeOf(AAssign.Expr.ResolvedType) = 'd') then
    begin
      ExtTemp := AllocTemp();
      EmitLine(Format('  %s =s truncd %s', [ExtTemp, ValTemp]));
      ValTemp := ExtTemp;
    end
    else if (QType = 'd') and (QbeTypeOf(AAssign.Expr.ResolvedType) = 's') then
    begin
      ExtTemp := AllocTemp();
      EmitLine(Format('  %s =d exts %s', [ExtTemp, ValTemp]));
      ValTemp := ExtTemp;
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
  ArgTemps: TStringList;
  I:        Integer;
  QType:    string;
  FuncName: string;
  VTblTemp: string;
  FPtrTemp: string;
  SlotOff:  Integer;
  IntfDesc: TInterfaceTypeDesc;
  PT:       TProceduralTypeDesc;
  SlotAddr: string;
  DataTemp: string;
  ItabName: string;
begin
  { Interface method dispatch: load obj + itab, index by method slot }
  if (ACall.ResolvedClassType <> nil) and
     (ACall.ResolvedClassType.Kind = tyInterface) then
  begin
    IntfDesc := TInterfaceTypeDesc(ACall.ResolvedClassType);
    SelfTemp := AllocTemp();
    VTblTemp := AllocTemp();
    if ACall.IsImplicitSelf then
    begin
      { Interface field of Self: obj/itab live in the object layout at
        Self + FieldOffset (obj) and Self + FieldOffset + 8 (itab). }
      FPtrTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_Self', [FPtrTemp]));
      if ACall.ImplicitBaseInfo.Offset > 0 then
      begin
        ArgTemp := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d', [ArgTemp, FPtrTemp, ACall.ImplicitBaseInfo.Offset]));
        FPtrTemp := ArgTemp;
      end;
      EmitLine(Format('  %s =l loadl %s', [SelfTemp, FPtrTemp]));
      ArgTemp := AllocTemp();
      EmitLine(Format('  %s =l add %s, 8', [ArgTemp, FPtrTemp]));
      EmitLine(Format('  %s =l loadl %s', [VTblTemp, ArgTemp]));
    end
    else if ACall.ObjExpr <> nil then
    begin
      { Receiver is an expression (e.g. a record/class field r.Foo, or an
        as-cast).  Its fat pointer is not in split _obj/_itab slots — let
        EmitInterfaceExprPair resolve obj/itab from the expression (it loads
        a field's contiguous fat pointer at addr / addr+8). }
      EmitInterfaceExprPair(ACall.ObjExpr, SelfTemp, VTblTemp);
    end
    else
    begin
      EmitLine(Format('  %s =l loadl %s_obj', [SelfTemp, VarRef(ACall.ObjectName, ACall.IsGlobal)]));
      EmitLine(Format('  %s =l loadl %s_itab', [VTblTemp, VarRef(ACall.ObjectName, ACall.IsGlobal)]));
    end;
    SlotOff  := IntfDesc.MethodIndex(ACall.Name) * 8;
    FPtrTemp := AllocTemp();
    if SlotOff = 0 then
      EmitLine(Format('  %s =l loadl %s', [FPtrTemp, VTblTemp]))
    else
    begin
      ArgTemp := AllocTemp();
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
    RT    := TRecordTypeDesc(ACall.ResolvedClassType);
    MDecl := TMethodDecl(ACall.ResolvedMethod);
    if (MDecl = nil) and SameText(ACall.Name, 'Free') then
    begin
      if (ACall.ObjExpr is TFieldAccessExpr) or
         (ACall.ObjExpr is TIdentExpr) then
      begin
        FPtrTemp := EmitLValueAddr(ACall.ObjExpr);
        SelfTemp := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [SelfTemp, FPtrTemp]));
        EmitLine(Format('  call $_ClassRelease(l %s)', [SelfTemp]));
        EmitLine(Format('  storel 0, %s', [FPtrTemp]));
      end
      else
      begin
        SelfTemp := EmitExpr(ACall.ObjExpr);
        EmitLine(Format('  call $_ClassRelease(l %s)', [SelfTemp]));
      end;
      Exit;
    end;
    SelfTemp := EmitExpr(ACall.ObjExpr);
    if ACall.IsProcFieldCall then
    begin
      PT := TProceduralTypeDesc(ACall.ResolvedProcType);
      if ACall.ProcFieldInfo.Offset > 0 then
      begin
        SlotAddr := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d',
          [SlotAddr, SelfTemp, ACall.ProcFieldInfo.Offset]));
      end
      else
        SlotAddr := SelfTemp;
      FPtrTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [FPtrTemp, SlotAddr]));
      if PT.IsMethodPtr then
      begin
        ArgTemp := AllocTemp();
        EmitLine(Format('  %s =l add %s, 8', [ArgTemp, SlotAddr]));
        DataTemp := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [DataTemp, ArgTemp]));
        ArgLine := Format('l %s', [DataTemp]);
      end
      else
        ArgLine := '';
      for I := 0 to ACall.Args.Count - 1 do
      begin
        if ArgLine <> '' then ArgLine := ArgLine + ', ';
        ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
        QType   := QbeTypeOf(TProcParamInfo(PT.Params.Items[I]).TypeDesc);
        ArgTemp := CoerceArg(ArgTemp, TASTExpr(ACall.Args.Items[I]), QType);
        ArgLine := ArgLine + Format('%s %s',
          [QbeParamTypeOf(TProcParamInfo(PT.Params.Items[I]).TypeDesc), ArgTemp]);
      end;
      EmitLine(Format('  call %s(%s)', [FPtrTemp, ArgLine]));
      if ExprOwnsRef(ACall.ObjExpr) then
        EmitLine(Format('  call $_ClassRelease(l %s)', [SelfTemp]));
      Exit;
    end;
    ArgLine := Format('l %s', [SelfTemp]);
    ArgTemps := TStringList.Create();
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Items[I]);
      if Par.IsVarParam then
      begin
        ArgTemps.Add('');
        ArgLine := ArgLine + Format(', l %s',
          [EmitLValueAddr(TASTExpr(ACall.Args.Items[I]))]);
      end
      else if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyInterface) then
      begin
        ArgTemps.Add('');
        ArgLine := ArgLine + InterfaceArgFragment(TASTExpr(ACall.Args.Items[I]));
      end
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
        ArgTemps.Add(ArgTemp);
        EnsureConstStringRef(ArgTemp, Par);
        QType   := QbeTypeOf(Par.ResolvedType);
        ArgTemp := CoerceArg(ArgTemp, TASTExpr(ACall.Args.Items[I]), QType);
        ArgLine := ArgLine + Format(', %s %s', [QbeParamTypeOf(Par.ResolvedType), ArgTemp]);
      end;
    end;
    { Virtual methods on an arbitrary receiver expression must dispatch
      through the vtable — the static-class type seen here may be an
      abstract base whose direct method symbol does not exist (the slot
      points at $_AbstractMethodError).  Mirror the same vtable-load
      sequence used below for the IsImplicitSelf / ObjectName paths. }
    if (MDecl <> nil) and (MDecl.VTableSlot >= 0) then
    begin
      VTblTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [VTblTemp, SelfTemp]));
      FPtrTemp := AllocTemp();
      SlotOff  := (MDecl.VTableSlot + 1) * 8;
      ArgTemp  := AllocTemp();
      EmitLine(Format('  %s =l add %s, %d', [ArgTemp, VTblTemp, SlotOff]));
      EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
      EmitLine(Format('  call %s(%s)', [FPtrTemp, ArgLine]));
      EmitOwnedArgReleases(ACall.Args, ArgTemps, MDecl.Params);
      ReleaseConstStringArgs(ACall.Args, ArgTemps, MDecl.Params);
      ArgTemps.Free();
      { Receiver was a +1-owned temporary (function/property return) used
        transiently — release it so the temporary does not leak. }
      if ExprOwnsRef(ACall.ObjExpr) then
        EmitLine(Format('  call $_ClassRelease(l %s)', [SelfTemp]));
      Exit;
    end;
    if MDecl.OwnerTypeName <> '' then
      FuncName := '$' + MethodEmitName(MDecl, MDecl.OwnerTypeName, ACall.Name)
    else
      FuncName := '$' + MethodEmitName(MDecl, RT.Name, ACall.Name);
    EmitLine(Format('  call %s(%s)', [FuncName, ArgLine]));
    EmitOwnedArgReleases(ACall.Args, ArgTemps, MDecl.Params);
    ReleaseConstStringArgs(ACall.Args, ArgTemps, MDecl.Params);
    ArgTemps.Free();
    if ExprOwnsRef(ACall.ObjExpr) then
      EmitLine(Format('  call $_ClassRelease(l %s)', [SelfTemp]));
    Exit;
  end;

  { Built-in Free: release the instance (decrement refcount; free at zero)
    and nil out the slot.  Under universal ARC, Free is a sanctioned synonym
    for immediate release — if other references remain, the block survives
    until their scope exits release them too.  Zeroing the slot makes a
    subsequent scope-exit release a safe no-op. }
  if (ACall.ResolvedMethod = nil) and SameText(ACall.Name, 'Free') then
  begin
    SelfTemp := AllocTemp();
    if ACall.IsImplicitSelf then
    begin
      { Free called on Self.Field: load Self, get field slot address, load value,
        release, then zero the slot. }
      EmitLine(Format('  %s =l loadl %%_var_Self', [SelfTemp]));
      if ACall.ImplicitBaseInfo.Offset > 0 then
      begin
        FPtrTemp := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d',
          [FPtrTemp, SelfTemp, ACall.ImplicitBaseInfo.Offset]));
      end
      else
        FPtrTemp := SelfTemp;
      ArgTemp := AllocTemp();
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
  SelfTemp := AllocTemp();
  if ACall.IsImplicitSelf then
  begin
    EmitLine(Format('  %s =l loadl %%_var_Self', [SelfTemp]));
    if ACall.ImplicitBaseInfo.Offset > 0 then
    begin
      FPtrTemp := AllocTemp();
      EmitLine(Format('  %s =l add %s, %d',
        [FPtrTemp, SelfTemp, ACall.ImplicitBaseInfo.Offset]));
      SelfTemp := FPtrTemp;
    end;
    if ACall.ImplicitBaseInfo.TypeDesc.Kind = tyRecord then
      { Record field of Self: address IS the record — no deref }
    else
    begin
      FPtrTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [FPtrTemp, SelfTemp]));
      SelfTemp := FPtrTemp;
    end;
  end
  else if (MDecl <> nil) and MDecl.IsRecordMethod and ACall.IsVarParam then
  begin
    { Record var-param receiver — slot holds the record address; load once. }
    EmitLine(Format('  %s =l loadl %%_var_%s', [SelfTemp, ACall.ObjectName]));
  end
  else if (MDecl <> nil) and MDecl.IsRecordMethod then
    { Regular record variable: VarRef IS the record address — pass directly. }
    SelfTemp := VarRef(ACall.ObjectName, ACall.IsGlobal)
  else if ACall.IsVarParam then
  begin
    { Var/out param: local slot holds caller's address — dereference twice }
    FPtrTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %%_var_%s', [FPtrTemp, ACall.ObjectName]));
    EmitLine(Format('  %s =l loadl %s', [SelfTemp, FPtrTemp]));
  end
  else
  begin
    EmitLine(Format('  %s =l loadl %s', [SelfTemp, VarRef(ACall.ObjectName, ACall.IsGlobal)]));
    EmitLine(Format('  call $_CheckNil(l %s)', [SelfTemp]));
  end;

  { Direct invocation of a procedural-typed field (F.Handler; / F.Handler();).
    The field slot lives at Self + Offset.  For a method-pointer field it is a
    16-byte (Code, Data) block — Code at slot+0, Data at slot+8; the loaded
    Data is passed as the implicit first argument so the callee sees its Self.
    A bare procedural field (not 'of object') holds a single function pointer
    and takes no implicit Self.  Mirrors EmitProcCall's indirect-call path. }
  if ACall.IsProcFieldCall then
  begin
    PT := TProceduralTypeDesc(ACall.ResolvedProcType);
    if ACall.ProcFieldInfo.Offset > 0 then
    begin
      SlotAddr := AllocTemp();
      EmitLine(Format('  %s =l add %s, %d',
        [SlotAddr, SelfTemp, ACall.ProcFieldInfo.Offset]));
    end
    else
      SlotAddr := SelfTemp;
    FPtrTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [FPtrTemp, SlotAddr]));
    if PT.IsMethodPtr then
    begin
      ArgTemp := AllocTemp();
      EmitLine(Format('  %s =l add %s, 8', [ArgTemp, SlotAddr]));
      DataTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [DataTemp, ArgTemp]));
      ArgLine := Format('l %s', [DataTemp]);
    end
    else
      ArgLine := '';
    for I := 0 to ACall.Args.Count - 1 do
    begin
      if ArgLine <> '' then ArgLine := ArgLine + ', ';
      ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
      QType   := QbeTypeOf(TProcParamInfo(PT.Params.Items[I]).TypeDesc);
      ArgTemp := CoerceArg(ArgTemp, TASTExpr(ACall.Args.Items[I]), QType);
      ArgLine := ArgLine + Format('%s %s',
        [QbeParamTypeOf(TProcParamInfo(PT.Params.Items[I]).TypeDesc), ArgTemp]);
    end;
    EmitLine(Format('  call %s(%s)', [FPtrTemp, ArgLine]));
    Exit;
  end;

  { Build argument string: l Self, then each explicit arg }
  ArgLine := Format('l %s', [SelfTemp]);
  ArgTemps := TStringList.Create();
  try
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Items[I]);
      if Par.IsVarParam then
      begin
        ArgTemps.Add('');
        ArgLine := ArgLine + Format(', l %s',
          [EmitLValueAddr(TASTExpr(ACall.Args.Items[I]))]);
      end
      else if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyInterface) then
      begin
        ArgTemps.Add('');
        if TASTExpr(ACall.Args.Items[I]).ResolvedType.Kind = tyClass then
        begin
          ArgTemp  := EmitExpr(TASTExpr(ACall.Args.Items[I]));
          ItabName := '$itab_' +
            ClassSymName(QBEMangle(TASTExpr(ACall.Args.Items[I]).ResolvedType.Name))
            + '_' + QBEMangle(Par.ResolvedType.Name);
          ArgLine := ArgLine + Format(', l %s, l %s', [ArgTemp, ItabName]);
        end
        else
          ArgLine := ArgLine + InterfaceArgFragment(TASTExpr(ACall.Args.Items[I]));
      end
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
        ArgTemps.Add(ArgTemp);
        EnsureConstStringRef(ArgTemp, Par);
        QType   := QbeTypeOf(Par.ResolvedType);
        ArgTemp := CoerceArg(ArgTemp, TASTExpr(ACall.Args.Items[I]), QType);
        ArgLine := ArgLine + Format(', %s %s',
          [QbeParamTypeOf(Par.ResolvedType), ArgTemp]);
      end;
    end;

    if MDecl.VTableSlot >= 0 then
    begin
      { Virtual dispatch: load vptr from instance[0], then load fptr from vtable.
        Slot 0 of vtable is typeinfo, so method N is at offset (N+1)*8. }
      VTblTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [VTblTemp, SelfTemp]));
      FPtrTemp := AllocTemp();
      SlotOff  := (MDecl.VTableSlot + 1) * 8;
      ArgTemp  := AllocTemp();
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
    EmitOwnedArgReleases(ACall.Args, ArgTemps, MDecl.Params);
    ReleaseConstStringArgs(ACall.Args, ArgTemps, MDecl.Params);
  finally
    ArgTemps.Free();
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

  BranchLabels := TStringList.Create();
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
        CmpTemp := AllocTemp();
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
    BranchLabels.Free();
  end;
end;

procedure TCodeGenQBE.EmitInheritedCall(ACall: TInheritedCallStmt);
var
  MDecl:    TMethodDecl;
  SelfTemp: string;
  ArgLine:  string;
  ArgTemp:  string;
  ArgTemp2: string;
  Par:      TMethodParam;
  QType:    string;
  I:        Integer;
begin
  { TObject inherited calls are no-ops — no method body exists }
  if ACall.ResolvedMethod = nil then Exit;

  MDecl := TMethodDecl(ACall.ResolvedMethod);

  { Load Self from the current method's local slot }
  SelfTemp := AllocTemp();
  EmitLine(Format('  %s =l loadl %%_var_Self', [SelfTemp]));

  { Build arg string: l Self, then each explicit arg }
  ArgLine := Format('l %s', [SelfTemp]);
  for I := 0 to ACall.Args.Count - 1 do
  begin
    Par     := TMethodParam(MDecl.Params.Items[I]);
    if Par.IsVarParam then
    begin
      { var/out param: pass the argument's address, not its value. }
      ArgLine := ArgLine + Format(', l %s',
        [EmitLValueAddr(TASTExpr(ACall.Args.Items[I]))]);
      Continue;
    end;
    if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyInterface) then
    begin
      if TASTExpr(ACall.Args.Items[I]).ResolvedType.Kind = tyClass then
      begin
        ArgTemp  := EmitExpr(TASTExpr(ACall.Args.Items[I]));
        ArgTemp2 := '$itab_' +
          ClassSymName(QBEMangle(TASTExpr(ACall.Args.Items[I]).ResolvedType.Name))
          + '_' + QBEMangle(Par.ResolvedType.Name);
        ArgLine := ArgLine + Format(', l %s, l %s', [ArgTemp, ArgTemp2]);
      end
      else
        ArgLine := ArgLine + InterfaceArgFragment(TASTExpr(ACall.Args.Items[I]));
      Continue;
    end;
    ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
    QType   := QbeTypeOf(Par.ResolvedType);
    ArgTemp := CoerceArg(ArgTemp, TASTExpr(ACall.Args.Items[I]), QType);
    ArgLine := ArgLine + Format(', %s %s', [QbeParamTypeOf(Par.ResolvedType), ArgTemp]);
  end;

  { Always a direct (static) call — inherited bypasses vtable dispatch.
    If the parent method returns a value, store it into %_var_Result so that
    "inherited F;" as a statement sets Result in the overriding function. }
  if (MDecl.ResolvedReturnType <> nil) and
     (MDecl.ResolvedReturnType.Kind <> tyVoid) then
  begin
    QType   := QbeTypeOf(MDecl.ResolvedReturnType);
    ArgTemp := AllocTemp();
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
      tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum,
      tySmallInt, tyWord:
        begin
          EmitLine(Format('  %%_var_%s =l alloc4 1', [Par.ParamName]));
          EmitLine(Format('  storew %%_par_%s, %%_var_%s',
            [Par.ParamName, Par.ParamName]));
        end;
      tyInt64, tyUInt64, tyString, tyClass, tyMetaClass:
        begin
          EmitLine(Format('  %%_var_%s =l alloc8 1', [Par.ParamName]));
          EmitLine(Format('  storel %%_par_%s, %%_var_%s',
            [Par.ParamName, Par.ParamName]));
        end;
      tySet:
        { A set is a w (≤32 members) or l (≤64) bitmask — spill at its width. }
        if TSetTypeDesc(Par.ResolvedType).BitCount <= 32 then
        begin
          EmitLine(Format('  %%_var_%s =l alloc4 1', [Par.ParamName]));
          EmitLine(Format('  storew %%_par_%s, %%_var_%s',
            [Par.ParamName, Par.ParamName]));
        end
        else
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
      tyInterface:
        begin
          { Two-slot fat pointer (obj + itab) — matches the local-var layout
            and the standalone-routine param path, so interface dispatch and
            value-param ARC both find %_var_X_obj / %_var_X_itab.  Without this
            a method with a by-value interface param fell into the generic
            single-slot `else` below: the signature passed a single `w` and the
            `storel %_par_X` here was invalid QBE. }
          EmitLine(Format('  %%_var_%s_obj =l alloc8 1', [Par.ParamName]));
          EmitLine(Format('  storel %%_par_%s_obj, %%_var_%s_obj',
            [Par.ParamName, Par.ParamName]));
          EmitLine(Format('  %%_var_%s_itab =l alloc8 1', [Par.ParamName]));
          EmitLine(Format('  storel %%_par_%s_itab, %%_var_%s_itab',
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
    else if (Par.ResolvedType <> nil) and
            (Par.ResolvedType.Kind = tyInterface) then
      { Interfaces are two-slot fat pointers (obj + itab); caller passes both,
        callee allocs two local slots in EmitParamAllocs.  Mirrors the
        standalone-routine path so method dispatch and value-param ARC both
        find %_var_<p>_obj / %_var_<p>_itab. }
      Sig := Sig + Format(', l %%_par_%s_obj, l %%_par_%s_itab',
        [Par.ParamName, Par.ParamName])
    else
      Sig := Sig + Format(', %s %%_par_%s',
        [QbeParamTypeOf(Par.ResolvedType), Par.ParamName]);
  end;

  if IsFunc then
  begin
    RetQType := QbeTypeOf(AMethod.ResolvedReturnType);
    if AMethod.ResolvedReturnType.Kind = tyRecord then
      EmitLine(Format('%sfunction %s(%s) {', [ExportPrefix(), FuncName, Sig]))
    else
      EmitLine(Format('%sfunction %s %s(%s) {', [ExportPrefix(), RetQType, FuncName, Sig]));
  end
  else
    EmitLine(Format('%sfunction %s(%s) {', [ExportPrefix(), FuncName, Sig]));

  EmitLine('@start');
  EmitParamAllocs(AMethod, nil);

  { ARC: addref string and class value params on entry — balances the
    release pass at method exit. const params are skipped: the caller
    guarantees the object stays alive for the whole call, so the callee
    needs no retain/release. }
  for I := 0 to AMethod.Params.Count - 1 do
  begin
    Par := TMethodParam(AMethod.Params.Items[I]);
    if Par.IsVarParam or Par.IsOpenArray or Par.IsConstParam then Continue;
    if Par.ResolvedType.Kind = tyString then
    begin
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_StringAddRef(l %s)', [ValTemp]));
    end
    else if Par.ResolvedType.Kind = tyClass then
    begin
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_ClassAddRef(l %s)', [ValTemp]));
    end
    else if Par.ResolvedType.Kind = tyInterface then
    begin
      { Interfaces ARC through the object slot of their fat pointer; the
        itab is static and needs no refcounting. }
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s_obj',
        [ValTemp, Par.ParamName]));
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

  { ARC: release string and class value params on exit. const params are
    skipped to match the entry pass (no retain was taken). }
  for I := 0 to AMethod.Params.Count - 1 do
  begin
    Par := TMethodParam(AMethod.Params.Items[I]);
    if Par.IsVarParam or Par.IsOpenArray or Par.IsConstParam then Continue;
    if Par.ResolvedType.Kind = tyString then
    begin
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_StringRelease(l %s)', [ValTemp]));
    end
    else if Par.ResolvedType.Kind = tyClass then
    begin
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [ValTemp]));
    end
    else if Par.ResolvedType.Kind = tyInterface then
    begin
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s_obj', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [ValTemp]));
    end;
  end;

  if IsFunc then
  begin
    if AMethod.ResolvedReturnType.Kind = tyRecord then
      EmitLine('  ret')  { sret: caller's buffer already holds result }
    else
    begin
      RetTemp := AllocTemp();
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
  AttrsStr:        string;
  AttrsLine:       string;
  MName:           string;
  MethLine:        string;
begin
  { System-unit emission gated on FSystemDefsEmitted so AppendUnit
    (phase 6c-J emission below) can emit these earlier without
    duplicating against the program path.  Once set, both paths
    skip the System block; per-class typeinfo continues for both. }
  if not FSystemDefsEmitted then
  begin
    EmitLine('export data $typeinfo_TObject = { l 0, l 0, l ' +
             EmitClassNameRef('TObject') + ', l 0' +
             ', l 8, l $_FieldCleanup_TObject, l $vtable_TObject, l 0 }');
    EmitLine('export data $typeinfo_TCustomAttribute = { l $typeinfo_TObject, l 0, l ' +
             EmitClassNameRef('TCustomAttribute') + ', l 0' +
             ', l 8, l $_FieldCleanup_TCustomAttribute' +
             ', l $vtable_TCustomAttribute, l 0 }');
  end;

  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    CD := TClassTypeDef(TD.Def);

    if RT.Parent <> nil then
      ParentStr := '$typeinfo_' + ClassSymName(RT.Parent.Name)
    else
      ParentStr := '0';
    if RT.ImplementsCount() > 0 then
      ImplStr := '$impllist_' + ClassSymName(TD.Name)
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
      MethLine := 'data $methods_' + ClassSymName(TD.Name) + ' = { l ' + IntToStr(PubCount);
      for J := 0 to CD.Methods.Count - 1 do
      begin
        MD := TMethodDecl(CD.Methods.Items[J]);
        if not MD.IsPublished then Continue;
        MethLine := MethLine +
                    ', l ' + EmitMethodNameRef(TD.Name, MD.Name) +
                    ', l $' + MethodEmitName(MD, TD.Name, MD.Name);
      end;
      MethLine := MethLine + ' }';
      EmitLine(MethLine);
      MethStr := '$methods_' + ClassSymName(TD.Name);
    end
    else
      MethStr := '0';

    if RT.ClassAttributeCount() > 0 then
    begin
      AttrsLine := 'data $attrs_' + ClassSymName(TD.Name) + ' = { l ' + IntToStr(RT.ClassAttributeCount());
      for J := 0 to RT.ClassAttributeCount() - 1 do
        AttrsLine := AttrsLine + ', l $typeinfo_' + ClassSymName(RT.ClassAttributeAt(J));
      AttrsLine := AttrsLine + ' }';
      EmitLine(AttrsLine);
      AttrsStr := '$attrs_' + ClassSymName(TD.Name);
    end
    else
      AttrsStr := '0';

    EmitLine('data $typeinfo_' + ClassSymName(TD.Name) +
             ' = { l ' + ParentStr + ', l ' + ImplStr +
             ', l ' + EmitClassNameRef(TD.Name) +
             ', l ' + MethStr +
             ', l ' + IntToStr(RT.TotalSize()) +
             ', l $_FieldCleanup_' + ClassSymName(TD.Name) +
             ', l $vtable_' + ClassSymName(TD.Name) +
             ', l ' + AttrsStr + ' }');
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
    if RT.ImplementsCount() > 0 then
      ImplStr := '$impllist_' + MName
    else
      ImplStr := '0';
    EmitLine('data $typeinfo_' + MName + ' = { l ' + ParentStr + ', l ' + ImplStr +
             ', l ' + EmitClassNameRef(GI.TypeName) + ', l 0' +
             ', l ' + IntToStr(RT.TotalSize()) +
             ', l $_FieldCleanup_' + MName +
             ', l $vtable_' + MName + ', l 0 }');
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
  if not FSystemDefsEmitted then
  begin
    EmitLine('export data $vtable_TObject = { l $typeinfo_TObject' +
             ', l $TObject_Destroy, l $TObject_ToString }');
    EmitLine('export data $vtable_TCustomAttribute = { l $typeinfo_TCustomAttribute' +
             ', l $TObject_Destroy, l $TObject_ToString }');
  end;
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    if not RT.HasVTable() then Continue;
    { TypeInfo pointer is always the first vtable entry }
    Line := 'data $vtable_' + ClassSymName(TD.Name) +
            ' = { l $typeinfo_' + ClassSymName(TD.Name);
    for S := 0 to RT.VTableCount() - 1 do
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
    if not RT.HasVTable() then Continue;
    MName := QBEMangle(GI.TypeName);
    Line  := 'data $vtable_' + MName + ' = { l $typeinfo_' + MName;
    for S := 0 to RT.VTableCount() - 1 do
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
  MDecl:       TMethodDecl;
  MName:       string;
begin
  { Typeinfo blocks for every plain interface }
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if not (TD.Def is TInterfaceTypeDef) then Continue;
    EmitLine('data $typeinfo_' + ClassSymName(TD.Name) + ' = { l 0 }');
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
    if ClassRT.ImplementsCount() = 0 then Continue;

    { One itab per interface — when a class's vtable slot for a given
      interface method is abstract (e.g. the class is an abstract base that
      declares the interface but defers implementation to subclasses), the
      itab entry must point at $_AbstractMethodError instead of the would-be
      symbol, which does not exist. }
    for J := 0 to ClassRT.ImplementsCount() - 1 do
    begin
      IntfDesc   := ClassRT.ImplementsIntfAt(J);
      IntfMangle := QBEMangle(IntfDesc.Name);
      ItabLine   := 'data $itab_' + ClassSymName(TD.Name) + '_' + IntfMangle + ' = {';
      for K := 0 to IntfDesc.MethodCount() - 1 do
      begin
        MethName := IntfDesc.MethodName(K);
        if IsAbstractClassMethod(ClassRT, MethName) then
          MethRef := '$_AbstractMethodError'
        else
          MethRef := '$' + ClassSymName(TD.Name) + '_' + MethName;
        if K = 0 then
          ItabLine := ItabLine + ' l ' + MethRef
        else
          ItabLine := ItabLine + ', l ' + MethRef;
      end;
      ItabLine := ItabLine + ' }';
      EmitLine(ItabLine);
    end;

    { One impllist per class: NULL-terminated (typeinfo_intf, itab) pairs }
    ImplLine := 'data $impllist_' + ClassSymName(TD.Name) + ' = {';
    for J := 0 to ClassRT.ImplementsCount() - 1 do
    begin
      IntfDesc   := ClassRT.ImplementsIntfAt(J);
      IntfMangle := QBEMangle(IntfDesc.Name);
      if J = 0 then
        ImplLine := ImplLine + ' l $typeinfo_' + IntfTypeInfoName(IntfDesc.Name) +
                               ', l $itab_' + ClassSymName(TD.Name) + '_' + IntfMangle
      else
        ImplLine := ImplLine + ', l $typeinfo_' + IntfTypeInfoName(IntfDesc.Name) +
                               ', l $itab_' + ClassSymName(TD.Name) + '_' + IntfMangle;
    end;
    ImplLine := ImplLine + ', l 0 }';
    EmitLine(ImplLine);
  end;

  { Itab and impllist for generic class instances that implement interfaces }
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI      := TGenericInstance(AProg.GenericInstances.Items[I]);
    ClassRT := TRecordTypeDesc(GI.TypeDesc);
    if ClassRT.ImplementsCount() = 0 then Continue;
    MName := QBEMangle(GI.TypeName);

    { One itab per interface }
    for J := 0 to ClassRT.ImplementsCount() - 1 do
    begin
      IntfDesc   := ClassRT.ImplementsIntfAt(J);
      IntfMangle := QBEMangle(IntfDesc.Name);
      ItabLine   := 'data $itab_' + MName + '_' + IntfMangle + ' = {';
      for K := 0 to IntfDesc.MethodCount() - 1 do
      begin
        MethName := IntfDesc.MethodName(K);
        if IsAbstractClassMethod(ClassRT, MethName) then
          MethRef := '$_AbstractMethodError'
        else
        begin
          { Use ResolvedQbeName when set — it carries the unit-prefix-mangled
            name that matches the function definition emitted by EmitMethodDef.
            Fall back to MName_MethName for instances without a resolved name. }
          MDecl := FindMethodInClassDef(GI.ClassDef, MethName);
          if (MDecl <> nil) and (MDecl.ResolvedQbeName <> '') then
            MethRef := '$' + QBEMangle(MDecl.ResolvedQbeName)
          else
            MethRef := '$' + MName + '_' + MethName;
        end;
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
    for J := 0 to ClassRT.ImplementsCount() - 1 do
    begin
      IntfDesc   := ClassRT.ImplementsIntfAt(J);
      IntfMangle := QBEMangle(IntfDesc.Name);
      if J = 0 then
        ImplLine := ImplLine + ' l $typeinfo_' + IntfTypeInfoName(IntfDesc.Name) +
                               ', l $itab_' + MName + '_' + IntfMangle
      else
        ImplLine := ImplLine + ', l $typeinfo_' + IntfTypeInfoName(IntfDesc.Name) +
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
  Walk:   TRecordTypeDesc;
begin
  EmitLine(Format('%sfunction $_FieldCleanup_%s(l %%self) {', [ExportPrefix(), AMangledName]));
  EmitLine('@start');
  Walk := ARec;
  while Walk <> nil do
  begin
    if Walk.HasDestroyMethod then
    begin
      { Prefer the destructor's resolved emit name when set by semantic
        (this carries the overload-mangled '<Class>_Destroy$...' form);
        fall back to the unit-prefix-mangled '<unit>_<Class>_Destroy'. }
      if Walk.DestroyResolvedQbeName <> '' then
        EmitLine(Format('  call $%s(l %%self)',
          [QBEMangle(Walk.DestroyResolvedQbeName)]))
      else
        EmitLine(Format('  call $%s%s_Destroy(l %%self)',
          [ClassUnitPrefix(Walk.Name), QBEMangle(Walk.Name)]));
      Break;
    end;
    Walk := Walk.Parent;
  end;
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Items[I]);
    if F.TypeDesc = nil then Continue;
    { Nested record field: delegate to the shared per-field walker so its
      managed sub-fields (strings, classes, dyn-arrays, interfaces, deeper
      records) are released too. }
    if F.TypeDesc.Kind = tyRecord then
    begin
      if F.Offset > 0 then
      begin
        PtrT := AllocTemp();
        EmitLine(Format('  %s =l add %%self, %d', [PtrT, F.Offset]));
      end
      else
        PtrT := '%self';
      EmitRecordReleaseFields(TRecordTypeDesc(F.TypeDesc), PtrT);
      Continue;
    end;
    if not (F.TypeDesc.IsString() or (F.TypeDesc.Kind = tyClass)
            or (F.TypeDesc.Kind = tyDynArray)
            or (F.TypeDesc.Kind = tyInterface)) then
      Continue;
    { Unretained class field: non-owning — nothing to release or clear. }
    if F.IsUnretained and (F.TypeDesc.Kind = tyClass) then
      Continue;
    if F.Offset > 0 then
    begin
      PtrT := AllocTemp();
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
    Temp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [Temp, PtrT]));
    if F.TypeDesc.IsString() then
      EmitLine(Format('  call $_StringRelease(l %s)', [Temp]))
    else if F.TypeDesc.Kind = tyDynArray then
      EmitLine(Format('  call $_DynArrayRelease(l %s)', [Temp]))
    else
      { tyClass and tyInterface both release the obj slot via _ClassRelease;
        an interface's itab slot is static rodata so no release is needed. }
      EmitLine(Format('  call $_ClassRelease(l %s)', [Temp]));
    EmitLine(Format('  storel 0, %s', [PtrT]));
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
  if not FSystemDefsEmitted then
  begin
    EmitLine('export function $_FieldCleanup_TObject(l %self) {');
    EmitLine('@start');
    EmitLine('  ret');
    EmitLine('}');
    EmitLine('');
    EmitLine('export function $_FieldCleanup_TCustomAttribute(l %self) {');
    EmitLine('@start');
    EmitLine('  ret');
    EmitLine('}');
    EmitLine('');
  end;
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    EmitFieldCleanupFn(ClassSymName(TD.Name), RT);
  end;
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AProg.GenericInstances.Items[I]);
    RT := TRecordTypeDesc(GI.TypeDesc);
    EmitFieldCleanupFn(ClassSymName(QBEMangle(GI.TypeName)), RT);
  end;
end;

procedure TCodeGenQBE.EmitMethodDefs(AProg: TProgram);
var
  I, J:    Integer;
  TD:      TTypeDecl;
  CD:      TClassTypeDef;
  RD:      TRecordTypeDef;
  GI:      TGenericInstance;
  GRI:     TGenericRecordInstance;
  MDecl:   TMethodDecl;
  Methods: TObjectList;
begin
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if TD.Def is TClassTypeDef then
    begin
      CD      := TClassTypeDef(TD.Def);
      Methods := CD.Methods;
    end
    else if TD.Def is TRecordTypeDef then
    begin
      RD      := TRecordTypeDef(TD.Def);
      Methods := RD.Methods;
    end
    else
      Continue;
    for J := 0 to Methods.Count - 1 do
      if TMethodDecl(Methods.Items[J]).Body <> nil then
        EmitMethodDef(TD.Name, TMethodDecl(Methods.Items[J]));
  end;

  { Generic class instances — emit with mangled type name }
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

  { Generic record instances — emit method bodies }
  for I := 0 to AProg.GenericRecordInstances.Count - 1 do
  begin
    GRI := TGenericRecordInstance(AProg.GenericRecordInstances.Items[I]);
    for J := 0 to GRI.RecordDef.Methods.Count - 1 do
    begin
      MDecl := TMethodDecl(GRI.RecordDef.Methods.Items[J]);
      if MDecl.Body <> nil then
        EmitMethodDef(QBEMangle(GRI.TypeName), MDecl);
    end;
  end;
end;

procedure TCodeGenQBE.EmitFuncDef(ADecl: TMethodDecl; AExported: Boolean);
var
  Sig:             string;
  I:               Integer;
  Par:             TMethodParam;
  FuncName:        string;
  IsFunc:          Boolean;
  RetQType:        string;
  RetTemp:         string;
  ValTemp:         string;
  Prefix:          string;
  SavedExitLbl:    string;
  SavedCaptures:   TStringList;
  NestedDecl:      TMethodDecl;
  CapName:         string;
  NestedFuncName:  string;
begin
  if ADecl.IsExternal then Exit;  { no body to emit for external declarations }
  if ADecl.Body = nil then Exit;  { forward declaration — impl appears elsewhere }

  { Emit any nested procedures declared inside this function's body before
    emitting this function itself.  Each nested proc gets a mangled name
    OuterName_InnerName to avoid global symbol collisions.  They are emitted
    as non-exported (file-scope) functions. }
  for I := 0 to ADecl.Body.ProcDecls.Count - 1 do
  begin
    NestedDecl := TMethodDecl(ADecl.Body.ProcDecls.Items[I]);
    if NestedDecl.Body = nil then Continue;
    { Assign a mangled QBE name: OuterName_InnerName.
      Always override — the semantic pass set it to just InnerName,
      but nested procs must be unique in the global symbol space. }
    NestedDecl.ResolvedQbeName := ADecl.Name + '_' + NestedDecl.Name;
    EmitFuncDef(NestedDecl, False);
  end;

  if ADecl.ResolvedQbeName <> '' then
    FuncName := '$' + QBEMangle(ADecl.ResolvedQbeName)
  else
    FuncName := '$' + QBEMangle(ADecl.Name);
  IsFunc   := ADecl.ResolvedReturnType <> nil;
  if AExported or FExportAll then Prefix := 'export ' else Prefix := '';

  { Captured outer-scope variables are prepended as implicit pointer params.
    The call site in the enclosing function passes the address of each var. }
  Sig := '';
  if (ADecl.CapturedVars <> nil) and (ADecl.CapturedVars.Count > 0) then
    for I := 0 to ADecl.CapturedVars.Count - 1 do
    begin
      CapName := ADecl.CapturedVars.Strings[I];
      Sig := Sig + Format('l %%_cap_%s', [CapName]);
      if ADecl.Params.Count > 0 then Sig := Sig + ', ';
    end;

  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Items[I]);
    if Sig <> '' then Sig := Sig + ', ';
    if Par.IsOpenArray then
      Sig := Sig + Format('l %%_par_%s, l %%_par_%s_high',
        [Par.ParamName, Par.ParamName])
    else if Par.IsVarParam then
      Sig := Sig + Format('l %%_par_%s', [Par.ParamName])
    else if (Par.ResolvedType <> nil) and
            (Par.ResolvedType.Kind = tyInterface) then
      { Interfaces are two-slot fat pointers: object reference and
        interface dispatch table.  Caller passes both; callee allocs
        two local slots in the param-storage prologue below. }
      Sig := Sig + Format('l %%_par_%s_obj, l %%_par_%s_itab',
        [Par.ParamName, Par.ParamName])
    else
      Sig := Sig + Format('%s %%_par_%s', [QbeParamTypeOf(Par.ResolvedType), Par.ParamName]);
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
        tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum,
        tySmallInt, tyWord:
          begin
            EmitLine(Format('  %%_var_%s =l alloc4 1', [Par.ParamName]));
            EmitLine(Format('  storew %%_par_%s, %%_var_%s',
              [Par.ParamName, Par.ParamName]));
          end;
        tySet:
          { w (≤32 members) or l (≤64) bitmask — spill at its width. }
          if TSetTypeDesc(Par.ResolvedType).BitCount <= 32 then
          begin
            EmitLine(Format('  %%_var_%s =l alloc4 1', [Par.ParamName]));
            EmitLine(Format('  storew %%_par_%s, %%_var_%s',
              [Par.ParamName, Par.ParamName]));
          end
          else
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
        tyInterface:
          begin
            { Two-slot fat pointer — matches the local-var layout used
              by interface-aware codegen (e.g. EmitMethodCall reads
              %_var_X_obj / %_var_X_itab to dispatch). }
            EmitLine(Format('  %%_var_%s_obj =l alloc8 1', [Par.ParamName]));
            EmitLine(Format('  storel %%_par_%s_obj, %%_var_%s_obj',
              [Par.ParamName, Par.ParamName]));
            EmitLine(Format('  %%_var_%s_itab =l alloc8 1', [Par.ParamName]));
            EmitLine(Format('  storel %%_par_%s_itab, %%_var_%s_itab',
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
    retained copy that is balanced by the release pass at function exit).
    const params are skipped: the caller keeps the object alive for the
    whole call, so no retain/release is needed. }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Items[I]);
    if Par.IsVarParam or Par.IsOpenArray or Par.IsConstParam then Continue;
    if Par.ResolvedType.Kind = tyString then
    begin
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_StringAddRef(l %s)', [ValTemp]));
    end
    else if Par.ResolvedType.Kind = tyClass then
    begin
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_ClassAddRef(l %s)', [ValTemp]));
    end
    else if Par.ResolvedType.Kind = tyInterface then
    begin
      { Interfaces ARC through the object slot of their fat pointer; the
        itab is static and needs no refcounting. }
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s_obj',
        [ValTemp, Par.ParamName]));
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

  SavedExitLbl  := FExitLabel;
  SavedCaptures := FCapturedVars;
  FExitLabel    := AllocLabel('func_exit');
  if (ADecl.CapturedVars <> nil) and (ADecl.CapturedVars.Count > 0) then
    FCapturedVars := ADecl.CapturedVars
  else
    FCapturedVars := nil;
  try
    EmitBlock(ADecl.Body);
  finally
    FExitLabel    := SavedExitLbl;
    FCapturedVars := SavedCaptures;
  end;

  { ARC: release string and class value params on exit (balances the
    addref inserted at function entry). const params are skipped to match
    the entry pass (no retain was taken). }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Items[I]);
    if Par.IsVarParam or Par.IsOpenArray or Par.IsConstParam then Continue;
    if Par.ResolvedType.Kind = tyString then
    begin
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_StringRelease(l %s)', [ValTemp]));
    end
    else if Par.ResolvedType.Kind = tyClass then
    begin
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [ValTemp]));
    end
    else if Par.ResolvedType.Kind = tyInterface then
    begin
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s_obj', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [ValTemp]));
    end;
  end;

  if IsFunc then
  begin
    if ADecl.ResolvedReturnType.Kind = tyRecord then
      EmitLine('  ret')  { sret: caller's buffer already holds result }
    else
    begin
      RetTemp := AllocTemp();
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
  ArgTemps:  TStringList;
  I:         Integer;
  SetQT:     string;
  SetLoad:   string;
  SetStore:  string;
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
      FPtrTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s',
        [FPtrTemp, VarRef(ACall.Name, ACall.IndirectCallIsGlobal)]));
      ArgTemp := AllocTemp();
      EmitLine(Format('  %s =l add %s, 8',
        [ArgTemp, VarRef(ACall.Name, ACall.IndirectCallIsGlobal)]));
      ArgTemp2 := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [ArgTemp2, ArgTemp]));
      ArgLine := Format('l %s', [ArgTemp2]);
    end
    else
    begin
      FPtrTemp := AllocTemp();
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
      ArgTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_Self', [ArgTemp]));
      ArgLine := Format('l %s', [ArgTemp]);
      ArgTemps := TStringList.Create();
      try
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
              ArgTemp2 := AllocTemp();
              EmitLine(Format('  %s =l loadl %%_var_%s_high',
                [ArgTemp2, TIdentExpr(TASTExpr(ACall.Args.Items[I])).Name]));
              ArgLine := ArgLine + Format(', l %s, l %s', [ArgTemp, ArgTemp2]);
            end;
          end
          else if Par.IsVarParam then
            ArgLine := ArgLine + Format(', l %s',
              [EmitLValueAddr(TASTExpr(ACall.Args.Items[I]))])
          else if (Par.ResolvedType <> nil) and
                  (Par.ResolvedType.Kind = tyInterface) then
          begin
            if TASTExpr(ACall.Args.Items[I]).ResolvedType.Kind = tyClass then
            begin
              ArgTemp  := EmitExpr(TASTExpr(ACall.Args.Items[I]));
              ArgTemp2 := '$itab_' +
                ClassSymName(QBEMangle(TASTExpr(ACall.Args.Items[I]).ResolvedType.Name))
                + '_' + QBEMangle(Par.ResolvedType.Name);
              ArgLine := ArgLine + Format(', l %s, l %s', [ArgTemp, ArgTemp2]);
            end
            else
            begin
              EmitInterfaceExprPair(TASTExpr(ACall.Args.Items[I]),
                ArgTemp, ArgTemp2);
              ArgLine := ArgLine + Format(', l %s, l %s', [ArgTemp, ArgTemp2]);
            end;
          end
          else
          begin
            ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
            while ArgTemps.Count < I do ArgTemps.Add('');
            ArgTemps.Add(ArgTemp);
            EnsureConstStringRef(ArgTemp, Par);
            ArgTemp := CoerceArg(ArgTemp, TASTExpr(ACall.Args.Items[I]), QbeTypeOf(Par.ResolvedType));
            ArgLine := ArgLine + Format(', %s %s',
              [QbeParamTypeOf(Par.ResolvedType), ArgTemp]);
          end;
        end;
        EmitLine(Format('  call $%s(%s)',
          [MethodEmitName(MDecl, MDecl.OwnerTypeName, ACall.Name), ArgLine]));
        ReleaseConstStringArgs(ACall.Args, ArgTemps, MDecl.Params);
        Exit;
      finally
        ArgTemps.Free();
      end;
    end;
    ArgLine := '';
    { Captured-var pointers are prepended as implicit leading args.
      The callee receives them as l %_cap_<Name> params.
      Each captured var is stack-allocated in the outer function (ensured by
      EmitVarAllocs treating captured vars as address-taken), so %_var_<Name>
      is a valid alloc slot whose address can be passed directly.
      If we are ourselves nested and this var is one of our own captures,
      forward the pointer we received. }
    if (MDecl.CapturedVars <> nil) and (MDecl.CapturedVars.Count > 0) then
      for I := 0 to MDecl.CapturedVars.Count - 1 do
      begin
        if ArgLine <> '' then ArgLine := ArgLine + ', ';
        if IsCaptured(MDecl.CapturedVars.Strings[I]) then
          ArgLine := ArgLine + Format('l %%_cap_%s', [MDecl.CapturedVars.Strings[I]])
        else
          ArgLine := ArgLine + Format('l %%_var_%s', [MDecl.CapturedVars.Strings[I]]);
      end;
    ArgTemps := TStringList.Create();
    try
      for I := 0 to ACall.Args.Count - 1 do
      begin
        Par := TMethodParam(MDecl.Params.Items[I]);
        if ArgLine <> '' then ArgLine := ArgLine + ', ';
        if Par.IsOpenArray then
        begin
          ArgTemps.Add('');
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
            ArgTemp2 := AllocTemp();
            EmitLine(Format('  %s =l loadl %%_var_%s_high',
              [ArgTemp2, TIdentExpr(TASTExpr(ACall.Args.Items[I])).Name]));
            ArgLine := ArgLine + Format('l %s, l %s', [ArgTemp, ArgTemp2]);
          end;
        end
        else if Par.IsVarParam then
        begin
          ArgTemps.Add('');
          ArgLine := ArgLine + Format('l %s',
            [EmitLValueAddr(TASTExpr(ACall.Args.Items[I]))]);
        end
        else if (Par.ResolvedType <> nil) and
                (Par.ResolvedType.Kind = tyInterface) then
        begin
          ArgTemps.Add('');
          if TASTExpr(ACall.Args.Items[I]).ResolvedType.Kind = tyClass then
          begin
            ArgTemp  := EmitExpr(TASTExpr(ACall.Args.Items[I]));
            ArgTemp2 := '$itab_' +
              ClassSymName(QBEMangle(TASTExpr(ACall.Args.Items[I]).ResolvedType.Name))
              + '_' + QBEMangle(Par.ResolvedType.Name);
            ArgLine := ArgLine + Format('l %s, l %s', [ArgTemp, ArgTemp2]);
          end
          else
          begin
            EmitInterfaceExprPair(TASTExpr(ACall.Args.Items[I]),
              ArgTemp, ArgTemp2);
            ArgLine := ArgLine + Format('l %s, l %s', [ArgTemp, ArgTemp2]);
          end;
        end
        else
        begin
          ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
          ArgTemps.Add(ArgTemp);
          EnsureConstStringRef(ArgTemp, Par);
          ArgTemp := CoerceArg(ArgTemp, TASTExpr(ACall.Args.Items[I]), QbeTypeOf(Par.ResolvedType));
          ArgLine := ArgLine + Format('%s %s', [QbeParamTypeOf(Par.ResolvedType), ArgTemp]);
        end;
      end;
      if MDecl.IsExternal and (MDecl.ExternalName <> '') then
        EmitLine(Format('  call $%s(%s)', [MDecl.ExternalName, ArgLine]))
      else if MDecl.ResolvedQbeName <> '' then
        EmitLine(Format('  call $%s(%s)', [QBEMangle(MDecl.ResolvedQbeName), ArgLine]))
      else
        EmitLine(Format('  call $%s(%s)', [QBEMangle(ACall.Name), ArgLine]));
      EmitOwnedArgReleases(ACall.Args, ArgTemps, MDecl.Params);
      ReleaseConstStringArgs(ACall.Args, ArgTemps, MDecl.Params);
    finally
      ArgTemps.Free();
    end;
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
    EmitLine(Format('  call $_BlaiseFreeMem(l %s)', [ArgTemp]));
  end
  else if UCaseName = 'ZEROMEM' then
  begin
    ArgTemp  := EmitExpr(TASTExpr(ACall.Args.Items[0]));
    ArgTemp2 := EmitExpr(TASTExpr(ACall.Args.Items[1]));
    SizeTemp := AllocTemp();
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
      ArgTemp2 := AllocTemp();
      if (TASTExpr(ACall.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(ACall.Args.Items[0]).ResolvedType.Kind in [tyInt64, tyUInt64, tyClass, tyPointer]) then
      begin
        EmitLine(Format('  %s =l copy %%_var_%s', [ArgTemp2, ArgTemp]));
        if ACall.Args.Count >= 2 then
          SizeTemp := EmitExpr(TASTExpr(ACall.Args.Items[1]))
        else
          SizeTemp := '1';
        ArgLine := AllocTemp();
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
        ArgLine := AllocTemp();
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
      ArgTemp2 := AllocTemp();
      if (TASTExpr(ACall.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(ACall.Args.Items[0]).ResolvedType.Kind in [tyInt64, tyUInt64, tyClass, tyPointer]) then
      begin
        EmitLine(Format('  %s =l loadl %s', [ArgTemp2, ArgTemp]));
        if ACall.Args.Count >= 2 then
          SizeTemp := EmitExpr(TASTExpr(ACall.Args.Items[1]))
        else
          SizeTemp := '1';
        ArgLine := AllocTemp();
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
        ArgLine := AllocTemp();
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
    SetQT := QbeTypeOf(TASTExpr(ACall.Args.Items[0]).ResolvedType);
    SetLoad := LoadInstrFor(TASTExpr(ACall.Args.Items[0]).ResolvedType);
    SetStore := StoreInstrFor(TASTExpr(ACall.Args.Items[0]).ResolvedType);
    ArgTemp  := EmitLValueAddr(TASTExpr(ACall.Args.Items[0]));
    ArgTemp2 := AllocTemp();
    EmitLine(Format('  %s =%s %s %s', [ArgTemp2, SetQT, SetLoad, ArgTemp]));
    SizeTemp := EmitExpr(TASTExpr(ACall.Args.Items[1]));
    ArgLine  := AllocTemp();
    EmitLine(Format('  %s =%s shl 1, %s', [ArgLine, SetQT, SizeTemp]));
    SizeTemp := AllocTemp();
    EmitLine(Format('  %s =%s or %s, %s', [SizeTemp, SetQT, ArgTemp2, ArgLine]));
    EmitLine(Format('  %s %s, %s', [SetStore, SizeTemp, ArgTemp]));
  end
  else if UCaseName = 'EXCLUDE' then
  begin
    { Exclude(S, elem): S := S and (not (1 shl ord(elem))) }
    SetQT := QbeTypeOf(TASTExpr(ACall.Args.Items[0]).ResolvedType);
    SetLoad := LoadInstrFor(TASTExpr(ACall.Args.Items[0]).ResolvedType);
    SetStore := StoreInstrFor(TASTExpr(ACall.Args.Items[0]).ResolvedType);
    ArgTemp  := EmitLValueAddr(TASTExpr(ACall.Args.Items[0]));
    ArgTemp2 := AllocTemp();
    EmitLine(Format('  %s =%s %s %s', [ArgTemp2, SetQT, SetLoad, ArgTemp]));
    SizeTemp := EmitExpr(TASTExpr(ACall.Args.Items[1]));
    ArgLine  := AllocTemp();
    EmitLine(Format('  %s =%s shl 1, %s', [ArgLine, SetQT, SizeTemp]));
    SizeTemp := AllocTemp();
    EmitLine(Format('  %s =%s xor %s, -1', [SizeTemp, SetQT, ArgLine]));
    ArgLine  := AllocTemp();
    EmitLine(Format('  %s =%s and %s, %s', [ArgLine, SetQT, ArgTemp2, SizeTemp]));
    EmitLine(Format('  %s %s, %s', [SetStore, ArgLine, ArgTemp]));
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

  OldTemp := AllocTemp();
  EmitLine(Format('  %s =l loadl %s', [OldTemp, Addr]));

  ArgLine := Format('l %s', [OldTemp]);
  for I := 1 to AExtraArgCount do
  begin
    Extra := EmitExpr(TASTExpr(ACall.Args.Items[I]));
    ArgLine := ArgLine + Format(', w %s', [Extra]);
  end;

  NewTemp := AllocTemp();
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
  OldPtr  := AllocTemp();
  EmitLine(Format('  %s =l loadl %s', [OldPtr, Addr]));
  NTemp   := EmitExpr(TASTExpr(ACall.Args.Items[1]));
  DAT     := TDynArrayTypeDesc(TASTExpr(ACall.Args.Items[0]).ResolvedType);
  ElemSz  := DAT.ElementType.RawSize();
  NewPtr  := AllocTemp();
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
  if (AStmt.BaseTy <> nil) and AStmt.BaseTy.IsString() then
  begin
    OldTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [OldTemp, PtrTemp]));
    ValTemp := EmitExpr(AStmt.ValExpr);
    EmitLine(Format('  call $_StringAddRef(l %s)', [ValTemp]));
    EmitLine(Format('  call $_StringRelease(l %s)', [OldTemp]));
    EmitLine(Format('  storel %s, %s', [ValTemp, PtrTemp]));
    Exit;
  end;
  { ARC: class reference stored through a typed pointer needs retain/release.
    Mirrors the string path so generic ^T storage on TList<TObject>,
    TStack<TObject> etc. keeps a strong reference to the stored object. }
  if (AStmt.BaseTy <> nil) and (AStmt.BaseTy.Kind = tyClass) then
  begin
    OldTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [OldTemp, PtrTemp]));
    ValTemp := EmitExpr(AStmt.ValExpr);
    EmitLine(Format('  call $_ClassAddRef(l %s)', [ValTemp]));
    EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
    EmitLine(Format('  storel %s, %s', [ValTemp, PtrTemp]));
    Exit;
  end;
  if (AStmt.BaseTy <> nil) and (AStmt.BaseTy.Kind in [tyByte, tyBoolean]) then
    ValTemp := EmitByteRhs(AStmt.ValExpr)
  else
    ValTemp := EmitExpr(AStmt.ValExpr);
  QType   := QbeTypeOf(AStmt.BaseTy);
  { Byte/Boolean stores must use storeb — storew would write four
    bytes and clobber three adjacent bytes.  Symmetric with the
    loadub fix in the TDerefExpr branch of EmitExpr. }
  if (AStmt.BaseTy <> nil) and
     (AStmt.BaseTy.Kind in [tyByte, tyBoolean]) then
    StoreInstr := 'storeb'
  else if QType = 'w' then StoreInstr := 'storew'
                      else StoreInstr := 'storel';
  EmitLine(Format('  %s %s, %s', [StoreInstr, ValTemp, PtrTemp]));
end;

procedure TCodeGenQBE.EmitWrite(ACall: TProcCall; ANewline: Boolean);
var
  ArgExpr:  TASTExpr;
  ArgTemp:  string;
  T2:       string;
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
    IsString := (ArgExpr.ResolvedType <> nil) and ArgExpr.ResolvedType.IsString();
    ArgTemp  := EmitExpr(ArgExpr);
    if IsString then
      EmitLine(Format('  call $_SysWriteStr(w %s, l %s)', [FdLit, ArgTemp]))
    else if (ArgExpr.ResolvedType <> nil) and
            (ArgExpr.ResolvedType.Kind = tyBoolean) then
      EmitLine(Format('  call $_SysWriteBool(w %s, w %s)', [FdLit, ArgTemp]))
    else if (ArgExpr.ResolvedType <> nil) and
            (ArgExpr.ResolvedType.Kind = tyDouble) then
      EmitLine(Format('  call $_SysWriteDouble(w %s, d %s)', [FdLit, ArgTemp]))
    else if (ArgExpr.ResolvedType <> nil) and
            (ArgExpr.ResolvedType.Kind = tySingle) then
      EmitLine(Format('  call $_SysWriteSingle(w %s, s %s)', [FdLit, ArgTemp]))
    else if (ArgExpr.ResolvedType <> nil) and
            (ArgExpr.ResolvedType.Kind = tyUInt64) then
      EmitLine(Format('  call $_SysWriteUInt64(w %s, l %s)', [FdLit, ArgTemp]))
    else if (ArgExpr.ResolvedType <> nil) and
            (ArgExpr.ResolvedType.Kind in [tyUInt32, tyWord]) then
    begin
      { Unsigned 32-bit value: zero-extend to 64 bits and use the unsigned
        writer, so a value above 2^31 prints as a large positive number rather
        than a negative signed wrap.  (Byte/Boolean/Enum stay on the signed
        32-bit writer: their value range is always non-negative there.) }
      T2 := AllocTemp();
      EmitLine(Format('  %s =l extuw %s', [T2, ArgTemp]));
      EmitLine(Format('  call $_SysWriteUInt64(w %s, l %s)', [FdLit, T2]));
    end
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
  ArgTemps:   TStringList;
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
  SAT:          TStaticArrayTypeDesc;
  ElemSize:     Integer;
  FmtArgCount:  Integer;
  FmtArrTemp:   string;
  FmtSlotTemp:  string;
  FmtValTemp:   string;
  IsIntArg:     Boolean;
  FT:           string;
  ItabName:     string;
  PT:           TProceduralTypeDesc;
  SlotAddr:     string;
  DataTemp:     string;
  SQT:          string;
begin
  if AExpr is TFuncCallExpr then
  begin
    { Standalone function call expression }
    FC := TFuncCallExpr(AExpr);
    { SizeOf(TypeName) → integer literal = byte size of the type }
      if SameText(FC.Name,'SizeOf') then
      begin
        T := AllocTemp();
        EmitLine(Format('  %s =w copy %d',
          [T, TASTExpr(FC.Args.Items[0]).ResolvedType.ByteSize()]));
        Exit(T);
      end;

      { GetMem(N) → _BlaiseGetMem(N) → pointer.  _BlaiseGetMem takes
        Integer (w), no extension needed. }
      if SameText(FC.Name,'GetMem') then
      begin
        ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_BlaiseGetMem(w %s)', [T, ArgTemp]));
        Exit(T);
      end;

      { ReallocMem(P, N) → _BlaiseReallocMem(P, N) → pointer.  Size arg
        is Integer (w). }
      if SameText(FC.Name,'ReallocMem') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_BlaiseReallocMem(l %s, w %s)', [T, L, R]));
        Exit(T);
      end;

      { Open-array intrinsics }
      if SameText(FC.Name,'High') then
      begin
        T := AllocTemp();
        case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
          tyStaticArray:
            EmitLine(Format('  %s =w copy %d', [T,
              TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).HighBound]));
          tyDynArray:
          begin
            { High(A) = Length(A) - 1; delegate to RTL helper }
            L := EmitExpr(TASTExpr(FC.Args.Items[0]));
            R := AllocTemp();
            EmitLine(Format('  %s =w call $_DynArrayLength(l %s)', [R, L]));
            EmitLine(Format('  %s =w sub %s, 1', [T, R]));
          end;
          tyString:
          begin
            { High(S) = Length(S) - 1; load length from ARC header at data_ptr-8 }
            L := EmitExpr(TASTExpr(FC.Args.Items[0]));
            R := AllocTemp();
            EmitLine(Format('  %s =l sub %s, 8', [R, L]));
            EmitLine(Format('  %s =w loadsw %s', [T, R]));
            R := AllocTemp();
            EmitLine(Format('  %s =w sub %s, 1', [R, T]));
            T := R;
          end;
          tyByte:     EmitLine(Format('  %s =w copy 255', [T]));
          tyBoolean:  EmitLine(Format('  %s =w copy 1', [T]));
          tySmallInt: EmitLine(Format('  %s =w copy 32767', [T]));
          tyWord:     EmitLine(Format('  %s =w copy 65535', [T]));
          tyInteger:  EmitLine(Format('  %s =w copy 2147483647', [T]));
          tyUInt32:   EmitLine(Format('  %s =w copy 4294967295', [T]));
          tyInt64:    EmitLine(Format('  %s =l copy 9223372036854775807', [T]));
          tyUInt64:   EmitLine(Format('  %s =l copy 18446744073709551615', [T]));
          tyEnum:     EmitLine(Format('  %s =w copy %d', [T,
            TEnumTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).Members.Count - 1]));
        else
          begin
            { Open-array: load the high-index slot and truncate to Integer (w).
              QBE has no truncl; assigning an l value to a w temp implicitly truncates. }
            L := TIdentExpr(FC.Args.Items[0]).Name;
            R := AllocTemp();
            EmitLine(Format('  %s =l loadl %%_var_%s_high', [R, L]));
            EmitLine(Format('  %s =w copy %s', [T, R]));
          end;
        end;
        Exit(T);
      end;

      if SameText(FC.Name,'Low') then
      begin
        T := AllocTemp();
        case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
          tyStaticArray:
            EmitLine(Format('  %s =w copy %d', [T,
              TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).LowBound]));
          tyString:
            EmitLine(Format('  %s =w copy 0', [T]));
          tyByte, tyBoolean, tyWord, tyUInt32, tyEnum:
            EmitLine(Format('  %s =w copy 0', [T]));
          tySmallInt: EmitLine(Format('  %s =w copy -32768', [T]));
          tyInteger:  EmitLine(Format('  %s =w copy -2147483648', [T]));
          tyInt64:    EmitLine(Format('  %s =l copy -9223372036854775808', [T]));
          tyUInt64:   EmitLine(Format('  %s =l copy 0', [T]));
        else
          EmitLine(Format('  %s =w copy 0', [T]));
        end;
        Exit(T);
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
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_StringFromPChar(l %s)', [T, L]));
        Exit(T);
      end;

      { Built-in string/array length }
      if SameText(FC.Name,'Length') then
      begin
        T := AllocTemp();
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
            R := AllocTemp();
            EmitLine(Format('  %s =l loadl %%_var_%s_high', [R, L]));
            EmitLine(Format('  %s =w add %s, 1', [T, R]));
          end;
          tyDynArray:
          begin
            { Length stored at data_ptr − 4; nil ptr → length 0 }
            L := EmitExpr(TASTExpr(FC.Args.Items[0]));
            R := AllocTemp();
            EmitLine(Format('  %s =w call $_DynArrayLength(l %s)', [R, L]));
            EmitLine(Format('  %s =w copy %s', [T, R]));
          end;
        else
          { tyString: delegate to RTL }
          L := EmitExpr(TASTExpr(FC.Args.Items[0]));
          EmitLine(Format('  %s =w call $_StringLength(l %s)', [T, L]));
        end;
        Exit(T);
      end;

      if SameText(FC.Name,'Pos') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp();
        EmitLine(Format('  %s =w call $_StringPos(l %s, l %s)', [T, L, R]));
        Exit(T);
      end;

      if SameText(FC.Name,'PosEx') then
      begin
        L       := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R       := EmitExpr(TASTExpr(FC.Args.Items[1]));
        ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[2]));
        T := AllocTemp();
        EmitLine(Format('  %s =w call $_StringPosEx(l %s, l %s, w %s)',
          [T, L, R, ArgTemp]));
        Exit(T);
      end;

      if SameText(FC.Name,'Copy') then
      begin
        L       := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R       := EmitExpr(TASTExpr(FC.Args.Items[1]));
        ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[2]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_StringCopy(l %s, w %s, w %s)',
          [T, L, R, ArgTemp]));
        Exit(T);
      end;

      if SameText(FC.Name,'UpperCase') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_StringUpperCase(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'LowerCase') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_StringLowerCase(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'Trim') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_StringTrim(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'SameText') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp();
        EmitLine(Format('  %s =w call $_StringSameText(l %s, l %s)', [T, L, R]));
        Exit(T);
      end;

      if SameText(FC.Name,'Assigned') then
      begin
        { Assigned(P) ≡ P <> nil — emit a pointer comparison. }
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =w cnel %s, 0', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'IntToStr') then
      begin
        { Route to _Int64ToStr / _UInt64ToStr / _IntToStr based on the
          argument's resolved type.  Matches FPC's overloaded
          IntToStr(Int64) / IntToStr(QWord) / IntToStr(Integer). }
        if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
           (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyUInt64) then
        begin
          L := EmitExpr(TASTExpr(FC.Args.Items[0]));
          T := AllocTemp();
          EmitLine(Format('  %s =l call $_UInt64ToStr(l %s)', [T, L]));
        end
        else if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
                (QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType) = 'l') then
        begin
          L := EmitExpr(TASTExpr(FC.Args.Items[0]));
          T := AllocTemp();
          EmitLine(Format('  %s =l call $_Int64ToStr(l %s)', [T, L]));
        end
        else
        begin
          L := EmitExpr(TASTExpr(FC.Args.Items[0]));
          T := AllocTemp();
          EmitLine(Format('  %s =l call $_IntToStr(w %s)', [T, L]));
        end;
        Exit(T);
      end;

      if SameText(FC.Name,'Int64ToStr') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_Int64ToStr(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'UInt64ToStr') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_UInt64ToStr(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'DoubleToStr') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_DoubleToStr(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'SingleToStr') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_SingleToStr(s %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'StrToDouble') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =d call $_StrToDouble(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'Abs') then
      begin
        L   := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T   := AllocTemp();
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        case QType of
          'w': EmitLine(Format('  %s =w call $_AbsInt(w %s)',   [T, L]));
          'l': EmitLine(Format('  %s =l call $_AbsInt64(l %s)', [T, L]));
          'd': EmitLine(Format('  %s =d call $fabs(d %s)',      [T, L]));
          's': EmitLine(Format('  %s =s call $fabsf(s %s)',     [T, L]));
        else   EmitLine(Format('  %s =w call $_AbsInt(w %s)',   [T, L]));
        end;
        Exit(T);
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
        T := AllocTemp();
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $sqrtf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $sqrt(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Ceil') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        R := AllocTemp();
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
        Exit(R);
      end;

      if SameText(FC.Name, 'Floor') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        R := AllocTemp();
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
        Exit(R);
      end;

      if SameText(FC.Name, 'Trunc') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =w stosi %s', [T, L]))
        else
          EmitLine(Format('  %s =w dtosi %s', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Round') then
      begin
        { Round half-away from zero: C99 round() rounds .5 away from zero,
          matching the behaviour of Delphi/FPC Round(). }
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        R := AllocTemp();
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
        Exit(R);
      end;

      if SameText(FC.Name, 'Ln') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $logf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $log(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Log2') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $log2f(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $log2(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Log10') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $log10f(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $log10(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Power') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp();
        EmitLine(Format('  %s =d call $pow(d %s, d %s)', [T, L, R]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Sin') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $sinf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $sin(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Cos') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $cosf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $cos(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Tan') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $tanf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $tan(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'ArcTan') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $atanf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $atan(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'ArcTan2') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp();
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $atan2f(s %s, s %s)', [T, L, R]))
        else
          EmitLine(Format('  %s =d call $atan2(d %s, d %s)', [T, L, R]));
        Exit(T);
      end;

      if SameText(FC.Name, 'ArcSin') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $asinf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $asin(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'ArcCos') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $acosf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $acos(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Sinh') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $sinhf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $sinh(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Cosh') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $coshf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $cosh(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Tanh') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =s call $tanhf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $tanh(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'IsNaN') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =w call $__isnanf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =w call $__isnan(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'IsInfinite') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        QType := QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType);
        if QType = 's' then
          EmitLine(Format('  %s =w call $__isinff(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =w call $__isinf(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'StrToInt') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =w call $_StrToInt(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'MethodAddress') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_MethodAddress(l %s, l %s)', [T, L, R]));
        Exit(T);
      end;

      { HasClassAttribute(AClass, AAttrClass): Boolean — query attribute RTTI.
        Both arguments are metaclass expressions (typeinfo pointers).
        Lowers to '$_HasClassAttribute(l ti_class, l ti_attr)' returning w. }
      if FC.IsBuiltinHasClassAttr then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp();
        EmitLine(Format('  %s =w call $_HasClassAttribute(l %s, l %s)', [T, L, R]));
        Exit(T);
      end;

      { ClassCreate(Cls, ...args): runtime equivalent of TFoo.Create(args).
        Allocates via _ClassCreate (which reads totalsize/fieldcleanup/vtable
        from Cls's typeinfo), then calls $<BaseClass>_Create statically with
        the new pointer and the supplied args.  Returns the new pointer. }
      if SameText(FC.Name,'ClassCreate') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));   { metaclass = typeinfo ptr }
        T := AllocTemp();
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
              [QbeParamTypeOf(Par.ResolvedType), ArgTemp]);
          end;
          EmitLine(Format('  call $%s(%s)',
            [MethodEmitName(MDecl, MDecl.OwnerTypeName, 'Create'), ArgLine]));
        end;
        Exit(T);
      end;

      if SameText(FC.Name,'StrToInt64') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_StrToInt64(l %s)', [T, L]));
        Exit(T);
      end;

      { Format(fmt, arg0, arg1, ...) → stack array of (tag, value) pairs
        passed to $_StringFormat(l fmt, l args, w count).
        Each arg is stored as a 16-byte record: [tag:l, value:l].
        tag=0 for integer types, tag=1 for string/pointer types. }
      if SameText(FC.Name,'Format') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        { Collect format arguments into a list of (expr, isInt) pairs }
        if (FC.Args.Count = 2) and (FC.Args.Items[1] is TArrayLiteralExpr) then
          FmtArgCount := TArrayLiteralExpr(FC.Args.Items[1]).Elements.Count
        else
          FmtArgCount := FC.Args.Count - 1;
        if FmtArgCount > 0 then
        begin
          FmtArrTemp := AllocTemp();
          EmitLine(Format('  %s =l alloc8 %d', [FmtArrTemp, FmtArgCount * 16]));
          for I := 0 to FmtArgCount - 1 do
          begin
            if (FC.Args.Count = 2) and (FC.Args.Items[1] is TArrayLiteralExpr) then
            begin
              ArgTemp := EmitExpr(TASTExpr(TArrayLiteralExpr(FC.Args.Items[1]).Elements.Items[I]));
              IsIntArg := TASTExpr(TArrayLiteralExpr(FC.Args.Items[1]).Elements.Items[I]).ResolvedType.Kind in
                [tyInteger, tyBoolean, tyByte, tyUInt32, tyInt64, tyUInt64,
                 tySmallInt, tyWord, tyEnum];
            end
            else
            begin
              ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[I + 1]));
              IsIntArg := TASTExpr(FC.Args.Items[I + 1]).ResolvedType.Kind in
                [tyInteger, tyBoolean, tyByte, tyUInt32, tyInt64, tyUInt64,
                 tySmallInt, tyWord, tyEnum];
            end;
            FmtSlotTemp := AllocTemp();
            EmitLine(Format('  %s =l add %s, %d', [FmtSlotTemp, FmtArrTemp, I * 16]));
            if IsIntArg then
              EmitLine(Format('  storel 0, %s', [FmtSlotTemp]))
            else
              EmitLine(Format('  storel 1, %s', [FmtSlotTemp]));
            FmtValTemp := AllocTemp();
            EmitLine(Format('  %s =l add %s, 8', [FmtValTemp, FmtSlotTemp]));
            if IsIntArg then
            begin
              { Integer args may be w-typed; widen to l for storel. }
              if (FC.Args.Count = 2) and (FC.Args.Items[1] is TArrayLiteralExpr) then
                QType := QbeTypeOf(TASTExpr(TArrayLiteralExpr(FC.Args.Items[1]).Elements.Items[I]).ResolvedType)
              else
                QType := QbeTypeOf(TASTExpr(FC.Args.Items[I + 1]).ResolvedType);
              if QType = 'w' then
              begin
                FmtSlotTemp := AllocTemp();
                EmitLine(Format('  %s =l extsw %s', [FmtSlotTemp, ArgTemp]));
                ArgTemp := FmtSlotTemp;
              end;
            end;
            EmitLine(Format('  storel %s, %s', [ArgTemp, FmtValTemp]));
          end;
        end
        else
        begin
          FmtArrTemp := AllocTemp();
          EmitLine(Format('  %s =l copy 0', [FmtArrTemp]));
        end;
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_StringFormatN(l %s, l %s, w %d)', [T, L, FmtArrTemp, FmtArgCount]));
        Exit(T);
      end;

      if SameText(FC.Name,'OrdAt') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp();
        EmitLine(Format('  %s =w call $_OrdAt(l %s, w %s)', [T, L, R]));
        Exit(T);
      end;

      if SameText(FC.Name,'Ord') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        { String/char arg: get ordinal of first byte via OrdAt(str, 0) }
        { Enum/integer arg: already an integer — just copy }
        if TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyString then
          EmitLine(Format('  %s =w call $_OrdAt(l %s, w 0)', [T, L]))
        else
          EmitLine(Format('  %s =w copy %s', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'Chr') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_Chr(w %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'UpCase') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
           TASTExpr(FC.Args.Items[0]).ResolvedType.IsString() then
        begin
          T := AllocTemp();
          EmitLine(Format('  %s =w call $_OrdAt(l %s, w 0)', [T, L]));
          L := T;
        end;
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_UpCase(w %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'CompareStr') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp();
        EmitLine(Format('  %s =w call $_StringCompare(l %s, l %s)', [T, L, R]));
        Exit(T);
      end;

      if SameText(FC.Name,'CompareText') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp();
        EmitLine(Format('  %s =w call $_StringCompareText(l %s, l %s)', [T, L, R]));
        Exit(T);
      end;

      { CLI arguments }
      if SameText(FC.Name,'ParamCount') then
      begin
        T := AllocTemp();
        EmitLine(Format('  %s =w call $_ParamCount()', [T]));
        Exit(T);
      end;

      if SameText(FC.Name,'GetProcessID') then
      begin
        T := AllocTemp();
        EmitLine(Format('  %s =w call $_GetProcessID()', [T]));
        Exit(T);
      end;

      if SameText(FC.Name,'GetTempDir') then
      begin
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_GetTempDir()', [T]));
        Exit(T);
      end;

      if SameText(FC.Name,'GetCurrentDir') then
      begin
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_GetCurrentDir()', [T]));
        Exit(T);
      end;

      if SameText(FC.Name,'GetTempFileName') then
      begin
        L       := EmitExpr(TASTExpr(FC.Args.Items[0]));
        R       := EmitExpr(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_GetTempFileName(l %s, l %s)', [T, L, R]));
        Exit(T);
      end;

      if SameText(FC.Name,'ParamStr') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_ParamStr(w %s)', [T, L]));
        Exit(T);
      end;

      { File I/O functions }
      if SameText(FC.Name,'ReadFile') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_ReadFile(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'FileExists') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =w call $_FileExists(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'DirectoryExists') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =w call $_DirectoryExists(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'ForceDirectories') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =w call $_ForceDirectories(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'FileAge') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_FileAge(l %s)', [T, L]));
        Exit(T);
      end;

      { Environment and process }
      if SameText(FC.Name,'GetEnvVar') or SameText(FC.Name,'GetEnvironmentVariable') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_GetEnvVar(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'CurrentExceptionMessage') then
      begin
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_CurrentExceptionMessage()', [T]));
        Exit(T);
      end;

      if SameText(FC.Name,'Exec') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =w call $_Exec(l %s)', [T, L]));
        Exit(T);
      end;

      { File path manipulation }
      if SameText(FC.Name,'ChangeFileExt') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_ChangeFileExt(l %s, l %s)',
          [T, L, EmitExpr(TASTExpr(FC.Args.Items[1]))]));
        Exit(T);
      end;

      if SameText(FC.Name,'ExtractFileName') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_ExtractFileName(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'ExtractFilePath') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_ExtractFilePath(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'ExtractFileDir') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_ExtractFileDir(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'ExtractFileExt') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_ExtractFileExt(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'ExcludeTrailingPathDelimiter') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_ExcludeTrailingPathDelimiter(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'IncludeTrailingPathDelimiter') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_IncludeTrailingPathDelimiter(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'RenameFile') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =w call $_RenameFile(l %s, l %s)',
          [T, L, EmitExpr(TASTExpr(FC.Args.Items[1]))]));
        Exit(T);
      end;

      if SameText(FC.Name,'SetCurrentDir') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =w call $_SetCurrentDir(l %s)', [T, L]));
        Exit(T);
      end;

      { Process management built-ins }
      if SameText(FC.Name,'ProcessCreate') then
      begin
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_ProcessCreate()', [T]));
        Exit(T);
      end;

      if SameText(FC.Name,'ProcessRunning') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =w call $_ProcessRunning(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'ProcessReadOutput') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_ProcessReadOutput(l %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name,'ProcessExitCode') then
      begin
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        EmitLine(Format('  %s =w call $_ProcessExitCode(l %s)', [T, L]));
        Exit(T);
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
          FPtrTemp := AllocTemp();
          EmitLine(Format('  %s =l loadl %s',
            [FPtrTemp, VarRef(FC.Name, FC.IndirectCallIsGlobal)]));
          ArgTemp := AllocTemp();
          EmitLine(Format('  %s =l add %s, 8',
            [ArgTemp, VarRef(FC.Name, FC.IndirectCallIsGlobal)]));
          T := AllocTemp();
          EmitLine(Format('  %s =l loadl %s', [T, ArgTemp]));
          ArgLine := Format('l %s', [T]);
        end
        else
        begin
          FPtrTemp := AllocTemp();
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
          T      := AllocTemp();
          EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FPtrTemp, ArgLine]));
          Result := T;
        end;
        Exit;
      end;

      { Type cast TypeName(Expr) — ResolvedDecl is nil; copy/extend/truncate to target QBE type }
      if FC.ResolvedDecl = nil then
      begin
        ArgTemp  := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T        := AllocTemp();
        QType    := QbeTypeOf(FC.ResolvedType);
        if FC.ResolvedType.Kind = tyByte then
          { Byte(X): truncate to 8 bits — mask to [0..255] }
          EmitLine(Format('  %s =w and %s, 255', [T, ArgTemp]))
        else if FC.ResolvedType.Kind in [tySmallInt, tyWord] then
          { SmallInt(X) / Word(X): truncate to 16 bits.  Sign extension on
            read is the load instruction's job (loadsh vs loaduh). }
          EmitLine(Format('  %s =w and %s, 65535', [T, ArgTemp]))
        else if QType = 'w' then
          EmitLine(Format('  %s =w copy %s', [T, ArgTemp]))
        else
        begin
          { Widening from w to l: zero-extend for pointer/unsigned targets,
            sign-extend otherwise (QBE rejects 'l copy w'). }
          if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
             (QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType) = 'w') then
          begin
            if FC.ResolvedType.Kind in [tyUInt64, tyPointer, tyPChar] then
              EmitLine(Format('  %s =l extuw %s', [T, ArgTemp]))
            else
              EmitLine(Format('  %s =l extsw %s', [T, ArgTemp]));
          end
          else
            EmitLine(Format('  %s =l copy %s', [T, ArgTemp]));
        end;
        Exit(T);
      end;

      MDecl    := TMethodDecl(FC.ResolvedDecl);
      QType    := QbeTypeOf(MDecl.ResolvedReturnType);

      { Try inline emission first.  Falls through to the regular call when
        the callee is not an inline candidate or the call shape does not
        qualify (recursive nesting, etc.).
        Inlining only fires for non-record return; the sret path below
        handles records and inlining would not save the buffer alloc. }
      if MDecl.IsInlineCandidate and not FC.IsImplicitSelfMethod and
         (MDecl.ResolvedReturnType <> nil) and
         (MDecl.ResolvedReturnType.Kind <> tyRecord) then
      begin
        if TryEmitInlineCall(FC, T) then
        begin
          Exit(T);
        end;
      end;

      { sret: record-returning function — caller allocates a zero-init buffer
        and passes its address as the first (hidden) parameter. }
      if MDecl.ResolvedReturnType.Kind = tyRecord then
      begin
        RT      := TRecordTypeDesc(MDecl.ResolvedReturnType);
        SretBuf := AllocTemp();
        if RT.MaxAlign() >= 8 then
          EmitLine(Format('  %s =l alloc8 %d', [SretBuf, RT.TotalSize()]))
        else
          EmitLine(Format('  %s =l alloc4 %d', [SretBuf, RT.TotalSize()]));
        if RT.TotalSize() > 0 then
          EmitLine(Format('  call $memset(l %s, w 0, l %d)', [SretBuf, RT.TotalSize()]));
        EmitRecordCallSret(AExpr, SretBuf);
        Exit(SretBuf);
      end;
      if FC.IsImplicitSelfMethod then
      begin
        ArgTemp := AllocTemp();
        EmitLine(Format('  %s =l loadl %%_var_Self', [ArgTemp]));
        ArgLine  := Format('l %s', [ArgTemp]);
        FuncName := '$' + MethodEmitName(MDecl, MDecl.OwnerTypeName, FC.Name);
        ArgTemps := TStringList.Create();
        try
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
                ArgTemp2 := AllocTemp();
                EmitLine(Format('  %s =l loadl %%_var_%s_high',
                  [ArgTemp2, TIdentExpr(TASTExpr(FC.Args.Items[I])).Name]));
                ArgLine := ArgLine + Format(', l %s, l %s', [ArgTemp, ArgTemp2]);
              end;
            end
            else if Par.IsVarParam then
              ArgLine := ArgLine + Format(', l %s',
                [EmitLValueAddr(TASTExpr(FC.Args.Items[I]))])
            else if (Par.ResolvedType <> nil) and
                    (Par.ResolvedType.Kind = tyInterface) then
            begin
              EmitInterfaceExprPair(TASTExpr(FC.Args.Items[I]),
                ArgTemp, ArgTemp2);
              ArgLine := ArgLine + Format(', l %s, l %s', [ArgTemp, ArgTemp2]);
            end
            else
            begin
              ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[I]));
              while ArgTemps.Count < I do ArgTemps.Add('');
              ArgTemps.Add(ArgTemp);
              EnsureConstStringRef(ArgTemp, Par);
              ArgTemp := CoerceArg(ArgTemp, TASTExpr(FC.Args.Items[I]), QbeTypeOf(Par.ResolvedType));
              ArgLine := ArgLine + Format(', %s %s',
                [QbeParamTypeOf(Par.ResolvedType), ArgTemp]);
            end;
          end;
          T := AllocTemp();
          EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FuncName, ArgLine]));
          ReleaseConstStringArgs(FC.Args, ArgTemps, MDecl.Params);
          Exit(MaybeNormalizeExtReturn(T, MDecl));
        finally
          ArgTemps.Free();
        end;
      end;
      if MDecl.IsExternal and (MDecl.ExternalName <> '') then
        FuncName := '$' + MDecl.ExternalName
      else if MDecl.ResolvedQbeName <> '' then
        FuncName := '$' + QBEMangle(MDecl.ResolvedQbeName)
      else
        FuncName := '$' + QBEMangle(FC.Name);
      ArgLine  := '';
      ArgTemps := TStringList.Create();
      try
        for I := 0 to FC.Args.Count - 1 do
        begin
          Par := TMethodParam(MDecl.Params.Items[I]);
          if ArgLine <> '' then ArgLine := ArgLine + ', ';
          if Par.IsOpenArray then
          begin
            ArgTemps.Add('');
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
              ArgTemp2 := AllocTemp();
              EmitLine(Format('  %s =l loadl %%_var_%s_high',
                [ArgTemp2, TIdentExpr(TASTExpr(FC.Args.Items[I])).Name]));
              ArgLine := ArgLine + Format('l %s, l %s', [ArgTemp, ArgTemp2]);
            end;
          end
          else if Par.IsVarParam then
          begin
            ArgTemps.Add('');
            ArgLine := ArgLine + Format('l %s',
              [EmitLValueAddr(TASTExpr(FC.Args.Items[I]))]);
          end
          else if (Par.ResolvedType <> nil) and
                  (Par.ResolvedType.Kind = tyInterface) then
          begin
            ArgTemps.Add('');
            EmitInterfaceExprPair(TASTExpr(FC.Args.Items[I]),
              ArgTemp, ArgTemp2);
            ArgLine := ArgLine + Format('l %s, l %s', [ArgTemp, ArgTemp2]);
          end
          else
          begin
            ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[I]));
            ArgTemps.Add(ArgTemp);
            EnsureConstStringRef(ArgTemp, Par);
            ArgTemp := CoerceArg(ArgTemp, TASTExpr(FC.Args.Items[I]), QbeTypeOf(Par.ResolvedType));
            ArgLine := ArgLine + Format('%s %s', [QbeParamTypeOf(Par.ResolvedType), ArgTemp]);
          end;
        end;
        T := AllocTemp();
        EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FuncName, ArgLine]));
        EmitOwnedArgReleases(FC.Args, ArgTemps, MDecl.Params);
        ReleaseConstStringArgs(FC.Args, ArgTemps, MDecl.Params);
        Result := MaybeNormalizeExtReturn(T, MDecl);
      finally
        ArgTemps.Free();
      end;
    Exit;
  end;

  if AExpr is TMethodCallExpr then
  begin
    MCallExpr := TMethodCallExpr(AExpr);

    { Procedure-type field call expression: load (Code, Data) pair and
      dispatch indirectly. Only applies to function-of-object fields that
      return a value (otherwise they go through TMethodCallStmt). }
    if MCallExpr.IsProcFieldCall then
    begin
      PT := TProceduralTypeDesc(MCallExpr.ResolvedProcType);
      if MCallExpr.ObjExpr <> nil then
        SelfTemp := EmitExpr(MCallExpr.ObjExpr)
      else if MCallExpr.IsVarParam then
      begin
        FPtrTemp := AllocTemp();
        SelfTemp := AllocTemp();
        EmitLine(Format('  %s =l loadl %%_var_%s', [FPtrTemp, MCallExpr.ObjectName]));
        EmitLine(Format('  %s =l loadl %s', [SelfTemp, FPtrTemp]));
      end
      else
      begin
        SelfTemp := AllocTemp();
        EmitLine(Format('  %s =l loadl %s',
          [SelfTemp, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)]));
      end;
      if MCallExpr.ProcFieldInfo.Offset > 0 then
      begin
        SlotAddr := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d',
          [SlotAddr, SelfTemp, MCallExpr.ProcFieldInfo.Offset]));
      end
      else
        SlotAddr := SelfTemp;
      FPtrTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [FPtrTemp, SlotAddr]));
      if PT.IsMethodPtr then
      begin
        ArgTemp := AllocTemp();
        EmitLine(Format('  %s =l add %s, 8', [ArgTemp, SlotAddr]));
        DataTemp := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [DataTemp, ArgTemp]));
        ArgLine := Format('l %s', [DataTemp]);
      end
      else
        ArgLine := '';
      for I := 0 to MCallExpr.Args.Count - 1 do
      begin
        if ArgLine <> '' then ArgLine := ArgLine + ', ';
        ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Items[I]));
        QType   := QbeTypeOf(TProcParamInfo(PT.Params.Items[I]).TypeDesc);
        ArgTemp := CoerceArg(ArgTemp, TASTExpr(MCallExpr.Args.Items[I]), QType);
        ArgLine := ArgLine + Format('%s %s',
          [QbeParamTypeOf(TProcParamInfo(PT.Params.Items[I]).TypeDesc), ArgTemp]);
      end;
      T := AllocTemp();
      EmitLine(Format('  %s =l call %s(%s)', [T, FPtrTemp, ArgLine]));
      Exit(T);
    end;

    { Interface method call expression: dispatch through itab }
    if (MCallExpr.ResolvedClassType <> nil) and
       (MCallExpr.ResolvedClassType.Kind = tyInterface) then
    begin
      IntfDesc := TInterfaceTypeDesc(MCallExpr.ResolvedClassType);
      if MCallExpr.ObjExpr <> nil then
        { Receiver is an expression (record/class field, as-cast, implicit
          Self field) — resolve its fat pointer rather than the split
          _obj/_itab slots that only a named interface local/global has. }
        EmitInterfaceExprPair(MCallExpr.ObjExpr, SelfTemp, VTblTemp)
      else
      begin
        SelfTemp := AllocTemp();
        EmitLine(Format('  %s =l loadl %s_obj',
          [SelfTemp, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)]));
        VTblTemp := AllocTemp();
        EmitLine(Format('  %s =l loadl %s_itab',
          [VTblTemp, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)]));
      end;
      SlotOff := IntfDesc.MethodIndex(MCallExpr.Name) * 8;
      FPtrTemp := AllocTemp();
      if SlotOff = 0 then
        EmitLine(Format('  %s =l loadl %s', [FPtrTemp, VTblTemp]))
      else
      begin
        ArgTemp := AllocTemp();
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
      T := AllocTemp();
      EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FPtrTemp, ArgLine]));
      Exit(T);
    end;

    RT := TRecordTypeDesc(MCallExpr.ResolvedClassType);

    { Constructor call with args: TypeName.Create(args) }
    if MCallExpr.IsConstructorCall then
    begin
      SelfTemp := AllocTemp();
      EmitLine(Format('  %s =l call $_ClassAlloc(l %d, l $_FieldCleanup_%s)',
        [SelfTemp, RT.TotalSize(), ClassSymName(QBEMangle(RT.Name))]));
      if RT.HasVTable() then
        EmitLine(Format('  storel $vtable_%s, %s',
          [ClassSymName(QBEMangle(RT.Name)), SelfTemp]));
      { No _ClassAddRef here — the assignment site (EmitAssignment) is
        responsible for the retain on the receiving slot.  Adding it here
        as well produces a double-AddRef that prevents the object from
        ever reaching refcount zero. }
      if FDebugMode then
      begin
        L := AllocTemp();
        EmitLine(Format('  %s =l add $typeinfo_%s, 16',
          [L, ClassSymName(QBEMangle(RT.Name))]));
        R := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [R, L]));
        EmitLine(Format('  call $_LeakTrackerRegister(l %s, l %s)', [SelfTemp, R]));
      end;
      { If there's a user-defined Create method, call it }
      if MCallExpr.ResolvedMethod <> nil then
      begin
        MDecl   := TMethodDecl(MCallExpr.ResolvedMethod);
        ArgLine := Format('l %s', [SelfTemp]);
        ArgTemps := TStringList.Create();
        try
          for I := 0 to MCallExpr.Args.Count - 1 do
          begin
            Par := TMethodParam(MDecl.Params.Items[I]);
            if Par.IsVarParam then
            begin
              ArgTemps.Add('');
              ArgLine := ArgLine + Format(', l %s',
                [EmitLValueAddr(TASTExpr(MCallExpr.Args.Items[I]))]);
            end
            else if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyInterface) then
            begin
              ArgTemps.Add('');
              { Class expression passed to an interface param: emit obj and
                look up the static itab using the known target interface name. }
              if TASTExpr(MCallExpr.Args.Items[I]).ResolvedType.Kind = tyClass then
              begin
                ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Items[I]));
                ItabName := '$itab_' +
                  ClassSymName(QBEMangle(TASTExpr(MCallExpr.Args.Items[I]).ResolvedType.Name))
                  + '_' + QBEMangle(Par.ResolvedType.Name);
                ArgLine := ArgLine + Format(', l %s, l %s', [ArgTemp, ItabName]);
              end
              else
                ArgLine := ArgLine + InterfaceArgFragment(TASTExpr(MCallExpr.Args.Items[I]));
            end
            else
            begin
              ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Items[I]));
              if Par.IsVarParam then ArgTemps.Add('') else ArgTemps.Add(ArgTemp);
              EnsureConstStringRef(ArgTemp, Par);
              ArgTemp := CoerceArg(ArgTemp, TASTExpr(MCallExpr.Args.Items[I]),
                QbeTypeOf(Par.ResolvedType));
              ArgLine := ArgLine + Format(', %s %s',
                [QbeParamTypeOf(Par.ResolvedType), ArgTemp]);
            end;
          end;
          if MDecl.OwnerTypeName <> '' then
            FuncName := '$' + MethodEmitName(MDecl, MDecl.OwnerTypeName, MCallExpr.Name)
          else
            FuncName := '$' + MethodEmitName(MDecl, RT.Name, MCallExpr.Name);
          EmitLine(Format('  call %s(%s)', [FuncName, ArgLine]));
          EmitOwnedArgReleases(MCallExpr.Args, ArgTemps, MDecl.Params);
          ReleaseConstStringArgs(MCallExpr.Args, ArgTemps, MDecl.Params);
        finally
          ArgTemps.Free();
        end;
      end;
      Exit(SelfTemp);
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
        FPtrTemp := AllocTemp();
        SelfTemp := AllocTemp();
        EmitLine(Format('  %s =l loadl %%_var_%s', [FPtrTemp, MCallExpr.ObjectName]));
        EmitLine(Format('  %s =l loadl %s', [SelfTemp, FPtrTemp]));
      end
      else
      begin
        SelfTemp := AllocTemp();
        EmitLine(Format('  %s =l loadl %s',
          [SelfTemp, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)]));
      end;
      { For a class instance receiver, load typeinfo from vtable[0] }
      if (MCallExpr.ResolvedClassType <> nil) and
         (MCallExpr.ResolvedClassType.Kind = tyClass) then
      begin
        VTblTemp := AllocTemp();
        Ptr      := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [VTblTemp, SelfTemp]));
        EmitLine(Format('  %s =l loadl %s', [Ptr, VTblTemp]));
        SelfTemp := Ptr;
      end;
      { Evaluate the argument — a class ref or Pointer variable }
      ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Items[0]));
      T := AllocTemp();
      EmitLine(Format('  %s =w call $_InheritsFrom(l %s, l %s)',
        [T, SelfTemp, ArgTemp]));
      Exit(T);
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
        FPtrTemp := AllocTemp();
        SelfTemp := AllocTemp();
        EmitLine(Format('  %s =l loadl %%_var_%s', [FPtrTemp, MCallExpr.ObjectName]));
        EmitLine(Format('  %s =l loadl %s', [SelfTemp, FPtrTemp]));
      end
      else
      begin
        SelfTemp := AllocTemp();
        EmitLine(Format('  %s =l loadl %s',
          [SelfTemp, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)]));
      end;
      VTblTemp := AllocTemp();
      FPtrTemp := AllocTemp();
      ArgTemp  := AllocTemp();
      T        := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [VTblTemp, SelfTemp]));
      EmitLine(Format('  %s =l add %s, 16', [ArgTemp, VTblTemp]));
      EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
      EmitLine(Format('  %s =l call %s(l %s)', [T, FPtrTemp, SelfTemp]));
      Exit(T);
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
      SretBuf := AllocTemp();
      if RT.MaxAlign() >= 8 then
        EmitLine(Format('  %s =l alloc8 %d', [SretBuf, RT.TotalSize()]))
      else
        EmitLine(Format('  %s =l alloc4 %d', [SretBuf, RT.TotalSize()]));
      if RT.TotalSize() > 0 then
        EmitLine(Format('  call $memset(l %s, w 0, l %d)', [SretBuf, RT.TotalSize()]));
      EmitRecordCallSret(AExpr, SretBuf);
      Exit(SretBuf);
    end;

    { Load the object pointer (Self): either from a named variable or from
      evaluating the receiver expression (e.g. a typecast). }
    if MCallExpr.ObjExpr <> nil then
      SelfTemp := EmitExpr(MCallExpr.ObjExpr)
    else if MDecl.IsRecordMethod and MCallExpr.IsVarParam then
    begin
      { Record var-param receiver — slot holds the record address; load once. }
      SelfTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s', [SelfTemp, MCallExpr.ObjectName]));
    end
    else if MDecl.IsRecordMethod then
      { Regular record variable: VarRef IS the record address — pass directly. }
      SelfTemp := VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)
    else if MCallExpr.IsVarParam then
    begin
      { Var/out param of class type: local slot holds caller's address — dereference twice }
      SelfTemp := AllocTemp();
      FPtrTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s', [FPtrTemp, MCallExpr.ObjectName]));
      EmitLine(Format('  %s =l loadl %s', [SelfTemp, FPtrTemp]));
    end
    else
    begin
      SelfTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [SelfTemp, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)]));
    end;

    { Build argument string }
    ArgLine := Format('l %s', [SelfTemp]);
    ArgTemps := TStringList.Create();
    for I := 0 to MCallExpr.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Items[I]);
      if Par.IsVarParam then
      begin
        ArgTemps.Add('');
        ArgLine := ArgLine + Format(', l %s',
          [EmitLValueAddr(TASTExpr(MCallExpr.Args.Items[I]))]);
      end
      else if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyInterface) then
      begin
        ArgTemps.Add('');
        ArgLine := ArgLine + InterfaceArgFragment(TASTExpr(MCallExpr.Args.Items[I]));
      end
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Items[I]));
        ArgTemps.Add(ArgTemp);
        EnsureConstStringRef(ArgTemp, Par);
        ArgTemp := CoerceArg(ArgTemp, TASTExpr(MCallExpr.Args.Items[I]),
          QbeTypeOf(Par.ResolvedType));
        ArgLine := ArgLine + Format(', %s %s', [QbeParamTypeOf(Par.ResolvedType), ArgTemp]);
      end;
    end;

    T := AllocTemp();
    if MDecl.VTableSlot >= 0 then
    begin
      { Virtual dispatch: load vptr then function pointer from vtable }
      VTblTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [VTblTemp, SelfTemp]));
      FPtrTemp := AllocTemp();
      SlotOff  := (MDecl.VTableSlot + 1) * 8;
      ArgTemp  := AllocTemp();
      EmitLine(Format('  %s =l add %s, %d', [ArgTemp, VTblTemp, SlotOff]));
      EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
      EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FPtrTemp, ArgLine]));
    end
    else
      EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FuncName, ArgLine]));
    EmitOwnedArgReleases(MCallExpr.Args, ArgTemps, MDecl.Params);
    ReleaseConstStringArgs(MCallExpr.Args, ArgTemps, MDecl.Params);
    ArgTemps.Free();
    { Receiver was a +1-owned temporary (function/property return) used as
      the call target — release it so the temporary does not leak.  The
      method's return value (T) is independent and already owns its own ref. }
    if (MCallExpr.ObjExpr <> nil) and ExprOwnsRef(MCallExpr.ObjExpr) then
      EmitLine(Format('  call $_ClassRelease(l %s)', [SelfTemp]));
    Exit(T);
  end;

  if AExpr is TNilLiteral then
  begin
    T := AllocTemp();
    EmitLine(Format('  %s =l copy 0', [T]));
    Exit(T);
  end;

  if AExpr is TIndirectFuncCallExpr then
  begin
    { Call through an expression of procedural type: Expr(args).
      EmitExpr on the callee yields the function pointer value directly
      (e.g. from an array element load).  Use it as the call target without
      an additional loadl.  For method pointers the value is the address of
      the 16-byte (Code, Data) block, so load both halves from it. }
    T := EmitExpr(TIndirectFuncCallExpr(AExpr).CalleeExpr);
    if TProceduralTypeDesc(TIndirectFuncCallExpr(AExpr).ResolvedProcType).IsMethodPtr then
    begin
      FPtrTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [FPtrTemp, T]));
      ArgTemp2 := AllocTemp();
      EmitLine(Format('  %s =l add %s, 8', [ArgTemp2, T]));
      ArgTemp  := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [ArgTemp, ArgTemp2]));
      ArgLine  := Format('l %s', [ArgTemp]);
    end
    else
    begin
      FPtrTemp := T;  { already the function pointer value }
      ArgLine  := '';
    end;
    for I := 0 to TIndirectFuncCallExpr(AExpr).Args.Count - 1 do
    begin
      if ArgLine <> '' then ArgLine := ArgLine + ', ';
      ArgTemp := EmitExpr(TASTExpr(TIndirectFuncCallExpr(AExpr).Args.Items[I]));
      ArgLine := ArgLine + Format('%s %s',
        [QbeTypeOf(TProcParamInfo(
           TProceduralTypeDesc(TIndirectFuncCallExpr(AExpr).ResolvedProcType).Params.Items[I]
         ).TypeDesc), ArgTemp]);
    end;
    if TProceduralTypeDesc(TIndirectFuncCallExpr(AExpr).ResolvedProcType).ReturnType <> nil then
      QType := QbeTypeOf(TProceduralTypeDesc(TIndirectFuncCallExpr(AExpr).ResolvedProcType).ReturnType)
    else
      QType := 'w';
    T := AllocTemp();
    EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FPtrTemp, ArgLine]));
    Result := T;
  end
  else if AExpr is TIntLiteral then
  begin
    T := AllocTemp();
    if TIntLiteral(AExpr).IsUInt64 or
       (TIntLiteral(AExpr).Value < -2147483648) or
       (TIntLiteral(AExpr).Value > 2147483647) then
      EmitLine(Format('  %s =l copy %s', [T, IntToStr(TIntLiteral(AExpr).Value)]))
    else
      EmitLine(Format('  %s =w copy %s', [T, IntToStr(TIntLiteral(AExpr).Value)]));
    Result := T;
  end
  else if AExpr is TFloatLiteral then
  begin
    T := AllocTemp();
    { QBE float literal syntax: d_3.14 for double, s_3.14 for single.
      The type is always Double for unadorned float literals. }
    EmitLine(Format('  %s =d copy d_%s', [T, TFloatLiteral(AExpr).Value]));
    Result := T;
  end
  else if AExpr is TStringLiteral then
  begin
    if TStringLiteral(AExpr).IsCharCoerce then
    begin
      T := AllocTemp();
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
          T := AllocTemp();
          EmitLine(Format('  %s =l loadl %s',
            [T, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
          L := T;
        end;
      { Step 2: load vtable pointer from instance[0] }
      T := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [T, L]));
      { Step 3: load typeinfo from vtable[0] }
      Ptr := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [Ptr, T]));
      { Step 4: load nameptr from typeinfo[16] (third slot) }
      T := AllocTemp();
      EmitLine(Format('  %s =l add %s, 16', [T, Ptr]));
      Ptr := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [Ptr, T]));
      Exit(Ptr);
    end;

    { Built-in: Obj.ClassType — returns the typeinfo pointer (the value
      stored at vtable[0]).  Two indirections: instance → vtable → typeinfo. }
    if FldAccess.IsClassTypeAccess then
    begin
      if FldAccess.Base <> nil then
        L := EmitExpr(FldAccess.Base)
      else
      begin
        T := AllocTemp();
        EmitLine(Format('  %s =l loadl %s',
          [T, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
        L := T;
      end;
      { vtable pointer at instance[0] }
      T := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [T, L]));
      { typeinfo pointer at vtable[0] }
      Ptr := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [Ptr, T]));
      Exit(Ptr);
    end;

    { Built-in: Obj.ToString — virtual dispatch via vtable slot 1.
      vtable[0]=typeinfo, vtable[1]=Destroy, vtable[2]=ToString → offset 16. }
    if FldAccess.IsBuiltinToString then
    begin
      if FldAccess.Base <> nil then
        L := EmitExpr(FldAccess.Base)
      else
      begin
        T := AllocTemp();
        EmitLine(Format('  %s =l loadl %s',
          [T, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
        L := T;
      end;
      VTblTemp := AllocTemp();
      FPtrTemp := AllocTemp();
      ArgTemp  := AllocTemp();
      T        := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [VTblTemp, L]));
      EmitLine(Format('  %s =l add %s, 16', [ArgTemp, VTblTemp]));
      EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
      EmitLine(Format('  %s =l call %s(l %s)', [T, FPtrTemp, L]));
      Exit(T);
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
          SretBuf := AllocTemp();
          if RT.MaxAlign() >= 8 then
            EmitLine(Format('  %s =l alloc8 %d', [SretBuf, RT.TotalSize()]))
          else
            EmitLine(Format('  %s =l alloc4 %d', [SretBuf, RT.TotalSize()]));
          if RT.TotalSize() > 0 then
            EmitLine(Format('  call $memset(l %s, w 0, l %d)', [SretBuf, RT.TotalSize()]));
          EmitLine(Format('  call $%s(l %s, l %s)',
            [MethodEmitName(MDecl, MDecl.OwnerTypeName, FldAccess.FieldName),
             SretBuf, L]));
          Result := SretBuf;
        end
        else
        begin
          QType := QbeTypeOf(MDecl.ResolvedReturnType);
          T := AllocTemp();
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
          Ptr := AllocTemp();
          if FldAccess.FieldInfo.Offset > 0 then
            EmitLine(Format('  %s =l add %s, %d', [Ptr, L, FldAccess.FieldInfo.Offset]))
          else
            Ptr := L;
          L := AllocTemp();
          EmitLine(Format('  %s =l loadl %s', [L, Ptr]));
        end;
        QType := QbeTypeOf(FldAccess.PropRead.TypeDesc);
        T := AllocTemp();
        if FldAccess.PropIndexExpr <> nil then
        begin
          IdxTemp  := EmitExpr(FldAccess.PropIndexExpr);
          IdxQType := QbeTypeOf(FldAccess.PropRead.IndexTypeDesc);
          EmitLine(Format('  %s =%s call $%s%s_%s(l %s, %s %s)',
            [T, QType,
             ClassUnitPrefix(FldAccess.PropOwnerType),
             FldAccess.PropOwnerType, FldAccess.PropRead.ReadMethod,
             L, IdxQType, IdxTemp]));
        end
        else
          EmitLine(Format('  %s =%s call $%s%s_%s(l %s)',
            [T, QType,
             ClassUnitPrefix(FldAccess.PropOwnerType),
             FldAccess.PropOwnerType, FldAccess.PropRead.ReadMethod, L]));
        Exit(T);
      end;
      if FldAccess.FieldInfo = nil then
        raise ECodeGenError.Create(Format(
          'Chained field ''%s'' has no resolved field info', [FldAccess.FieldName]));
      if FldAccess.IsArrayAccess then
      begin
        if FldAccess.FieldInfo.Offset > 0 then
        begin
          Ptr := AllocTemp();
          EmitLine(Format('  %s =l add %s, %d', [Ptr, L, FldAccess.FieldInfo.Offset]));
          L := Ptr;
        end;
        if FldAccess.FieldInfo.TypeDesc.Kind = tyDynArray then
        begin
          ElemSize := TDynArrayTypeDesc(FldAccess.FieldInfo.TypeDesc).ElementType.RawSize();
          Ptr := AllocTemp();
          EmitLine(Format('  %s =l loadl %s', [Ptr, L]));
          IdxTemp := EmitExpr(FldAccess.PropIndexExpr);
          T := AllocTemp();
          EmitLine(Format('  %s =l extsw %s', [T, IdxTemp]));
          L := AllocTemp();
          EmitLine(Format('  %s =l mul %s, %d', [L, T, ElemSize]));
          T := AllocTemp();
          EmitLine(Format('  %s =l add %s, %s', [T, Ptr, L]));
          if TDynArrayTypeDesc(FldAccess.FieldInfo.TypeDesc).ElementType.Kind = tyRecord then
            Exit(T);
          QType := QbeTypeOf(TDynArrayTypeDesc(FldAccess.FieldInfo.TypeDesc).ElementType);
          LoadInstr := LoadInstrFor(TDynArrayTypeDesc(FldAccess.FieldInfo.TypeDesc).ElementType);
          L := AllocTemp();
          EmitLine(Format('  %s =%s %s %s', [L, QType, LoadInstr, T]));
          Exit(L);
        end
        else if FldAccess.FieldInfo.TypeDesc.Kind = tyStaticArray then
        begin
          SAT := TStaticArrayTypeDesc(FldAccess.FieldInfo.TypeDesc);
          ElemSize := SAT.ElementType.RawSize();
          IdxTemp := EmitExpr(FldAccess.PropIndexExpr);
          T := AllocTemp();
          EmitLine(Format('  %s =l extsw %s', [T, IdxTemp]));
          if SAT.LowBound <> 0 then
          begin
            Ptr := AllocTemp();
            EmitLine(Format('  %s =l sub %s, %d', [Ptr, T, SAT.LowBound]));
            T := Ptr;
          end;
          Ptr := AllocTemp();
          EmitLine(Format('  %s =l mul %s, %d', [Ptr, T, ElemSize]));
          T := AllocTemp();
          EmitLine(Format('  %s =l add %s, %s', [T, L, Ptr]));
          if SAT.ElementType.Kind = tyRecord then
            Exit(T);
          QType := QbeTypeOf(SAT.ElementType);
          LoadInstr := LoadInstrFor(SAT.ElementType);
          L := AllocTemp();
          EmitLine(Format('  %s =%s %s %s', [L, QType, LoadInstr, T]));
          Exit(L);
        end;
      end;
      if FldAccess.FieldInfo.Offset > 0 then
      begin
        Ptr := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d',
          [Ptr, L, FldAccess.FieldInfo.Offset]));
      end
      else
        Ptr := L;
      if FldAccess.FieldInfo.TypeDesc.Kind in [tyRecord, tyStaticArray] then
        Exit(Ptr);
      QType     := QbeTypeOf(FldAccess.FieldInfo.TypeDesc);
      LoadInstr := LoadInstrFor(FldAccess.FieldInfo.TypeDesc);
      T         := AllocTemp();
      EmitLine(Format('  %s =%s %s %s', [T, QType, LoadInstr, Ptr]));
      Exit(T);
    end;
    if FldAccess.IsImplicitSelf then
    begin
      { Implicit Self.Base.Field — Base is a field of Self }
      L := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_Self', [L]));
      if FldAccess.ImplicitBaseInfo.Offset > 0 then
      begin
        Ptr := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d',
          [Ptr, L, FldAccess.ImplicitBaseInfo.Offset]));
        L := Ptr;
      end;
      if FldAccess.IsClassAccess then
      begin
        Ptr := AllocTemp();
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
          SretBuf := AllocTemp();
          if RT.MaxAlign() >= 8 then
            EmitLine(Format('  %s =l alloc8 %d', [SretBuf, RT.TotalSize()]))
          else
            EmitLine(Format('  %s =l alloc4 %d', [SretBuf, RT.TotalSize()]));
          if RT.TotalSize() > 0 then
            EmitLine(Format('  call $memset(l %s, w 0, l %d)', [SretBuf, RT.TotalSize()]));
          EmitLine(Format('  call $%s(l %s, l %s)',
            [MethodEmitName(MDecl, MDecl.OwnerTypeName, FldAccess.FieldName),
             SretBuf, L]));
          Result := SretBuf;
        end
        else
        begin
          QType := QbeTypeOf(MDecl.ResolvedReturnType);
          T := AllocTemp();
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
        T     := AllocTemp();
        QType := QbeTypeOf(FldAccess.PropRead.TypeDesc);
        if FldAccess.PropIndexExpr <> nil then
        begin
          IdxTemp  := EmitExpr(FldAccess.PropIndexExpr);
          IdxQType := QbeTypeOf(FldAccess.PropRead.IndexTypeDesc);
          EmitLine(Format('  %s =%s call $%s%s_%s(l %s, %s %s)',
            [T, QType,
             ClassUnitPrefix(FldAccess.PropOwnerType),
             QBEMangle(FldAccess.PropOwnerType),
             FldAccess.PropRead.ReadMethod, L, IdxQType, IdxTemp]));
        end
        else
          EmitLine(Format('  %s =%s call $%s%s_%s(l %s)',
            [T, QType,
             ClassUnitPrefix(FldAccess.PropOwnerType),
             QBEMangle(FldAccess.PropOwnerType),
             FldAccess.PropRead.ReadMethod, L]));
        Exit(T);
      end;
      if FldAccess.FieldInfo.Offset > 0 then
      begin
        Ptr := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d',
          [Ptr, L, FldAccess.FieldInfo.Offset]));
      end
      else
        Ptr := L;
      { Method-ptr field: 16-byte inline TMethod.  Return the field address so
        callers (memcpy, call-site) treat the field's storage as the value. }
      if (FldAccess.FieldInfo.TypeDesc.Kind = tyProcedural) and
         TProceduralTypeDesc(FldAccess.FieldInfo.TypeDesc).IsMethodPtr then
      begin
        Exit(Ptr);
      end;
      if FldAccess.FieldInfo.TypeDesc.Kind in [tyRecord, tyStaticArray] then
        Exit(Ptr);
      QType     := QbeTypeOf(FldAccess.FieldInfo.TypeDesc);
      LoadInstr := LoadInstrFor(FldAccess.FieldInfo.TypeDesc);
      T         := AllocTemp();
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
        SretBuf := AllocTemp();
        if RT.MaxAlign() >= 8 then
          EmitLine(Format('  %s =l alloc8 %d', [SretBuf, RT.TotalSize()]))
        else
          EmitLine(Format('  %s =l alloc4 %d', [SretBuf, RT.TotalSize()]));
        if RT.TotalSize() > 0 then
          EmitLine(Format('  call $memset(l %s, w 0, l %d)', [SretBuf, RT.TotalSize()]));
        EmitRecordCallSret(AExpr, SretBuf);
        Result := SretBuf;
      end
      else
      begin
        { For class variables, load the object pointer from the variable.
          For record var-params (Self inside a record method), dereference
          the pointer slot to get the actual record address.
          For regular record variables, the variable address IS the record. }
        if MDecl.IsRecordMethod and FldAccess.IsVarParam then
        begin
          L := AllocTemp();
          EmitLine(Format('  %s =l loadl %s',
            [L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
        end
        else if MDecl.IsRecordMethod then
          L := VarRef(FldAccess.RecordName, FldAccess.IsGlobal)
        else
        begin
          L := AllocTemp();
          EmitLine(Format('  %s =l loadl %s',
            [L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
        end;
        QType := QbeTypeOf(MDecl.ResolvedReturnType);
        T := AllocTemp();
        if MDecl.VTableSlot >= 0 then
        begin
          { Virtual dispatch: load vptr, then load function pointer from
            vtable[(VTableSlot+1)*8] (slot 0 is reserved for typeinfo). }
          VTblTemp := AllocTemp();
          FPtrTemp := AllocTemp();
          SlotOff  := (MDecl.VTableSlot + 1) * 8;
          ArgTemp  := AllocTemp();
          EmitLine(Format('  %s =l loadl %s', [VTblTemp, L]));
          EmitLine(Format('  %s =l add %s, %d', [ArgTemp, VTblTemp, SlotOff]));
          EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
          EmitLine(Format('  %s =%s call %s(l %s)', [T, QType, FPtrTemp, L]));
        end
        else
          EmitLine(Format('  %s =%s call $%s(l %s)',
            [T, QType, MethodEmitName(MDecl, MDecl.OwnerTypeName, FldAccess.FieldName), L]));
        Result := T;
      end;
    end
    else if FldAccess.IsInterfaceCall then
    begin
      { Zero-arg method call through interface itab: M.GetCount where M: IFoo }
      IntfDesc := TInterfaceTypeDesc(FldAccess.ResolvedClassType);
      SelfTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s_obj',
        [SelfTemp, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
      VTblTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s_itab',
        [VTblTemp, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
      SlotOff  := IntfDesc.MethodIndex(FldAccess.FieldName) * 8;
      FPtrTemp := AllocTemp();
      if SlotOff = 0 then
        EmitLine(Format('  %s =l loadl %s', [FPtrTemp, VTblTemp]))
      else
      begin
        ArgTemp := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d', [ArgTemp, VTblTemp, SlotOff]));
        EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
      end;
      QType := QbeTypeOf(FldAccess.ResolvedType);
      T := AllocTemp();
      EmitLine(Format('  %s =%s call %s(l %s)', [T, QType, FPtrTemp, SelfTemp]));
      Result := T;
    end
    else if FldAccess.IsConstant then
    begin
      if FldAccess.ConstArraySymbol <> '' then
      begin
        if FldAccess.PropIndexExpr <> nil then
        begin
          SAT      := TStaticArrayTypeDesc(FldAccess.ConstArrayType);
          ElemSize := SAT.ElementType.RawSize();
          IdxTemp  := EmitExpr(FldAccess.PropIndexExpr);
          L        := AllocTemp();
          EmitLine(Format('  %s =l extsw %s', [L, IdxTemp]));
          if SAT.LowBound <> 0 then
          begin
            Ptr := AllocTemp();
            EmitLine(Format('  %s =l sub %s, %d', [Ptr, L, SAT.LowBound]));
            L := Ptr;
          end;
          Ptr := AllocTemp();
          EmitLine(Format('  %s =l mul %s, %d', [Ptr, L, ElemSize]));
          L := AllocTemp();
          EmitLine(Format('  %s =l add $%s, %s', [L, FldAccess.ConstArraySymbol, Ptr]));
          QType := QbeTypeOf(SAT.ElementType);
          T     := AllocTemp();
          LoadInstr := LoadInstrFor(SAT.ElementType);
          EmitLine(Format('  %s =%s %s %s', [T, QType, LoadInstr, L]));
          Exit(T);
        end;
        Exit('$' + FldAccess.ConstArraySymbol);
      end
      else if FldAccess.ResolvedType.Kind = tyString then
      begin
        T := AllocTemp();
        EmitLine(Format('  %s =l call $_StringRetain(l $%s)',
          [T, EmitStrLit(FldAccess.ConstString)]));
        Result := T;
      end
      else
      begin
        T := AllocTemp();
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
      T := AllocTemp();
      EmitLine(Format('  %s =l call $_ClassAlloc(l %d, l $_FieldCleanup_%s)',
        [T, TRecordTypeDesc(FldAccess.ResolvedType).TotalSize(),
         ClassSymName(QBEMangle(FldAccess.ResolvedType.Name))]));
      { Store vtable pointer at offset 0 if this class has virtual methods }
      if TRecordTypeDesc(FldAccess.ResolvedType).HasVTable() then
        EmitLine(Format('  storel $vtable_%s, %s',
          [ClassSymName(QBEMangle(FldAccess.ResolvedType.Name)), T]));
      if FDebugMode then
      begin
        { Load classname ptr from typeinfo[2] (offset +16) and register with leak tracker }
        L := AllocTemp();
        EmitLine(Format('  %s =l add $typeinfo_%s, 16',
          [L, ClassSymName(QBEMangle(FldAccess.ResolvedType.Name))]));
        R := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [R, L]));
        EmitLine(Format('  call $_LeakTrackerRegister(l %s, l %s)', [T, R]));
      end;
      { Call user-defined Create body if one exists }
      if FldAccess.ResolvedMethod <> nil then
      begin
        MDecl := TMethodDecl(FldAccess.ResolvedMethod);
        if MDecl.OwnerTypeName <> '' then
          FuncName := '$' + MethodEmitName(MDecl, MDecl.OwnerTypeName, FldAccess.FieldName)
        else
          FuncName := '$' + MethodEmitName(MDecl, QBEMangle(FldAccess.ResolvedType.Name), FldAccess.FieldName);
        EmitLine(Format('  call %s(l %s)', [FuncName, T]));
      end;
      Result := T;
    end
    else if FldAccess.IsCharAccess then
    begin
      { String field subscript: Rec.Field[N] (1-based) — load field, then read byte at N-1. }
      L := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
      if FldAccess.FieldInfo.Offset > 0 then
      begin
        Ptr := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d', [Ptr, L, FldAccess.FieldInfo.Offset]));
        L := Ptr;
      end;
      { Load the string pointer (the field value) }
      Ptr := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [Ptr, L]));
      { Compute 0-based byte offset: idx - 1 }
      T := EmitExpr(FldAccess.PropIndexExpr);
      IdxTemp := AllocTemp();
      EmitLine(Format('  %s =l extsw %s', [IdxTemp, T]));
      Ptr2    := AllocTemp();
      EmitLine(Format('  %s =l sub %s, 1', [Ptr2, IdxTemp]));
      IdxTemp := AllocTemp();
      EmitLine(Format('  %s =l add %s, %s', [IdxTemp, Ptr, Ptr2]));
      T := AllocTemp();
      EmitLine(Format('  %s =w loadub %s', [T, IdxTemp]));
      Result := T;
    end
    else if FldAccess.IsArrayAccess then
    begin
      { Array field subscript: Rec.Arr[I] — load array base, compute element addr. }
      L := AllocTemp();
      if FldAccess.IsVarParam then
      begin
        T := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [T, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
        L := T;
      end
      else
        EmitLine(Format('  %s =l copy %s', [L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
      if FldAccess.FieldInfo.Offset > 0 then
      begin
        Ptr := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d', [Ptr, L, FldAccess.FieldInfo.Offset]));
        L := Ptr;
      end;
      if FldAccess.FieldInfo.TypeDesc.Kind = tyDynArray then
      begin
        ElemSize := TDynArrayTypeDesc(FldAccess.FieldInfo.TypeDesc).ElementType.RawSize();
        Ptr := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [Ptr, L]));
        IdxTemp := EmitExpr(FldAccess.PropIndexExpr);
        T := AllocTemp();
        EmitLine(Format('  %s =l extsw %s', [T, IdxTemp]));
        L := AllocTemp();
        EmitLine(Format('  %s =l mul %s, %d', [L, T, ElemSize]));
        T := AllocTemp();
        EmitLine(Format('  %s =l add %s, %s', [T, Ptr, L]));
        if TDynArrayTypeDesc(FldAccess.FieldInfo.TypeDesc).ElementType.Kind = tyRecord then
          Exit(T);
        QType := QbeTypeOf(TDynArrayTypeDesc(FldAccess.FieldInfo.TypeDesc).ElementType);
        LoadInstr := LoadInstrFor(TDynArrayTypeDesc(FldAccess.FieldInfo.TypeDesc).ElementType);
        L := AllocTemp();
        EmitLine(Format('  %s =%s %s %s', [L, QType, LoadInstr, T]));
        Exit(L);
      end
      else if FldAccess.FieldInfo.TypeDesc.Kind = tyStaticArray then
      begin
        SAT := TStaticArrayTypeDesc(FldAccess.FieldInfo.TypeDesc);
        ElemSize := SAT.ElementType.RawSize();
        IdxTemp := EmitExpr(FldAccess.PropIndexExpr);
        T := AllocTemp();
        EmitLine(Format('  %s =l extsw %s', [T, IdxTemp]));
        if SAT.LowBound <> 0 then
        begin
          Ptr := AllocTemp();
          EmitLine(Format('  %s =l sub %s, %d', [Ptr, T, SAT.LowBound]));
          T := Ptr;
        end;
        Ptr := AllocTemp();
        EmitLine(Format('  %s =l mul %s, %d', [Ptr, T, ElemSize]));
        T := AllocTemp();
        EmitLine(Format('  %s =l add %s, %s', [T, L, Ptr]));
        if SAT.ElementType.Kind = tyRecord then
          Exit(T);
        QType := QbeTypeOf(SAT.ElementType);
        LoadInstr := LoadInstrFor(SAT.ElementType);
        L := AllocTemp();
        EmitLine(Format('  %s =%s %s %s', [L, QType, LoadInstr, T]));
        Exit(L);
      end
      else if FldAccess.FieldInfo.TypeDesc.Kind = tyOpenArray then
      begin
        ElemSize := TOpenArrayTypeDesc(FldAccess.FieldInfo.TypeDesc).ElementType.RawSize();
        Ptr := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [Ptr, L]));
        IdxTemp := EmitExpr(FldAccess.PropIndexExpr);
        T := AllocTemp();
        EmitLine(Format('  %s =l extsw %s', [T, IdxTemp]));
        L := AllocTemp();
        EmitLine(Format('  %s =l mul %s, %d', [L, T, ElemSize]));
        T := AllocTemp();
        EmitLine(Format('  %s =l add %s, %s', [T, Ptr, L]));
        if TOpenArrayTypeDesc(FldAccess.FieldInfo.TypeDesc).ElementType.Kind = tyRecord then
          Exit(T);
        QType := QbeTypeOf(TOpenArrayTypeDesc(FldAccess.FieldInfo.TypeDesc).ElementType);
        LoadInstr := LoadInstrFor(TOpenArrayTypeDesc(FldAccess.FieldInfo.TypeDesc).ElementType);
        L := AllocTemp();
        EmitLine(Format('  %s =%s %s %s', [L, QType, LoadInstr, T]));
        Exit(L);
      end;
    end
    else if FldAccess.PropRead <> nil then
    begin
      { Method-backed property read: load Self pointer and call getter.
        When FieldInfo is also non-nil, the getter is on a field of the record
        (e.g. Rec.Field[I]) — load the field first, then use that as Self. }
      L := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
      if FldAccess.FieldInfo <> nil then
      begin
        { Load the field value to get the actual object the getter is called on }
        Ptr := AllocTemp();
        if FldAccess.FieldInfo.Offset > 0 then
          EmitLine(Format('  %s =l add %s, %d', [Ptr, L, FldAccess.FieldInfo.Offset]))
        else
          Ptr := L;
        L := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [L, Ptr]));
      end;
      T     := AllocTemp();
      QType := QbeTypeOf(FldAccess.PropRead.TypeDesc);
      if FldAccess.PropIndexExpr <> nil then
      begin
        IdxTemp  := EmitExpr(FldAccess.PropIndexExpr);
        IdxQType := QbeTypeOf(FldAccess.PropRead.IndexTypeDesc);
        EmitLine(Format('  %s =%s call $%s%s_%s(l %s, %s %s)',
          [T, QType,
           ClassUnitPrefix(FldAccess.PropOwnerType),
           QBEMangle(FldAccess.PropOwnerType),
           FldAccess.PropRead.ReadMethod, L, IdxQType, IdxTemp]));
      end
      else
        EmitLine(Format('  %s =%s call $%s%s_%s(l %s)',
          [T, QType,
           ClassUnitPrefix(FldAccess.PropOwnerType),
           QBEMangle(FldAccess.PropOwnerType),
           FldAccess.PropRead.ReadMethod, L]));
      Result := T;
    end
    else if FldAccess.IsClassAccess then
    begin
      { Load heap pointer, then load field }
      L := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
      if FldAccess.FieldInfo.Offset > 0 then
      begin
        Ptr := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d', [Ptr, L, FldAccess.FieldInfo.Offset]));
      end
      else
        Ptr := L;
      { Method-ptr field: 16-byte inline TMethod — return field address. }
      if (FldAccess.FieldInfo.TypeDesc.Kind = tyProcedural) and
         TProceduralTypeDesc(FldAccess.FieldInfo.TypeDesc).IsMethodPtr then
      begin
        Exit(Ptr);
      end;
      QType     := QbeTypeOf(FldAccess.FieldInfo.TypeDesc);
      LoadInstr := LoadInstrFor(FldAccess.FieldInfo.TypeDesc);
      T         := AllocTemp();
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
        L := AllocTemp();
        EmitLine(Format('  %s =l loadl %s',
          [L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
        if FldAccess.FieldInfo.Offset > 0 then
        begin
          Ptr := AllocTemp();
          EmitLine(Format('  %s =l add %s, %d',
            [Ptr, L, FldAccess.FieldInfo.Offset]));
        end
        else
          Ptr := L;
      end
      else
        Ptr := FieldPtr(FldAccess.RecordName, FldAccess.FieldInfo.Offset, FldAccess.IsGlobal);
      { Method-ptr field: 16-byte inline TMethod — return field address. }
      if (FldAccess.FieldInfo.TypeDesc.Kind = tyProcedural) and
         TProceduralTypeDesc(FldAccess.FieldInfo.TypeDesc).IsMethodPtr then
      begin
        Exit(Ptr);
      end;
      if FldAccess.FieldInfo.TypeDesc.Kind in [tyRecord, tyStaticArray] then
        Exit(Ptr);
      QType     := QbeTypeOf(FldAccess.FieldInfo.TypeDesc);
      LoadInstr := LoadInstrFor(FldAccess.FieldInfo.TypeDesc);
      T         := AllocTemp();
      EmitLine(Format('  %s =%s %s %s', [T, QType, LoadInstr, Ptr]));
      Result := T;
    end;
  end
  else if AExpr is TIdentExpr then
  begin
    T := AllocTemp();

    { Inline frame: identifier may name a callee parameter (mapped to a
      caller-side temp) or the callee's Result variable.  We check this
      before any other ident handling because inlined bodies should not
      consult the surrounding caller's variable scope for these names. }
    if InsideInlineFrame() then
    begin
      if InlineParamTemp(TIdentExpr(AExpr).Name, ArgTemp) then
      begin
        QType := QbeTypeOf(AExpr.ResolvedType);
        EmitLine(Format('  %s =%s copy %s', [T, QType, ArgTemp]));
        Exit(T);
      end;
      if SameText(TIdentExpr(AExpr).Name, 'Result') then
      begin
        QType := InlineResultQType();
        case QType of
          'w': EmitLine(Format('  %s =w loadw %s', [T, InlineResultTemp()]));
          'l': EmitLine(Format('  %s =l loadl %s', [T, InlineResultTemp()]));
          'd': EmitLine(Format('  %s =d loadd %s', [T, InlineResultTemp()]));
          's': EmitLine(Format('  %s =s loads %s', [T, InlineResultTemp()]));
        else
          EmitLine(Format('  %s =l loadl %s', [T, InlineResultTemp()]));
        end;
        Exit(T);
      end;
    end;

    if TIdentExpr(AExpr).IsImplicitSelf then
    begin
      { Bare field name — equivalent to Self.FieldName: load Self, add offset }
      ImplFld := TFieldInfo(TIdentExpr(AExpr).ImplicitFieldInfo);
      SelfT   := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_Self', [SelfT]));
      { Record-typed field: return the field's storage address, not a loaded value }
      if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyRecord) then
      begin
        if ImplFld.Offset > 0 then
        begin
          PtrT := AllocTemp();
          EmitLine(Format('  %s =l add %s, %d', [PtrT, SelfT, ImplFld.Offset]));
          Result := PtrT;
        end
        else
          Result := SelfT;
        Exit;
      end;
      T := AllocTemp();
      QType := QbeTypeOf(AExpr.ResolvedType);
      if ImplFld.Offset > 0 then
      begin
        PtrT := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d', [PtrT, SelfT, ImplFld.Offset]));
        if QType = 'w' then
          EmitLine(Format('  %s =w %s %s', [T, LoadInstrFor(ImplFld.TypeDesc), PtrT]))
        else
          EmitLine(Format('  %s =l loadl %s', [T, PtrT]));
      end
      else
      begin
        if QType = 'w' then
          EmitLine(Format('  %s =w %s %s', [T, LoadInstrFor(ImplFld.TypeDesc), SelfT]))
        else
          EmitLine(Format('  %s =l loadl %s', [T, SelfT]));
      end;
      Exit(T);
    end;

    if TIdentExpr(AExpr).IsImplicitSelfMethod then
    begin
      { Bare zero-arg method call on Self — emit direct call }
      NoArgCall := TFuncCallExpr.Create();
      try
        NoArgCall.Name                 := TIdentExpr(AExpr).Name;
        NoArgCall.ResolvedType         := AExpr.ResolvedType;
        NoArgCall.ResolvedDecl         := TIdentExpr(AExpr).ImplicitMethodDecl;
        NoArgCall.IsImplicitSelfMethod := True;
        Result := EmitExpr(NoArgCall);
      finally
        NoArgCall.Free();
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
        [T, ClassSymName(QBEMangle(TIdentExpr(AExpr).Name))]));
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
    else if IsCaptured(TIdentExpr(AExpr).Name) then
    begin
      { Captured outer-scope variable: %_cap_Name IS the address of the var
        in the enclosing function's stack frame.  Load the value directly
        from that address (no extra pointer hop). }
      QType := QbeTypeOf(AExpr.ResolvedType);
      if (AExpr.ResolvedType <> nil) and
         (AExpr.ResolvedType.Kind in [tyRecord, tyStaticArray]) then
      begin
        { Aggregate: %_cap_Name is the storage address — return directly. }
        EmitLine(Format('  %s =l copy %%_cap_%s', [T, TIdentExpr(AExpr).Name]));
        Exit(T);
      end;
      case QType of
        'l': EmitLine(Format('  %s =l loadl %%_cap_%s', [T, TIdentExpr(AExpr).Name]));
        'd': EmitLine(Format('  %s =d loadd %%_cap_%s', [T, TIdentExpr(AExpr).Name]));
        's': EmitLine(Format('  %s =s loads %%_cap_%s', [T, TIdentExpr(AExpr).Name]));
      else
        EmitLine(Format('  %s =w loadw %%_cap_%s', [T, TIdentExpr(AExpr).Name]));
      end;
    end
    else if TIdentExpr(AExpr).IsVarParam and
            (AExpr.ResolvedType <> nil) and
            (AExpr.ResolvedType.Kind in [tyRecord, tyStaticArray]) then
    begin
      { Var param of aggregate type: the param slot already holds the address
        of the caller's storage — load and return that as the storage address. }
      EmitLine(Format('  %s =l loadl %%_var_%s', [T, TIdentExpr(AExpr).Name]));
      Exit(T);
    end
    else if TIdentExpr(AExpr).IsVarParam then
    begin
      { Var param of scalar type: load pointer, then dereference to get value }
      Ptr := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s', [Ptr, TIdentExpr(AExpr).Name]));
      QType := QbeTypeOf(AExpr.ResolvedType);
      if QType = 'l' then
        EmitLine(Format('  %s =l loadl %s', [T, Ptr]))
      else
        EmitLine(Format('  %s =w loadw %s', [T, Ptr]));
    end
    else if TIdentExpr(AExpr).ConstArraySymbol <> '' then
    begin
      { Array const referenced bare — its storage is a mangled global data
        label (not $Name, which would collide with RTL/other-scope symbols). }
      Exit('$' + TIdentExpr(AExpr).ConstArraySymbol);
    end
    else if (AExpr.ResolvedType <> nil) and
            (AExpr.ResolvedType.Kind in [tyRecord, tyStaticArray]) then
    begin
      { Aggregate variable — return its storage address directly (no load). }
      Exit(VarRef(TIdentExpr(AExpr).Name, TIdentExpr(AExpr).IsGlobal));
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
       (BinExpr.ResolvedType <> nil) and BinExpr.ResolvedType.IsNumeric() then
    begin
      L := EmitExpr(BinExpr.Left);
      R := EmitExpr(BinExpr.Right);
      T := AllocTemp();
      if BinExpr.ResolvedType.Kind in [tyInt64, tyUInt64] then
      begin
        { Extend w operands to l before the l-typed instruction.
          Sign-extend for tyInt64, zero-extend for tyUInt64. }
        if (BinExpr.Left.ResolvedType = nil) or
           not (BinExpr.Left.ResolvedType.Kind in [tyInt64, tyUInt64]) then
        begin
          ArgTemp := AllocTemp();
          if BinExpr.ResolvedType.Kind = tyUInt64 then
            EmitLine(Format('  %s =l extuw %s', [ArgTemp, L]))
          else
            EmitLine(Format('  %s =l extsw %s', [ArgTemp, L]));
          L := ArgTemp;
        end;
        if (BinExpr.Right.ResolvedType = nil) or
           not (BinExpr.Right.ResolvedType.Kind in [tyInt64, tyUInt64]) then
        begin
          ArgTemp := AllocTemp();
          if BinExpr.ResolvedType.Kind = tyUInt64 then
            EmitLine(Format('  %s =l extuw %s', [ArgTemp, R]))
          else
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
      Exit(T);
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
      T := AllocTemp();
      EmitLine(Format('  %s =w phi @%s %s, @%s %s',
        [T, ArgTemp, L, SelfTemp, R]));
      Exit(T);
    end;
    L := EmitExpr(BinExpr.Left);
    R := EmitExpr(BinExpr.Right);
    T := AllocTemp();
    { String concatenation: delegate to RTL }
    if (BinExpr.Op = boAdd) and
       (BinExpr.Left.ResolvedType <> nil) and
       BinExpr.Left.ResolvedType.IsString() then
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
      Exit(T);
    end;
    { Pointer arithmetic: Pointer/PChar +/- Integer — result is same pointer type }
    if (BinExpr.Op in [boAdd, boSub]) and
       (BinExpr.Left.ResolvedType <> nil) and
       (BinExpr.Left.ResolvedType.Kind in [tyPointer, tyPChar]) then
    begin
      ArgTemp := AllocTemp();
      EmitLine(Format('  %s =l extsw %s', [ArgTemp, R]));
      if BinExpr.Op = boAdd then
        EmitLine(Format('  %s =l add %s, %s', [T, L, ArgTemp]))
      else
        EmitLine(Format('  %s =l sub %s, %s', [T, L, ArgTemp]));
      Exit(T);
    end;
    { String equality/inequality: content comparison via RTL helper }
    if (BinExpr.Left.ResolvedType <> nil) and
       BinExpr.Left.ResolvedType.IsString() and
       (BinExpr.Op in [boEQ, boNE]) then
    begin
      EmitLine(Format('  %s =w call $_StringEquals(l %s, l %s)', [T, L, R]));
      if BinExpr.Op = boNE then
      begin
        ArgTemp := AllocTemp();
        EmitLine(Format('  %s =w ceqw %s, 0', [ArgTemp, T]));
        T := ArgTemp;
      end;
      Exit(T);
    end;
    { Set membership: elem in SetVar — (set >> ord(elem)) & 1 }
    if BinExpr.Op = boIn then
    begin
      SQT := QbeTypeOf(BinExpr.Right.ResolvedType);
      ArgTemp := AllocTemp();
      EmitLine(Format('  %s =%s shr %s, %s', [ArgTemp, SQT, R, L]));
      EmitLine(Format('  %s =w and %s, 1', [T, ArgTemp]));
      Exit(T);
    end;

    { Set arithmetic: union, difference, intersection }
    if (BinExpr.Left.ResolvedType <> nil) and
       (BinExpr.Left.ResolvedType.Kind = tySet) then
    begin
      SQT := QbeTypeOf(BinExpr.Left.ResolvedType);
      case BinExpr.Op of
        boAdd:  { union: or }
          EmitLine(Format('  %s =%s or %s, %s', [T, SQT, L, R]));
        boSub:  { difference: L and (not R) }
        begin
          ArgTemp := AllocTemp();
          EmitLine(Format('  %s =%s xor %s, -1', [ArgTemp, SQT, R]));
          EmitLine(Format('  %s =%s and %s, %s', [T, SQT, L, ArgTemp]));
        end;
        boMul:  { intersection: and }
          EmitLine(Format('  %s =%s and %s, %s', [T, SQT, L, R]));
        boEQ:
          if SQT = 'l' then
            EmitLine(Format('  %s =w ceql %s, %s', [T, L, R]))
          else
            EmitLine(Format('  %s =w ceqw %s, %s', [T, L, R]));
        boNE:
          if SQT = 'l' then
            EmitLine(Format('  %s =w cnel %s, %s', [T, L, R]))
          else
            EmitLine(Format('  %s =w cnew %s, %s', [T, L, R]));
      else
        raise ECodeGenError.Create(Format(
          'Operator not supported for set types at line %d', [BinExpr.Line]));
      end;
      Exit(T);
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
    { Int64 / UInt64 comparison: result is Boolean (w) but operands must
      be compared as l.  Unsigned comparison instructions are used when
      either operand is tyUInt64. }
    else if (BinExpr.Op in [boEQ, boNE, boLT, boGT, boLE, boGE]) and
            (((BinExpr.Left.ResolvedType <> nil) and
              (BinExpr.Left.ResolvedType.Kind in [tyInt64, tyUInt64])) or
             ((BinExpr.Right.ResolvedType <> nil) and
              (BinExpr.Right.ResolvedType.Kind in [tyInt64, tyUInt64]))) then
    begin
      ArgTemp := '';  { silence "uninitialised" hint }
      if (BinExpr.Left.ResolvedType = nil) or
         not (BinExpr.Left.ResolvedType.Kind in [tyInt64, tyUInt64]) then
      begin
        ArgTemp := AllocTemp();
        EmitLine(Format('  %s =l extsw %s', [ArgTemp, L]));
        L := ArgTemp;
      end;
      if (BinExpr.Right.ResolvedType = nil) or
         not (BinExpr.Right.ResolvedType.Kind in [tyInt64, tyUInt64]) then
      begin
        ArgTemp := AllocTemp();
        EmitLine(Format('  %s =l extsw %s', [ArgTemp, R]));
        R := ArgTemp;
      end;
      if ((BinExpr.Left.ResolvedType <> nil) and
          (BinExpr.Left.ResolvedType.Kind = tyUInt64)) or
         ((BinExpr.Right.ResolvedType <> nil) and
          (BinExpr.Right.ResolvedType.Kind = tyUInt64)) then
      begin
        case BinExpr.Op of
          boEQ: Op := 'ceql';
          boNE: Op := 'cnel';
          boLT: Op := 'cultl';
          boGT: Op := 'cugtl';
          boLE: Op := 'culel';
          boGE: Op := 'cugel';
        end;
      end
      else
      begin
        case BinExpr.Op of
          boEQ: Op := 'ceql';
          boNE: Op := 'cnel';
          boLT: Op := 'csltl';
          boGT: Op := 'csgtl';
          boLE: Op := 'cslel';
          boGE: Op := 'csgel';
        end;
      end;
      EmitLine(Format('  %s =w %s %s, %s', [T, Op, L, R]));
    end
    // Int64 / UInt64 arithmetic: l-typed instructions; extend w operands to
    // l as needed.  Signed types sign-extend (extsw) and use signed div/rem;
    // unsigned types zero-extend (extuw) and use udiv/urem.
    else if (BinExpr.ResolvedType <> nil) and
            (BinExpr.ResolvedType.Kind in [tyInt64, tyUInt64]) then
    begin
      if (BinExpr.Left.ResolvedType = nil) or
         not (BinExpr.Left.ResolvedType.Kind in [tyInt64, tyUInt64]) then
      begin
        ArgTemp := AllocTemp();
        if BinExpr.ResolvedType.Kind = tyUInt64 then
          EmitLine(Format('  %s =l extuw %s', [ArgTemp, L]))
        else
          EmitLine(Format('  %s =l extsw %s', [ArgTemp, L]));
        L := ArgTemp;
      end;
      // For shift ops, the shift count stays w (QBE accepts w shift count for l shifts).
      // For arithmetic ops, extend the right operand to l too.
      if not (BinExpr.Op in [boShl, boShr, boSar]) then
      begin
        if (BinExpr.Right.ResolvedType = nil) or
           not (BinExpr.Right.ResolvedType.Kind in [tyInt64, tyUInt64]) then
        begin
          ArgTemp := AllocTemp();
          if BinExpr.ResolvedType.Kind = tyUInt64 then
            EmitLine(Format('  %s =l extuw %s', [ArgTemp, R]))
          else
            EmitLine(Format('  %s =l extsw %s', [ArgTemp, R]));
          R := ArgTemp;
        end;
      end;
      if BinExpr.ResolvedType.Kind = tyUInt64 then
      begin
        case BinExpr.Op of
          boAdd: Op := 'add';
          boSub: Op := 'sub';
          boMul: Op := 'mul';
          boDiv: Op := 'udiv';
          boMod: Op := 'urem';
          boAnd: Op := 'and';
          boOr:  Op := 'or';
          boXor: Op := 'xor';
          boShl: Op := 'shl';
          boShr: Op := 'shr';
          boSar: Op := 'sar';
        else
          Op := 'add';
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
          boAnd: Op := 'and';
          boOr:  Op := 'or';
          boXor: Op := 'xor';
          boShl: Op := 'shl';
          boShr: Op := 'shr';
          boSar: Op := 'sar';
        else
          Op := 'add';
        end;
      end;
      EmitLine(Format('  %s =l %s %s, %s', [T, Op, L, R]));
    end
    { Float arithmetic/comparison: QBE uses d/s typed instructions.
      Integer operands mixed with float are promoted via swtof/sltof.
      Single operands are widened to Double via exts when result is Double. }
    else if (BinExpr.ResolvedType <> nil) and BinExpr.ResolvedType.IsFloat() then
    begin
      if BinExpr.ResolvedType.Kind = tySingle then
        FT := 's'
      else
        FT := 'd';
      if (BinExpr.Left.ResolvedType <> nil) and
         not BinExpr.Left.ResolvedType.IsFloat() then
      begin
        ArgTemp := AllocTemp();
        if QbeTypeOf(BinExpr.Left.ResolvedType) = 'l' then
          EmitLine(Format('  %s =%s sltof %s', [ArgTemp, FT, L]))
        else
          EmitLine(Format('  %s =%s swtof %s', [ArgTemp, FT, L]));
        L := ArgTemp;
      end
      else if (FT = 'd') and (BinExpr.Left.ResolvedType <> nil) and
              (BinExpr.Left.ResolvedType.Kind = tySingle) then
      begin
        ArgTemp := AllocTemp();
        EmitLine(Format('  %s =d exts %s', [ArgTemp, L]));
        L := ArgTemp;
      end;
      if (BinExpr.Right.ResolvedType <> nil) and
         not BinExpr.Right.ResolvedType.IsFloat() then
      begin
        ArgTemp := AllocTemp();
        if QbeTypeOf(BinExpr.Right.ResolvedType) = 'l' then
          EmitLine(Format('  %s =%s sltof %s', [ArgTemp, FT, R]))
        else
          EmitLine(Format('  %s =%s swtof %s', [ArgTemp, FT, R]));
        R := ArgTemp;
      end
      else if (FT = 'd') and (BinExpr.Right.ResolvedType <> nil) and
              (BinExpr.Right.ResolvedType.Kind = tySingle) then
      begin
        ArgTemp := AllocTemp();
        EmitLine(Format('  %s =d exts %s', [ArgTemp, R]));
        R := ArgTemp;
      end;
      case BinExpr.Op of
        boAdd:   Op := 'add';
        boSub:   Op := 'sub';
        boMul:   Op := 'mul';
        boDiv:   Op := 'div';
        boSlash: Op := 'div';
      else    Op := 'add';
      end;
      EmitLine(Format('  %s =%s %s %s, %s', [T, FT, Op, L, R]));
    end
    else if BinExpr.ResolvedType.Kind = tyBoolean then
    begin
      { Float comparison — at least one operand is float.
        Both-Single → s-typed compares; otherwise widen to d. }
      if (BinExpr.Left.ResolvedType <> nil) and BinExpr.Left.ResolvedType.IsFloat() then
      begin
        if (BinExpr.Left.ResolvedType.Kind = tySingle) and
           (BinExpr.Right.ResolvedType <> nil) and
           (BinExpr.Right.ResolvedType.Kind = tySingle) then
          FT := 's'
        else
          FT := 'd';
        if (BinExpr.Right.ResolvedType <> nil) and
           not BinExpr.Right.ResolvedType.IsFloat() then
        begin
          ArgTemp := AllocTemp();
          if QbeTypeOf(BinExpr.Right.ResolvedType) = 'l' then
            EmitLine(Format('  %s =%s sltof %s', [ArgTemp, FT, R]))
          else
            EmitLine(Format('  %s =%s swtof %s', [ArgTemp, FT, R]));
          R := ArgTemp;
        end
        else if (FT = 'd') and (BinExpr.Right.ResolvedType <> nil) and
                (BinExpr.Right.ResolvedType.Kind = tySingle) then
        begin
          ArgTemp := AllocTemp();
          EmitLine(Format('  %s =d exts %s', [ArgTemp, R]));
          R := ArgTemp;
        end;
        if (FT = 'd') and (BinExpr.Left.ResolvedType <> nil) and
           (BinExpr.Left.ResolvedType.Kind = tySingle) then
        begin
          ArgTemp := AllocTemp();
          EmitLine(Format('  %s =d exts %s', [ArgTemp, L]));
          L := ArgTemp;
        end;
        case BinExpr.Op of
          boEQ: Op := 'ceq' + FT;
          boNE: Op := 'cne' + FT;
          boLT: Op := 'clt' + FT;
          boGT: Op := 'cgt' + FT;
          boLE: Op := 'cle' + FT;
          boGE: Op := 'cge' + FT;
        else    Op := 'ceq' + FT;
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
        boSar: Op := 'sar';
      else
        Op := 'add';
      end;
      EmitLine(Format('  %s =w %s %s, %s', [T, Op, L, R]));
    end;
    Result := T;
  end
  else if AExpr is TNotExpr then
  begin
    L := EmitExpr(TNotExpr(AExpr).Expr);
    T := AllocTemp();
    if (AExpr.ResolvedType <> nil) and
       (AExpr.ResolvedType.Kind in [tyInt64, tyUInt64]) then
      EmitLine(Format('  %s =l xor %s, -1', [T, L]))
    else if (AExpr.ResolvedType <> nil) and
            (AExpr.ResolvedType.Kind = tyBoolean) then
      EmitLine(Format('  %s =w xor %s, 1', [T, L]))
    else
      EmitLine(Format('  %s =w xor %s, -1', [T, L]));
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
      L     := AllocTemp();
      { Byte / Boolean dereferences must use loadub — loadw would read
        four bytes and corrupt the value with adjacent memory.  Same
        narrowing applies to array element loads (line ~1886). }
      if (AExpr.ResolvedType <> nil) and
         (AExpr.ResolvedType.Kind in [tyByte, tyBoolean]) then
        EmitLine(Format('  %s =w loadub %s', [L, T]))
      else
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

procedure TCodeGenQBE.EmitInterfaceToFieldSlots(AExpr: TASTExpr;
  const AObjSlotPtr, AItabSlotPtr: string; AIntfType: TTypeDesc);
{ Assign an interface expression into two memory slots (obj pointer and itab
  pointer) that live at known addresses in the object layout (e.g. a class
  field).  AIntfType is the declared interface type of the destination slot,
  needed to name the static itab when the source is a class.  Handles all
  source expression shapes:
    - interface source → load obj/itab from the source's fat-pointer slots
    - class source → emit obj + the static $itab_<Class>_<Interface> symbol
  ARC: retains the incoming obj and releases whatever was in the field. }
var
  IntfDesc: TInterfaceTypeDesc;
  ClassRT:  TRecordTypeDesc;
  NewObj, NewItab, OldObj, ItabName: string;
begin
  if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyInterface) then
  begin
    { Interface source: load obj/itab from the source's fat-pointer slots }
    EmitInterfaceExprPair(AExpr, NewObj, NewItab);
  end
  else if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyClass) then
  begin
    { Class source: emit obj and reference the static itab for the
      (concrete class, destination interface) pair — the same symbol the
      interface direct-assignment path uses.  _GetItab is a runtime lookup
      keyed by interface typeinfo and is for as-casts; here both types are
      known statically, so the constant itab symbol is correct and cheaper. }
    if (AIntfType = nil) or (AIntfType.Kind <> tyInterface) then
      raise ECodeGenError.Create(
        'EmitInterfaceToFieldSlots: class source needs a destination interface type');
    IntfDesc := TInterfaceTypeDesc(AIntfType);
    ClassRT  := TRecordTypeDesc(AExpr.ResolvedType);
    NewObj   := EmitExpr(AExpr);
    NewItab  := '$itab_' + QBEMangle(ClassSymName(ClassRT.Name)) + '_' +
                QBEMangle(IntfDesc.Name);
  end
  else
    raise ECodeGenError.Create('EmitInterfaceToFieldSlots: unsupported source type');
  OldObj := AllocTemp();
  EmitLine(Format('  %s =l loadl %s', [OldObj, AObjSlotPtr]));
  if not ExprOwnsRef(AExpr) then
    EmitLine(Format('  call $_ClassAddRef(l %s)', [NewObj]));
  EmitLine(Format('  call $_ClassRelease(l %s)', [OldObj]));
  EmitLine(Format('  storel %s, %s', [NewObj, AObjSlotPtr]));
  EmitLine(Format('  storel %s, %s', [NewItab, AItabSlotPtr]));
end;

procedure TCodeGenQBE.EmitInterfaceExprPair(AExpr: TASTExpr;
  out AObjTemp, AItabTemp: string);
var
  ObjT, ItabT: string;
  OkT, LblOk, LblFail, LblEnd: string;
  AE: TAsExpr;
  IE: TIdentExpr;
  IEFld: TFieldInfo;
  ClassRT: TRecordTypeDesc;
begin
  if AExpr is TIdentExpr then
  begin
    IE := TIdentExpr(AExpr);
    if IE.IsImplicitSelf and (IE.ImplicitFieldInfo <> nil) then
    begin
      { Interface field of Self: load from object layout at Self + FieldOffset }
      IEFld := TFieldInfo(IE.ImplicitFieldInfo);
      ObjT := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_Self', [ObjT]));
      if IEFld.Offset > 0 then
      begin
        ItabT := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d', [ItabT, ObjT, IEFld.Offset]));
        ObjT := ItabT;
      end;
      AObjTemp  := AllocTemp();
      AItabTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [AObjTemp, ObjT]));
      ItabT := AllocTemp();
      EmitLine(Format('  %s =l add %s, 8', [ItabT, ObjT]));
      EmitLine(Format('  %s =l loadl %s', [AItabTemp, ItabT]));
    end
    else
    begin
      AObjTemp  := AllocTemp();
      AItabTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s_obj', [AObjTemp,
        VarRef(IE.Name, IE.IsGlobal)]));
      EmitLine(Format('  %s =l loadl %s_itab', [AItabTemp,
        VarRef(IE.Name, IE.IsGlobal)]));
    end;
  end
  else if AExpr is TAsExpr then
  begin
    AE := TAsExpr(AExpr);
    ObjT := EmitExpr(AE.Obj);
    ItabT := AllocTemp();
    EmitLine(Format('  %s =l call $_GetItab(l %s, l $typeinfo_%s)',
      [ItabT, ObjT, ClassSymName(AE.TypeName)]));
    OkT     := AllocTemp();
    LblOk   := AllocLabel('as_ok');
    LblFail := AllocLabel('as_fail');
    LblEnd  := AllocLabel('as_end');
    EmitLine(Format('  %s =w cnel %s, 0', [OkT, ItabT]));
    EmitLine(Format('  jnz %s, @%s, @%s', [OkT, LblOk, LblFail]));
    EmitLine('@' + LblFail);
    EmitLine('  call $_Raise_InvalidCast()');
    EmitLine(Format('  jmp @%s', [LblEnd]));
    EmitLine('@' + LblOk);
    EmitLine(Format('  jmp @%s', [LblEnd]));
    EmitLine('@' + LblEnd);
    AObjTemp  := ObjT;
    AItabTemp := ItabT;
  end
  else if AExpr is TFieldAccessExpr then
  begin
    { Interface stored in a record/class field: the fat pointer is contiguous
      in the field's memory — obj at the field address, itab at +8.  (Plain
      interface locals/globals use split _obj/_itab slots, handled above; a
      record field never does.)  EmitLValueAddr resolves the field address. }
    ObjT := EmitLValueAddr(AExpr);
    AObjTemp  := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [AObjTemp, ObjT]));
    ItabT := AllocTemp();
    EmitLine(Format('  %s =l add %s, 8', [ItabT, ObjT]));
    AItabTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [AItabTemp, ItabT]));
  end
  else
    raise ECodeGenError.Create(
      'Unsupported interface expression form for argument passing: ' +
      AExpr.ClassName);
end;

function TCodeGenQBE.InterfaceArgFragment(AExpr: TASTExpr): string;
var
  ObjTemp, ItabTemp: string;
begin
  EmitInterfaceExprPair(AExpr, ObjTemp, ItabTemp);
  Result := Format(', l %s, l %s', [ObjTemp, ItabTemp]);
end;

function TCodeGenQBE.EmitIsExpr(AExpr: TIsExpr): string;
var
  ObjTemp: string;
  ResTemp: string;
begin
  ObjTemp := EmitExpr(AExpr.Obj);
  ResTemp := AllocTemp();
  if (AExpr.ResolvedTargetType <> nil) and
     (AExpr.ResolvedTargetType.Kind = tyInterface) then
    EmitLine(Format('  %s =w call $_ImplementsInterface(l %s, l $typeinfo_%s)',
      [ResTemp, ObjTemp, ClassSymName(AExpr.TypeName)]))
  else
    EmitLine(Format('  %s =w call $_IsInstance(l %s, l $typeinfo_%s)',
      [ResTemp, ObjTemp, ClassSymName(AExpr.TypeName)]));
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
  SlotTemp := AllocTemp();
  EmitLine(Format('  %s =l alloc8 1', [SlotTemp]));

  OkTemp  := AllocTemp();
  LblOk   := AllocLabel('as_ok');
  LblFail := AllocLabel('as_fail');
  LblEnd  := AllocLabel('as_end');

  EmitLine(Format('  %s =w call $_IsInstance(l %s, l $typeinfo_%s)',
    [OkTemp, ObjTemp, ClassSymName(AExpr.TypeName)]));
  EmitLine(Format('  jnz %s, @%s, @%s', [OkTemp, LblOk, LblFail]));

  EmitLine('@' + LblFail);
  EmitLine('  call $_Raise_InvalidCast()');
  EmitLine(Format('  storel 0, %s', [SlotTemp]));  { unreachable; satisfies SSA }
  EmitLine(Format('  jmp @%s', [LblEnd]));

  EmitLine('@' + LblOk);
  EmitLine(Format('  storel %s, %s', [ObjTemp, SlotTemp]));
  EmitLine(Format('  jmp @%s', [LblEnd]));

  EmitLine('@' + LblEnd);
  ResTemp := AllocTemp();
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
  OkTemp  := AllocTemp();
  EmitLine(Format('  %s =w call $_ImplementsInterface(l %s, l $typeinfo_%s)',
    [OkTemp, ObjTemp, ClassSymName(AExpr.IntfTypeName)]));

  if AExpr.OutVarName = '' then
  begin
    { 2-arg form — just return the Boolean result }
    Exit(OkTemp);
  end;

  { 3-arg form — on success populate the out-var's fat pointer }
  ResSlot := AllocTemp();
  EmitLine(Format('  %s =l alloc4 1', [ResSlot]));
  LblYes := AllocLabel('supports_yes');
  LblNo  := AllocLabel('supports_no');
  LblEnd := AllocLabel('supports_end');

  EmitLine(Format('  jnz %s, @%s, @%s', [OkTemp, LblYes, LblNo]));

  EmitLine('@' + LblYes);
  OutRef   := VarRef(AExpr.OutVarName, AExpr.OutVarIsGlobal);
  ItabTemp := AllocTemp();
  EmitLine(Format('  %s =l call $_GetItab(l %s, l $typeinfo_%s)',
    [ItabTemp, ObjTemp, ClassSymName(AExpr.IntfTypeName)]));
  { ARC: retain new obj, release old obj slot of out-var }
  OldTemp := AllocTemp();
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
  ResTemp := AllocTemp();
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
  else if AMDecl <> nil then
    Result := QBEMangle(
      ClassUnitPrefix(ATypeName) + ATypeName + '_' + AMDecl.Name)
  else
    Result := QBEMangle(
      ClassUnitPrefix(ATypeName) + ATypeName + '_' + AMethodName);
end;

function TCodeGenQBE.ClassSymName(const AClassName: string): string;
begin
  Result := ClassUnitPrefix(AClassName) + AClassName;
end;

{ Return the symbol name suffix used for $typeinfo_<X> of an interface.
  Generic interface instances (name contains '<') are registered by
  QBEMangle(name) with no unit prefix — that is how EmitTypeInfoAndItabs
  emits the definition (GII.InstName).  Plain interfaces get the normal
  ClassSymName treatment. }
function TCodeGenQBE.IntfTypeInfoName(const AIntfName: string): string;
begin
  if Pos('<', AIntfName) >= 0 then
    Result := QBEMangle(AIntfName)
  else
    Result := ClassSymName(AIntfName);
end;

function TCodeGenQBE.FindMethodInClassDef(AClassDef: TClassTypeDef;
  const AName: string): TMethodDecl;
var
  I: Integer;
  M: TMethodDecl;
begin
  Result := nil;
  for I := 0 to AClassDef.Methods.Count - 1 do
  begin
    M := TMethodDecl(AClassDef.Methods.Items[I]);
    if SameText(M.Name, AName) then
      Exit(M);
  end;
end;

function TCodeGenQBE.ClassUnitPrefix(const AClassName: string): string;
var
  Sym: TSymbol;
  Owner: string;
  I: Integer;
  Ch: string;
begin
  Result := '';
  if FSymTable = nil then Exit;
  Sym := FSymTable.Lookup(AClassName);
  if Sym = nil then Exit;
  Owner := Sym.OwningUnit;
  { Allowlist mirrors uSemantic.IsUnmangledUnit. }
  if Owner = '' then Exit;
  if SameText(Owner, 'System') then Exit;
  if (Length(Owner) >= 4) and SameText(Copy(Owner, 0, 4), 'rtl.') then Exit;
  if (Length(Owner) >= 7) and SameText(Copy(Owner, 0, 7), 'blaise_') then Exit;
  for I := 0 to Length(Owner) - 1 do
  begin
    Ch := Copy(Owner, I, 1);
    if Ch = '.' then Result := Result + '_'
    else                Result := Result + Ch;
  end;
  Result := Result + '_';
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
        Result := Result + '\x' + Chr(Hi) + Chr(Lo)
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
  FOutput.Clear();
  FStrLits.Clear();
  FStrLitsEmitted := 0;
  FTempCount  := 0;
  FLabelCount := 0;

  CollectThreadVarNames(AProg.Block);

  Body := TIRBuffer.Create();
  try
    SavedOutput := FOutput;
    FOutput := Body;
    try
      EmitFieldCleanupDefs(AProg);
      EmitMethodDefs(AProg);
      EmitStandaloneDefs(AProg);
      FExitLabel := 'main_exit';
      EmitMainHeader();
      EmitBlock(AProg.Block);
      EmitMainFooter();
      FExitLabel := '';
    finally
      FOutput := SavedOutput;
    end;

    EmitLine('# Generated by Blaise Compiler');
    EmitLine('# Source: ' + AProg.Name);
    EmitLine('');
    EmitDataSection();
    EmitGlobalVarData(AProg.Block);
    EmitGlobalConstData(AProg.Block);
    EmitLocalArrayConstsInProgram(AProg);
    EmitInterfaceDefs(AProg);
    EmitTypeInfoDefs(AProg);
    EmitVTableDefs(AProg);
    EmitFFIRecordTypeDecls();
    FOutput.AppendBuffer(Body);
  finally
    Body.Free();
  end;
end;

procedure TCodeGenQBE.GenerateUnit(AUnit: TUnit);
var
  I, J, S:   Integer;
  ImplDecl:  TMethodDecl;
  IntfNames: TStringList;
  Body:      TIRBuffer;
  SavedOut:  TIRBuffer;
  GI:        TGenericInstance;
  GRI:       TGenericRecordInstance;
  GFI:       TGenericFuncInstance;
  MDecl:     TMethodDecl;
  RT:        TRecordTypeDesc;
  VLine:     string;
  E:         TVTableEntry;
begin
  FOutput.Clear();
  FStrLits.Clear();
  FStrLitsEmitted := 0;
  FTempCount  := 0;
  FLabelCount := 0;

  CollectThreadVarNames(AUnit.IntfBlock);
  CollectThreadVarNames(AUnit.ImplBlock);

  IntfNames := TStringList.Create();
  try
    IntfNames.CaseSensitive := False;
    for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
      IntfNames.Add(TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]).Name);

    Body := TIRBuffer.Create();
    try
      SavedOut := FOutput;
      FOutput  := Body;
      try
        for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
        begin
          ImplDecl := TMethodDecl(AUnit.ImplBlock.ProcDecls.Items[I]);
          EmitFuncDef(ImplDecl, IntfNames.IndexOf(ImplDecl.Name) >= 0);
        end;
        for I := 0 to AUnit.GenericInstances.Count - 1 do
        begin
          GI := TGenericInstance(AUnit.GenericInstances.Items[I]);
          for J := 0 to GI.ClassDef.Methods.Count - 1 do
          begin
            MDecl := TMethodDecl(GI.ClassDef.Methods.Items[J]);
            if MDecl.Body <> nil then
              EmitMethodDef(GI.TypeName, MDecl);
          end;
        end;
        for I := 0 to AUnit.GenericRecordInstances.Count - 1 do
        begin
          GRI := TGenericRecordInstance(AUnit.GenericRecordInstances.Items[I]);
          for J := 0 to GRI.RecordDef.Methods.Count - 1 do
          begin
            MDecl := TMethodDecl(GRI.RecordDef.Methods.Items[J]);
            if MDecl.Body <> nil then
              EmitMethodDef(GRI.TypeName, MDecl);
          end;
        end;
        for I := 0 to AUnit.GenericFuncInstances.Count - 1 do
        begin
          GFI := TGenericFuncInstance(AUnit.GenericFuncInstances.Items[I]);
          EmitFuncDef(GFI.MethodDecl, True);
        end;
      finally
        FOutput := SavedOut;
      end;

      EmitLine('# Generated by Blaise Compiler');
      EmitLine('# Unit: ' + AUnit.Name);
      EmitLine('');
      EmitDataSection();
      EmitGlobalVarData(AUnit.IntfBlock);
      EmitGlobalVarData(AUnit.ImplBlock);
      EmitGlobalConstData(AUnit.IntfBlock);
      EmitGlobalConstData(AUnit.ImplBlock);
      EmitLocalArrayConstsInUnit(AUnit);
      for I := 0 to AUnit.GenericInstances.Count - 1 do
      begin
        GI := TGenericInstance(AUnit.GenericInstances.Items[I]);
        RT := TRecordTypeDesc(GI.TypeDesc);
        EmitLine(Format('data $typeinfo_%s = { l 0 }', [QBEMangle(GI.TypeName)]));
        if RT.HasVTable() then
        begin
          VLine := Format('data $vtable_%s = { l $typeinfo_%s',
            [QBEMangle(GI.TypeName), QBEMangle(GI.TypeName)]);
          for S := 0 to RT.VTableCount() - 1 do
          begin
            E := RT.VTableEntryAt(S);
            if E.IsAbstract then
              VLine := VLine + ', l $_AbstractMethodError'
            else
              VLine := VLine + ', l $' + QBEMangle(StrCopyTail(E.ImplName, 1));
          end;
          VLine := VLine + ' }';
          EmitLine(VLine);
        end;
        EmitFieldCleanupFn(ClassSymName(QBEMangle(GI.TypeName)), RT);
      end;
      EmitFFIRecordTypeDecls();
      FOutput.AppendBuffer(Body);
    finally
      Body.Free();
    end;
  finally
    IntfNames.Free();
  end;
end;

procedure TCodeGenQBE.SetSymbolTable(ASymTable: TSymbolTable);
begin
  FSymTable := ASymTable;
end;

procedure TCodeGenQBE.SetDebugMode(AEnabled: Boolean);
begin
  FDebugMode := AEnabled;
end;

procedure TCodeGenQBE.SetExportAll(AEnabled: Boolean);
begin
  FExportAll := AEnabled;
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
  GI:           TGenericInstance;
  GRI:          TGenericRecordInstance;
  MName:        string;
  MethRef:      string;
  ParentStr:    string;
  ImplStr:      string;
  MethStr:      string;
  AttrsStr:     string;
  AttrsLine:    string;
  MethLine:     string;
  ItabLine:     string;
  ItabRef:      string;
  ImplLine:     string;
  MethName:     string;
  IntfMangle:   string;
  VLine:        string;
  E:            TVTableEntry;
  GII:          TGenericInterfaceInstance;
begin
  { No clears — output and string literal table accumulate across calls.
    Counter resets are safe: QBE temps and block labels are function-scoped. }
  FTempCount  := 0;
  FLabelCount := 0;

  CollectThreadVarNames(AUnit.IntfBlock);
  CollectThreadVarNames(AUnit.ImplBlock);

  IntfNames := TStringList.Create();
  try
    IntfNames.CaseSensitive := False;
    for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
      IntfNames.Add(TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]).Name);

    Body := TIRBuffer.Create();
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

        { Class and record method bodies from interface type declarations.
          After LinkClassMethodImpls the definition's TMethodDecl nodes
          hold the bodies and parameter types are resolved by AnalyseMethodBodies. }
        for I := 0 to AUnit.IntfBlock.TypeDecls.Count - 1 do
        begin
          TD := TTypeDecl(AUnit.IntfBlock.TypeDecls.Items[I]);
          if TD.Def is TClassTypeDef then
          begin
            CD := TClassTypeDef(TD.Def);
            for J := 0 to CD.Methods.Count - 1 do
            begin
              MDecl := TMethodDecl(CD.Methods.Items[J]);
              if MDecl.Body <> nil then
                EmitMethodDef(TD.Name, MDecl);
            end;
          end
          else if TD.Def is TRecordTypeDef then
          begin
            for J := 0 to TRecordTypeDef(TD.Def).Methods.Count - 1 do
            begin
              MDecl := TMethodDecl(TRecordTypeDef(TD.Def).Methods.Items[J]);
              if MDecl.Body <> nil then
                EmitMethodDef(TD.Name, MDecl);
            end;
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
            EmitFieldCleanupFn(ClassSymName(TD.Name), RT);
          end;

        { System-unit (TObject / TCustomAttribute) FieldCleanup stubs.
          Emitted once per codegen pass when this unit declares any
          class.  In monolithic mode QBE emits these as local symbols
          (no .globl), so each .o gets its own private copy.  In
          separate-compilation mode (FExportAll) they would collide
          across per-unit .o files, so skip them here — the main
          program's AppendProgram emits the authoritative copies. }
        if (not FExportAll) and (not FSystemDefsEmitted) and (FSymTable <> nil) then
          for I := 0 to AUnit.IntfBlock.TypeDecls.Count - 1 do
          begin
            TD := TTypeDecl(AUnit.IntfBlock.TypeDecls.Items[I]);
            if TD.Def is TClassTypeDef then
            begin
              EmitLine('function $_FieldCleanup_TObject(l %self) {');
              EmitLine('@start');
              EmitLine('  ret');
              EmitLine('}');
              EmitLine('');
              EmitLine('function $_FieldCleanup_TCustomAttribute(l %self) {');
              EmitLine('@start');
              EmitLine('  ret');
              EmitLine('}');
              EmitLine('');
              Break;
            end;
          end;

        { Generic class instances declared in this unit — method bodies and
          per-instance field cleanup functions.  Mirrors the program path in
          EmitMethodDefs and EmitFieldCleanupFns for AProg.GenericInstances. }
        for I := 0 to AUnit.GenericInstances.Count - 1 do
        begin
          GI := TGenericInstance(AUnit.GenericInstances.Items[I]);
          for J := 0 to GI.ClassDef.Methods.Count - 1 do
          begin
            MDecl := TMethodDecl(GI.ClassDef.Methods.Items[J]);
            if MDecl.Body <> nil then
              EmitMethodDef(QBEMangle(GI.TypeName), MDecl);
          end;
          EmitFieldCleanupFn(ClassSymName(QBEMangle(GI.TypeName)),
                             TRecordTypeDesc(GI.TypeDesc));
        end;
        for I := 0 to AUnit.GenericRecordInstances.Count - 1 do
        begin
          GRI := TGenericRecordInstance(AUnit.GenericRecordInstances.Items[I]);
          for J := 0 to GRI.RecordDef.Methods.Count - 1 do
          begin
            MDecl := TMethodDecl(GRI.RecordDef.Methods.Items[J]);
            if MDecl.Body <> nil then
              EmitMethodDef(QBEMangle(GRI.TypeName), MDecl);
          end;
        end;
      finally
        FOutput := SavedOut;
      end;

      EmitLine('# Unit: ' + AUnit.Name);
      EmitLine('');
      EmitPendingStrLits();

      { Per-class data sections: typeinfo, vtables, interface tables.
        All require FSymTable to look up resolved TRecordTypeDesc. }
      if FSymTable <> nil then
      begin
        { Interface typeinfo blocks }
        for I := 0 to AUnit.IntfBlock.TypeDecls.Count - 1 do
        begin
          TD := TTypeDecl(AUnit.IntfBlock.TypeDecls.Items[I]);
          if TD.Def is TInterfaceTypeDef then
            EmitLine(ExportPrefix() + 'data $typeinfo_' + ClassSymName(TD.Name) + ' = { l 0 }');
        end;

        { System-unit (TObject / TCustomAttribute) typeinfo + vtable.
          Emitted alongside the FieldCleanup stubs above, also gated
          on FSystemDefsEmitted.  Skipped in separate-compilation mode
          (FExportAll) — the main program provides these. }
        if (not FExportAll) and (not FSystemDefsEmitted) then
          for I := 0 to AUnit.IntfBlock.TypeDecls.Count - 1 do
          begin
            TD := TTypeDecl(AUnit.IntfBlock.TypeDecls.Items[I]);
            if TD.Def is TClassTypeDef then
            begin
              EmitLine('data $typeinfo_TObject = { l 0, l 0, l ' +
                       EmitClassNameRef('TObject') + ', l 0' +
                       ', l 8, l $_FieldCleanup_TObject, l $vtable_TObject, l 0 }');
              EmitLine('data $typeinfo_TCustomAttribute = { l $typeinfo_TObject, l 0, l ' +
                       EmitClassNameRef('TCustomAttribute') + ', l 0' +
                       ', l 8, l $_FieldCleanup_TCustomAttribute' +
                       ', l $vtable_TCustomAttribute, l 0 }');
              EmitLine('');
              EmitLine('data $vtable_TObject = { l $typeinfo_TObject' +
                       ', l $TObject_Destroy, l $TObject_ToString }');
              EmitLine('data $vtable_TCustomAttribute = { l $typeinfo_TCustomAttribute' +
                       ', l $TObject_Destroy, l $TObject_ToString }');
              EmitLine('');
              FSystemDefsEmitted := True;
              Break;
            end;
          end;

        { Class typeinfo blocks — full 8-slot layout matching EmitTypeInfoDefs }
        for I := 0 to AUnit.IntfBlock.TypeDecls.Count - 1 do
        begin
          TD := TTypeDecl(AUnit.IntfBlock.TypeDecls.Items[I]);
          if not (TD.Def is TClassTypeDef) then Continue;
          CD := TClassTypeDef(TD.Def);
          TDesc := FSymTable.FindType(TD.Name);
          if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
          RT := TRecordTypeDesc(TDesc);
          if RT.Parent <> nil then
            ParentStr := '$typeinfo_' + ClassSymName(RT.Parent.Name)
          else
            ParentStr := '0';
          if RT.ImplementsCount() > 0 then
            ImplStr := '$impllist_' + ClassSymName(TD.Name)
          else
            ImplStr := '0';

          PubCount := 0;
          for J := 0 to CD.Methods.Count - 1 do
            if TMethodDecl(CD.Methods.Items[J]).IsPublished then
              Inc(PubCount);
          if PubCount > 0 then
          begin
            MethLine := ExportPrefix() + 'data $methods_' + ClassSymName(TD.Name) + ' = { l ' + IntToStr(PubCount);
            for J := 0 to CD.Methods.Count - 1 do
            begin
              MDecl := TMethodDecl(CD.Methods.Items[J]);
              if not MDecl.IsPublished then Continue;
              MethLine := MethLine +
                          ', l ' + EmitMethodNameRef(TD.Name, MDecl.Name) +
                          ', l $' + MethodEmitName(MDecl, TD.Name, MDecl.Name);
            end;
            MethLine := MethLine + ' }';
            EmitLine(MethLine);
            MethStr := '$methods_' + ClassSymName(TD.Name);
          end
          else
            MethStr := '0';

          if RT.ClassAttributeCount() > 0 then
          begin
            AttrsLine := ExportPrefix() + 'data $attrs_' + ClassSymName(TD.Name) + ' = { l ' + IntToStr(RT.ClassAttributeCount());
            for J := 0 to RT.ClassAttributeCount() - 1 do
              AttrsLine := AttrsLine + ', l $typeinfo_' + ClassSymName(RT.ClassAttributeAt(J));
            AttrsLine := AttrsLine + ' }';
            EmitLine(AttrsLine);
            AttrsStr := '$attrs_' + ClassSymName(TD.Name);
          end
          else
            AttrsStr := '0';

          EmitLine(ExportPrefix() + 'data $typeinfo_' + ClassSymName(TD.Name) +
                   ' = { l ' + ParentStr + ', l ' + ImplStr +
                   ', l ' + EmitClassNameRef(TD.Name) +
                   ', l ' + MethStr +
                   ', l ' + IntToStr(RT.TotalSize()) +
                   ', l $_FieldCleanup_' + ClassSymName(TD.Name) +
                   ', l $vtable_' + ClassSymName(TD.Name) +
                   ', l ' + AttrsStr + ' }');
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
          if not RT.HasVTable() then Continue;
          VLine := ExportPrefix() + 'data $vtable_' + ClassSymName(TD.Name) +
                   ' = { l $typeinfo_' + ClassSymName(TD.Name);
          for S := 0 to RT.VTableCount() - 1 do
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

        { Generic interface-instance typeinfo (e.g. IMap<string,Integer>).
          The address of this block is the interface's runtime identity token;
          the generic-class-instance impllist below references it.  The program
          path emits these from AProg.GenericIntfInstances in EmitInterfaceDefs;
          the unit path must do the same for AUnit.GenericIntfInstances, or a
          generic class implementing a generic interface inside a unit (e.g.
          TDictionary -> IMap) links against an undefined typeinfo symbol. }
        for I := 0 to AUnit.GenericIntfInstances.Count - 1 do
        begin
          GII := TGenericInterfaceInstance(AUnit.GenericIntfInstances.Items[I]);
          EmitLine(ExportPrefix() + 'data $typeinfo_' + GII.InstName + ' = { l 0 }');
        end;

        { Generic class instance typeinfo + vtable + itab/impllist.  Mirrors
          the program path in EmitTypeInfoDefs, EmitVTableDefs, and the
          generic-instance itab/impllist loop. }
        for I := 0 to AUnit.GenericInstances.Count - 1 do
        begin
          GI    := TGenericInstance(AUnit.GenericInstances.Items[I]);
          RT    := TRecordTypeDesc(GI.TypeDesc);
          MName := QBEMangle(GI.TypeName);
          if RT.Parent <> nil then
            ParentStr := '$typeinfo_' + QBEMangle(RT.Parent.Name)
          else
            ParentStr := '0';
          if RT.ImplementsCount() > 0 then
            ImplStr := '$impllist_' + MName
          else
            ImplStr := '0';
          EmitLine(ExportPrefix() + 'data $typeinfo_' + MName +
                   ' = { l ' + ParentStr + ', l ' + ImplStr +
                   ', l ' + EmitClassNameRef(GI.TypeName) + ', l 0' +
                   ', l ' + IntToStr(RT.TotalSize()) +
                   ', l $_FieldCleanup_' + MName +
                   ', l $vtable_' + MName + ', l 0 }');

          if RT.HasVTable() then
          begin
            VLine := ExportPrefix() + 'data $vtable_' + MName + ' = { l $typeinfo_' + MName;
            for S := 0 to RT.VTableCount() - 1 do
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

          if RT.ImplementsCount() > 0 then
          begin
            for J := 0 to RT.ImplementsCount() - 1 do
            begin
              IntfDesc   := RT.ImplementsIntfAt(J);
              IntfMangle := QBEMangle(IntfDesc.Name);
              ItabLine   := ExportPrefix() + 'data $itab_' + MName + '_' + IntfMangle + ' = {';
              for K := 0 to IntfDesc.MethodCount() - 1 do
              begin
                MethName := IntfDesc.MethodName(K);
                if IsAbstractClassMethod(RT, MethName) then
                  MethRef := '$_AbstractMethodError'
                else
                begin
                  MDecl := FindMethodInClassDef(GI.ClassDef, MethName);
                  if (MDecl <> nil) and (MDecl.ResolvedQbeName <> '') then
                    MethRef := '$' + QBEMangle(MDecl.ResolvedQbeName)
                  else
                    MethRef := '$' + MName + '_' + MethName;
                end;
                if K = 0 then
                  ItabLine := ItabLine + ' l ' + MethRef
                else
                  ItabLine := ItabLine + ', l ' + MethRef;
              end;
              ItabLine := ItabLine + ' }';
              EmitLine(ItabLine);
            end;
            ImplLine := ExportPrefix() + 'data $impllist_' + MName + ' = {';
            for J := 0 to RT.ImplementsCount() - 1 do
            begin
              IntfDesc   := RT.ImplementsIntfAt(J);
              IntfMangle := QBEMangle(IntfDesc.Name);
              if J = 0 then
                ImplLine := ImplLine + ' l $typeinfo_' + IntfTypeInfoName(IntfDesc.Name) +
                                       ', l $itab_' + MName + '_' + IntfMangle
              else
                ImplLine := ImplLine + ', l $typeinfo_' + IntfTypeInfoName(IntfDesc.Name) +
                                       ', l $itab_' + MName + '_' + IntfMangle;
            end;
            ImplLine := ImplLine + ', l 0 }';
            EmitLine(ImplLine);
          end;
        end;

        { Interface itab and impllist blocks for implementing classes }
        for I := 0 to AUnit.IntfBlock.TypeDecls.Count - 1 do
        begin
          TD := TTypeDecl(AUnit.IntfBlock.TypeDecls.Items[I]);
          if not (TD.Def is TClassTypeDef) then Continue;
          TDesc := FSymTable.FindType(TD.Name);
          if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
          ClassRT := TRecordTypeDesc(TDesc);
          if ClassRT.ImplementsCount() = 0 then Continue;
          for J := 0 to ClassRT.ImplementsCount() - 1 do
          begin
            IntfDesc   := ClassRT.ImplementsIntfAt(J);
            IntfMangle := QBEMangle(IntfDesc.Name);
            ItabLine   := ExportPrefix() + 'data $itab_' + ClassSymName(TD.Name) + '_' + IntfMangle + ' = {';
            for K := 0 to IntfDesc.MethodCount() - 1 do
            begin
              MethName := IntfDesc.MethodName(K);
              if (ClassRT.FindVTableSlot(MethName) >= 0) and
                 ClassRT.VTableEntryAt(ClassRT.FindVTableSlot(MethName)).IsAbstract then
                ItabRef := '$_AbstractMethodError'
              else
                ItabRef := '$' + ClassSymName(TD.Name) + '_' + MethName;
              if K = 0 then
                ItabLine := ItabLine + ' l ' + ItabRef
              else
                ItabLine := ItabLine + ', l ' + ItabRef;
            end;
            ItabLine := ItabLine + ' }';
            EmitLine(ItabLine);
          end;
          ImplLine := ExportPrefix() + 'data $impllist_' + ClassSymName(TD.Name) + ' = {';
          for J := 0 to ClassRT.ImplementsCount() - 1 do
          begin
            IntfDesc   := ClassRT.ImplementsIntfAt(J);
            IntfMangle := QBEMangle(IntfDesc.Name);
            if J = 0 then
              ImplLine := ImplLine + ' l $typeinfo_' + IntfTypeInfoName(IntfDesc.Name) +
                                     ', l $itab_' + ClassSymName(TD.Name) + '_' + IntfMangle
            else
              ImplLine := ImplLine + ', l $typeinfo_' + IntfTypeInfoName(IntfDesc.Name) +
                                     ', l $itab_' + ClassSymName(TD.Name) + '_' + IntfMangle;
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
      EmitLocalArrayConstsInUnit(AUnit);

      EmitFFIRecordTypeDecls();
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
        EmitPendingStrLits();
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
        EmitPendingStrLits();
      end;
    finally
      Body.Free();
    end;
  finally
    IntfNames.Free();
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

  CollectThreadVarNames(AProg.Block);

  Body := TIRBuffer.Create();
  try
    SavedOutput := FOutput;
    FOutput := Body;
    try
      EmitFieldCleanupDefs(AProg);
      EmitMethodDefs(AProg);
      EmitStandaloneDefs(AProg);
      FExitLabel := 'main_exit';
      EmitMainHeader();
      EmitBlock(AProg.Block);
      EmitMainFooter();
      FExitLabel := '';
    finally
      FOutput := SavedOutput;
    end;

    EmitLine('# Generated by Blaise Compiler');
    EmitLine('# Source: ' + AProg.Name);
    EmitLine('');
    EmitDataSection();  { emits remaining string literals + $__fmt_* (once) }
    EmitGlobalVarData(AProg.Block);
    EmitGlobalConstData(AProg.Block);
    EmitLocalArrayConstsInProgram(AProg);
    EmitInterfaceDefs(AProg);
    EmitTypeInfoDefs(AProg);
    EmitVTableDefs(AProg);
    EmitFFIRecordTypeDecls();
    FOutput.AppendBuffer(Body);
  finally
    Body.Free();
  end;
end;

function TCodeGenQBE.GetOutput: string;
begin
  Result := FOutput.Text();
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
    Exit(EmitExpr(AExpr.StrExpr));
  end;
  { Static array element read: A[I] where A: array[L..H] of T }
  if AExpr.StrExpr.ResolvedType.Kind = tyStaticArray then
  begin
    SAT      := TStaticArrayTypeDesc(AExpr.StrExpr.ResolvedType);
    ElemSize := SAT.ElementType.RawSize();
    LowBnd   := SAT.LowBound;
    StrPtr  := EmitExpr(AExpr.StrExpr);
    IdxW    := EmitExpr(AExpr.IndexExpr);
    IdxL    := AllocTemp();
    Offset  := AllocTemp();
    ElemPtr := AllocTemp();
    EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
    if LowBnd <> 0 then
    begin
      Adj := AllocTemp();
      EmitLine(Format('  %s =l sub %s, %d', [Adj, IdxL, LowBnd]));
      EmitLine(Format('  %s =l mul %s, %d', [Offset, Adj, ElemSize]));
    end
    else
      EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
    EmitLine(Format('  %s =l add %s, %s', [ElemPtr, StrPtr, Offset]));
    { Record elements: return address directly — records are by-value via pointer }
    if SAT.ElementType.Kind = tyRecord then
    begin
      Exit(ElemPtr);
    end;
    QLoad := LoadInstrFor(SAT.ElementType);
    QType := QbeTypeOf(SAT.ElementType);
    ByteVal := AllocTemp();
    EmitLine(Format('  %s =%s %s %s', [ByteVal, QType, QLoad, ElemPtr]));
    Exit(ByteVal);
  end;

  { Open-array element access: A[I] where A: array of T }
  if AExpr.StrExpr.ResolvedType.Kind = tyOpenArray then
  begin
    ElemType := TOpenArrayTypeDesc(AExpr.StrExpr.ResolvedType);
    ElemSize := ElemType.ElementType.ByteSize();
    QLoad    := LoadInstrFor(ElemType.ElementType);
    QType   := QbeTypeOf(ElemType.ElementType);
    StrPtr  := EmitExpr(AExpr.StrExpr);
    IdxW    := EmitExpr(AExpr.IndexExpr);
    IdxL    := AllocTemp();
    Offset  := AllocTemp();
    ElemPtr := AllocTemp();
    ByteVal := AllocTemp();
    EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
    EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
    EmitLine(Format('  %s =l add %s, %s', [ElemPtr, StrPtr, Offset]));
    EmitLine(Format('  %s =%s %s %s', [ByteVal, QType, QLoad, ElemPtr]));
    Exit(ByteVal);
  end;

  { Dynamic array element read: A[I] — data_ptr + I * ElemSize }
  if AExpr.StrExpr.ResolvedType.Kind = tyDynArray then
  begin
    ElemSize := TDynArrayTypeDesc(AExpr.StrExpr.ResolvedType).ElementType.RawSize();
    QLoad   := LoadInstrFor(TDynArrayTypeDesc(AExpr.StrExpr.ResolvedType).ElementType);
    QType   := QbeTypeOf(TDynArrayTypeDesc(AExpr.StrExpr.ResolvedType).ElementType);
    StrPtr  := EmitExpr(AExpr.StrExpr);
    IdxW    := EmitExpr(AExpr.IndexExpr);
    IdxL    := AllocTemp();
    Offset  := AllocTemp();
    ElemPtr := AllocTemp();
    ByteVal := AllocTemp();
    EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
    EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
    EmitLine(Format('  %s =l add %s, %s', [ElemPtr, StrPtr, Offset]));
    EmitLine(Format('  %s =%s %s %s', [ByteVal, QType, QLoad, ElemPtr]));
    Exit(ByteVal);
  end;

  { PChar byte access: P[I] (0-based) — loadub at ptr + I }
  if AExpr.StrExpr.ResolvedType.Kind = tyPChar then
  begin
    StrPtr  := EmitExpr(AExpr.StrExpr);
    IdxW    := EmitExpr(AExpr.IndexExpr);
    IdxL    := AllocTemp();
    BytePtr := AllocTemp();
    ByteVal := AllocTemp();
    EmitLine(Format('  %s =l extuw %s', [IdxL, IdxW]));
    EmitLine(Format('  %s =l add %s, %s', [BytePtr, StrPtr, IdxL]));
    EmitLine(Format('  %s =w loadub %s', [ByteVal, BytePtr]));
    Exit(ByteVal);
  end;

  { String byte access: S[N] (0-based).
    Data-pointer convention: str_ptr IS the char data.
    S[N] = byte at str_ptr + N }
  StrPtr  := EmitExpr(AExpr.StrExpr);    { data pointer (l) }
  IdxW    := EmitExpr(AExpr.IndexExpr);  { 0-based index (w) }
  IdxL    := AllocTemp();
  BytePtr := AllocTemp();
  ByteVal := AllocTemp();
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
      ElemSize := SAT.ElementType.RawSize();
      LowBnd   := SAT.LowBound;
      StrPtr   := EmitExpr(Sub.StrExpr);
      IdxW     := EmitExpr(Sub.IndexExpr);
      IdxL     := AllocTemp();
      Offset   := AllocTemp();
      ElemPtr  := AllocTemp();
      EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
      if LowBnd <> 0 then
      begin
        Adj := AllocTemp();
        EmitLine(Format('  %s =l sub %s, %d', [Adj, IdxL, LowBnd]));
        EmitLine(Format('  %s =l mul %s, %d', [Offset, Adj, ElemSize]));
      end
      else
        EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
      EmitLine(Format('  %s =l add %s, %s', [ElemPtr, StrPtr, Offset]));
      Exit(ElemPtr);
    end;
    if Sub.StrExpr.ResolvedType.Kind = tyOpenArray then
    begin
      OAT      := TOpenArrayTypeDesc(Sub.StrExpr.ResolvedType);
      ElemSize := OAT.ElementType.RawSize();
      StrPtr   := EmitExpr(Sub.StrExpr);
      IdxW     := EmitExpr(Sub.IndexExpr);
      IdxL     := AllocTemp();
      Offset   := AllocTemp();
      ElemPtr  := AllocTemp();
      EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
      EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
      EmitLine(Format('  %s =l add %s, %s', [ElemPtr, StrPtr, Offset]));
      Exit(ElemPtr);
    end;
    { Dynamic-array element address: @A[I] — EmitExpr on a dyn-array var
      already returns the heap data pointer, so the address computation
      mirrors the open-array case (no LowBound). }
    if Sub.StrExpr.ResolvedType.Kind = tyDynArray then
    begin
      ElemSize := TDynArrayTypeDesc(Sub.StrExpr.ResolvedType).ElementType.RawSize();
      StrPtr   := EmitExpr(Sub.StrExpr);
      IdxW     := EmitExpr(Sub.IndexExpr);
      IdxL     := AllocTemp();
      Offset   := AllocTemp();
      ElemPtr  := AllocTemp();
      EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
      EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
      EmitLine(Format('  %s =l add %s, %s', [ElemPtr, StrPtr, Offset]));
      Exit(ElemPtr);
    end;
  end;
  if AExpr.Expr is TIdentExpr then
  begin
    { @FuncName: semantic recorded a tyProcedural ResolvedType when the
      identifier names a standalone function or procedure.  In that case
      the address is the function's QBE label, not a stack-variable ref.
      Prefer the resolved decl's mangled name (handles unit-prefixed
      routine symbols).  Fall back to the bare source name only when
      semantic didn't attach a decl — keeps behaviour for any path
      that constructs a TAddrOfExpr post-semantic. }
    if (TIdentExpr(AExpr.Expr).ResolvedType <> nil) and
       (TIdentExpr(AExpr.Expr).ResolvedType.Kind = tyProcedural) then
    begin
      if AExpr.ResolvedFreeRoutine <> nil then
        Exit('$' + TMethodDecl(AExpr.ResolvedFreeRoutine).ResolvedQbeName)
      else
        Exit('$' + TIdentExpr(AExpr.Expr).Name);
    end;
    Result := EmitVarArgAddr(TIdentExpr(AExpr.Expr));
    Exit;
  end;
  { @Rec.Arr[I] — address of array-field element.  The parser absorbs [I]
    into TFieldAccessExpr.PropIndexExpr; semantic sets IsArrayAccess.  Compute
    the element address the same way EmitAddrOfExpr handles TStringSubscriptExpr. }
  if (AExpr.Expr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr.Expr).IsArrayAccess then
  begin
    FldExpr := TFieldAccessExpr(AExpr.Expr);
    if FldExpr.Base <> nil then
      StrPtr := EmitInstancePtr(FldExpr.Base)
    else if FldExpr.IsVarParam then
    begin
      StrPtr := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [StrPtr, VarRef(FldExpr.RecordName, FldExpr.IsGlobal)]));
    end
    else
      StrPtr := VarRef(FldExpr.RecordName, FldExpr.IsGlobal);
    if FldExpr.FieldInfo.Offset > 0 then
    begin
      ObjPtr := AllocTemp();
      EmitLine(Format('  %s =l add %s, %d', [ObjPtr, StrPtr, FldExpr.FieldInfo.Offset]));
      StrPtr := ObjPtr;
    end;
    if FldExpr.FieldInfo.TypeDesc.Kind = tyDynArray then
    begin
      ElemSize := TDynArrayTypeDesc(FldExpr.FieldInfo.TypeDesc).ElementType.RawSize();
      ObjPtr := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [ObjPtr, StrPtr]));
      StrPtr := ObjPtr;
    end
    else if FldExpr.FieldInfo.TypeDesc.Kind = tyStaticArray then
      ElemSize := TStaticArrayTypeDesc(FldExpr.FieldInfo.TypeDesc).ElementType.RawSize()
    else
      ElemSize := TOpenArrayTypeDesc(FldExpr.FieldInfo.TypeDesc).ElementType.RawSize();
    IdxW    := EmitExpr(FldExpr.PropIndexExpr);
    IdxL    := AllocTemp();
    Offset  := AllocTemp();
    ElemPtr := AllocTemp();
    EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
    if (FldExpr.FieldInfo.TypeDesc.Kind = tyStaticArray) and
       (TStaticArrayTypeDesc(FldExpr.FieldInfo.TypeDesc).LowBound <> 0) then
    begin
      Adj := AllocTemp();
      EmitLine(Format('  %s =l sub %s, %d',
        [Adj, IdxL, TStaticArrayTypeDesc(FldExpr.FieldInfo.TypeDesc).LowBound]));
      EmitLine(Format('  %s =l mul %s, %d', [Offset, Adj, ElemSize]));
    end
    else
      EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
    EmitLine(Format('  %s =l add %s, %s', [ElemPtr, StrPtr, Offset]));
    Exit(ElemPtr);
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
    MBlock   := AllocTemp();
    EmitLine(Format('  %s =l alloc8 16', [MBlock]));
    DataSlot := AllocTemp();
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
      ObjPtr := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [ObjPtr, VarRef(FldExpr.RecordName, FldExpr.IsGlobal)]));
    end;
    EmitLine(Format('  storel %s, %s', [ObjPtr, DataSlot]));
    Exit(MBlock);
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
  OldVal:     string;
  PCharBase:  string;
begin
  { PChar subscript write: P[I] := Integer — storeb at ptr + I.
    EmitByteRhs short-circuits Chr(N) so we store N directly instead of
    truncating the low byte of a _Chr-allocated string pointer. }
  if AStmt.ResolvedArrayType.Kind = tyPChar then
  begin
    IdxW     := EmitExpr(AStmt.IndexExpr);
    IdxL     := AllocTemp();
    ElemPtr  := AllocTemp();
    ElemVal  := EmitByteRhs(AStmt.ValueExpr);
    PCharBase := AllocTemp();
    if AStmt.IsGlobal then
      EmitLine(Format('  %s =l loadl $%s', [PCharBase, AStmt.ArrayName]))
    else if IsPromoted(AStmt.ArrayName) then
      EmitLine(Format('  %s =l copy %%_var_%s', [PCharBase, AStmt.ArrayName]))
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
    ElemSize  := ElemType.RawSize();
    PCharBase := AllocTemp();
    { load the data pointer from the variable slot }
    if AStmt.IsGlobal then
      EmitLine(Format('  %s =l loadl $%s', [PCharBase, AStmt.ArrayName]))
    else if IsPromoted(AStmt.ArrayName) then
      EmitLine(Format('  %s =l copy %%_var_%s', [PCharBase, AStmt.ArrayName]))
    else
      EmitLine(Format('  %s =l loadl %%_var_%s', [PCharBase, AStmt.ArrayName]));
    IdxW    := EmitExpr(AStmt.IndexExpr);
    IdxL    := AllocTemp();
    Offset  := AllocTemp();
    ElemPtr := AllocTemp();
    if ElemType.Kind in [tyByte, tyBoolean] then
      ElemVal := EmitByteRhs(AStmt.ValueExpr)
    else
      ElemVal := EmitExpr(AStmt.ValueExpr);
    EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
    EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
    EmitLine(Format('  %s =l add %s, %s', [ElemPtr, PCharBase, Offset]));
    case ElemType.Kind of
      tyByte, tyBoolean:           StoreInstr := 'storeb';
      tySmallInt, tyWord:          StoreInstr := 'storeh';
      tyInteger, tyUInt32, tyEnum: StoreInstr := 'storew';
    else
      begin
        StoreInstr := 'storel';
        { Extend w-typed value to l if needed (e.g. integer literals into
          Int64/UInt64 slots).  Signed for tyInt64, unsigned for tyUInt64. }
        if (ElemVal <> '') and (ElemType.Kind in [tyInt64, tyUInt64]) and
           (AStmt.ValueExpr.ResolvedType <> nil) and
           not (AStmt.ValueExpr.ResolvedType.Kind in [tyInt64, tyUInt64]) then
        begin
          Adj := AllocTemp();
          if ElemType.Kind = tyUInt64 then
            EmitLine(Format('  %s =l extuw %s', [Adj, ElemVal]))
          else
            EmitLine(Format('  %s =l extsw %s', [Adj, ElemVal]));
          ElemVal := Adj;
        end;
      end;
    end;
    { ARC for managed element types: retain new, release old, then store. }
    if ElemType.Kind = tyString then
    begin
      OldVal := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [OldVal, ElemPtr]));
      EmitLine(Format('  call $_StringAddRef(l %s)',  [ElemVal]));
      EmitLine(Format('  call $_StringRelease(l %s)', [OldVal]));
    end
    else if ElemType.Kind = tyClass then
    begin
      OldVal := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [OldVal, ElemPtr]));
      EmitLine(Format('  call $_ClassAddRef(l %s)',  [ElemVal]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [OldVal]));
    end;
    EmitLine(Format('  %s %s, %s', [StoreInstr, ElemVal, ElemPtr]));
    Exit;
  end;

  SAT      := TStaticArrayTypeDesc(AStmt.ResolvedArrayType);
  ElemType := SAT.ElementType;
  ElemSize := ElemType.RawSize();
  LowBnd   := SAT.LowBound;
  IdxW    := EmitExpr(AStmt.IndexExpr);
  IdxL    := AllocTemp();
  Offset  := AllocTemp();
  ElemPtr := AllocTemp();
  EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
  if LowBnd <> 0 then
  begin
    Adj := AllocTemp();
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
  if ElemType.Kind in [tyByte, tyBoolean] then
    ElemVal := EmitByteRhs(AStmt.ValueExpr)
  else
    ElemVal := EmitExpr(AStmt.ValueExpr);
  case ElemType.Kind of
    tyByte, tyBoolean: StoreInstr := 'storeb';
    tySmallInt, tyWord: StoreInstr := 'storeh';
    tyInteger, tyUInt32, tyEnum: StoreInstr := 'storew';
    tyInt64, tyUInt64, tyString, tyClass, tyPointer, tyPChar, tyMetaClass,
    tyProcedural: StoreInstr := 'storel';
  else
    StoreInstr := 'storew';
  end;
  { ARC for managed element types: retain new, release old, then store. }
  if ElemType.Kind = tyString then
  begin
    OldVal := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [OldVal, ElemPtr]));
    EmitLine(Format('  call $_StringAddRef(l %s)',  [ElemVal]));
    EmitLine(Format('  call $_StringRelease(l %s)', [OldVal]));
  end
  else if ElemType.Kind = tyClass then
  begin
    OldVal := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [OldVal, ElemPtr]));
    EmitLine(Format('  call $_ClassAddRef(l %s)',  [ElemVal]));
    EmitLine(Format('  call $_ClassRelease(l %s)', [OldVal]));
  end;
  EmitLine(Format('  %s %s, %s', [StoreInstr, ElemVal, ElemPtr]));
end;

function TCodeGenQBE.EmitSetLiteralExpr(AExpr: TArrayLiteralExpr): string;
var
  Mask:   Int64;
  I:      Integer;
  Elem:   TASTExpr;
  IdExpr: TIdentExpr;
  Tmp:    string;
  QT:     string;
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
    Mask := Mask or (Int64(1) shl IdExpr.ConstValue);
  end;
  Tmp := AllocTemp();
  QT := QbeTypeOf(AExpr.ResolvedType);
  EmitLine(Format('  %s =%s copy %s', [Tmp, QT, IntToStr(Mask)]));
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
    Exit(EmitSetLiteralExpr(AExpr));
  end;

  OAType   := TOpenArrayTypeDesc(AExpr.ResolvedType);
  ElemType := OAType.ElementType;
  ElemSize := ElemType.ByteSize();
  TotalBytes := AExpr.Elements.Count * ElemSize;
  if TotalBytes < 1 then TotalBytes := 1;
  case ElemType.Kind of
    tyString, tyClass, tyPointer, tyPChar, tyInt64, tyUInt64, tyMetaClass:
    begin
      AllocInstr := 'alloc8';
      StoreInstr := 'storel';
    end;
  else
    AllocInstr := 'alloc4';
    StoreInstr := 'storew';
  end;
  BufPtr := AllocTemp();
  EmitLine(Format('  %s =l %s %d', [BufPtr, AllocInstr, TotalBytes]));
  for I := 0 to AExpr.Elements.Count - 1 do
  begin
    ElemVal := EmitExpr(TASTExpr(AExpr.Elements.Items[I]));
    if I = 0 then
      EmitLine(Format('  %s %s, %s', [StoreInstr, ElemVal, BufPtr]))
    else
    begin
      Offset  := AllocTemp();
      ElemPtr := AllocTemp();
      EmitLine(Format('  %s =l copy %d', [Offset, I * ElemSize]));
      EmitLine(Format('  %s =l add %s, %s', [ElemPtr, BufPtr, Offset]));
      EmitLine(Format('  %s %s, %s', [StoreInstr, ElemVal, ElemPtr]));
    end;
  end;
  Result := BufPtr;
end;

end.
