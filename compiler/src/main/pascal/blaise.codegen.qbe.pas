{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.qbe;

{ QBE IR emitter for Blaise.
  WriteLn/Write are built-ins emitted as calls to _SysWriteStr/_SysWriteInt/
  _SysWriteInt64/_SysWriteBool/_SysWriteNewline (rtl.platform.posix.pas).
  Records are stack-allocated; field access uses pointer arithmetic. }

interface

uses
  SysUtils, StrUtils, Classes, uAST, uSymbolTable, uStrCompat, blaise.codegen,
  blaise.codegen.arcshapes,
  blaise.codegen.target, uDebugFacts;

// Raw byte copy used by TIRBuffer — maps to libc memcpy.
// Blaise links blaise_rtl.a which already pulls in libc.
procedure _ir_memcpy(Dst, Src: Pointer; N: Int64); external name 'memcpy';

type
  ECodeGenError = class(Exception);

  { TConstArgMode — caller-side protection mode for a const-string argument —
    now lives in blaise.codegen.arcshapes (shared with the native backend);
    see ConstArgMode for the classification rules. }

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
    FCurrentUnitName:  string;
    FProgramName: string;     { set by Generate/AppendProgram — program-scope
                                classes keep bare symbol names (no unit prefix),
                                matching uSemantic.CurrentUnitPrefix }       { name of the unit/program being emitted }
    { mem2reg: parallel lists tracking which locals are promoted SSA temps.
      FPromotedLocals[i] = var name; FPromotedTypes[i] = QBE type ('w','l','d','s').
      Cleared at the start of each function by EmitVarAllocs. }
    FPromotedLocals: TStringList;
    FPromotedTypes:  TStringList;
    { Locals/params of the function being emitted that are NOT safe to pass
      borrowed to a const-string param: their address escapes (explicit @,
      passed to a var/out param, or captured by a nested procedure), so a
      callee could release the buffer through the alias mid-call.  Rebuilt
      by EmitVarAllocs for every function; consulted by ConstArgMode. }
    FConstArgUnsafe: TStringList;

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

    { Obj temps of owned (+1) interface pairs materialised by
      EmitInterfaceExprPair for call-shaped sources (a function or itab call
      returning an interface used as receiver or argument).  The dispatch
      site that consumed the pair captures a mark before evaluating its
      receiver/args and flushes the releases right after its call
      instruction — the object must stay alive across the call. }
    FPendingObjReleases: TStringList;

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
    function  IntfObjAddr(const AName: string; AIsGlobal, AIsVarParam: Boolean): string;
    function  IntfItabAddr(const AName: string; AIsGlobal, AIsVarParam: Boolean): string;
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
    { 'export data ' when OPDF-debug mode is on (so the .opdf section can
      reference the vtable across object files), else plain 'data '. }
    function  VTableDataPrefix: string;
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
    { True for inline-aggregate value types whose "value" in QBE is the
      ADDRESS of their storage (not a loaded register): records, static arrays,
      and JUMBO (>64-member) sets.  Used at the read/arg/return sites that must
      return a storage address rather than a loaded scalar. }
    function  IsAggregateAddrType(AType: TTypeDesc): Boolean;
    { mem2reg helpers }
    { Returns True if AKind is a scalar type promotable to a QBE SSA temp. }
    function  IsPromotableKind(AKind: TTypeKind): Boolean;
    { Returns the QBE value type ('w','l','d','s') for a promotable kind. }
    function  PromotedQType(AKind: TTypeKind; AType: TTypeDesc): string;
    { CollectAddressTaken and its stmt/expr walkers live in
      blaise.codegen.arcshapes (shared with the native backend). }
    { Returns True if ABlock contains any try/finally or try/except statement
      (recursively).  Promoted locals are unsafe across setjmp/longjmp. }
    function  BlockHasTry(ABlock: TBlock): Boolean;
    function  StmtHasTry(AStmt: TASTStmt): Boolean;
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
    procedure EmitGlobalVarInit(const AVarName: string; AType: TTypeDesc;
                                CD: TConstDecl; const APrefix: string);
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
    { Returns True when a catchable EDivByZero can be raised, i.e. SysUtils
      (which declares EDivByZero + _RaiseDivByZero) is in scope.  When False
      the div/mod guard is omitted and a zero divisor traps in hardware. }
    function  DivGuardAvailable(): Boolean;
    { Emit a divisor==0 check before an integer div/rem.  ADivisor is the QBE
      temp holding the right operand; AIsLong selects l vs w comparison. }
    procedure EmitDivZeroGuard(const ADivisor: string; AIsLong: Boolean);
    procedure EmitCompoundStmt(AStmt: TCompoundStmt);
    procedure EmitAssignment(AAssign: TAssignment);
    procedure EmitFieldAssignment(AAssign: TFieldAssignment);
    function  EmitFloatArg(AExpr: TASTExpr; out AQType: string): string;
    function  EmitFloatArgAsDouble(AExpr: TASTExpr): string;
    procedure EmitFieldElemStore(AAssign: TFieldAssignment;
      const AFieldPtr: string);
    procedure EmitMethodCall(ACall: TMethodCallStmt);
    { After a call, release any value-argument temporaries that carried a
      +1-owned reference (function/property/method returns passed directly).
      The callee took ownership via its parameter-entry AddRef and releases
      at scope exit, so the caller's temporary would otherwise leak.
      AArgs and AArgTemps are parallel: AArgTemps.Strings[i] is the temp for
      AArgs.Items[i], or '' if that arg was not a value temp (e.g. var param). }
    procedure EmitOwnedArgReleases(AArgs: TObjectList; AArgTemps: TStringList;
      AParams: TObjectList);
    { Caller-side protection for const-string params.  A const param skips
      the callee-side _StringAddRef/_StringRelease pair (5a5b5d4), so the
      caller must keep the argument alive for the duration of the call.
      ConstArgMode classifies by argument shape:

        camBorrowed — string literals and named string consts: immortal
                      data, no ARC ops are emitted at all.
        camConsume  — +1 owned temps (function/method/getter returns): no
                      AddRef; the single post-call Release consumes the
                      transferred reference (these previously leaked).
        camBorrowed — also plain non-captured, non-address-taken local and
                      by-value/const parameter variables: the frame's own
                      reference outlives the call (unless the signature has
                      a var/out string param that could alias — then pin).
        camPin      — everything aliasable or unowned: globals, fields,
                      var-param reads, captured or address-taken locals,
                      rc=0 concat results — AddRef before, Release after. }
    function  ConstArgMode(AArg: TASTExpr; AParams: TObjectList): TConstArgMode;
    procedure EnsureConstStringRef(const AArgTemp: string; APar: TMethodParam;
      AArg: TASTExpr; AParams: TObjectList);
    procedure ReleaseConstStringArgs(AArgs: TObjectList;
      AArgTemps: TStringList; AParams: TObjectList);
    procedure EmitInheritedCall(ACall: TInheritedCallStmt);
    function  EmitInheritedCallExpr(ACall: TInheritedCallExpr): string;
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
      out AObjTemp, AItabTemp: string; AIntfType: TTypeDesc = nil);
    { Emit AExpr as an interface argument and return the ', l %obj, l %itab'
      call-argument fragment.  Wraps EmitInterfaceExprPair so the method-call
      arg loops can pass an interface param as the two-slot fat pointer the
      callee now expects, without each site declaring extra temps.  AIntfType
      is the target interface type (the param's type); needed when AExpr is a
      class instance being narrowed to that interface, to pick its itab. }
    function  InterfaceArgFragment(AExpr: TASTExpr;
      AIntfType: TTypeDesc = nil): string;
    function  OpenArrayArgFragment(AArg: TASTExpr): string;
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
    function  EmitConstArrayLiteral(AExpr: TArrayLiteralExpr): string;
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
    { Interface-dispatched (itab) call whose return type is an interface:
      the callee writes the fat pointer through a hidden first sret arg.
      ACall is a TMethodCallExpr (args form) or a TFieldAccessExpr with
      IsInterfaceCall set (zero-arg form). }
    procedure EmitIntfSretDispatch(ACall: TASTExpr; const ASretAddr: string);
    { Call target for a record/interface-returning method call: when the
      method is virtual, emit the vptr + slot loads and return the loaded
      function-pointer temp; otherwise return the static '$' symbol.
      ASelfTemp must already hold the receiver instance pointer. }
    function SretMethodCallTarget(AMDecl: TMethodDecl;
      const ASelfTemp, AMethName: string): string;
    { Build the visible-argument fragment (', t %a, ...') for an itab
      dispatch site.  No TMethodParam list exists there — only the var-param
      flags recorded on the interface descriptor and each argument's
      resolved type — so: var/out positions pass the slot address, interface
      args pass both fat-pointer slots, records use the aggregate FFI type,
      and scalars use their natural QBE type. }
    function  IntfDispatchArgFragment(AIntfDesc: TInterfaceTypeDesc;
      AMethIdx: Integer; AArgs: TObjectList): string;
    { Deferred releases for owned interface pairs produced while building a
      call (see FPendingObjReleases).  Capture the mark before evaluating
      receiver/args, flush right after the call instruction. }
    function  PendingReleaseMark(): Integer;
    procedure FlushPendingReleases(AMark: Integer);
    procedure EmitRecordReturnCallSite(const AFuncName, AVisibleArgs: string;
                                       ARetType: TRecordTypeDesc;
                                       const ADestAddr: string);
    function  ClassifyRecordReturn(ARec: TRecordTypeDesc): TRecReturnClass;
    function  IsRecordManagedClean(ARec: TRecordTypeDesc): Boolean;
    function  IsRecordAllIntegerLeaves(ARec: TRecordTypeDesc): Boolean;
    function  IsRecordAllFloatLeaves(ARec: TRecordTypeDesc): Boolean;
    function  IsRecordAllIntOrFloatLeaves(ARec: TRecordTypeDesc): Boolean;
    function  EightbyteIsSSE(ARec: TRecordTypeDesc;
                             AStartByte: Integer): Boolean;
    procedure EmitRecordReturnSignature(var ASig: string;
                                        AClass: TRecReturnClass);
    procedure EmitRecordReturnPrologue(ARetRec: TRecordTypeDesc;
                                       AClass: TRecReturnClass);
    procedure EmitRecordReturnEpilogue(ARetRec: TRecordTypeDesc;
                                       AClass: TRecReturnClass);
    function  EmitRecordReturnDeclType(ARetRec: TRecordTypeDesc;
                                       AClass: TRecReturnClass): string;
    { Emit a field-by-field ARC-aware copy from ASrcAddr to ADestAddr for a
      record described by ARec.  String fields use AddRef/Release; class fields
      use ClassAddRef/ClassRelease; other fields are copied with a plain store. }
    procedure EmitRecordCopy(ARec: TRecordTypeDesc;
                             const ADestAddr, ASrcAddr: string);
    { Returns True if AExpr is a function or method call that returns a record.
      Used in EmitAssignment to choose the sret path over a storel. }
    function  IsRecordCall(AExpr: TASTExpr): Boolean;
    { Returns True if AExpr is a function or method call that returns an
      interface.  Used in EmitAssignment to choose the sret path. }
    function  IsInterfaceCall(AExpr: TASTExpr): Boolean;
    { Release every ARC-managed field of a record at AAddr in-line (no copy).
      Used before overwriting a record slot to prevent reference leaks. }
    procedure EmitRecordReleaseFields(ARec: TRecordTypeDesc; const AAddr: string);
    { Mirror of EmitRecordReleaseFields: AddRef every ARC-managed field of a
      record at AAddr.  Used in the by-value record param prologue so the
      callee owns retains on managed-field contents, balancing the matching
      EmitRecordReleaseFields call on exit. }
    procedure EmitRecordAddRefFields(ARec: TRecordTypeDesc; const AAddr: string);
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
    function  FlattenRecordToAggLetters(ARec: TRecordTypeDesc): string;
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
    { Compute the QBE call target for a property accessor.  When AVSlot >= 0
      the accessor is virtual: emit the vptr+slot loads and return the
      function-pointer temp.  Otherwise return the static mangled symbol
      $<prefix><Owner>_<Method>.  The slot is computed by the semantic pass
      (PropAccessorVSlot) so codegen needs no symbol-table access.  Each call
      site then emits its own `call <target>(...)` with the right signature. }
    function  PropAccessorTarget(const AOwnerType, AMethod: string;
      AVSlot: Integer; ASelfTemp: string): string;
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
    FOpdfMode:  Boolean;
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
    procedure SetOpdfMode(AEnabled: Boolean);
    function  GetDebugFacts: TDbgFacts;
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
  FConstArgUnsafe  := TStringList.Create();
  FConstArgUnsafe.CaseSensitive := True;
  FConstArgUnsafe.Sorted := True;
  FConstArgUnsafe.Duplicates := dupIgnore;
  FPromotedTypes   := TStringList.Create();
  FArcSlotWritten  := TStringList.Create();
  FArcSlotWritten.CaseSensitive := True;
  FPendingObjReleases := TStringList.Create();
  FPendingObjReleases.CaseSensitive := True;
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
  FConstArgUnsafe.Free();
  FPromotedTypes.Free();
  FArcSlotWritten.Free();
  FPendingObjReleases.Free();
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
  { OPDF mode exports every function symbol: the .opdf companion object is
    assembled separately and its scope records reference function labels —
    local symbols would fail to link (same rationale as VTableDataPrefix). }
  if FExportAll or FOpdfMode then
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
{ Operand strings ADDRESSING an interface variable's obj / itab slots.
  Plain locals and globals use split slots Name_obj / Name_itab.  A var/out
  parameter's single slot holds the address of the caller's contiguous
  16-byte fat pointer — obj at +0, itab at +8 — so the address is computed
  with a load (and an add for the itab half). }
function TCodeGenQBE.IntfObjAddr(const AName: string; AIsGlobal, AIsVarParam: Boolean): string;
begin
  if AIsVarParam then
  begin
    Result := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [Result, VarRef(AName, False)]));
  end
  else
    Result := VarRef(AName, AIsGlobal) + '_obj';
end;

function TCodeGenQBE.IntfItabAddr(const AName: string; AIsGlobal, AIsVarParam: Boolean): string;
var
  P: string;
begin
  if AIsVarParam then
  begin
    P := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [P, VarRef(AName, False)]));
    Result := AllocTemp();
    EmitLine(Format('  %s =l add %s, 8', [Result, P]));
  end
  else if AIsGlobal then
  begin
    { Global interface data is ONE 16-byte item $Name_obj; the itab half
      lives at +8 — there is no $Name_itab symbol. }
    Result := AllocTemp();
    EmitLine(Format('  %s =l add %s_obj, 8', [Result, VarRef(AName, True)]));
  end
  else
    Result := VarRef(AName, AIsGlobal) + '_itab';
end;

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
  { RTL one-time setup the per-unit init dispatch below misses for archive
    units (e.g. blaise_weak's WeakMutex — see _BlaiseInit). }
  EmitLine('  call $_BlaiseInit()');
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
    tyInterface:                            Result := 'l';  { obj pointer (fat-pointer first slot) }
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
  { Jumbo set: passed by pointer to its bitmap (the callee copies it into a
    local slot for value semantics). }
  else if (AType <> nil) and (AType.Kind = tySet) and
          TSetTypeDesc(AType).IsJumbo() then
    Result := 'l'
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

function TCodeGenQBE.FlattenRecordToAggLetters(ARec: TRecordTypeDesc): string;
var
  I:   Integer;
  F:   TFieldInfo;
  Sub: string;
begin
  Result := '';
  if ARec = nil then Exit;
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Items[I]);
    if F.TypeDesc.Kind = tyRecord then
      Sub := Self.FlattenRecordToAggLetters(TRecordTypeDesc(F.TypeDesc))
    else
      Sub := QbeAggFieldType(F.TypeDesc);
    if Sub = '' then Exit('');
    if Result <> '' then Result := Result + ', ';
    Result := Result + Sub;
  end;
end;

procedure TCodeGenQBE.EmitFFIRecordTypeDecls;
var
  I:    Integer;
  R:    TRecordTypeDesc;
  Frag: string;
begin
  for I := 0 to FFFIRecordTypes.Count - 1 do
  begin
    R := TRecordTypeDesc(FFFIRecordTypes.Objects[I]);
    if FFFIRecordEmitted.IndexOf(R.Name) >= 0 then Continue;
    Frag := FlattenRecordToAggLetters(R);
    if Frag <> '' then
      EmitLine(Format('type :_ffi_%s = align %d { %s }',
        [R.Name, R.AllocAlign(), Frag]))
    else
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

function TCodeGenQBE.IsAggregateAddrType(AType: TTypeDesc): Boolean;
begin
  if AType = nil then Exit(False);
  Result := (AType.Kind in [tyRecord, tyStaticArray]) or
            ((AType.Kind = tySet) and TSetTypeDesc(AType).IsJumbo());
end;

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
  { Rebuild the borrowed-arg blocklist for this function: address-taken
    locals (explicit @, var/out args) plus anything captured by a nested
    procedure.  Computed unconditionally — ConstArgMode needs it even when
    the try-block guard below skips mem2reg promotion. }
  FConstArgUnsafe.Clear();
  AddrTaken := CollectAddressTaken(ABlock);
  for I := 0 to AddrTaken.Count - 1 do
    FConstArgUnsafe.Add(AddrTaken.Strings[I]);
  AddrTaken.Free();
  if ABlock <> nil then
    for I := 0 to ABlock.ProcDecls.Count - 1 do
      if TMethodDecl(ABlock.ProcDecls.Items[I]).CapturedVars <> nil then
        for J := 0 to TMethodDecl(ABlock.ProcDecls.Items[I]).CapturedVars.Count - 1 do
          FConstArgUnsafe.Add(
            TMethodDecl(ABlock.ProcDecls.Items[I]).CapturedVars.Strings[J]);
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
            { Jumbo (>64-member) sets are inline byte-array aggregates, not
              register values — promoting one to a single SSA temp would
              silently truncate it to 8 bytes. }
            if (Decl.ResolvedType.Kind = tySet) and
               TSetTypeDesc(Decl.ResolvedType).IsJumbo() then
              IsMethodPtr := True;
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
            else if TSetTypeDesc(Decl.ResolvedType).BitCount <= 64 then
            begin
              EmitLine(Format('  %%_var_%s =l alloc8 1', [VarName]));
              EmitLine(Format('  storel 0, %%_var_%s', [VarName]));
            end
            else
            begin
              { Jumbo set: inline byte-array bitmap, zero-init via memset (like
                a static array). }
              ArrSize := TSetTypeDesc(Decl.ResolvedType).RawSize();
              EmitLine(Format('  %%_var_%s =l alloc8 %d', [VarName, ArrSize]));
              EmitLine(Format('  call $memset(l %%_var_%s, w 0, l %d)',
                [VarName, ArrSize]));
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
            { Interface var = fat pointer: ONE contiguous 16-byte block —
              obj at +0, itab at +8 — so its base address can be passed to
              a var/out interface parameter.  Both halves nil-init. }
            EmitLine(Format('  %%_var_%s_obj  =l alloc8 16', [VarName]));
            EmitLine(Format('  %%_var_%s_itab =l add %%_var_%s_obj, 8',
              [VarName, VarName]));
            EmitLine(Format('  storel 0, %%_var_%s_obj',    [VarName]));
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
      { Initialised global: emit the folded value into the data section instead
        of a zero slot.  threadvars cannot carry a non-zero static initialiser
        (they live in .tbss), so the parser/semantic restrict initialisers to
        non-threadvar globals — assert by falling through to the zero path. }
      if (Decl.InitConst <> nil) and not Decl.IsThreadVar then
      begin
        Self.EmitGlobalVarInit(VarName, Decl.ResolvedType, Decl.InitConst, Pfx);
        Continue;
      end;
      case Decl.ResolvedType.Kind of
        tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum:
          EmitLine(Format('%s $%s = { w 0 }', [Pfx, VarName]));
        tySmallInt, tyWord:
          EmitLine(Format('%s $%s = { h 0 }', [Pfx, VarName]));
        tySet:
          if TSetTypeDesc(Decl.ResolvedType).BitCount <= 32 then
            EmitLine(Format('%s $%s = { w 0 }', [Pfx, VarName]))
          else if TSetTypeDesc(Decl.ResolvedType).BitCount <= 64 then
            EmitLine(Format('%s $%s = { l 0 }', [Pfx, VarName]))
          else
            { Jumbo set: zero-filled inline byte-array bitmap. }
            EmitLine(Format('%s $%s = { z %d }',
              [Pfx, VarName, TSetTypeDesc(Decl.ResolvedType).RawSize()]));
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
          { ONE contiguous 16-byte fat pointer: obj at +0, itab at +8.
            Itab accesses compute $Name_obj + 8 (IntfItabAddr) — keeping a
            separate $Name_itab item would not be adjacent, which breaks
            passing the variable to a var/out interface parameter. }
          EmitLine(Format('%s $%s_obj = { l 0, l 0 }', [Pfx, VarName]));
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

{ Emit an initialised global variable's data slot from its folded const value.
  Scalar/string/enum/boolean/real values become a single typed field; static
  array values become an inline element list (same layout as array consts).
  APrefix is the QBE storage prefix ('export data' / 'export thread data'). }
procedure TCodeGenQBE.EmitGlobalVarInit(const AVarName: string; AType: TTypeDesc;
  CD: TConstDecl; const APrefix: string);
var
  J:          Integer;
  Parts:      string;
  StrIdx:     Integer;
  IsStrArray: Boolean;
  ElemKind:   TTypeKind;
  ElemSig:    string;
  SAT:        TStaticArrayTypeDesc;
begin
  { Static array initialiser: inline element list. }
  if (AType.Kind = tyStaticArray) and CD.IsArrayConst then
  begin
    SAT := TStaticArrayTypeDesc(AType);
    ElemKind := SAT.ElementType.Kind;
    IsStrArray := ElemKind = tyString;
    if IsStrArray then
    begin
      for J := 0 to CD.ArrayElements.Count - 1 do
        if FStrLits.IndexOf(CD.ArrayElements[J]) < 0 then
          FStrLits.Add(CD.ArrayElements[J]);
      EmitPendingStrLits();
    end;
    { Per-element QBE field sigil by element width. }
    case ElemKind of
      tyByte, tyBoolean:           ElemSig := 'b';
      tySmallInt, tyWord:          ElemSig := 'h';
      tyInteger, tyUInt32, tyEnum: ElemSig := 'w';
      tyInt64, tyUInt64, tyString, tyPointer, tyPChar: ElemSig := 'l';
      tyDouble:                    ElemSig := 'd';
      tySingle:                    ElemSig := 's';
    else
      ElemSig := 'w';
    end;
    Parts := '';
    for J := 0 to CD.ArrayElements.Count - 1 do
    begin
      if J > 0 then Parts := Parts + ', ';
      if IsStrArray then
      begin
        StrIdx := FStrLits.IndexOf(CD.ArrayElements[J]);
        Parts := Parts + Format('l $__s%d + 12', [StrIdx]);
      end
      else
        Parts := Parts + Format('%s %s', [ElemSig, CD.ArrayElements[J]]);
    end;
    EmitLine(Format('%s $%s = { %s }', [APrefix, AVarName, Parts]));
    Exit;
  end;

  { String scalar: point at an immortal static string header ($__sN + 12). }
  if AType.IsString() then
  begin
    if FStrLits.IndexOf(CD.StrVal) < 0 then
      FStrLits.Add(CD.StrVal);
    EmitPendingStrLits();
    StrIdx := FStrLits.IndexOf(CD.StrVal);
    EmitLine(Format('%s $%s = { l $__s%d + 12 }', [APrefix, AVarName, StrIdx]));
    Exit;
  end;

  { Scalar numeric / boolean / enum / real. }
  case AType.Kind of
    tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum:
      EmitLine(Format('%s $%s = { w %d }', [APrefix, AVarName, CD.IntVal]));
    tySmallInt, tyWord:
      EmitLine(Format('%s $%s = { h %d }', [APrefix, AVarName, CD.IntVal]));
    tyInt64, tyUInt64:
      EmitLine(Format('%s $%s = { l %d }', [APrefix, AVarName, CD.IntVal]));
    tyPointer, tyPChar:
      EmitLine(Format('%s $%s = { l %d }', [APrefix, AVarName, CD.IntVal]));
    tyDouble:
      EmitLine(Format('%s $%s = { d d_%s }', [APrefix, AVarName, CD.StrVal]));
    tySingle:
      EmitLine(Format('%s $%s = { s s_%s }', [APrefix, AVarName, CD.StrVal]));
  else
    { Unsupported kinds are rejected in semantic; emit a zero slot defensively. }
    EmitLine(Format('%s $%s = { l 0 }', [APrefix, AVarName]));
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
  { Jumbo set constant: emit the bitmap as a byte blob under the mangled label.
    Shares the const-data pass with array consts. }
  if (CD.ConstSetBytes <> nil) and (CD.ConstSetBytes.Count > 0) then
  begin
    if APrefix <> '' then
      Label_ := APrefix + '_' + CD.Name
    else if CD.ResolvedSetQbeName <> '' then
      Label_ := CD.ResolvedSetQbeName
    else
      Label_ := CD.Name;
    Parts := '';
    for J := 0 to CD.ConstSetBytes.Count - 1 do
    begin
      if J > 0 then Parts := Parts + ', ';
      Parts := Parts + Format('b %s', [CD.ConstSetBytes[J]]);
    end;
    if APrefix <> '' then
      EmitLine(Format('export data $%s = { %s }', [Label_, Parts]))
    else
      EmitLine(Format('data $%s = { %s }', [Label_, Parts]));
    Exit;
  end;
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
    them here would nil variables that the outer except handler still reads.

    Restore codegen-time FExcDepth/FFinallyStack to the try-entry level first:
    both paths are emitted sequentially but are runtime alternatives, so each
    must balance the bookkeeping independently.  Without this the second and
    later try blocks in a function are emitted with FExcDepth one too low and
    a non-local exit inside them skips the frame pop (stale g_exc_top → crash
    on the next raise). }
  Inc(FExcDepth);
  FFinallyStack.Add(AStmt.FinallyBody);
  EmitLine('@' + LblFinExc);
  ExcTemp := AllocTemp();
  EmitLine(Format('  %s =l call $_CurrentException()', [ExcTemp]));
  EmitLine('  call $_PopExcFrame()');
  Dec(FExcDepth);
  FFinallyStack.Delete(FFinallyStack.Count - 1);
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
  ExtTemp:    string;
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

  { Exception path: capture exception before popping frame, then pop.
    Restore codegen-time FExcDepth/FFinallyStack to the try-entry level first:
    both paths are emitted sequentially but are runtime alternatives, so each
    must balance the bookkeeping independently (see EmitTryFinallyStmt). }
  Inc(FExcDepth);
  FFinallyStack.Add(nil);
  EmitLine('@' + LblExcept);

  if AStmt.Handlers.Count > 0 then
  begin
    { Capture current exception while frame is still on the stack (g_exc_top
      points to our frame, so _CurrentException returns its exception field). }
    ExcTemp := AllocTemp();
    EmitLine(Format('  %s =l call $_CurrentException()', [ExcTemp]));
    EmitLine('  call $_PopExcFrame()');
    Dec(FExcDepth);
    FFinallyStack.Delete(FFinallyStack.Count - 1);

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
          otherwise retained).  Release any PRIOR binding first — the slot is
          shared by every same-named handler in the function. }
        ExtTemp := AllocTemp();
        EmitLine(Format('  %s =l loadl %%_var_%s', [ExtTemp, H.VarName]));
        EmitLine(Format('  call $_ClassAddRef(l %s)', [ExcTemp]));
        EmitLine(Format('  call $_ClassRelease(l %s)', [ExtTemp]));
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
    FFinallyStack.Delete(FFinallyStack.Count - 1);
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

function TCodeGenQBE.DivGuardAvailable(): Boolean;
begin
  { EDivByZero is declared in SysUtils.  If it resolves through the active
    symbol table, SysUtils is in scope and $SysUtils_RaiseDivByZero is
    linkable, so the guard can raise a catchable exception.  Otherwise the
    divisor-zero path must fall through to the hardware trap. }
  Result := (FSymTable <> nil) and (FSymTable.Lookup('EDivByZero') <> nil);
end;

procedure TCodeGenQBE.EmitDivZeroGuard(const ADivisor: string; AIsLong: Boolean);
var
  CmpTemp:  string;
  RaiseLbl: string;
  OkLbl:    string;
begin
  if not Self.DivGuardAvailable() then
    Exit;
  CmpTemp  := AllocTemp();
  RaiseLbl := AllocLabel('divzero_raise');
  OkLbl    := AllocLabel('divzero_ok');
  if AIsLong then
    EmitLine(Format('  %s =w ceql %s, 0', [CmpTemp, ADivisor]))
  else
    EmitLine(Format('  %s =w ceqw %s, 0', [CmpTemp, ADivisor]));
  EmitLine(Format('  jnz %s, @%s, @%s', [CmpTemp, RaiseLbl, OkLbl]));
  EmitLine(Format('@%s', [RaiseLbl]));
  EmitLine('  call $SysUtils__RaiseDivByZero()');
  { _RaiseDivByZero longjmps and never returns; the jmp keeps QBE happy by
    giving the block a terminator. }
  EmitLine(Format('  jmp @%s', [OkLbl]));
  EmitLine(Format('@%s', [OkLbl]));
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
    CmpT := AllocTemp();
    if AStmt.SetIsJumbo then
      { Jumbo: MaskT is the set's bitmap address; test membership via _SetIn. }
      EmitLine(Format('  %s =w call $_SetIn(l %s, w %s)', [CmpT, MaskT, IdxW]))
    else
    begin
      EmitLine(Format('  %s =%s shr %s, %s', [BitT, SetMQT, MaskT, IdxW]));
      EmitLine(Format('  %s =w and %s, 1', [CmpT, BitT]));
    end;
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

  { Move the enumerator into the synthetic slot.  GetEnumerator's
    result is an owned +1 (constructor/call result) — transfer it; an
    extra AddRef leaks one enumerator per loop because the function
    epilogue releases the slot exactly once. }
  OldT := AllocTemp();
  EmitLine(Format('  %s =l loadl %s', [OldT, EnumSlot]));
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

{ True when the expression produces a fresh sret record temporary that
  nothing else holds — i.e. a record-returning function/method call.  A
  plain variable reference (record-typed TIdentExpr) is NOT a temp: its
  storage belongs to the enclosing scope and must not be cleaned up here. }
function IsRecordSretTempExpr(AExpr: TASTExpr): Boolean;
begin
  Result := False;
  if AExpr = nil then Exit;
  if AExpr.ResolvedType = nil then Exit;
  if AExpr.ResolvedType.Kind <> tyRecord then Exit;
  if AExpr is TFuncCallExpr then
    Result := TFuncCallExpr(AExpr).ResolvedDecl <> nil
  else if AExpr is TMethodCallExpr then
    Result := not TMethodCallExpr(AExpr).IsConstructorCall;
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
    { Record-typed sret temporary from an inline call (DoSomething(GetRec())):
      release each managed leaf of the temp buffer.  The buffer itself is
      stack-allocated and dies with the caller's frame, but its string /
      dynarray / class / interface fields hold heap refs that need balancing.
      Reg-returned (POD) records have no managed leaves, so the helper is
      a safe no-op in that case. }
    if IsRecordSretTempExpr(Arg) then
    begin
      EmitRecordReleaseFields(TRecordTypeDesc(Arg.ResolvedType),
        AArgTemps.Strings[I]);
      Continue;
    end;
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
function TCodeGenQBE.ConstArgMode(AArg: TASTExpr;
  AParams: TObjectList): TConstArgMode;
var
  I:  Integer;
  P:  TMethodParam;
  IE: TIdentExpr;
begin
  Result := camPin;
  if AArg = nil then Exit;
  if AArg is TStringLiteral then
    Exit(camBorrowed);
  if AArg is TIdentExpr then
  begin
    IE := TIdentExpr(AArg);
    if IE.IsImplicitSelfMethod then
      Exit(camConsume);   { bare zero-arg method call — +1 owned return }
    if IE.IsConstant then
      Exit(camBorrowed);  { named string const — immortal literal data }
    if (not IE.IsGlobal) and (IE.ParamMode = pmNone) and
       (IE.ImplicitFieldInfo = nil) and not IsCaptured(IE.Name) and
       (FConstArgUnsafe.IndexOf(IE.Name) < 0) then
    begin
      { Plain local / by-value or const param: the frame's own reference
        outlives the call.  One alias can still defeat that — a var/out
        STRING param in the same signature, F(const A: string; var B:
        string) called as F(L, L): the callee's write to B releases L's
        buffer while A borrows it.  Pin when the signature has one. }
      if AParams <> nil then
        for I := 0 to AParams.Count - 1 do
        begin
          P := TMethodParam(AParams.Items[I]);
          if P.IsVarParam and (P.ResolvedType <> nil) and
             P.ResolvedType.IsString() then
            Exit(camPin);
        end;
      Exit(camBorrowed);
    end;
    Exit(camPin);         { global, var-param read, implicit-Self field,
                            address-taken or nested-captured local }
  end;
  if ExprOwnsRef(AArg) then
    Exit(camConsume);     { function/method/getter return — +1 owned temp }
end;

procedure TCodeGenQBE.EnsureConstStringRef(const AArgTemp: string;
  APar: TMethodParam; AArg: TASTExpr; AParams: TObjectList);
begin
  if (APar = nil) or (AArgTemp = '') then Exit;
  if APar.IsConstParam and (APar.ResolvedType <> nil) and
     (APar.ResolvedType.Kind = tyString) then
  begin
    if ConstArgMode(AArg, AParams) = camPin then
      EmitLine(Format('  call $_StringAddRef(l %s)', [AArgTemp]));
  end;
end;

{ call $_StringRelease(l <ArgTemps[I]>) for each pinned or consumed
  const-string argument (borrowed args emitted no AddRef and need no
  Release; consumed args take ownership of the +1 temp here). }
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
    begin
      if ConstArgMode(TASTExpr(AArgs.Items[I]), AParams) <> camBorrowed then
        EmitLine(Format('  call $_StringRelease(l %s)',
          [AArgTemps.Strings[I]]));
    end;
  end;
end;

procedure TCodeGenQBE.EmitAssignment(AAssign: TAssignment);
var
  ValTemp, OldTemp, QType, StoreInstr, PtrTemp: string;
  ObjAddr, ItabAddr: string;
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
  SretBuf:   string;
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
    ObjAddr  := IntfObjAddr(AAssign.Name, AAssign.IsGlobal, AAssign.IsVarParam);
    ItabAddr := IntfItabAddr(AAssign.Name, AAssign.IsGlobal, AAssign.IsVarParam);
    if AAssign.IsWeakLhs then
      EmitLine(Format('  call $_WeakAssign(l %s, l %s)', [ObjAddr, ObjTemp]))
    else
    begin
      OldTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [OldTemp, ObjAddr]));
      EmitLine(Format('  call $_ClassAddRef(l %s)',  [ObjTemp]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
      EmitLine(Format('  storel %s, %s',  [ObjTemp, ObjAddr]));
    end;
    EmitLine(Format('  storel %s, %s', [ItabTemp, ItabAddr]));
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
    ObjAddr  := IntfObjAddr(AAssign.Name, AAssign.IsGlobal, AAssign.IsVarParam);
    ItabAddr := IntfItabAddr(AAssign.Name, AAssign.IsGlobal, AAssign.IsVarParam);
    if AAssign.IsWeakLhs then
      EmitLine(Format('  call $_WeakAssign(l %s, l %s)', [ObjAddr, ValTemp]))
    else
    begin
      OldTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [OldTemp, ObjAddr]));
      if not ExprOwnsRef(AAssign.Expr) then
        EmitLine(Format('  call $_ClassAddRef(l %s)',  [ValTemp]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
      EmitLine(Format('  storel %s, %s',  [ValTemp, ObjAddr]));
    end;
    EmitLine(Format('  storel %s, %s', [ItabName, ItabAddr]));
    Exit;
  end;

  { Interface := call returning an interface — the callee writes the fat
    pointer (obj+itab) into a caller-supplied 16-byte sret buffer.  Load both
    slots from the buffer and store into the LHS split slots with ARC.  This
    must run BEFORE the interface-to-interface branch below: a zero-arg
    interface-method call is a TFieldAccessExpr, which that branch would
    otherwise mistake for a plain field read. }
  if (AAssign.ResolvedLhsType <> nil) and
     (AAssign.ResolvedLhsType.Kind = tyInterface) and
     IsInterfaceCall(AAssign.Expr) then
  begin
    SretBuf := AllocTemp();
    EmitLine(Format('  %s =l alloc8 16', [SretBuf]));
    EmitLine(Format('  call $memset(l %s, w 0, l 16)', [SretBuf]));
    EmitRecordCallSret(AAssign.Expr, SretBuf);
    ObjTemp := AllocTemp();
    ItabTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [ObjTemp, SretBuf]));
    ValTemp := AllocTemp();
    EmitLine(Format('  %s =l add %s, 8', [ValTemp, SretBuf]));
    EmitLine(Format('  %s =l loadl %s', [ItabTemp, ValTemp]));
    ObjAddr  := IntfObjAddr(AAssign.Name, AAssign.IsGlobal, AAssign.IsVarParam);
    ItabAddr := IntfItabAddr(AAssign.Name, AAssign.IsGlobal, AAssign.IsVarParam);
    if AAssign.IsWeakLhs then
      EmitLine(Format('  call $_WeakAssign(l %s, l %s)', [ObjAddr, ObjTemp]))
    else
    begin
      { The callee returns an OWNED +1 fat pointer — no caller AddRef. }
      OldTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [OldTemp, ObjAddr]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
      EmitLine(Format('  storel %s, %s', [ObjTemp, ObjAddr]));
    end;
    EmitLine(Format('  storel %s, %s', [ItabTemp, ItabAddr]));
    Exit;
  end;

  { Interface-to-interface direct assignment: F := G where both sides are
    interface-typed.  Copy obj and itab from G's fat pointer to F's; for
    strong F, retain the backing object and release F's prior obj ref;
    for weak F, route the obj through _WeakAssign.

    The source may be a plain interface local/global (split _obj/_itab slots) or
    an interface stored in a record/class field (a contiguous fat pointer).
    EmitInterfaceExprPair resolves obj/itab for every supported source shape
    (TIdentExpr, implicit-Self field, as-cast, TFieldAccessExpr) — without it a
    TFieldAccessExpr source (G := H.G) fell through to the scalar store path and
    emitted a bogus single-slot `storew ..., $F` against a name that has no
    `$F` data definition (only `$F_obj`/`$F_itab`). }
  if (AAssign.ResolvedLhsType <> nil) and
     (AAssign.ResolvedLhsType.Kind = tyInterface) and
     (AAssign.Expr.ResolvedType <> nil) and
     (AAssign.Expr.ResolvedType.Kind = tyInterface) and
     ((AAssign.Expr is TIdentExpr) or
      (AAssign.Expr is TFieldAccessExpr) or
      (AAssign.Expr is TStringSubscriptExpr)) then
  begin
    EmitInterfaceExprPair(AAssign.Expr, ObjTemp, ItabTemp);
    ObjAddr  := IntfObjAddr(AAssign.Name, AAssign.IsGlobal, AAssign.IsVarParam);
    ItabAddr := IntfItabAddr(AAssign.Name, AAssign.IsGlobal, AAssign.IsVarParam);
    if AAssign.IsWeakLhs then
    begin
      EmitLine(Format('  call $_WeakAssign(l %s, l %s)', [ObjAddr, ObjTemp]));
      EmitLine(Format('  storel %s, %s', [ItabTemp, ItabAddr]));
      Exit;
    end;
    OldTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [OldTemp, ObjAddr]));
    EmitLine(Format('  call $_ClassAddRef(l %s)',  [ObjTemp]));
    EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
    EmitLine(Format('  storel %s, %s',  [ObjTemp, ObjAddr]));
    EmitLine(Format('  storel %s, %s', [ItabTemp, ItabAddr]));
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
    ObjAddr  := IntfObjAddr(AAssign.Name, AAssign.IsGlobal, AAssign.IsVarParam);
    ItabAddr := IntfItabAddr(AAssign.Name, AAssign.IsGlobal, AAssign.IsVarParam);
    if AAssign.IsWeakLhs then
      EmitLine(Format('  call $_WeakClear(l %s)', [ObjAddr]))
    else
    begin
      OldTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [OldTemp, ObjAddr]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
      EmitLine(Format('  storel 0, %s', [ObjAddr]));
    end;
    EmitLine(Format('  storel 0, %s', [ItabAddr]));
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
          (AAssign.ResolvedLhsType.Kind = tySet) and
          TSetTypeDesc(AAssign.ResolvedLhsType).IsJumbo() then
  begin
    { Jumbo set assignment: the RHS evaluates to the source bitmap address
      (a set variable, a set-op result buffer, or a const blob); copy the
      whole bitmap into the destination slot. }
    ValTemp := EmitExpr(AAssign.Expr);
    EmitLine(Format('  call $memcpy(l %s, l %s, l %d)',
      [VarRef(AAssign.Name, AAssign.IsGlobal), ValTemp,
       TSetTypeDesc(AAssign.ResolvedLhsType).RawSize()]));
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
      if Id.ParamMode <> pmNone then
      begin
        { var-param class ident: slot -> caller var -> instance. }
        Result := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [Result, Loaded]));
        Exit;
      end;
      Result := Loaded;
    end
    else if Id.ParamMode <> pmNone then
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
        if Fld.IsVarParam then
        begin
          { var-param class: the slot holds the ADDRESS of the caller's
            variable — load again to reach the instance pointer. }
          Base := AllocTemp();
          EmitLine(Format('  %s =l loadl %s', [Base, Loaded]));
        end
        else
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
  if AIdent.ParamMode <> pmNone then
  begin
    // The local slot holds the caller's pointer — load it so we pass the
    // original address, not the address of the local slot.
    Result := AllocTemp();
    EmitLine(Format('  %s =l loadl %%_var_%s', [Result, AIdent.Name]));
  end
  else if (AIdent.ResolvedType <> nil) and
          (AIdent.ResolvedType.Kind = tyInterface) then
  begin
    { Interface variable: the fat pointer lives in one contiguous 16-byte
      block (locals: one alloc; globals: one 16-byte data item) whose base
      is the _obj slot — that base IS the var-arg address. }
    Result := VarRef(AIdent.Name, AIdent.IsGlobal) + '_obj';
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
  AddrWrap: TAddrOfExpr;
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
        location adjacent to the slot itself.  A var-param class slot holds
        the ADDRESS of the caller's variable: load twice. }
      T := AllocTemp();
      EmitLine(Format('  %s =l loadl %s',
        [T, VarRef(FldAcc.RecordName, FldAcc.IsGlobal)]));
      if FldAcc.IsVarParam then
      begin
        BaseAddr := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [BaseAddr, T]));
      end
      else
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
  { Array element a[i] as a var/out actual — its address is what @a[i] would
    compute, so reuse EmitAddrOfExpr via a transient TAddrOfExpr wrapper. }
  if AExpr is TStringSubscriptExpr then
  begin
    AddrWrap := TAddrOfExpr.Create();
    try
      AddrWrap.Expr := AExpr;
      Result := EmitAddrOfExpr(AddrWrap);
    finally
      AddrWrap.Expr := nil;   { do not free AExpr — owned by the caller }
      AddrWrap.Free();
    end;
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

function TCodeGenQBE.IsInterfaceCall(AExpr: TASTExpr): Boolean;
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
              (MDecl.ResolvedReturnType.Kind = tyInterface);
  end
  else if AExpr is TMethodCallExpr then
  begin
    { Interface dispatch: ResolvedMethod is nil by design (the target is
      resolved through the itab); the call's own resolved type carries the
      interface method's return type. }
    if (TMethodCallExpr(AExpr).ResolvedClassType <> nil) and
       (TMethodCallExpr(AExpr).ResolvedClassType.Kind = tyInterface) then
    begin
      Result := (AExpr.ResolvedType <> nil) and
                (AExpr.ResolvedType.Kind = tyInterface);
      Exit;
    end;
    if TMethodCallExpr(AExpr).ResolvedMethod = nil then Exit;
    MDecl := TMethodDecl(TMethodCallExpr(AExpr).ResolvedMethod);
    Result := (MDecl.ResolvedReturnType <> nil) and
              (MDecl.ResolvedReturnType.Kind = tyInterface);
  end
  else if AExpr is TFieldAccessExpr then
  begin
    FldA := TFieldAccessExpr(AExpr);
    { Zero-arg interface method call through itab dispatch — same rule as
      the TMethodCallExpr interface-dispatch case above. }
    if FldA.IsInterfaceCall then
    begin
      Result := (AExpr.ResolvedType <> nil) and
                (AExpr.ResolvedType.Kind = tyInterface);
      Exit;
    end;
    if not FldA.IsMethodCall then Exit;
    if FldA.ResolvedMethod = nil then Exit;
    MDecl := TMethodDecl(FldA.ResolvedMethod);
    Result := (MDecl.ResolvedReturnType <> nil) and
              (MDecl.ResolvedReturnType.Kind = tyInterface);
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

function TCodeGenQBE.IsRecordManagedClean(ARec: TRecordTypeDesc): Boolean;
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

function TCodeGenQBE.IsRecordAllIntegerLeaves(ARec: TRecordTypeDesc): Boolean;
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

function TCodeGenQBE.IsRecordAllFloatLeaves(ARec: TRecordTypeDesc): Boolean;
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

function TCodeGenQBE.IsRecordAllIntOrFloatLeaves(ARec: TRecordTypeDesc): Boolean;
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

function TCodeGenQBE.EightbyteIsSSE(ARec: TRecordTypeDesc;
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

function TCodeGenQBE.ClassifyRecordReturn(ARec: TRecordTypeDesc): TRecReturnClass;
var
  Sz:               Integer;
  Eb0SSE, Eb1SSE:   Boolean;
begin
  Result := rcSret;
  if (ARec = nil) or (ARec.Kind <> tyRecord) then Exit;
  if ARec.Fields.Count = 0 then Exit;
  if not Self.IsRecordManagedClean(ARec) then Exit;
  Sz := ARec.TotalSize();

  if GTarget.OS = osWindows then
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

procedure TCodeGenQBE.EmitRecordReturnSignature(var ASig: string;
  AClass: TRecReturnClass);
begin
  case AClass of
    rcSret:
      begin
        if ASig <> '' then
          ASig := 'l %_par__sret, ' + ASig
        else
          ASig := 'l %_par__sret';
      end;
  end;
end;

procedure TCodeGenQBE.EmitRecordReturnPrologue(ARetRec: TRecordTypeDesc;
  AClass: TRecReturnClass);
begin
  case AClass of
    rcSret:
      EmitLine('  %_var_Result =l copy %_par__sret');
    rcInt1, rcInt2, rcSSE1, rcSSE2, rcIntSSE, rcSSEInt, rcWin64Agg:
      begin
        if ARetRec.MaxAlign() >= 8 then
          EmitLine(Format('  %%_var_Result =l alloc8 %d', [ARetRec.TotalSize()]))
        else
          EmitLine(Format('  %%_var_Result =l alloc4 %d', [ARetRec.TotalSize()]));
        if ARetRec.TotalSize() > 0 then
          EmitLine(Format('  call $memset(l %%_var_Result, w 0, l %d)',
            [ARetRec.TotalSize()]));
      end;
  end;
end;

function RecInt1LoadInstr(ASize: Integer): string;
begin
  case ASize of
    1: Result := 'loadub';
    2: Result := 'loaduh';
    4: Result := 'loaduw';
    8: Result := 'loadl';
  else
    Result := '';
  end;
end;

function RecInt1StoreInstr(ASize: Integer): string;
begin
  case ASize of
    1: Result := 'storeb';
    2: Result := 'storeh';
    4: Result := 'storew';
    8: Result := 'storel';
  else
    Result := '';
  end;
end;

function RecInt1RetType(ASize: Integer): string;
begin
  if ASize = 8 then Result := 'l' else Result := 'w';
end;

procedure TCodeGenQBE.EmitRecordReturnEpilogue(ARetRec: TRecordTypeDesc;
  AClass: TRecReturnClass);
var
  RetT, RetTy, LoadOp: string;
  Sz: Integer;
begin
  case AClass of
    rcSret:
      EmitLine('  ret');
    rcInt1:
      begin
        Sz     := ARetRec.TotalSize();
        RetTy  := RecInt1RetType(Sz);
        LoadOp := RecInt1LoadInstr(Sz);
        RetT   := AllocTemp();
        EmitLine(Format('  %s =%s %s %%_var_Result',
          [RetT, RetTy, LoadOp]));
        EmitLine(Format('  ret %s', [RetT]));
      end;
    rcInt2:
      EmitLine('  ret %_var_Result');
    rcSSE1:
      begin
        RetT := AllocTemp();
        if ARetRec.TotalSize() = 4 then
        begin
          EmitLine(Format('  %s =s loads %%_var_Result', [RetT]));
          EmitLine(Format('  ret %s', [RetT]));
        end
        else
        begin
          EmitLine(Format('  %s =d loadd %%_var_Result', [RetT]));
          EmitLine(Format('  ret %s', [RetT]));
        end;
      end;
    rcSSE2:
      EmitLine('  ret %_var_Result');
    rcIntSSE, rcSSEInt:
      EmitLine('  ret %_var_Result');
    rcWin64Agg:
      EmitLine('  ret %_var_Result');
  end;
end;

function TCodeGenQBE.EmitRecordReturnDeclType(ARetRec: TRecordTypeDesc;
  AClass: TRecReturnClass): string;
begin
  Result := '';
  case AClass of
    rcInt1:                                Result := RecInt1RetType(ARetRec.TotalSize());
    rcInt2, rcSSE2, rcIntSSE, rcSSEInt:    Result := FFIRecordTypeRef(ARetRec);
    rcSSE1:
      if ARetRec.TotalSize() = 4 then Result := 's' else Result := 'd';
    rcWin64Agg:                            Result := FFIRecordTypeRef(ARetRec);
  end;
end;

procedure TCodeGenQBE.EmitRecordReturnCallSite(
  const AFuncName, AVisibleArgs: string; ARetType: TRecordTypeDesc;
  const ADestAddr: string);
var
  ArgLine, RetT, AggRef: string;
  Sz: Integer;
begin
  { Jumbo set returns always use the plain sret path (a hidden dest pointer +
    void return); they share this call helper with records but must not go
    through ClassifyRecordReturn (which reads record-specific size fields). }
  if (ARetType <> nil) and (TTypeDesc(ARetType).Kind = tySet) then
  begin
    if AVisibleArgs <> '' then
      ArgLine := Format('l %s, %s', [ADestAddr, AVisibleArgs])
    else
      ArgLine := Format('l %s', [ADestAddr]);
    EmitLine(Format('  call %s(%s)', [AFuncName, ArgLine]));
    Exit;
  end;
  case Self.ClassifyRecordReturn(ARetType) of
    rcSret:
      begin
        if AVisibleArgs <> '' then
          ArgLine := Format('l %s, %s', [ADestAddr, AVisibleArgs])
        else
          ArgLine := Format('l %s', [ADestAddr]);
        EmitLine(Format('  call %s(%s)', [AFuncName, ArgLine]));
      end;
    rcInt1:
      begin
        Sz   := ARetType.TotalSize();
        RetT := AllocTemp();
        EmitLine(Format('  %s =%s call %s(%s)',
          [RetT, RecInt1RetType(Sz), AFuncName, AVisibleArgs]));
        EmitLine(Format('  %s %s, %s',
          [RecInt1StoreInstr(Sz), RetT, ADestAddr]));
      end;
    rcInt2, rcSSE2, rcIntSSE, rcSSEInt, rcWin64Agg:
      begin
        AggRef := FFIRecordTypeRef(ARetType);
        RetT   := AllocTemp();
        EmitLine(Format('  %s =%s call %s(%s)',
          [RetT, AggRef, AFuncName, AVisibleArgs]));
        EmitLine(Format('  call $memcpy(l %s, l %s, l %d)',
          [ADestAddr, RetT, ARetType.TotalSize()]));
      end;
    rcSSE1:
      begin
        RetT := AllocTemp();
        if ARetType.TotalSize() = 4 then
        begin
          EmitLine(Format('  %s =s call %s(%s)',
            [RetT, AFuncName, AVisibleArgs]));
          EmitLine(Format('  stores %s, %s', [RetT, ADestAddr]));
        end
        else
        begin
          EmitLine(Format('  %s =d call %s(%s)',
            [RetT, AFuncName, AVisibleArgs]));
          EmitLine(Format('  stored %s, %s', [RetT, ADestAddr]));
        end;
      end;
  end;
end;

function TCodeGenQBE.PendingReleaseMark(): Integer;
begin
  Result := FPendingObjReleases.Count;
end;

procedure TCodeGenQBE.FlushPendingReleases(AMark: Integer);
begin
  while FPendingObjReleases.Count > AMark do
  begin
    EmitLine(Format('  call $_ClassRelease(l %s)',
      [FPendingObjReleases.Strings[FPendingObjReleases.Count - 1]]));
    FPendingObjReleases.Delete(FPendingObjReleases.Count - 1);
  end;
end;

function TCodeGenQBE.IntfDispatchArgFragment(AIntfDesc: TInterfaceTypeDesc;
  AMethIdx: Integer; AArgs: TObjectList): string;
var
  I: Integer;
  Arg: TASTExpr;
  ArgTemp: string;
begin
  Result := '';
  if AArgs = nil then Exit;
  for I := 0 to AArgs.Count - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    if AIntfDesc.MethodParamIsVar(AMethIdx, I) then
      { var/out params pass the slot address — same rule as direct calls;
        covers managed types (string, dynarray) whose slot the callee
        rebinds. }
      Result := Result + Format(', l %s', [EmitLValueAddr(Arg)])
    else if (Arg.ResolvedType <> nil) and
            (Arg.ResolvedType.Kind = tyInterface) then
      { Interface args are two-slot fat pointers; the callee declares
        obj + itab params. }
      Result := Result + InterfaceArgFragment(Arg)
    else if Arg.ResolvedType <> nil then
    begin
      ArgTemp := EmitExpr(Arg);
      { QbeParamTypeOf gives records the same :_ffi_<Name> aggregate ABI
        the implementing method declares; scalars get their natural type
        (w/l/s/d) instead of an unconditional w. }
      Result := Result + Format(', %s %s',
        [QbeParamTypeOf(Arg.ResolvedType), ArgTemp]);
    end
    else
    begin
      ArgTemp := EmitExpr(Arg);
      Result := Result + Format(', w %s', [ArgTemp]);
    end;
  end;
end;

procedure TCodeGenQBE.EmitIntfSretDispatch(ACall: TASTExpr;
  const ASretAddr: string);
var
  IntfDesc: TInterfaceTypeDesc;
  MethName: string;
  AArgs: TObjectList;
  MCall: TMethodCallExpr;
  FldA: TFieldAccessExpr;
  SelfTemp: string;
  VTblTemp: string;
  FPtrTemp: string;
  ArgTemp: string;
  ArgLine: string;
  SlotOff: Integer;
  PMark: Integer;
begin
  PMark := PendingReleaseMark();
  AArgs := nil;
  if ACall is TMethodCallExpr then
  begin
    MCall := TMethodCallExpr(ACall);
    IntfDesc := TInterfaceTypeDesc(MCall.ResolvedClassType);
    MethName := MCall.Name;
    AArgs := MCall.Args;
    if MCall.ObjExpr <> nil then
      { Receiver is an expression (record/class field, implicit-Self field,
        as-cast) — resolve its fat pointer rather than split slots. }
      EmitInterfaceExprPair(MCall.ObjExpr, SelfTemp, VTblTemp)
    else
    begin
      SelfTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s',
        [SelfTemp, IntfObjAddr(MCall.ObjectName, MCall.IsGlobal, MCall.IsVarParam)]));
      VTblTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s',
        [VTblTemp, IntfItabAddr(MCall.ObjectName, MCall.IsGlobal, MCall.IsVarParam)]));
    end;
  end
  else
  begin
    { Zero-arg interface method call: F := G.GetThing — receiver is the
      named interface local/global/var-param G. }
    FldA := TFieldAccessExpr(ACall);
    IntfDesc := TInterfaceTypeDesc(FldA.ResolvedClassType);
    MethName := FldA.FieldName;
    SelfTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s',
      [SelfTemp, IntfObjAddr(FldA.RecordName, FldA.IsGlobal, FldA.IsVarParam)]));
    VTblTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s',
      [VTblTemp, IntfItabAddr(FldA.RecordName, FldA.IsGlobal, FldA.IsVarParam)]));
  end;
  SlotOff := IntfDesc.MethodIndex(MethName) * 8;
  FPtrTemp := AllocTemp();
  if SlotOff = 0 then
    EmitLine(Format('  %s =l loadl %s', [FPtrTemp, VTblTemp]))
  else
  begin
    ArgTemp := AllocTemp();
    EmitLine(Format('  %s =l add %s, %d', [ArgTemp, VTblTemp, SlotOff]));
    EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
  end;
  { Callee signature is (sret, Self, args...) — the same shape every
    interface-returning method body declares (`l %_par__sret, l %_par_Self`). }
  ArgLine := Format('l %s, l %s', [ASretAddr, SelfTemp]) +
    IntfDispatchArgFragment(IntfDesc, IntfDesc.MethodIndex(MethName), AArgs);
  EmitLine(Format('  call %s(%s)', [FPtrTemp, ArgLine]));
  FlushPendingReleases(PMark);
end;

function TCodeGenQBE.SretMethodCallTarget(AMDecl: TMethodDecl;
  const ASelfTemp, AMethName: string): string;
var
  VTblTemp: string;
  SlotTemp: string;
begin
  if AMDecl.VTableSlot >= 0 then
  begin
    { Virtual dispatch: load vptr from instance[0], then the fptr from the
      vtable.  Slot 0 of the vtable is typeinfo, so method N is at offset
      (N+1)*8.  A static call here would bind the declaring class's body —
      wrong for overrides, and a link error for virtual-abstract methods
      (no body is emitted for them). }
    VTblTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [VTblTemp, ASelfTemp]));
    SlotTemp := AllocTemp();
    EmitLine(Format('  %s =l add %s, %d',
      [SlotTemp, VTblTemp, (AMDecl.VTableSlot + 1) * 8]));
    Result := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [Result, SlotTemp]));
  end
  else
    Result := '$' + MethodEmitName(AMDecl, AMDecl.OwnerTypeName, AMethName);
end;

procedure TCodeGenQBE.EmitRecordCallSret(AExpr: TASTExpr;
  const ASretAddr: string);
var
  FCallExpr: TFuncCallExpr;
  MCallExpr: TMethodCallExpr;
  FldAccess: TFieldAccessExpr;
  MDecl:     TMethodDecl;
  VisArgs:   string;
  ArgTemp:   string;
  SelfTemp:  string;
  Par:       TMethodParam;
  I:         Integer;
  FuncName:  string;
  Ptr:       string;
  RetType:   TRecordTypeDesc;
  PMark:     Integer;
begin
  PMark := PendingReleaseMark();
  if AExpr is TFuncCallExpr then
  begin
    FCallExpr := TFuncCallExpr(AExpr);
    MDecl := TMethodDecl(FCallExpr.ResolvedDecl);
    RetType := TRecordTypeDesc(MDecl.ResolvedReturnType);
    if FCallExpr.IsImplicitSelfMethod then
    begin
      SelfTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_Self', [SelfTemp]));
      FuncName := SretMethodCallTarget(MDecl, SelfTemp, FCallExpr.Name);
      VisArgs  := Format('l %s', [SelfTemp]);
    end
    else
    begin
      if (MDecl <> nil) and (MDecl.ResolvedQbeName <> '') then
        FuncName := '$' + QBEMangle(MDecl.ResolvedQbeName)
      else
        FuncName := '$' + QBEMangle(FCallExpr.Name);
      VisArgs  := '';
    end;
    for I := 0 to FCallExpr.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Items[I]);
      if Par.IsVarParam then
      begin
        if VisArgs <> '' then VisArgs := VisArgs + ', ';
        VisArgs := VisArgs + Format('l %s',
          [EmitLValueAddr(TASTExpr(FCallExpr.Args.Items[I]))]);
      end
      else if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyInterface) then
      begin
        if VisArgs = '' then
          VisArgs := Copy(InterfaceArgFragment(TASTExpr(FCallExpr.Args.Items[I]),
            Par.ResolvedType), 2, MaxInt)
        else
          VisArgs := VisArgs + InterfaceArgFragment(TASTExpr(FCallExpr.Args.Items[I]),
            Par.ResolvedType);
      end
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(FCallExpr.Args.Items[I]));
        ArgTemp := CoerceArg(ArgTemp, TASTExpr(FCallExpr.Args.Items[I]),
          QbeTypeOf(Par.ResolvedType));
        if VisArgs <> '' then VisArgs := VisArgs + ', ';
        VisArgs := VisArgs + Format('%s %s',
          [QbeParamTypeOf(Par.ResolvedType), ArgTemp]);
      end;
    end;
    EmitRecordReturnCallSite(FuncName, VisArgs, RetType, ASretAddr);
    FlushPendingReleases(PMark);
  end
  else if AExpr is TMethodCallExpr then
  begin
    MCallExpr := TMethodCallExpr(AExpr);
    if (MCallExpr.ResolvedClassType <> nil) and
       (MCallExpr.ResolvedClassType.Kind = tyInterface) then
    begin
      { Interface-method call through itab dispatch — ResolvedMethod is nil,
        so the direct-call path below cannot be used. }
      EmitIntfSretDispatch(MCallExpr, ASretAddr);
      Exit;
    end;
    MDecl := TMethodDecl(MCallExpr.ResolvedMethod);
    RetType := TRecordTypeDesc(MDecl.ResolvedReturnType);
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
    FuncName := SretMethodCallTarget(MDecl, SelfTemp, MCallExpr.Name);
    VisArgs  := Format('l %s', [SelfTemp]);
    for I := 0 to MCallExpr.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Items[I]);
      if Par.IsVarParam then
        VisArgs := VisArgs + Format(', l %s',
          [EmitLValueAddr(TASTExpr(MCallExpr.Args.Items[I]))])
      else if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyInterface) then
        VisArgs := VisArgs + InterfaceArgFragment(TASTExpr(MCallExpr.Args.Items[I]),
          Par.ResolvedType)
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Items[I]));
        ArgTemp := CoerceArg(ArgTemp, TASTExpr(MCallExpr.Args.Items[I]),
          QbeTypeOf(Par.ResolvedType));
        VisArgs := VisArgs + Format(', %s %s',
          [QbeParamTypeOf(Par.ResolvedType), ArgTemp]);
      end;
    end;
    EmitRecordReturnCallSite(FuncName, VisArgs, RetType, ASretAddr);
    FlushPendingReleases(PMark);
  end
  else if AExpr is TFieldAccessExpr then
  begin
    FldAccess := TFieldAccessExpr(AExpr);
    if FldAccess.IsInterfaceCall then
    begin
      { Zero-arg interface method call through itab dispatch. }
      EmitIntfSretDispatch(FldAccess, ASretAddr);
      Exit;
    end;
    MDecl := TMethodDecl(FldAccess.ResolvedMethod);
    RetType := TRecordTypeDesc(MDecl.ResolvedReturnType);
    if FldAccess.IsImplicitSelf then
    begin
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
      SelfTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s',
        [SelfTemp, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
    end
    else if MDecl.IsRecordMethod then
      SelfTemp := VarRef(FldAccess.RecordName, FldAccess.IsGlobal)
    else
    begin
      SelfTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s',
        [SelfTemp, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
    end;
    FuncName := SretMethodCallTarget(MDecl, SelfTemp, FldAccess.FieldName);
    VisArgs  := Format('l %s', [SelfTemp]);
    EmitRecordReturnCallSite(FuncName, VisArgs, RetType, ASretAddr);
    FlushPendingReleases(PMark);
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

procedure TCodeGenQBE.EmitRecordAddRefFields(ARec: TRecordTypeDesc;
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
      if F.Offset > 0 then
      begin
        FldAddr := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d', [FldAddr, AAddr, F.Offset]));
      end
      else
        FldAddr := AAddr;
      EmitRecordAddRefFields(TRecordTypeDesc(F.TypeDesc), FldAddr);
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
      EmitLine(Format('  call $_StringAddRef(l %s)', [ValT]))
    else if F.TypeDesc.Kind = tyDynArray then
      EmitLine(Format('  call $_DynArrayAddRef(l %s)', [ValT]))
    else
      EmitLine(Format('  call $_ClassAddRef(l %s)', [ValT]));
  end;
end;

{ Element write into an array-typed field: Receiver.Field[Index] := Value.
  AFieldPtr addresses the FIELD slot (computed by EmitFieldAssignment for
  every receiver shape).  For a dynamic-array field the data pointer is
  loaded from the slot; for a static-array field the slot IS the inline
  storage.  The value is stored by ELEMENT type with the same ARC and
  record-copy rules as plain array subscript writes. }
procedure TCodeGenQBE.EmitFieldElemStore(AAssign: TFieldAssignment;
  const AFieldPtr: string);
var
  ArrT:     TTypeDesc;
  ElemT:    TTypeDesc;
  LowBnd:   Integer;
  ElemSize: Integer;
  BaseT:    string;
  IdxW:     string;
  IdxL:     string;
  Adj:      string;
  Offset:   string;
  ElemPtr:  string;
  ValTemp:  string;
  OldTemp:  string;
begin
  ArrT := AAssign.FieldInfo.TypeDesc;
  if ArrT.Kind = tyDynArray then
  begin
    ElemT := TDynArrayTypeDesc(ArrT).ElementType;
    LowBnd := 0;
    BaseT := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [BaseT, AFieldPtr]));  { data pointer }
  end
  else
  begin
    ElemT := TStaticArrayTypeDesc(ArrT).ElementType;
    LowBnd := TStaticArrayTypeDesc(ArrT).LowBound;
    BaseT := AFieldPtr;  { inline storage starts at the field slot }
  end;
  ElemSize := ElemT.RawSize();
  IdxW := EmitExpr(AAssign.PropIndexExpr);
  IdxL := AllocTemp();
  EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
  if LowBnd <> 0 then
  begin
    Adj := AllocTemp();
    EmitLine(Format('  %s =l sub %s, %d', [Adj, IdxL, LowBnd]));
    IdxL := Adj;
  end;
  Offset := AllocTemp();
  EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
  ElemPtr := AllocTemp();
  EmitLine(Format('  %s =l add %s, %s', [ElemPtr, BaseT, Offset]));

  if ElemT.Kind = tyRecord then
  begin
    ValTemp := EmitExpr(AAssign.Expr);
    EmitRecordCopy(TRecordTypeDesc(ElemT), ElemPtr, ValTemp);
    Exit;
  end;
  if ElemT.Kind in [tyByte, tyBoolean] then
    ValTemp := EmitByteRhs(AAssign.Expr)
  else
    ValTemp := EmitExpr(AAssign.Expr);
  { Extend w-typed values into 8-byte integer elements. }
  if (ElemT.Kind in [tyInt64, tyUInt64]) and
     (AAssign.Expr.ResolvedType <> nil) and
     not (AAssign.Expr.ResolvedType.Kind in [tyInt64, tyUInt64]) then
  begin
    Adj := AllocTemp();
    if ElemT.Kind = tyUInt64 then
      EmitLine(Format('  %s =l extuw %s', [Adj, ValTemp]))
    else
      EmitLine(Format('  %s =l extsw %s', [Adj, ValTemp]));
    ValTemp := Adj;
  end;
  { ARC for managed element types: retain new, release old, then store. }
  if ElemT.IsString() then
  begin
    OldTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [OldTemp, ElemPtr]));
    EmitLine(Format('  call $_StringAddRef(l %s)',  [ValTemp]));
    EmitLine(Format('  call $_StringRelease(l %s)', [OldTemp]));
  end
  else if ElemT.Kind = tyClass then
  begin
    OldTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [OldTemp, ElemPtr]));
    EmitLine(Format('  call $_ClassAddRef(l %s)',  [ValTemp]));
    EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
  end;
  EmitLine(Format('  %s %s, %s', [StoreInstrFor(ElemT), ValTemp, ElemPtr]));
end;

procedure TCodeGenQBE.EmitFieldAssignment(AAssign: TFieldAssignment);
var
  Ptr, PtrTemp, ValTemp, OldTemp, QType, StoreInstr, ExtTemp: string;
  IsArc: Boolean;
  IsStr: Boolean;
  SelfPtr: string;
  IdxTemp: string;
  IdxQType: string;
  PropTgt: string;
  IntfDesc: TInterfaceTypeDesc;
  SlotOff: Integer;
begin
  { Interface property write: I.Prop := V — FieldName holds the SETTER
    (rewritten by semantic); dispatch it through the itab with V as the
    single argument, mirroring EmitMethodCall's interface branch. }
  if AAssign.IntfWriteDesc <> nil then
  begin
    IntfDesc := TInterfaceTypeDesc(AAssign.IntfWriteDesc);
    SelfPtr := AllocTemp();
    PtrTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s',
      [SelfPtr, IntfObjAddr(AAssign.RecordName, AAssign.IsGlobal, AAssign.IsVarParam)]));
    EmitLine(Format('  %s =l loadl %s',
      [PtrTemp, IntfItabAddr(AAssign.RecordName, AAssign.IsGlobal, AAssign.IsVarParam)]));
    SlotOff := IntfDesc.MethodIndex(AAssign.FieldName) * 8;
    Ptr := AllocTemp();
    if SlotOff = 0 then
      EmitLine(Format('  %s =l loadl %s', [Ptr, PtrTemp]))
    else
    begin
      OldTemp := AllocTemp();
      EmitLine(Format('  %s =l add %s, %d', [OldTemp, PtrTemp, SlotOff]));
      EmitLine(Format('  %s =l loadl %s', [Ptr, OldTemp]));
    end;
    ValTemp := EmitExpr(AAssign.Expr);
    if (AAssign.Expr.ResolvedType <> nil) and
       (AAssign.Expr.ResolvedType.Kind in
         [tyPointer, tyClass, tyInterface, tyPChar, tyString]) then
      EmitLine(Format('  call %s(l %s, l %s)', [Ptr, SelfPtr, ValTemp]))
    else
      EmitLine(Format('  call %s(l %s, w %s)', [Ptr, SelfPtr, ValTemp]));
    Exit;
  end;

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
      PropTgt := PropAccessorTarget(AAssign.PropOwnerType,
        AAssign.PropWriteInfo.WriteMethod, AAssign.PropAccessorVSlot, SelfPtr);
      EmitLine(Format('  call %s(l %s, %s %s, %s %s)',
        [PropTgt, SelfPtr, IdxQType, IdxTemp, QType, ValTemp]));
    end
    else
    begin
      PropTgt := PropAccessorTarget(AAssign.PropOwnerType,
        AAssign.PropWriteInfo.WriteMethod, AAssign.PropAccessorVSlot, SelfPtr);
      EmitLine(Format('  call %s(l %s, %s %s)',
        [PropTgt, SelfPtr, QType, ValTemp]));
    end;
    Exit;
  end;

  if AAssign.FieldInfo = nil then
    raise ECodeGenError.Create(Format(
      'Field assignment ''%s.%s'' has no resolved field info',
      [AAssign.RecordName, AAssign.FieldName]));

  { Interface-typed field: the RHS must be stored as a two-slot fat pointer
    (obj + itab), not a single value.  EmitInterfaceToFieldSlots evaluates the
    RHS itself, so the generic single-value EmitExpr below must be skipped for
    this case (re-evaluating would double any side effects).  Element writes
    also evaluate the RHS themselves (after the index). }
  if (AAssign.FieldInfo.TypeDesc.Kind <> tyInterface) and
     not AAssign.IsElemWrite then
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
    { Load the heap pointer stored in the class variable.  var-param class:
      the slot holds the caller variable's address — one more load first. }
    PtrTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [PtrTemp, VarRef(AAssign.RecordName, AAssign.IsGlobal)]));
    if AAssign.IsVarParam then
    begin
      Ptr := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [Ptr, PtrTemp]));
      PtrTemp := Ptr;
    end;
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

  { Element write into an array-typed field: Ptr addresses the FIELD;
    redirect to the selected element and store by element type. }
  if AAssign.IsElemWrite then
  begin
    EmitFieldElemStore(AAssign, Ptr);
    Exit;
  end;

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
      { Class field consumes a +1-owned RHS (function/method call results
        transfer ownership — the callee retained into Result and does not
        release it); everything else needs the assignment-site retain.
        Mirrors the implicit-Self class-field path. }
      if not ExprOwnsRef(AAssign.Expr) then
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

{ Emit an argument bound to an open-array parameter and return the
  'l <data>, l <high>' fragment (no leading separator).  Handles inline
  array literals, static arrays coerced to open arrays, and forwarding an
  open-array parameter. }
function TCodeGenQBE.OpenArrayArgFragment(AArg: TASTExpr): string;
var
  ArgTemp:    string;
  HighTemp:   string;
  LenTemp:    string;
  LenExtTemp: string;
begin
  if AArg is TArrayLiteralExpr then
  begin
    ArgTemp := EmitArrayLiteralExpr(TArrayLiteralExpr(AArg));
    Result := Format('l %s, l %d',
      [ArgTemp, TArrayLiteralExpr(AArg).Elements.Count - 1]);
    Exit;
  end;
  if (AArg.ResolvedType <> nil) and
     (AArg.ResolvedType.Kind = tyStaticArray) then
  begin
    { Static array coerced to open-array: pass base ptr + compile-time high }
    ArgTemp := EmitExpr(AArg);
    Result := Format('l %s, l %d', [ArgTemp,
      TStaticArrayTypeDesc(AArg.ResolvedType).HighBound -
      TStaticArrayTypeDesc(AArg.ResolvedType).LowBound]);
    Exit;
  end;
  if (AArg.ResolvedType <> nil) and
     (AArg.ResolvedType.Kind = tyDynArray) then
  begin
    { Dynamic array coerced to open-array: pass data ptr + (runtime length - 1)
      as the high index. }
    ArgTemp  := EmitExpr(AArg);
    LenTemp  := AllocTemp();
    EmitLine(Format('  %s =w call $_DynArrayLength(l %s)', [LenTemp, ArgTemp]));
    LenExtTemp := AllocTemp();
    EmitLine(Format('  %s =l extsw %s', [LenExtTemp, LenTemp]));
    HighTemp := AllocTemp();
    EmitLine(Format('  %s =l sub %s, 1', [HighTemp, LenExtTemp]));
    Result := Format('l %s, l %s', [ArgTemp, HighTemp]);
    Exit;
  end;
  { Forward an open-array param variable }
  ArgTemp  := EmitExpr(AArg);
  HighTemp := AllocTemp();
  EmitLine(Format('  %s =l loadl %%_var_%s_high',
    [HighTemp, TIdentExpr(AArg).Name]));
  Result := Format('l %s, l %s', [ArgTemp, HighTemp]);
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
  SretTemp: string;
  PMark:    Integer;
begin
  PMark := PendingReleaseMark();
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
      EmitLine(Format('  %s =l loadl %s',
        [SelfTemp, IntfObjAddr(ACall.ObjectName, ACall.IsGlobal, ACall.IsVarParam)]));
      EmitLine(Format('  %s =l loadl %s',
        [VTblTemp, IntfItabAddr(ACall.ObjectName, ACall.IsGlobal, ACall.IsVarParam)]));
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
    ArgLine := Format('l %s', [SelfTemp]) +
      IntfDispatchArgFragment(IntfDesc, IntfDesc.MethodIndex(ACall.Name),
        ACall.Args);
    if (ACall.ResolvedReturnTypeDesc <> nil) and
       (ACall.ResolvedReturnTypeDesc.Kind = tyInterface) then
    begin
      { Discarded interface return: the callee still writes its fat pointer
        through a hidden first sret arg — without a buffer it would write
        through whatever the first register holds.  Give it a throwaway
        buffer and release the returned (owned +1) obj. }
      SretTemp := AllocTemp();
      EmitLine(Format('  %s =l alloc8 16', [SretTemp]));
      EmitLine(Format('  call $memset(l %s, w 0, l 16)', [SretTemp]));
      EmitLine(Format('  call %s(l %s, %s)', [FPtrTemp, SretTemp, ArgLine]));
      ArgTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [ArgTemp, SretTemp]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [ArgTemp]));
    end
    else
      EmitLine(Format('  call %s(%s)', [FPtrTemp, ArgLine]));
    FlushPendingReleases(PMark);
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
      if Par.IsOpenArray then
      begin
        ArgTemps.Add('');
        ArgLine := ArgLine + ', ' +
          OpenArrayArgFragment(TASTExpr(ACall.Args.Items[I]));
      end
      else if Par.IsVarParam then
      begin
        ArgTemps.Add('');
        ArgLine := ArgLine + Format(', l %s',
          [EmitLValueAddr(TASTExpr(ACall.Args.Items[I]))]);
      end
      else if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyInterface) then
      begin
        ArgTemps.Add('');
        ArgLine := ArgLine + InterfaceArgFragment(TASTExpr(ACall.Args.Items[I]),
          Par.ResolvedType);
      end
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
        ArgTemps.Add(ArgTemp);
        EnsureConstStringRef(ArgTemp, Par, TASTExpr(ACall.Args.Items[I]), MDecl.Params);
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
      FlushPendingReleases(PMark);
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
    FlushPendingReleases(PMark);
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
      if Par.IsOpenArray then
      begin
        ArgTemps.Add('');
        ArgLine := ArgLine + ', ' +
          OpenArrayArgFragment(TASTExpr(ACall.Args.Items[I]));
      end
      else if Par.IsVarParam then
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
        EnsureConstStringRef(ArgTemp, Par, TASTExpr(ACall.Args.Items[I]), MDecl.Params);
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
    FlushPendingReleases(PMark);
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
  LoTemp:      string;
  HiTemp:      string;
  GeTemp:      string;
  LeTemp:      string;
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
        NextLbl := AllocLabel('case_next');
        if TASTExpr(Branch.Values.Items[J]) is TSetRangeExpr then
        begin
          { Range label lo..hi: match when (sel >= lo) and (sel <= hi).
            csgew/cslew are signed ordinal comparisons (enum/integer). }
          LoTemp  := EmitExpr(TSetRangeExpr(Branch.Values.Items[J]).LowExpr);
          GeTemp  := AllocTemp();
          EmitLine(Format('  %s =w csgew %s, %s', [GeTemp, SelTemp, LoTemp]));
          HiTemp  := EmitExpr(TSetRangeExpr(Branch.Values.Items[J]).HighExpr);
          LeTemp  := AllocTemp();
          EmitLine(Format('  %s =w cslew %s, %s', [LeTemp, SelTemp, HiTemp]));
          CmpTemp := AllocTemp();
          EmitLine(Format('  %s =w and %s, %s', [CmpTemp, GeTemp, LeTemp]));
        end
        else
        begin
          ValTemp := EmitExpr(TASTExpr(Branch.Values.Items[J]));
          CmpTemp := AllocTemp();
          if AStmt.IsStringCase then
            EmitLine(Format('  %s =w call $_StringEquals(l %s, l %s)',
              [CmpTemp, SelTemp, ValTemp]))
          else
            EmitLine(Format('  %s =w ceqw %s, %s', [CmpTemp, SelTemp, ValTemp]));
        end;
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
  PMark:    Integer;
begin
  { TObject inherited calls are no-ops — no method body exists }
  if ACall.ResolvedMethod = nil then Exit;

  PMark := PendingReleaseMark();
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
  FlushPendingReleases(PMark);
end;

function TCodeGenQBE.EmitInheritedCallExpr(ACall: TInheritedCallExpr): string;
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
  { Expression form of `inherited Method(args)` — semantic guarantees a
    non-void function.  Same static-dispatch arg marshalling as
    EmitInheritedCall, but the call result is RETURNED (not stored to
    %_var_Result). }
  MDecl := TMethodDecl(ACall.ResolvedMethod);

  SelfTemp := AllocTemp();
  EmitLine(Format('  %s =l loadl %%_var_Self', [SelfTemp]));

  ArgLine := Format('l %s', [SelfTemp]);
  for I := 0 to ACall.Args.Count - 1 do
  begin
    Par := TMethodParam(MDecl.Params.Items[I]);
    if Par.IsVarParam then
    begin
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

  QType  := QbeTypeOf(MDecl.ResolvedReturnType);
  Result := AllocTemp();
  EmitLine(Format('  %s =%s call $%s(%s)',
    [Result, QType, MethodEmitName(MDecl, MDecl.OwnerTypeName, ACall.Name), ArgLine]));
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
        { A small set is a w (<=32) / l (<=64) bitmask spilled at its width.
          A jumbo set arrives as a pointer to the caller's bitmap; copy it into
          a fresh local bitmap slot for value semantics. }
        if TSetTypeDesc(Par.ResolvedType).IsJumbo() then
        begin
          EmitLine(Format('  %%_var_%s =l alloc8 %d',
            [Par.ParamName, TSetTypeDesc(Par.ResolvedType).RawSize()]));
          EmitLine(Format('  call $memcpy(l %%_var_%s, l %%_par_%s, l %d)',
            [Par.ParamName, Par.ParamName,
             TSetTypeDesc(Par.ResolvedType).RawSize()]));
        end
        else if TSetTypeDesc(Par.ResolvedType).BitCount <= 32 then
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
          EmitLine(Format('  %%_var_%s_obj =l alloc8 16', [Par.ParamName]));
          EmitLine(Format('  %%_var_%s_itab =l add %%_var_%s_obj, 8',
            [Par.ParamName, Par.ParamName]));
          EmitLine(Format('  storel %%_par_%s_obj, %%_var_%s_obj',
            [Par.ParamName, Par.ParamName]));
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
  RetDeclType:   string;
  RetTemp:       string;
  SavedExitLbl:  string;
  ValTemp:       string;
  RC:            TRecReturnClass;
begin
  if AMethod.ResolvedQbeName <> '' then
    FuncName := '$' + QBEMangle(AMethod.ResolvedQbeName)
  else
    FuncName := '$' + QBEMangle(ATypeName + '_' + AMethod.Name);
  IsFunc   := AMethod.ResolvedReturnType <> nil;

  RC := rcSret;
  if IsFunc and (AMethod.ResolvedReturnType.Kind = tyRecord) then
    RC := Self.ClassifyRecordReturn(TRecordTypeDesc(AMethod.ResolvedReturnType));

  Sig := 'l %_par_Self';
  if IsFunc and ((AMethod.ResolvedReturnType.Kind = tyInterface) or
     ((AMethod.ResolvedReturnType.Kind = tySet) and
      TSetTypeDesc(AMethod.ResolvedReturnType).IsJumbo())) then
    Sig := 'l %_par__sret, l %_par_Self'
  else if IsFunc and (AMethod.ResolvedReturnType.Kind = tyRecord) then
    EmitRecordReturnSignature(Sig, RC);
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
    if (AMethod.ResolvedReturnType.Kind = tyInterface) or
       ((AMethod.ResolvedReturnType.Kind = tySet) and
        TSetTypeDesc(AMethod.ResolvedReturnType).IsJumbo()) then
      { sret aggregate return — void function. }
      EmitLine(Format('%sfunction %s(%s) {', [ExportPrefix(), FuncName, Sig]))
    else if AMethod.ResolvedReturnType.Kind = tyRecord then
    begin
      RetDeclType := EmitRecordReturnDeclType(
        TRecordTypeDesc(AMethod.ResolvedReturnType), RC);
      if RetDeclType = '' then
        EmitLine(Format('%sfunction %s(%s) {', [ExportPrefix(), FuncName, Sig]))
      else
        EmitLine(Format('%sfunction %s %s(%s) {',
          [ExportPrefix(), RetDeclType, FuncName, Sig]));
    end
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
    end
    else if Par.ResolvedType.Kind = tyRecord then
    begin
      { By-value record: QBE materialises the aggregate and %_var_X holds
        its address.  Retain each managed leaf so subsequent
        field-reassignment's release-old does not free the caller's shared
        heap data; balanced by the release pass at method exit. }
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitRecordAddRefFields(TRecordTypeDesc(Par.ResolvedType), ValTemp);
    end;
  end;

  { For function methods, allocate/alias a zero-initialised Result slot }
  if IsFunc then
  begin
    if AMethod.ResolvedReturnType.Kind = tyRecord then
      EmitRecordReturnPrologue(TRecordTypeDesc(AMethod.ResolvedReturnType), RC)
    else if (AMethod.ResolvedReturnType.Kind = tySet) and
            TSetTypeDesc(AMethod.ResolvedReturnType).IsJumbo() then
    begin
      { sret: jumbo-set Result aliases the caller's buffer; zero-init it. }
      EmitLine('  %_var_Result =l copy %_par__sret');
      EmitLine(Format('  call $memset(l %%_var_Result, w 0, l %d)',
        [TSetTypeDesc(AMethod.ResolvedReturnType).RawSize()]));
    end
    else if AMethod.ResolvedReturnType.Kind = tyInterface then
    begin
      { sret: interface Result is a 16-byte fat pointer (obj+itab) in the
        caller's buffer.  Alias the two split slots to sret+0 and sret+8. }
      EmitLine('  %_var_Result_obj =l copy %_par__sret');
      EmitLine('  storel 0, %_var_Result_obj');
      EmitLine('  %_var_Result_itab =l add %_par__sret, 8');
      EmitLine('  storel 0, %_var_Result_itab');
    end
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
    end
    else if Par.ResolvedType.Kind = tyRecord then
    begin
      { Release the retains taken at entry on each managed leaf. }
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitRecordReleaseFields(TRecordTypeDesc(Par.ResolvedType), ValTemp);
    end;
  end;

  if IsFunc then
  begin
    if AMethod.ResolvedReturnType.Kind = tyRecord then
      EmitRecordReturnEpilogue(TRecordTypeDesc(AMethod.ResolvedReturnType), RC)
    else if (AMethod.ResolvedReturnType.Kind = tyInterface) or
            ((AMethod.ResolvedReturnType.Kind = tySet) and
             TSetTypeDesc(AMethod.ResolvedReturnType).IsJumbo()) then
      { sret aggregate return — written through %_par__sret; return void. }
      EmitLine('  ret')
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
    begin
      { A generic-instance parent (TBox<Integer>) is defined under the
        QBEMangle'd symbol (typeinfo_TBox_Integer) and carries no unit prefix,
        so reference it the same way.  Non-generic parents keep ClassSymName
        (which adds the unit prefix). }
      if StrPos('<', RT.Parent.Name) >= 0 then
        ParentStr := '$typeinfo_' + QBEMangle(RT.Parent.Name)
      else
        ParentStr := '$typeinfo_' + ClassSymName(RT.Parent.Name);
    end
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
    { TypeInfo pointer is always the first vtable entry.  In OPDF-debug mode the
      vtable is exported so the separately-assembled .opdf section can reference
      it (the OPDF class record stores each class's VMTAddress); otherwise it
      stays a local symbol, keeping non-debug output unchanged. }
    Line := VTableDataPrefix() + '$vtable_' + ClassSymName(TD.Name) +
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
    Line  := VTableDataPrefix() + '$vtable_' + MName + ' = { l $typeinfo_' + MName;
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
  EmitIntfs:   TObjectList;
  IntfWalk:    TInterfaceTypeDesc;
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

    { Collect each implemented interface PLUS every ancestor on its parent
      chain (IDog = interface(IAnimal) -> also emit an IAnimal itab), so a
      class instance can be narrowed directly to a base interface.  An
      ancestor's methods are a prefix of the descendant's itab, so the same
      impl pointers apply; the dedup keeps one itab per (class, interface). }
    EmitIntfs := TObjectList.Create(False);
    try
      for J := 0 to ClassRT.ImplementsCount() - 1 do
      begin
        IntfWalk := ClassRT.ImplementsIntfAt(J);
        while IntfWalk <> nil do
        begin
          if EmitIntfs.IndexOf(IntfWalk) < 0 then EmitIntfs.Add(IntfWalk);
          IntfWalk := IntfWalk.Parent;
        end;
      end;

      { One itab per interface — when a class's vtable slot for a given
        interface method is abstract (e.g. the class is an abstract base that
        declares the interface but defers implementation to subclasses), the
        itab entry must point at $_AbstractMethodError instead of the would-be
        symbol, which does not exist. }
      for J := 0 to EmitIntfs.Count - 1 do
      begin
        IntfDesc   := TInterfaceTypeDesc(EmitIntfs.Items[J]);
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

      { One impllist per class: NULL-terminated (typeinfo_intf, itab) pairs.
        Includes ancestor interfaces so _GetItab(obj, typeinfo_IBase) resolves. }
      ImplLine := 'data $impllist_' + ClassSymName(TD.Name) + ' = {';
      for J := 0 to EmitIntfs.Count - 1 do
      begin
        IntfDesc   := TInterfaceTypeDesc(EmitIntfs.Items[J]);
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
    finally
      EmitIntfs.Free();
    end;
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
  GMI:     TGenericMethodInstance;
  MDecl:   TMethodDecl;
  Methods: TObjectList;
  SavedUnit: string;
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
      if (TMethodDecl(Methods.Items[J]).Body <> nil) and
         { Generic-method templates (method-level <T>) are emitted per
           instantiation via GenericMethodInstances, not as a template body. }
         (TMethodDecl(Methods.Items[J]).TypeParams = nil) then
        EmitMethodDef(TD.Name, TMethodDecl(Methods.Items[J]));
  end;

  { Generic class instances — emit with mangled type name.  Method bodies
    are clones of the template AST: their Line fields refer to the unit
    that DECLARES the template, so allocation-site tracking must report
    that unit, not the instantiating one. }
  SavedUnit := FCurrentUnitName;
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AProg.GenericInstances.Items[I]);
    if GI.DefUnitName <> '' then
      FCurrentUnitName := GI.DefUnitName
    else
      FCurrentUnitName := SavedUnit;
    for J := 0 to GI.ClassDef.Methods.Count - 1 do
    begin
      MDecl := TMethodDecl(GI.ClassDef.Methods.Items[J]);
      if MDecl.Body <> nil then
        EmitMethodDef(QBEMangle(GI.TypeName), MDecl);
    end;
  end;
  FCurrentUnitName := SavedUnit;

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

  { Generic METHOD instances (method-level <T>) — emit each monomorphised body.
    Its ResolvedQbeName already encodes <Owner>_<Method><args>, so EmitMethodDef
    uses that label and adds the implicit Self param. }
  for I := 0 to AProg.GenericMethodInstances.Count - 1 do
  begin
    GMI := TGenericMethodInstance(AProg.GenericMethodInstances.Items[I]);
    if GMI.MethodDecl.Body <> nil then
      EmitMethodDef(GMI.OwnerType, GMI.MethodDecl);
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
  RetDeclType:     string;
  RetTemp:         string;
  ValTemp:         string;
  Prefix:          string;
  SavedExitLbl:    string;
  SavedCaptures:   TStringList;
  NestedDecl:      TMethodDecl;
  CapName:         string;
  NestedFuncName:  string;
  RC:              TRecReturnClass;
begin
  if ADecl.IsExternal then Exit;  { no body to emit for external declarations }
  if ADecl.Body = nil then Exit;  { forward declaration — impl appears elsewhere }
  { Generic template — its body has unbound type parameters (locals typed `T`
    never get a ResolvedType).  Only concrete instances are emitted, via the
    GenericFuncInstances list.  EmitStandaloneDefs already skips templates at
    the program level; unit emission (GenerateUnit/AppendUnit) reaches here
    without that guard, so enforce it centrally. }
  if ADecl.TypeParams <> nil then Exit;

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
  RC := rcSret;
  if IsFunc and (ADecl.ResolvedReturnType.Kind = tyRecord) then
    RC := Self.ClassifyRecordReturn(TRecordTypeDesc(ADecl.ResolvedReturnType));
  if AExported or FExportAll or FOpdfMode then Prefix := 'export ' else Prefix := '';

  { Captured outer-scope variables are prepended as implicit pointer params.
    The call site in the enclosing function passes the address of each var. }
  Sig := '';
  if (ADecl.CapturedVars <> nil) and (ADecl.CapturedVars.Count > 0) then
    for I := 0 to ADecl.CapturedVars.Count - 1 do
    begin
      CapName := ADecl.CapturedVars.Strings[I];
      if Sig <> '' then Sig := Sig + ', ';
      Sig := Sig + Format('l %%_cap_%s', [CapName]);
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
    if (ADecl.ResolvedReturnType.Kind = tyInterface) or
       ((ADecl.ResolvedReturnType.Kind = tySet) and
        TSetTypeDesc(ADecl.ResolvedReturnType).IsJumbo()) then
    begin
      { Interface and jumbo-set returns use a hidden sret pointer (the callee
        writes the aggregate through it) and return void. }
      if Sig <> '' then Sig := 'l %_par__sret, ' + Sig
      else Sig := 'l %_par__sret';
      EmitLine(Format('%sfunction %s(%s) {', [Prefix, FuncName, Sig]));
    end
    else if ADecl.ResolvedReturnType.Kind = tyRecord then
    begin
      EmitRecordReturnSignature(Sig, RC);
      RetDeclType := EmitRecordReturnDeclType(
        TRecordTypeDesc(ADecl.ResolvedReturnType), RC);
      if RetDeclType = '' then
        EmitLine(Format('%sfunction %s(%s) {', [Prefix, FuncName, Sig]))
      else
        EmitLine(Format('%sfunction %s %s(%s) {',
          [Prefix, RetDeclType, FuncName, Sig]));
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
          { Small set: w (<=32) / l (<=64) bitmask spilled at its width.
            Jumbo set: arrives as a pointer; copy into a local bitmap slot. }
          if TSetTypeDesc(Par.ResolvedType).IsJumbo() then
          begin
            EmitLine(Format('  %%_var_%s =l alloc8 %d',
              [Par.ParamName, TSetTypeDesc(Par.ResolvedType).RawSize()]));
            EmitLine(Format('  call $memcpy(l %%_var_%s, l %%_par_%s, l %d)',
              [Par.ParamName, Par.ParamName,
               TSetTypeDesc(Par.ResolvedType).RawSize()]));
          end
          else if TSetTypeDesc(Par.ResolvedType).BitCount <= 32 then
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
            EmitLine(Format('  %%_var_%s_obj =l alloc8 16', [Par.ParamName]));
            EmitLine(Format('  %%_var_%s_itab =l add %%_var_%s_obj, 8',
              [Par.ParamName, Par.ParamName]));
            EmitLine(Format('  storel %%_par_%s_obj, %%_var_%s_obj',
              [Par.ParamName, Par.ParamName]));
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
    end
    else if Par.ResolvedType.Kind = tyRecord then
    begin
      { By-value record: QBE materialises the aggregate; %_var_X holds its
        address.  Retain each managed leaf; balanced at function exit. }
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitRecordAddRefFields(TRecordTypeDesc(Par.ResolvedType), ValTemp);
    end;
  end;

  if IsFunc then
  begin
    if ADecl.ResolvedReturnType.Kind = tyRecord then
      EmitRecordReturnPrologue(TRecordTypeDesc(ADecl.ResolvedReturnType), RC)
    else if (ADecl.ResolvedReturnType.Kind = tySet) and
            TSetTypeDesc(ADecl.ResolvedReturnType).IsJumbo() then
    begin
      { sret: jumbo-set Result aliases the caller's buffer; zero-init it so a
        partial build (Include before full assignment) starts empty. }
      EmitLine('  %_var_Result =l copy %_par__sret');
      EmitLine(Format('  call $memset(l %%_var_Result, w 0, l %d)',
        [TSetTypeDesc(ADecl.ResolvedReturnType).RawSize()]));
    end
    else if ADecl.ResolvedReturnType.Kind = tyInterface then
    begin
      { sret: interface Result is a 16-byte fat pointer (obj+itab) in the
        caller's buffer.  Alias the two split slots to sret+0 and sret+8. }
      EmitLine('  %_var_Result_obj =l copy %_par__sret');
      EmitLine('  storel 0, %_var_Result_obj');
      EmitLine('  %_var_Result_itab =l add %_par__sret, 8');
      EmitLine('  storel 0, %_var_Result_itab');
    end
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
    end
    else if Par.ResolvedType.Kind = tyRecord then
    begin
      { Release the retains taken at entry on each managed leaf. }
      ValTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitRecordReleaseFields(TRecordTypeDesc(Par.ResolvedType), ValTemp);
    end;
  end;

  if IsFunc then
  begin
    if ADecl.ResolvedReturnType.Kind = tyRecord then
      EmitRecordReturnEpilogue(TRecordTypeDesc(ADecl.ResolvedReturnType), RC)
    else if (ADecl.ResolvedReturnType.Kind = tyInterface) or
            ((ADecl.ResolvedReturnType.Kind = tySet) and
             TSetTypeDesc(ADecl.ResolvedReturnType).IsJumbo()) then
      { sret: the aggregate was written through %_par__sret — return void. }
      EmitLine('  ret')
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
  PMark:     Integer;
begin
  PMark := PendingReleaseMark();
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
            else
              { Static array, dynamic array, or open-array variable — the
                fragment helper handles all three (and returns 'l ptr, l high'
                without a leading comma). }
              ArgLine := ArgLine + ', ' +
                Copy(OpenArrayArgFragment(TASTExpr(ACall.Args.Items[I])), 1, MaxInt);
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
                ArgTemp, ArgTemp2, Par.ResolvedType);
              ArgLine := ArgLine + Format(', l %s, l %s', [ArgTemp, ArgTemp2]);
            end;
          end
          else
          begin
            ArgTemp := EmitExpr(TASTExpr(ACall.Args.Items[I]));
            while ArgTemps.Count < I do ArgTemps.Add('');
            ArgTemps.Add(ArgTemp);
            EnsureConstStringRef(ArgTemp, Par, TASTExpr(ACall.Args.Items[I]), MDecl.Params);
            ArgTemp := CoerceArg(ArgTemp, TASTExpr(ACall.Args.Items[I]), QbeTypeOf(Par.ResolvedType));
            ArgLine := ArgLine + Format(', %s %s',
              [QbeParamTypeOf(Par.ResolvedType), ArgTemp]);
          end;
        end;
        EmitLine(Format('  call $%s(%s)',
          [MethodEmitName(MDecl, MDecl.OwnerTypeName, ACall.Name), ArgLine]));
        FlushPendingReleases(PMark);
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
          else
            { Static array, dynamic array, or open-array variable. }
            ArgLine := ArgLine + OpenArrayArgFragment(TASTExpr(ACall.Args.Items[I]));
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
          EnsureConstStringRef(ArgTemp, Par, TASTExpr(ACall.Args.Items[I]), MDecl.Params);
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
      FlushPendingReleases(PMark);
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
       IsCaptured(TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name) then
    begin
      { Captured outer-scope variable: %_cap_Name holds the ADDRESS of the
        outer var.  Load through it, add/sub, store back through it — the
        same indirection the assignment path uses (EmitLValueAddr does not
        cover captured vars, so handle it explicitly here). }
      ArgTemp  := '%_cap_' + TIdentExpr(TASTExpr(ACall.Args.Items[0])).Name;
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
    end
    else if (TASTExpr(ACall.Args.Items[0]) is TIdentExpr) and
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
    { Jumbo set: in-place bit set via the RTL helper. }
    if (TASTExpr(ACall.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(ACall.Args.Items[0]).ResolvedType.Kind = tySet) and
       TSetTypeDesc(TASTExpr(ACall.Args.Items[0]).ResolvedType).IsJumbo() then
    begin
      ArgTemp  := EmitLValueAddr(TASTExpr(ACall.Args.Items[0]));
      SizeTemp := EmitExpr(TASTExpr(ACall.Args.Items[1]));
      EmitLine(Format('  call $_SetInclude(l %s, w %s)', [ArgTemp, SizeTemp]));
    end
    else
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
    end;
  end
  else if UCaseName = 'EXCLUDE' then
  begin
    { Jumbo set: in-place bit clear via the RTL helper. }
    if (TASTExpr(ACall.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(ACall.Args.Items[0]).ResolvedType.Kind = tySet) and
       TSetTypeDesc(TASTExpr(ACall.Args.Items[0]).ResolvedType).IsJumbo() then
    begin
      ArgTemp  := EmitLValueAddr(TASTExpr(ACall.Args.Items[0]));
      SizeTemp := EmitExpr(TASTExpr(ACall.Args.Items[1]));
      EmitLine(Format('  call $_SetExclude(l %s, w %s)', [ArgTemp, SizeTemp]));
    end
    else
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
    end;
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
  { Address of the string slot.  EmitLValueAddr covers plain idents, var
    params, implicit-Self fields, field-access targets (R.F, C.F, P^.F)
    and raises for unsupported L-value shapes. }
  Addr := EmitLValueAddr(TASTExpr(ACall.Args.Items[0]));

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
  { EmitLValueAddr covers plain idents, var params, implicit-Self fields and
    field-access targets (R.F, C.F, P^.F); it raises for unsupported shapes. }
  Addr    := EmitLValueAddr(TASTExpr(ACall.Args.Items[0]));
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
  ExtTemp:    string;
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
  if AStmt.BaseTy <> nil then
    StoreInstr := StoreInstrFor(AStmt.BaseTy)
  else
    StoreInstr := 'storel';
  if (AStmt.BaseTy <> nil) and (AStmt.BaseTy.Kind = tySingle) and
     (QbeTypeOf(AStmt.ValExpr.ResolvedType) = 'd') then
  begin
    ExtTemp := AllocTemp();
    EmitLine(Format('  %s =s truncd %s', [ExtTemp, ValTemp]));
    ValTemp := ExtTemp;
  end
  else if (AStmt.BaseTy <> nil) and (AStmt.BaseTy.Kind = tyDouble) and
          (QbeTypeOf(AStmt.ValExpr.ResolvedType) = 's') then
  begin
    ExtTemp := AllocTemp();
    EmitLine(Format('  %s =d exts %s', [ExtTemp, ValTemp]));
    ValTemp := ExtTemp;
  end;
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

{ Emit a float-builtin argument: float-typed expressions pass through with
  their own QBE type ('s' or 'd'); integer-family expressions are widened
  to Double ('d') with the matching signed/unsigned conversion. }
function TCodeGenQBE.EmitFloatArg(AExpr: TASTExpr; out AQType: string): string;
var
  T: string;
begin
  Result := EmitExpr(AExpr);
  AQType := QbeTypeOf(AExpr.ResolvedType);
  if (AQType = 's') or (AQType = 'd') then
    Exit;
  T := AllocTemp();
  case AExpr.ResolvedType.Kind of
    tyInt64:  EmitLine(Format('  %s =d sltof %s', [T, Result]));
    tyUInt64: EmitLine(Format('  %s =d ultof %s', [T, Result]));
    tyUInt32: EmitLine(Format('  %s =d uwtof %s', [T, Result]));
  else
    EmitLine(Format('  %s =d swtof %s', [T, Result]));
  end;
  Result := T;
  AQType := 'd';
end;

{ As EmitFloatArg, but Single arguments are also widened to Double — for
  builtins that always call the double-precision C function (pow). }
function TCodeGenQBE.EmitFloatArgAsDouble(AExpr: TASTExpr): string;
var
  Q: string;
  T: string;
begin
  Result := EmitFloatArg(AExpr, Q);
  if Q = 's' then
  begin
    T := AllocTemp();
    EmitLine(Format('  %s =d exts %s', [T, Result]));
    Result := T;
  end;
end;

function TCodeGenQBE.EmitExpr(AExpr: TASTExpr): string;
var
  T, L, R, T2: string;
  Op:          string;
  PropTgt:     string;
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
  IsFloatArg:   Boolean;
  FmtArgElem:   TASTExpr;
  FmtCastTemp:  string;
  FT:           string;
  ItabName:     string;
  PT:           TProceduralTypeDesc;
  SlotAddr:     string;
  DataTemp:     string;
  SQT:          string;
  PMark:        Integer;
  CmpTemp:      string;
  SetTmpA:      string;
  SetTmpB:      string;
  SetNB:        Integer;   { jumbo set bitmap byte count }
  SetRS:        Integer;   { jumbo set slot size (RawSize, 8-rounded) }
begin
  PMark := PendingReleaseMark();
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
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
        if QType = 's' then
          EmitLine(Format('  %s =s call $sqrtf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $sqrt(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Ceil') then
      begin
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
        R := AllocTemp();
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
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
        R := AllocTemp();
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
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
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
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
        R := AllocTemp();
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
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
        if QType = 's' then
          EmitLine(Format('  %s =s call $logf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $log(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Log2') then
      begin
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
        if QType = 's' then
          EmitLine(Format('  %s =s call $log2f(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $log2(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Log10') then
      begin
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
        if QType = 's' then
          EmitLine(Format('  %s =s call $log10f(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $log10(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Power') then
      begin
        L := EmitFloatArgAsDouble(TASTExpr(FC.Args.Items[0]));
        R := EmitFloatArgAsDouble(TASTExpr(FC.Args.Items[1]));
        T := AllocTemp();
        EmitLine(Format('  %s =d call $pow(d %s, d %s)', [T, L, R]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Sin') then
      begin
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
        if QType = 's' then
          EmitLine(Format('  %s =s call $sinf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $sin(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Cos') then
      begin
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
        if QType = 's' then
          EmitLine(Format('  %s =s call $cosf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $cos(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Tan') then
      begin
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
        if QType = 's' then
          EmitLine(Format('  %s =s call $tanf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $tan(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'ArcTan') then
      begin
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
        if QType = 's' then
          EmitLine(Format('  %s =s call $atanf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $atan(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'ArcTan2') then
      begin
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        R := EmitFloatArg(TASTExpr(FC.Args.Items[1]), T2);
        T := AllocTemp();
        if QType = 's' then
          EmitLine(Format('  %s =s call $atan2f(s %s, s %s)', [T, L, R]))
        else
          EmitLine(Format('  %s =d call $atan2(d %s, d %s)', [T, L, R]));
        Exit(T);
      end;

      if SameText(FC.Name, 'ArcSin') then
      begin
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
        if QType = 's' then
          EmitLine(Format('  %s =s call $asinf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $asin(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'ArcCos') then
      begin
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
        if QType = 's' then
          EmitLine(Format('  %s =s call $acosf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $acos(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Sinh') then
      begin
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
        if QType = 's' then
          EmitLine(Format('  %s =s call $sinhf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $sinh(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Cosh') then
      begin
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
        if QType = 's' then
          EmitLine(Format('  %s =s call $coshf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $cosh(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'Tanh') then
      begin
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
        if QType = 's' then
          EmitLine(Format('  %s =s call $tanhf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =d call $tanh(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'IsNaN') then
      begin
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
        if QType = 's' then
          EmitLine(Format('  %s =w call $__isnanf(s %s)', [T, L]))
        else
          EmitLine(Format('  %s =w call $__isnan(d %s)', [T, L]));
        Exit(T);
      end;

      if SameText(FC.Name, 'IsInfinite') then
      begin
        L := EmitFloatArg(TASTExpr(FC.Args.Items[0]), QType);
        T := AllocTemp();
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
          if MDecl.VTableSlot >= 0 then
          begin
            VTblTemp := AllocTemp();
            EmitLine(Format('  %s =l loadl %s', [VTblTemp, T]));
            FPtrTemp := AllocTemp();
            SlotOff  := (MDecl.VTableSlot + 1) * 8;
            ArgTemp  := AllocTemp();
            EmitLine(Format('  %s =l add %s, %d', [ArgTemp, VTblTemp, SlotOff]));
            EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
            EmitLine(Format('  call %s(%s)', [FPtrTemp, ArgLine]));
          end
          else
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
              FmtArgElem := TASTExpr(TArrayLiteralExpr(FC.Args.Items[1]).Elements.Items[I])
            else
              FmtArgElem := TASTExpr(FC.Args.Items[I + 1]);
            IsFloatArg := FmtArgElem.ResolvedType.Kind in [tyDouble, tySingle];
            IsIntArg := FmtArgElem.ResolvedType.Kind in
              [tyInteger, tyBoolean, tyByte, tyUInt32, tyInt64, tyUInt64,
               tySmallInt, tyWord, tyEnum];

            { Tag: 0=int, 1=string/pointer, 2=float. }
            FmtSlotTemp := AllocTemp();
            EmitLine(Format('  %s =l add %s, %d', [FmtSlotTemp, FmtArrTemp, I * 16]));
            if IsFloatArg then
              EmitLine(Format('  storel 2, %s', [FmtSlotTemp]))
            else if IsIntArg then
              EmitLine(Format('  storel 0, %s', [FmtSlotTemp]))
            else
              EmitLine(Format('  storel 1, %s', [FmtSlotTemp]));
            FmtValTemp := AllocTemp();
            EmitLine(Format('  %s =l add %s, 8', [FmtValTemp, FmtSlotTemp]));

            if IsFloatArg then
            begin
              { Float: evaluate as a Double, then reinterpret the d-bits as l.
                'cast' between d and l is QBE's bit-preserving conversion —
                'storel <d-temp>' alone is a type error. }
              ArgTemp := EmitFloatArgAsDouble(FmtArgElem);
              FmtCastTemp := AllocTemp();
              EmitLine(Format('  %s =l cast %s', [FmtCastTemp, ArgTemp]));
              ArgTemp := FmtCastTemp;
            end
            else
            begin
              ArgTemp := EmitExpr(FmtArgElem);
              if IsIntArg then
              begin
                { Integer args may be w-typed; widen to l for storel. }
                QType := QbeTypeOf(FmtArgElem.ResolvedType);
                if QType = 'w' then
                begin
                  FmtSlotTemp := AllocTemp();
                  EmitLine(Format('  %s =l extsw %s', [FmtSlotTemp, ArgTemp]));
                  ArgTemp := FmtSlotTemp;
                end;
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

      if SameText(FC.Name,'Succ') or SameText(FC.Name,'Pred') then
      begin
        { Next/previous ordinal value: +1 / -1 on the integer-width value.
          Result type matches the argument (enum stays enum). }
        L := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T := AllocTemp();
        if SameText(FC.Name,'Succ') then
          EmitLine(Format('  %s =w add %s, 1', [T, L]))
        else
          EmitLine(Format('  %s =w sub %s, 1', [T, L]));
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
        if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
           (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyInterface) and
           (TASTExpr(FC.Args.Items[0]) is TIdentExpr) then
        begin
          ArgTemp := AllocTemp();
          EmitLine(Format('  %s =l loadl %s_obj',
            [ArgTemp, VarRef(TIdentExpr(TASTExpr(FC.Args.Items[0])).Name,
                             TIdentExpr(TASTExpr(FC.Args.Items[0])).IsGlobal)]));
        end
        else
          ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[0]));
        T        := AllocTemp();
        QType    := QbeTypeOf(FC.ResolvedType);
        if FC.ResolvedType.IsFloat() then
        begin
          { Double(X) / Single(X): emit a real numeric conversion, never a
            bit copy.  Integer sources convert with the matching
            signed/unsigned op; float sources widen/narrow as needed. }
          if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
             TASTExpr(FC.Args.Items[0]).ResolvedType.IsFloat() then
          begin
            if QbeTypeOf(TASTExpr(FC.Args.Items[0]).ResolvedType) = QType then
              EmitLine(Format('  %s =%s copy %s', [T, QType, ArgTemp]))
            else if QType = 'd' then
              EmitLine(Format('  %s =d exts %s', [T, ArgTemp]))
            else
              EmitLine(Format('  %s =s truncd %s', [T, ArgTemp]));
          end
          else
          begin
            case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
              tyInt64:  EmitLine(Format('  %s =%s sltof %s', [T, QType, ArgTemp]));
              tyUInt64: EmitLine(Format('  %s =%s ultof %s', [T, QType, ArgTemp]));
              tyUInt32: EmitLine(Format('  %s =%s uwtof %s', [T, QType, ArgTemp]));
            else
              EmitLine(Format('  %s =%s swtof %s', [T, QType, ArgTemp]));
            end;
          end;
        end
        else if FC.ResolvedType.Kind = tyByte then
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
      { sret: interface-returning function — 16-byte buffer for obj+itab. }
      if MDecl.ResolvedReturnType.Kind = tyInterface then
      begin
        SretBuf := AllocTemp();
        EmitLine(Format('  %s =l alloc8 16', [SretBuf]));
        EmitLine(Format('  call $memset(l %s, w 0, l 16)', [SretBuf]));
        EmitRecordCallSret(AExpr, SretBuf);
        Exit(SretBuf);
      end;
      { sret: jumbo-set-returning function — caller allocates a zero-init
        bitmap buffer and passes its address as the hidden first parameter. }
      if (MDecl.ResolvedReturnType.Kind = tySet) and
         TSetTypeDesc(MDecl.ResolvedReturnType).IsJumbo() then
      begin
        SetRS   := TSetTypeDesc(MDecl.ResolvedReturnType).RawSize();
        SretBuf := AllocTemp();
        EmitLine(Format('  %s =l alloc8 %d', [SretBuf, SetRS]));
        EmitLine(Format('  call $memset(l %s, w 0, l %d)', [SretBuf, SetRS]));
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
              else
                { Static array, dynamic array, or open-array variable. }
                ArgLine := ArgLine + ', ' +
                  OpenArrayArgFragment(TASTExpr(FC.Args.Items[I]));
            end
            else if Par.IsVarParam then
              ArgLine := ArgLine + Format(', l %s',
                [EmitLValueAddr(TASTExpr(FC.Args.Items[I]))])
            else if (Par.ResolvedType <> nil) and
                    (Par.ResolvedType.Kind = tyInterface) then
            begin
              EmitInterfaceExprPair(TASTExpr(FC.Args.Items[I]),
                ArgTemp, ArgTemp2, Par.ResolvedType);
              ArgLine := ArgLine + Format(', l %s, l %s', [ArgTemp, ArgTemp2]);
            end
            else
            begin
              ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[I]));
              while ArgTemps.Count < I do ArgTemps.Add('');
              ArgTemps.Add(ArgTemp);
              EnsureConstStringRef(ArgTemp, Par, TASTExpr(FC.Args.Items[I]), MDecl.Params);
              ArgTemp := CoerceArg(ArgTemp, TASTExpr(FC.Args.Items[I]), QbeTypeOf(Par.ResolvedType));
              ArgLine := ArgLine + Format(', %s %s',
                [QbeParamTypeOf(Par.ResolvedType), ArgTemp]);
            end;
          end;
          T := AllocTemp();
          EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FuncName, ArgLine]));
          FlushPendingReleases(PMark);
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
            else
              { Static array, dynamic array, or open-array variable. }
              ArgLine := ArgLine + OpenArrayArgFragment(TASTExpr(FC.Args.Items[I]));
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
              ArgTemp, ArgTemp2, Par.ResolvedType);
            ArgLine := ArgLine + Format('l %s, l %s', [ArgTemp, ArgTemp2]);
          end
          else
          begin
            ArgTemp := EmitExpr(TASTExpr(FC.Args.Items[I]));
            ArgTemps.Add(ArgTemp);
            EnsureConstStringRef(ArgTemp, Par, TASTExpr(FC.Args.Items[I]), MDecl.Params);
            ArgTemp := CoerceArg(ArgTemp, TASTExpr(FC.Args.Items[I]), QbeTypeOf(Par.ResolvedType));
            ArgLine := ArgLine + Format('%s %s', [QbeParamTypeOf(Par.ResolvedType), ArgTemp]);
          end;
        end;
        T := AllocTemp();
        EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FuncName, ArgLine]));
        FlushPendingReleases(PMark);
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
      PMark := PendingReleaseMark();
      IntfDesc := TInterfaceTypeDesc(MCallExpr.ResolvedClassType);
      if MCallExpr.ObjExpr <> nil then
        { Receiver is an expression (record/class field, as-cast, implicit
          Self field) — resolve its fat pointer rather than the split
          _obj/_itab slots that only a named interface local/global has. }
        EmitInterfaceExprPair(MCallExpr.ObjExpr, SelfTemp, VTblTemp)
      else
      begin
        SelfTemp := AllocTemp();
        EmitLine(Format('  %s =l loadl %s',
          [SelfTemp, IntfObjAddr(MCallExpr.ObjectName, MCallExpr.IsGlobal, MCallExpr.IsVarParam)]));
        VTblTemp := AllocTemp();
        EmitLine(Format('  %s =l loadl %s',
          [VTblTemp, IntfItabAddr(MCallExpr.ObjectName, MCallExpr.IsGlobal, MCallExpr.IsVarParam)]));
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
      { Evaluate arguments: var-param flags + resolved arg types decide the
        ABI — same rules as every other itab dispatch site. }
      ArgLine := Format('l %s', [SelfTemp]) +
        IntfDispatchArgFragment(IntfDesc,
          IntfDesc.MethodIndex(MCallExpr.Name), MCallExpr.Args);
      QType := QbeTypeOf(MCallExpr.ResolvedType);
      if QType = '' then QType := 'w';
      T := AllocTemp();
      EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FPtrTemp, ArgLine]));
      FlushPendingReleases(PMark);
      Exit(T);
    end;

    RT := TRecordTypeDesc(MCallExpr.ResolvedClassType);

    { Constructor call with args: TypeName.Create(args) }
    if MCallExpr.IsConstructorCall then
    begin
      SelfTemp := AllocTemp();
      if MCallExpr.IsMetaclassDispatch then
      begin
        { Metaclass-var dispatch: C.Create(args).  Load the metaclass value
          (a typeinfo pointer) and call _ClassCreate which reads size/cleanup/
          vtable from the typeinfo at runtime. }
        L := AllocTemp();
        EmitLine(Format('  %s =l loadl %s',
          [L, VarRef(MCallExpr.ObjectName, MCallExpr.IsGlobal)]));
        EmitLine(Format('  %s =l call $_ClassCreate(l %s)', [SelfTemp, L]));
      end
      else
      begin
        EmitLine(Format('  %s =l call $_ClassAlloc(l %d, l $_FieldCleanup_%s)',
          [SelfTemp, RT.TotalSize(), ClassSymName(QBEMangle(RT.Name))]));
        if RT.HasVTable() then
          EmitLine(Format('  storel $vtable_%s, %s',
            [ClassSymName(QBEMangle(RT.Name)), SelfTemp]));
      end;
      if FDebugMode then
      begin
        L := AllocTemp();
        EmitLine(Format('  %s =l add $typeinfo_%s, 16',
          [L, ClassSymName(QBEMangle(RT.Name))]));
        R := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [R, L]));
        EmitLine(Format('  call $_LeakTrackerRegister(l %s, l %s, l %s, l %d)',
          [SelfTemp, R, Self.EmitStrLit(FCurrentUnitName), MCallExpr.Line]));
      end;
      { If there's a user-defined Create method, call it }
      if MCallExpr.ResolvedMethod <> nil then
      begin
        MDecl   := TMethodDecl(MCallExpr.ResolvedMethod);
        PMark   := PendingReleaseMark();
        ArgLine := Format('l %s', [SelfTemp]);
        ArgTemps := TStringList.Create();
        try
          for I := 0 to MCallExpr.Args.Count - 1 do
          begin
            Par := TMethodParam(MDecl.Params.Items[I]);
            if Par.IsOpenArray then
            begin
              ArgTemps.Add('');
              ArgLine := ArgLine + ', ' +
                OpenArrayArgFragment(TASTExpr(MCallExpr.Args.Items[I]));
            end
            else if Par.IsVarParam then
            begin
              ArgTemps.Add('');
              ArgLine := ArgLine + Format(', l %s',
                [EmitLValueAddr(TASTExpr(MCallExpr.Args.Items[I]))]);
            end
            else if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyInterface) then
            begin
              ArgTemps.Add('');
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
              EnsureConstStringRef(ArgTemp, Par, TASTExpr(MCallExpr.Args.Items[I]), MDecl.Params);
              ArgTemp := CoerceArg(ArgTemp, TASTExpr(MCallExpr.Args.Items[I]),
                QbeTypeOf(Par.ResolvedType));
              ArgLine := ArgLine + Format(', %s %s',
                [QbeParamTypeOf(Par.ResolvedType), ArgTemp]);
            end;
          end;
          if MCallExpr.IsMetaclassDispatch and (MDecl.VTableSlot >= 0) then
          begin
            { Indirect ctor call via vtable: load vptr from instance[0],
              then load ctor address from vtable[ctorSlot]. }
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
            if MDecl.OwnerTypeName <> '' then
              FuncName := '$' + MethodEmitName(MDecl, MDecl.OwnerTypeName, MCallExpr.Name)
            else
              FuncName := '$' + MethodEmitName(MDecl, RT.Name, MCallExpr.Name);
            EmitLine(Format('  call %s(%s)', [FuncName, ArgLine]));
          end;
          FlushPendingReleases(PMark);
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
    { sret: interface-returning method }
    if MDecl.ResolvedReturnType.Kind = tyInterface then
    begin
      SretBuf := AllocTemp();
      EmitLine(Format('  %s =l alloc8 16', [SretBuf]));
      EmitLine(Format('  call $memset(l %s, w 0, l 16)', [SretBuf]));
      EmitRecordCallSret(AExpr, SretBuf);
      Exit(SretBuf);
    end;
    { sret: jumbo-set-returning method }
    if (MDecl.ResolvedReturnType.Kind = tySet) and
       TSetTypeDesc(MDecl.ResolvedReturnType).IsJumbo() then
    begin
      SetRS   := TSetTypeDesc(MDecl.ResolvedReturnType).RawSize();
      SretBuf := AllocTemp();
      EmitLine(Format('  %s =l alloc8 %d', [SretBuf, SetRS]));
      EmitLine(Format('  call $memset(l %s, w 0, l %d)', [SretBuf, SetRS]));
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
    PMark := PendingReleaseMark();
    ArgLine := Format('l %s', [SelfTemp]);
    ArgTemps := TStringList.Create();
    for I := 0 to MCallExpr.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Items[I]);
      if Par.IsOpenArray then
      begin
        ArgTemps.Add('');
        ArgLine := ArgLine + ', ' +
          OpenArrayArgFragment(TASTExpr(MCallExpr.Args.Items[I]));
      end
      else if Par.IsVarParam then
      begin
        ArgTemps.Add('');
        ArgLine := ArgLine + Format(', l %s',
          [EmitLValueAddr(TASTExpr(MCallExpr.Args.Items[I]))]);
      end
      else if (Par.ResolvedType <> nil) and (Par.ResolvedType.Kind = tyInterface) then
      begin
        ArgTemps.Add('');
        ArgLine := ArgLine + InterfaceArgFragment(TASTExpr(MCallExpr.Args.Items[I]),
          Par.ResolvedType);
      end
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args.Items[I]));
        ArgTemps.Add(ArgTemp);
        EnsureConstStringRef(ArgTemp, Par, TASTExpr(MCallExpr.Args.Items[I]), MDecl.Params);
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
    FlushPendingReleases(PMark);
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
        PropTgt := PropAccessorTarget(FldAccess.PropOwnerType,
          FldAccess.PropRead.ReadMethod, FldAccess.PropAccessorVSlot, L);
        T := AllocTemp();
        if FldAccess.PropIndexExpr <> nil then
        begin
          IdxTemp  := EmitExpr(FldAccess.PropIndexExpr);
          IdxQType := QbeTypeOf(FldAccess.PropRead.IndexTypeDesc);
          EmitLine(Format('  %s =%s call %s(l %s, %s %s)',
            [T, QType, PropTgt, L, IdxQType, IdxTemp]));
        end
        else
          EmitLine(Format('  %s =%s call %s(l %s)',
            [T, QType, PropTgt, L]));
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
      if IsAggregateAddrType(FldAccess.FieldInfo.TypeDesc) then
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
        QType := QbeTypeOf(FldAccess.PropRead.TypeDesc);
        PropTgt := PropAccessorTarget(FldAccess.PropOwnerType,
          FldAccess.PropRead.ReadMethod, FldAccess.PropAccessorVSlot, L);
        T     := AllocTemp();
        if FldAccess.PropIndexExpr <> nil then
        begin
          IdxTemp  := EmitExpr(FldAccess.PropIndexExpr);
          IdxQType := QbeTypeOf(FldAccess.PropRead.IndexTypeDesc);
          EmitLine(Format('  %s =%s call %s(l %s, %s %s)',
            [T, QType, PropTgt, L, IdxQType, IdxTemp]));
        end
        else
          EmitLine(Format('  %s =%s call %s(l %s)',
            [T, QType, PropTgt, L]));
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
      if IsAggregateAddrType(FldAccess.FieldInfo.TypeDesc) then
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
      else if MDecl.ResolvedReturnType.Kind = tyInterface then
      begin
        SretBuf := AllocTemp();
        EmitLine(Format('  %s =l alloc8 16', [SretBuf]));
        EmitLine(Format('  call $memset(l %s, w 0, l 16)', [SretBuf]));
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
      EmitLine(Format('  %s =l loadl %s',
        [SelfTemp, IntfObjAddr(FldAccess.RecordName, FldAccess.IsGlobal, FldAccess.IsVarParam)]));
      VTblTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s',
        [VTblTemp, IntfItabAddr(FldAccess.RecordName, FldAccess.IsGlobal, FldAccess.IsVarParam)]));
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
        { String class const via type: return the literal's data pointer,
          exactly like a plain string literal (EmitStrLit returns the temp;
          the consumer manages ARC).  The previous code called a non-existent
          $_StringRetain and double-wrapped the temp in '$'. }
        Result := EmitStrLit(FldAccess.ConstString)
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
        L := AllocTemp();
        EmitLine(Format('  %s =l add $typeinfo_%s, 16',
          [L, ClassSymName(QBEMangle(FldAccess.ResolvedType.Name))]));
        R := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [R, L]));
        EmitLine(Format('  call $_LeakTrackerRegister(l %s, l %s, l %s, l %d)',
          [T, R, Self.EmitStrLit(FCurrentUnitName), FldAccess.Line]));
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
      { String field subscript: Rec.Field[N] — 0-based, like every other
        Blaise subscript.  The receiver base follows the same ladder as
        the array path: class/var-param slots hold a POINTER (load it),
        implicit Self starts from the Self pointer, inline records use
        the slot address directly. }
      L := AllocTemp();
      if FldAccess.IsImplicitSelf then
      begin
        EmitLine(Format('  %s =l loadl %%_var_Self', [L]));
        if (FldAccess.ImplicitBaseInfo <> nil) and
           (FldAccess.ImplicitBaseInfo.Offset > 0) then
        begin
          T := AllocTemp();
          EmitLine(Format('  %s =l add %s, %d',
            [T, L, FldAccess.ImplicitBaseInfo.Offset]));
          L := T;
        end;
        if FldAccess.IsClassAccess then
        begin
          T := AllocTemp();
          EmitLine(Format('  %s =l loadl %s', [T, L]));
          L := T;
        end;
      end
      else if FldAccess.IsClassAccess or FldAccess.IsVarParam then
      begin
        EmitLine(Format('  %s =l loadl %s', [L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
        if FldAccess.IsClassAccess and FldAccess.IsVarParam then
        begin
          { var-param class: slot -> caller var -> instance. }
          T := AllocTemp();
          EmitLine(Format('  %s =l loadl %s', [T, L]));
          L := T;
        end;
      end
      else
        EmitLine(Format('  %s =l copy %s', [L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
      if FldAccess.FieldInfo.Offset > 0 then
      begin
        Ptr := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d', [Ptr, L, FldAccess.FieldInfo.Offset]));
        L := Ptr;
      end;
      { Load the string pointer (the field value) and read byte N. }
      Ptr := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [Ptr, L]));
      T := EmitExpr(FldAccess.PropIndexExpr);
      IdxTemp := AllocTemp();
      EmitLine(Format('  %s =l extsw %s', [IdxTemp, T]));
      Ptr2 := AllocTemp();
      EmitLine(Format('  %s =l add %s, %s', [Ptr2, Ptr, IdxTemp]));
      T := AllocTemp();
      EmitLine(Format('  %s =w loadub %s', [T, Ptr2]));
      Result := T;
    end
    else if FldAccess.IsArrayAccess then
    begin
      { Array field subscript: Rec.Arr[I] — load array base, compute element
        addr.  The receiver base address depends on the leaf shape: class
        variables and var-params hold a POINTER in their slot (load it);
        implicit-Self fields start from the Self pointer; inline records use
        the slot address directly. }
      L := AllocTemp();
      if FldAccess.IsImplicitSelf then
      begin
        EmitLine(Format('  %s =l loadl %%_var_Self', [L]));
        if (FldAccess.ImplicitBaseInfo <> nil) and
           (FldAccess.ImplicitBaseInfo.Offset > 0) then
        begin
          T := AllocTemp();
          EmitLine(Format('  %s =l add %s, %d',
            [T, L, FldAccess.ImplicitBaseInfo.Offset]));
          L := T;
        end;
        if FldAccess.IsClassAccess then
        begin
          T := AllocTemp();
          EmitLine(Format('  %s =l loadl %s', [T, L]));
          L := T;
        end;
      end
      else if FldAccess.IsClassAccess or FldAccess.IsVarParam then
      begin
        EmitLine(Format('  %s =l loadl %s', [L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
        if FldAccess.IsClassAccess and FldAccess.IsVarParam then
        begin
          { var-param class: slot -> caller var -> instance. }
          T := AllocTemp();
          EmitLine(Format('  %s =l loadl %s', [T, L]));
          L := T;
        end;
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
      end
      else
        raise ECodeGenError.Create(Format(
          'IsArrayAccess on non-array field ''%s'' (kind %d) at line %d',
          [FldAccess.FieldName, Ord(FldAccess.FieldInfo.TypeDesc.Kind),
           FldAccess.Line]));
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
      QType := QbeTypeOf(FldAccess.PropRead.TypeDesc);
      PropTgt := PropAccessorTarget(FldAccess.PropOwnerType,
        FldAccess.PropRead.ReadMethod, FldAccess.PropAccessorVSlot, L);
      T     := AllocTemp();
      if FldAccess.PropIndexExpr <> nil then
      begin
        IdxTemp  := EmitExpr(FldAccess.PropIndexExpr);
        IdxQType := QbeTypeOf(FldAccess.PropRead.IndexTypeDesc);
        EmitLine(Format('  %s =%s call %s(l %s, %s %s)',
          [T, QType, PropTgt, L, IdxQType, IdxTemp]));
      end
      else
        EmitLine(Format('  %s =%s call %s(l %s)',
          [T, QType, PropTgt, L]));
      Result := T;
    end
    else if FldAccess.IsClassAccess then
    begin
      { Load heap pointer, then load field.  var-param class: the slot holds
        the caller variable's address — one more load first. }
      L := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [L, VarRef(FldAccess.RecordName, FldAccess.IsGlobal)]));
      if FldAccess.IsVarParam then
      begin
        Ptr := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [Ptr, L]));
        L := Ptr;
      end;
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
      { Record / static-array field: inline aggregate storage — return the
        field ADDRESS, not a loaded scalar.  (Mirrors the record-field branch
        below; without this, passing a class-field record/array by value emitted
        `loadl` of the field address and passed the first 8 bytes as the
        aggregate, crashing the callee.) }
      if IsAggregateAddrType(FldAccess.FieldInfo.TypeDesc) then
        Exit(Ptr);
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
      if IsAggregateAddrType(FldAccess.FieldInfo.TypeDesc) then
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
      { Aggregate-address fields (record, static array, jumbo set): return the
        field's storage ADDRESS, not a loaded value.  A static-array field
        lives inline in the object, so a bare `FD` must yield &FD — loading it
        (as the scalar path below does) would dereference the first bytes of
        the array as a pointer and corrupt FD[i] access. }
      if (AExpr.ResolvedType <> nil) and
         IsAggregateAddrType(AExpr.ResolvedType) then
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
             ((AExpr.ResolvedType.Kind <> tyStaticArray) and
              not IsAggregateAddrType(AExpr.ResolvedType))) then
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
         IsAggregateAddrType(AExpr.ResolvedType) then
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
    else if TIdentExpr(AExpr).ParamMode = pmJumboSetValue then
    begin
      { Jumbo set value param: the QBE backend spills it into a local inline
        bitmap slot (value semantics), so %_var_X IS the bitmap address —
        return it directly without a load. }
      Exit(VarRef(TIdentExpr(AExpr).Name, TIdentExpr(AExpr).IsGlobal));
    end
    else if (TIdentExpr(AExpr).ParamMode <> pmNone) and
            (AExpr.ResolvedType <> nil) and
            IsAggregateAddrType(AExpr.ResolvedType) then
    begin
      { Var param of aggregate type: the param slot already holds the address
        of the caller's storage — load and return that as the storage address. }
      EmitLine(Format('  %s =l loadl %%_var_%s', [T, TIdentExpr(AExpr).Name]));
      Exit(T);
    end
    else if TIdentExpr(AExpr).ParamMode <> pmNone then
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
            IsAggregateAddrType(AExpr.ResolvedType) then
    begin
      { Aggregate variable — return its storage address directly (no load). }
      Exit(VarRef(TIdentExpr(AExpr).Name, TIdentExpr(AExpr).IsGlobal));
    end
    else if (AExpr.ResolvedType <> nil) and
            (AExpr.ResolvedType.Kind = tyInterface) then
    begin
      { Interface ident used as a single value (nil/identity compare): the
        fat pointer lives in split _obj/_itab slots — there is no single
        %_var_Name slot.  Load the obj half; this also covers an interface
        Result, whose _obj slot holds the sret-buffer address. }
      EmitLine(Format('  %s =l loadl %s',
        [T, IntfObjAddr(TIdentExpr(AExpr).Name, TIdentExpr(AExpr).IsGlobal,
            False)]));
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
    { String relational order: _StringCompare returns <0 / 0 / >0 (strcmp-like);
      compare that word against 0 with the corresponding signed op.  Without
      this the operands fall through to the generic comparison path, which
      compares the string POINTERS (and emits a mismatched-type compare that
      makes QBE abort: selcmp k != Kw). }
    if (BinExpr.Left.ResolvedType <> nil) and
       BinExpr.Left.ResolvedType.IsString() and
       (BinExpr.Op in [boLT, boGT, boLE, boGE]) then
    begin
      ArgTemp := AllocTemp();
      EmitLine(Format('  %s =w call $_StringCompare(l %s, l %s)', [ArgTemp, L, R]));
      case BinExpr.Op of
        boLT: EmitLine(Format('  %s =w csltw %s, 0', [T, ArgTemp]));
        boGT: EmitLine(Format('  %s =w csgtw %s, 0', [T, ArgTemp]));
        boLE: EmitLine(Format('  %s =w cslew %s, 0', [T, ArgTemp]));
        boGE: EmitLine(Format('  %s =w csgew %s, 0', [T, ArgTemp]));
      end;
      Exit(T);
    end;
    { Set membership: elem in SetVar }
    if BinExpr.Op = boIn then
    begin
      { Jumbo set: R is the bitmap address, L the ordinal — _SetIn(R, L). }
      if (BinExpr.Right.ResolvedType <> nil) and
         (BinExpr.Right.ResolvedType.Kind = tySet) and
         TSetTypeDesc(BinExpr.Right.ResolvedType).IsJumbo() then
      begin
        EmitLine(Format('  %s =w call $_SetIn(l %s, w %s)', [T, R, L]));
        Exit(T);
      end;
      { Small set: ((set >> ord) & 1) AND (ord < BitCount).  The range guard
        matters when the set is sized to a literal's max ordinal (e.g.
        'X in [low members]') but the tested element's ordinal may exceed the
        set width — a shift past the register width is undefined, so the guard
        forces a 0 result for out-of-range ordinals. }
      SQT := QbeTypeOf(BinExpr.Right.ResolvedType);
      ArgTemp := AllocTemp();
      EmitLine(Format('  %s =%s shr %s, %s', [ArgTemp, SQT, R, L]));
      T2 := AllocTemp();
      EmitLine(Format('  %s =w and %s, 1', [T2, ArgTemp]));
      ArgTemp := AllocTemp();
      EmitLine(Format('  %s =w csltw %s, %d',
        [ArgTemp, L, TSetTypeDesc(BinExpr.Right.ResolvedType).BitCount]));
      EmitLine(Format('  %s =w and %s, %s', [T, T2, ArgTemp]));
      Exit(T);
    end;

    { Set arithmetic: union, difference, intersection, equality }
    if (BinExpr.Left.ResolvedType <> nil) and
       (BinExpr.Left.ResolvedType.Kind = tySet) then
    begin
      { Jumbo set: L and R are bitmap addresses.  Binary set ops write into a
        fresh result buffer and return its address; equality returns a w 0/1.
        NBytes is the (compile-time) bitmap length. }
      if TSetTypeDesc(BinExpr.Left.ResolvedType).IsJumbo() then
      begin
        SetNB := TSetTypeDesc(BinExpr.Left.ResolvedType).RawByteSize();
        SetRS := TSetTypeDesc(BinExpr.Left.ResolvedType).RawSize();
        case BinExpr.Op of
          boAdd:
          begin
            EmitLine(Format('  %s =l alloc8 %d', [T, SetRS]));
            EmitLine(Format('  call $_SetUnion(l %s, l %s, l %s, w %d)',
              [T, L, R, SetNB]));
          end;
          boSub:
          begin
            EmitLine(Format('  %s =l alloc8 %d', [T, SetRS]));
            EmitLine(Format('  call $_SetDiff(l %s, l %s, l %s, w %d)',
              [T, L, R, SetNB]));
          end;
          boMul:
          begin
            EmitLine(Format('  %s =l alloc8 %d', [T, SetRS]));
            EmitLine(Format('  call $_SetInter(l %s, l %s, l %s, w %d)',
              [T, L, R, SetNB]));
          end;
          boEQ:
            EmitLine(Format('  %s =w call $_SetEqual(l %s, l %s, w %d)',
              [T, L, R, SetNB]));
          boNE:
          begin
            ArgTemp := AllocTemp();
            EmitLine(Format('  %s =w call $_SetEqual(l %s, l %s, w %d)',
              [ArgTemp, L, R, SetNB]));
            EmitLine(Format('  %s =w ceqw %s, 0', [T, ArgTemp]));
          end;
          boLE:  { subset: A subset of B }
            EmitLine(Format('  %s =w call $_SetSubset(l %s, l %s, w %d)',
              [T, L, R, SetNB]));
          boGE:  { superset: B subset of A }
            EmitLine(Format('  %s =w call $_SetSubset(l %s, l %s, w %d)',
              [T, R, L, SetNB]));
        else
          raise ECodeGenError.Create(Format(
            'Operator not supported for set types at line %d', [BinExpr.Line]));
        end;
        Exit(T);
      end;
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
        boLE,  { subset:   s <= t  iff  (s and not t) = 0 }
        boGE:  { superset: s >= t  iff  (t and not s) = 0 }
        begin
          { Pick which operand must be fully contained in the other. }
          if BinExpr.Op = boLE then
          begin ArgTemp := L; CmpTemp := R; end
          else
          begin ArgTemp := R; CmpTemp := L; end;
          { notOther := ~CmpTemp ; rem := ArgTemp and notOther ; result := rem = 0 }
          SetTmpA := AllocTemp();
          EmitLine(Format('  %s =%s xor %s, -1', [SetTmpA, SQT, CmpTemp]));
          SetTmpB := AllocTemp();
          EmitLine(Format('  %s =%s and %s, %s', [SetTmpB, SQT, ArgTemp, SetTmpA]));
          if SQT = 'l' then
            EmitLine(Format('  %s =w ceql %s, 0', [T, SetTmpB]))
          else
            EmitLine(Format('  %s =w ceqw %s, 0', [T, SetTmpB]));
        end;
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
        (BinExpr.Left.ResolvedType.Kind in [tyClass, tyNil, tyPointer, tyMetaClass, tyInterface])) or
       ((BinExpr.Right.ResolvedType <> nil) and
        (BinExpr.Right.ResolvedType.Kind in [tyClass, tyNil, tyPointer, tyMetaClass, tyInterface])) then
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
      if BinExpr.Op in [boDiv, boMod] then
        Self.EmitDivZeroGuard(R, True);
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
      if BinExpr.Op in [boDiv, boMod] then
        Self.EmitDivZeroGuard(R, False);
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
       IsAggregateAddrType(AExpr.ResolvedType) then
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
  else if AExpr is TInheritedCallExpr then
    Result := EmitInheritedCallExpr(TInheritedCallExpr(AExpr))
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
  if AExpr is TNilLiteral then
  begin
    OldObj := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [OldObj, AObjSlotPtr]));
    EmitLine(Format('  call $_ClassRelease(l %s)', [OldObj]));
    EmitLine(Format('  storel 0, %s', [AObjSlotPtr]));
    EmitLine(Format('  storel 0, %s', [AItabSlotPtr]));
    Exit;
  end;

  if IsInterfaceCall(AExpr) then
  begin
    { Sret convention: allocate a 16-byte buffer, call the function with
      it as a hidden first arg, then load obj+itab from the buffer.  The
      callee already AddRef'd into the buffer, so no caller-side AddRef. }
    NewItab := AllocTemp();
    EmitLine(Format('  %s =l alloc8 16', [NewItab]));
    EmitLine(Format('  call $memset(l %s, w 0, l 16)', [NewItab]));
    EmitRecordCallSret(AExpr, NewItab);
    NewObj := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [NewObj, NewItab]));
    OldObj := AllocTemp();
    EmitLine(Format('  %s =l add %s, 8', [OldObj, NewItab]));
    NewItab := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [NewItab, OldObj]));
    OldObj := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [OldObj, AObjSlotPtr]));
    EmitLine(Format('  call $_ClassRelease(l %s)', [OldObj]));
    EmitLine(Format('  storel %s, %s', [NewObj, AObjSlotPtr]));
    EmitLine(Format('  storel %s, %s', [NewItab, AItabSlotPtr]));
    Exit;
  end;

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
  out AObjTemp, AItabTemp: string; AIntfType: TTypeDesc = nil);
var
  ObjT, ItabT: string;
  OkT, LblOk, LblFail, LblEnd: string;
  AE: TAsExpr;
  IE: TIdentExpr;
  IEFld: TFieldInfo;
  ClassRT: TRecordTypeDesc;
  ItabName: string;
begin
  { Class instance narrowed to an interface: the value is a plain class
    pointer (obj), paired with the static itab for this (class, interface).
    Covers passing a class variable/global/field directly to an interface
    parameter — mirrors the class->interface assignment path.  Must precede
    the TIdentExpr branch, which assumes interface-typed split slots. }
  if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyClass) and
     (AIntfType <> nil) and (AIntfType.Kind = tyInterface) then
  begin
    ClassRT  := TRecordTypeDesc(AExpr.ResolvedType);
    ItabName := '$itab_' + QBEMangle(ClassSymName(ClassRT.Name)) + '_' +
                QBEMangle(AIntfType.Name);
    AObjTemp  := EmitExpr(AExpr);
    AItabTemp := AllocTemp();
    EmitLine(Format('  %s =l copy %s', [AItabTemp, ItabName]));
    Exit;
  end;

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
    else if IE.ParamMode <> pmNone then
    begin
      { var/out interface param: the slot holds the address of the caller's
        contiguous fat pointer — obj at +0, itab at +8. }
      ObjT := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [ObjT, VarRef(IE.Name, False)]));
      AObjTemp  := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [AObjTemp, ObjT]));
      ItabT := AllocTemp();
      EmitLine(Format('  %s =l add %s, 8', [ItabT, ObjT]));
      AItabTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [AItabTemp, ItabT]));
    end
    else
    begin
      AObjTemp  := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [AObjTemp,
        IntfObjAddr(IE.Name, IE.IsGlobal, False)]));
      AItabTemp := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [AItabTemp,
        IntfItabAddr(IE.Name, IE.IsGlobal, False)]));
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
  else if IsInterfaceCall(AExpr) then
  begin
    { Interface-returning CALL as the pair source (function-call receiver:
      GetDriver().Info(), or a chained itab call).  Must be checked before
      the stored-field branch — a zero-arg itab call is field-access shaped.
      Evaluate via the sret convention into a fresh 16-byte buffer and load
      the pair.  The callee AddRef'd into the buffer, so the pair is owned
      (+1) — defer the obj release to the consuming dispatch site (after
      its call instruction). }
    ObjT := AllocTemp();
    EmitLine(Format('  %s =l alloc8 16', [ObjT]));
    EmitLine(Format('  call $memset(l %s, w 0, l 16)', [ObjT]));
    EmitRecordCallSret(AExpr, ObjT);
    AObjTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [AObjTemp, ObjT]));
    ItabT := AllocTemp();
    EmitLine(Format('  %s =l add %s, 8', [ItabT, ObjT]));
    AItabTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [AItabTemp, ItabT]));
    FPendingObjReleases.Add(AObjTemp);
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
  else if (AExpr is TStringSubscriptExpr) and
          (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
          (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyStaticArray) then
  begin
    { Interface element in a STATIC array: EmitStringSubscriptExpr's
      static-array branch returns the contiguous element address when
      the element type is tyInterface (obj at +0, itab at +8).  Same
      layout as a record field — just a different address source.
      Dynamic-array subscripts return a loaded VALUE, not an address,
      so they must keep hitting the fail-loud else below until they
      get their own handling. }
    ObjT := EmitExpr(AExpr);
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

function TCodeGenQBE.InterfaceArgFragment(AExpr: TASTExpr;
  AIntfType: TTypeDesc = nil): string;
var
  ObjTemp, ItabTemp: string;
begin
  EmitInterfaceExprPair(AExpr, ObjTemp, ItabTemp, AIntfType);
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
  OutRef   := IntfObjAddr(AExpr.OutVarName, AExpr.OutVarIsGlobal, False);
  ItabTemp := AllocTemp();
  EmitLine(Format('  %s =l call $_GetItab(l %s, l $typeinfo_%s)',
    [ItabTemp, ObjTemp, ClassSymName(AExpr.IntfTypeName)]));
  { ARC: retain new obj, release old obj slot of out-var }
  OldTemp := AllocTemp();
  EmitLine(Format('  %s =l loadl %s', [OldTemp, OutRef]));
  EmitLine(Format('  call $_ClassAddRef(l %s)',  [ObjTemp]));
  EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
  EmitLine(Format('  storel %s, %s',  [ObjTemp, OutRef]));
  EmitLine(Format('  storel %s, %s', [ItabTemp,
    IntfItabAddr(AExpr.OutVarName, AExpr.OutVarIsGlobal, False)]));
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
  Clean: Boolean;
begin
  { Fast path: the overwhelming majority of names contain none of the
    mangled characters — return the input unchanged instead of rebuilding
    it with one concat (and its ARC churn) per character. }
  Clean := True;
  for I := 0 to Length(AName) - 1 do
  begin
    C := StrAt(AName, I);
    if (C = 60) or (C = 62) or (C = 44) or (C = 36) or (C = 64) or
       (C = 94) then
    begin
      Clean := False;
      break;
    end;
  end;
  if Clean then
    Exit(AName);
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
  { Program-scope classes keep bare names: uSemantic.CurrentUnitPrefix gives
    program-scope methods unprefixed ResolvedQbeNames, so reference sites
    (itabs, property setter calls) must not add a prefix either. }
  if (FProgramName <> '') and SameText(Owner, FProgramName) then Exit;
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

function TCodeGenQBE.PropAccessorTarget(const AOwnerType, AMethod: string;
  AVSlot: Integer; ASelfTemp: string): string;
var
  VTbl:    string;
  SlotPtr: string;
  FPtr:    string;
begin
  if AVSlot >= 0 then
  begin
    VTbl := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [VTbl, ASelfTemp]));
    SlotPtr := AllocTemp();
    EmitLine(Format('  %s =l add %s, %d', [SlotPtr, VTbl, (AVSlot + 1) * 8]));
    FPtr := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [FPtr, SlotPtr]));
    Result := FPtr;
  end
  else
    Result := Format('$%s%s_%s',
      [ClassUnitPrefix(AOwnerType), QBEMangle(AOwnerType), AMethod]);
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
  FCurrentUnitName := AProg.Name;
  FProgramName := AProg.Name;

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
  SavedUnit: string;
begin
  FOutput.Clear();
  FStrLits.Clear();
  FStrLitsEmitted := 0;
  FTempCount  := 0;
  FLabelCount := 0;
  FCurrentUnitName := AUnit.Name;

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
        { Generic instance method bodies are template clones — attribute
          allocation sites to the template's defining unit. }
        SavedUnit := FCurrentUnitName;
        for I := 0 to AUnit.GenericInstances.Count - 1 do
        begin
          GI := TGenericInstance(AUnit.GenericInstances.Items[I]);
          if GI.DefUnitName <> '' then
            FCurrentUnitName := GI.DefUnitName
          else
            FCurrentUnitName := SavedUnit;
          for J := 0 to GI.ClassDef.Methods.Count - 1 do
          begin
            MDecl := TMethodDecl(GI.ClassDef.Methods.Items[J]);
            if MDecl.Body <> nil then
              EmitMethodDef(GI.TypeName, MDecl);
          end;
        end;
        FCurrentUnitName := SavedUnit;
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
          VLine := Format('%s$vtable_%s = { l $typeinfo_%s',
            [VTableDataPrefix(), QBEMangle(GI.TypeName), QBEMangle(GI.TypeName)]);
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

procedure TCodeGenQBE.SetOpdfMode(AEnabled: Boolean);
begin
  FOpdfMode := AEnabled;
end;

function TCodeGenQBE.GetDebugFacts: TDbgFacts;
begin
  { QBE assigns frames and addresses itself — no exact facts available. }
  Result := nil;
end;

function TCodeGenQBE.VTableDataPrefix: string;
begin
  if FOpdfMode then
    Result := 'export data '
  else
    Result := 'data ';
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
  SavedUnit:    string;
begin
  { No clears — output and string literal table accumulate across calls.
    Counter resets are safe: QBE temps and block labels are function-scoped. }
  FTempCount  := 0;
  FLabelCount := 0;
  FCurrentUnitName := AUnit.Name;

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
          EmitMethodDefs and EmitFieldCleanupFns for AProg.GenericInstances.
          Method bodies are template clones — attribute allocation sites to
          the template's defining unit. }
        SavedUnit := FCurrentUnitName;
        for I := 0 to AUnit.GenericInstances.Count - 1 do
        begin
          GI := TGenericInstance(AUnit.GenericInstances.Items[I]);
          if GI.DefUnitName <> '' then
            FCurrentUnitName := GI.DefUnitName
          else
            FCurrentUnitName := SavedUnit;
          for J := 0 to GI.ClassDef.Methods.Count - 1 do
          begin
            MDecl := TMethodDecl(GI.ClassDef.Methods.Items[J]);
            if MDecl.Body <> nil then
              EmitMethodDef(QBEMangle(GI.TypeName), MDecl);
          end;
          EmitFieldCleanupFn(ClassSymName(QBEMangle(GI.TypeName)),
                             TRecordTypeDesc(GI.TypeDesc));
        end;
        FCurrentUnitName := SavedUnit;
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
  FCurrentUnitName := AProg.Name;
  FProgramName := AProg.Name;

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
    { Nested static-array elements: A[I] where A: array[..] of array[..] of T.
      The element is an inline sub-array; return its address so a further
      subscript A[I][J] can index into it (mirrors the record case). }
    if SAT.ElementType.Kind = tyStaticArray then
    begin
      Exit(ElemPtr);
    end;
    { Interface elements: the 16-byte fat pointer lives contiguously at
      ElemPtr (obj at +0, itab at +8).  Return the address; consumers
      (assignment to another interface, method dispatch, arg passing)
      route through EmitInterfaceExprPair, which has a TStringSubscriptExpr
      case that loads both halves from here. }
    if SAT.ElementType.Kind = tyInterface then
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
    EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
    EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
    EmitLine(Format('  %s =l add %s, %s', [ElemPtr, StrPtr, Offset]));
    { Record elements: return address directly — records are by-value via pointer }
    if ElemType.ElementType.Kind = tyRecord then
    begin
      Exit(ElemPtr);
    end;
    ByteVal := AllocTemp();
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
    EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
    EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
    EmitLine(Format('  %s =l add %s, %s', [ElemPtr, StrPtr, Offset]));
    { Record elements: return address directly — records are by-value via pointer }
    if TDynArrayTypeDesc(AExpr.StrExpr.ResolvedType).ElementType.Kind = tyRecord then
    begin
      Exit(ElemPtr);
    end;
    ByteVal := AllocTemp();
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
    else if FldExpr.IsClassAccess then
    begin
      { Class field leaf: the variable's slot holds a POINTER to the heap
        object — load it so the field offset reaches the field, not a
        location adjacent to the slot itself.  (Without this, @Obj.Arr[I]
        computed `add $Obj, off` instead of `loadl $Obj; add .., off`,
        producing a garbage address.)  A var-param class slot holds the
        ADDRESS of the caller's variable, so load twice. }
      StrPtr := AllocTemp();
      EmitLine(Format('  %s =l loadl %s',
        [StrPtr, VarRef(FldExpr.RecordName, FldExpr.IsGlobal)]));
      if FldExpr.IsVarParam then
      begin
        ObjPtr := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [ObjPtr, StrPtr]));
        StrPtr := ObjPtr;
      end;
    end
    else if FldExpr.IsImplicitSelf then
    begin
      StrPtr := AllocTemp();
      EmitLine(Format('  %s =l loadl %%_var_Self', [StrPtr]));
      if (FldExpr.ImplicitBaseInfo <> nil) and
         (FldExpr.ImplicitBaseInfo.Offset > 0) then
      begin
        ObjPtr := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d',
          [ObjPtr, StrPtr, FldExpr.ImplicitBaseInfo.Offset]));
        StrPtr := ObjPtr;
      end;
      if FldExpr.IsClassAccess then
      begin
        ObjPtr := AllocTemp();
        EmitLine(Format('  %s =l loadl %s', [ObjPtr, StrPtr]));
        StrPtr := ObjPtr;
      end;
    end
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
  ObjTemp:    string;   { interface RHS obj slot }
  ItabTemp:   string;   { interface RHS itab slot or itab name literal }
  ItabPtr:    string;   { ElemPtr + 8, target of itab store }
  IntfDesc:   TInterfaceTypeDesc;
  DefProp:    TPropertyInfo;
  RecvTemp:   string;
  IdxQType:   string;
  ValQType:   string;
  PropTgt:    string;
begin
  { Default array property write: Obj[I] := V lowered to a setter call.
    Semantic set PropWriteInfo; ArrayName is the receiver, IndexExpr/ValueExpr
    are the setter args.  Dispatch through the vtable when the setter is
    virtual (PropAccessorVSlot >= 0), else a static call. }
  if AStmt.PropWriteInfo <> nil then
  begin
    DefProp  := TPropertyInfo(AStmt.PropWriteInfo);
    RecvTemp := AllocTemp();
    EmitLine(Format('  %s =l loadl %s',
      [RecvTemp, VarRef(AStmt.ArrayName, AStmt.IsGlobal)]));
    if AStmt.IsVarParam then
    begin
      ElemPtr := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [ElemPtr, RecvTemp]));
      RecvTemp := ElemPtr;
    end;
    IdxW     := EmitExpr(AStmt.IndexExpr);
    IdxQType := QbeTypeOf(DefProp.IndexTypeDesc);
    ElemVal  := EmitExpr(AStmt.ValueExpr);
    ValQType := QbeTypeOf(DefProp.TypeDesc);
    PropTgt  := PropAccessorTarget(AStmt.PropOwnerType, DefProp.WriteMethod,
      AStmt.PropAccessorVSlot, RecvTemp);
    EmitLine(Format('  call %s(l %s, %s %s, %s %s)',
      [PropTgt, RecvTemp, IdxQType, IdxW, ValQType, ElemVal]));
    Exit;
  end;
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
    if AStmt.IsVarParam then
    begin
      { var/out param: the slot holds the ADDRESS of the caller's variable,
        which in turn holds the char pointer — one extra dereference. }
      ElemPtr := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [ElemPtr, PCharBase]));
      PCharBase := ElemPtr;
      ElemPtr := AllocTemp();
    end;
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
    { Chained / multi-dimensional write A[I][J] := V where the inner array
      is itself a dynamic array: BaseExpr (A[I]) evaluates to the inner
      dynarray value — its data pointer.  No variable-slot load needed. }
    if AStmt.BaseExpr <> nil then
    begin
      PCharBase := EmitExpr(AStmt.BaseExpr);
    end
    { load the data pointer from the variable slot }
    else if AStmt.IsImplicitSelf then
    begin
      { ArrayName is a dyn-array field of Self: Self + offset holds the
        data pointer. }
      EmitLine(Format('  %s =l loadl %%_var_Self', [PCharBase]));
      if AStmt.ImplicitFieldInfo.Offset > 0 then
      begin
        ElemPtr := AllocTemp();
        EmitLine(Format('  %s =l add %s, %d',
          [ElemPtr, PCharBase, AStmt.ImplicitFieldInfo.Offset]));
        PCharBase := ElemPtr;
      end;
      ElemPtr := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [ElemPtr, PCharBase]));
      PCharBase := ElemPtr;
    end
    else if AStmt.IsGlobal then
      EmitLine(Format('  %s =l loadl $%s', [PCharBase, AStmt.ArrayName]))
    else if IsPromoted(AStmt.ArrayName) then
      EmitLine(Format('  %s =l copy %%_var_%s', [PCharBase, AStmt.ArrayName]))
    else
      EmitLine(Format('  %s =l loadl %%_var_%s', [PCharBase, AStmt.ArrayName]));
    if AStmt.IsVarParam then
    begin
      { var/out param: the slot holds the ADDRESS of the caller's variable,
        which in turn holds the data pointer — one extra dereference. }
      ElemPtr := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [ElemPtr, PCharBase]));
      PCharBase := ElemPtr;
      ElemPtr := AllocTemp();
    end;
    IdxW    := EmitExpr(AStmt.IndexExpr);
    IdxL    := AllocTemp();
    Offset  := AllocTemp();
    ElemPtr := AllocTemp();
    { Record elements: copy the record contents into the element slot
      (ARC-aware fieldwise copy), never a single 8-byte store. }
    if ElemType.Kind = tyRecord then
    begin
      EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
      EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
      EmitLine(Format('  %s =l add %s, %s', [ElemPtr, PCharBase, Offset]));
      ElemVal := EmitExpr(AStmt.ValueExpr);
      EmitRecordCopy(TRecordTypeDesc(ElemType), ElemPtr, ElemVal);
      Exit;
    end;
    if ElemType.Kind in [tyByte, tyBoolean] then
      ElemVal := EmitByteRhs(AStmt.ValueExpr)
    else
      ElemVal := EmitExpr(AStmt.ValueExpr);
    { Float element: coerce the value temp to the element width.  A literal
      like 1.5 evaluates to a `d` temp; storing it into a Single element needs
      a truncd first or QBE rejects the `stores`. }
    if ElemType.Kind in [tyDouble, tySingle] then
      ElemVal := CoerceArg(ElemVal, AStmt.ValueExpr, QbeTypeOf(ElemType));
    EmitLine(Format('  %s =l extsw %s', [IdxL, IdxW]));
    EmitLine(Format('  %s =l mul %s, %d', [Offset, IdxL, ElemSize]));
    EmitLine(Format('  %s =l add %s, %s', [ElemPtr, PCharBase, Offset]));
    case ElemType.Kind of
      tyByte, tyBoolean:           StoreInstr := 'storeb';
      tySmallInt, tyWord:          StoreInstr := 'storeh';
      tyInteger, tyUInt32, tyEnum: StoreInstr := 'storew';
      tyDouble:                    StoreInstr := 'stored';
      tySingle:                    StoreInstr := 'stores';
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
  if AStmt.BaseExpr <> nil then
  begin
    { Chained / multi-dimensional write A[I][J] := V: BaseExpr evaluates to
      the address of the inner array (a static-array element returns its
      address). }
    PCharBase := EmitExpr(AStmt.BaseExpr);
    EmitLine(Format('  %s =l add %s, %s', [ElemPtr, PCharBase, Offset]));
  end
  else if AStmt.IsImplicitSelf then
  begin
    { ArrayName is a static-array field of Self: the inline storage starts
      at Self + field offset. }
    PCharBase := AllocTemp();
    EmitLine(Format('  %s =l loadl %%_var_Self', [PCharBase]));
    if AStmt.ImplicitFieldInfo.Offset > 0 then
    begin
      Adj := AllocTemp();
      EmitLine(Format('  %s =l add %s, %d',
        [Adj, PCharBase, AStmt.ImplicitFieldInfo.Offset]));
      PCharBase := Adj;
    end;
    EmitLine(Format('  %s =l add %s, %s', [ElemPtr, PCharBase, Offset]));
  end
  else if AStmt.IsVarParam then
  begin
    { var/out param: the slot holds the ADDRESS of the caller's array —
      load it before adding the element offset (adding to the slot address
      itself would write into the parameter slot region). }
    PCharBase := AllocTemp();
    EmitLine(Format('  %s =l loadl %s',
      [PCharBase, VarRef(AStmt.ArrayName, AStmt.IsGlobal)]));
    EmitLine(Format('  %s =l add %s, %s', [ElemPtr, PCharBase, Offset]));
  end
  else
    EmitLine(Format('  %s =l add %s, %s',
      [ElemPtr, VarRef(AStmt.ArrayName, AStmt.IsGlobal), Offset]));
  if ElemType.Kind = tyRecord then
  begin
    ElemVal := EmitExpr(AStmt.ValueExpr);
    EmitRecordCopy(TRecordTypeDesc(ElemType), ElemPtr, ElemVal);
    Exit;
  end;
  { Interface element: the slot is a contiguous 16-byte fat pointer
    (obj at +0, itab at +8).  Three RHS shapes are supported, mirroring
    EmitAssignment's iface-LHS branches:
      class       — read class ptr as l, look up the itab via the
                    LHS element interface's name (`$itab_<Class>_<Iface>`).
      interface   — EmitInterfaceExprPair resolves obj/itab from the
                    source's storage shape (split slots, contiguous
                    field, contiguous array element).
      nil literal — write 0 into both halves.
    Without this special case the generic path below picks `storew`
    (QbeTypeOf falls to 'w' for tyInterface) and emits a single-slot
    store against the 16-byte slot, leaving itab uninitialised. }
  if ElemType.Kind = tyInterface then
  begin
    if AStmt.ValueExpr is TNilLiteral then
    begin
      OldVal := AllocTemp();
      EmitLine(Format('  %s =l loadl %s', [OldVal, ElemPtr]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [OldVal]));
      EmitLine(Format('  storel 0, %s', [ElemPtr]));
      ItabPtr := AllocTemp();
      EmitLine(Format('  %s =l add %s, 8', [ItabPtr, ElemPtr]));
      EmitLine(Format('  storel 0, %s', [ItabPtr]));
      Exit;
    end;
    if (AStmt.ValueExpr.ResolvedType <> nil) and
       (AStmt.ValueExpr.ResolvedType.Kind = tyClass) then
    begin
      { class → iface: itab name is `$itab_<ClassName>_<InterfaceName>`. }
      IntfDesc := TInterfaceTypeDesc(ElemType);
      ObjTemp  := EmitExpr(AStmt.ValueExpr);
      ItabTemp := Format('$itab_%s_%s',
        [QBEMangle(ClassSymName(TRecordTypeDesc(AStmt.ValueExpr.ResolvedType).Name)),
         QBEMangle(IntfDesc.Name)]);
    end
    else
      EmitInterfaceExprPair(AStmt.ValueExpr, ObjTemp, ItabTemp);
    { ARC: addref new backing object, release the slot's prior obj.
      A class RHS that already owns +1 (constructor or call result)
      transfers its reference instead — mirroring EmitAssignment's
      class->iface branch; an unconditional AddRef leaks. }
    OldVal := AllocTemp();
    EmitLine(Format('  %s =l loadl %s', [OldVal, ElemPtr]));
    if not (((AStmt.ValueExpr.ResolvedType <> nil) and
             (AStmt.ValueExpr.ResolvedType.Kind = tyClass)) and
            ExprOwnsRef(AStmt.ValueExpr)) then
      EmitLine(Format('  call $_ClassAddRef(l %s)',  [ObjTemp]));
    EmitLine(Format('  call $_ClassRelease(l %s)', [OldVal]));
    EmitLine(Format('  storel %s, %s', [ObjTemp, ElemPtr]));
    ItabPtr := AllocTemp();
    EmitLine(Format('  %s =l add %s, 8', [ItabPtr, ElemPtr]));
    EmitLine(Format('  storel %s, %s', [ItabTemp, ItabPtr]));
    Exit;
  end;
  if ElemType.Kind in [tyByte, tyBoolean] then
    ElemVal := EmitByteRhs(AStmt.ValueExpr)
  else
    ElemVal := EmitExpr(AStmt.ValueExpr);
  if (ElemType.Kind in [tyInt64, tyUInt64]) and
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
  { Float element: coerce value temp to element width (e.g. a `d` literal into
    a Single slot needs truncd before `stores`). }
  if ElemType.Kind in [tyDouble, tySingle] then
    ElemVal := CoerceArg(ElemVal, AStmt.ValueExpr, QbeTypeOf(ElemType));
  case ElemType.Kind of
    tyByte, tyBoolean: StoreInstr := 'storeb';
    tySmallInt, tyWord: StoreInstr := 'storeh';
    tyInteger, tyUInt32, tyEnum: StoreInstr := 'storew';
    tyDouble: StoreInstr := 'stored';
    tySingle: StoreInstr := 'stores';
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
  Mask:    Int64;
  I:       Integer;
  Elem:    TASTExpr;
  IdExpr:  TIdentExpr;
  Tmp:     string;
  QT:      string;
  ElemVal: string;
begin
  { Jumbo set literal: build the bitmap in a fresh stack buffer — memset 0,
    then set each member's bit via _SetInclude.  Elements may be non-constant
    (evaluated at runtime), unlike the small-set fast path. }
  if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tySet) and
     TSetTypeDesc(AExpr.ResolvedType).IsJumbo() then
  begin
    Tmp := AllocTemp();
    EmitLine(Format('  %s =l alloc8 %d',
      [Tmp, TSetTypeDesc(AExpr.ResolvedType).RawSize()]));
    EmitLine(Format('  call $memset(l %s, w 0, l %d)',
      [Tmp, TSetTypeDesc(AExpr.ResolvedType).RawSize()]));
    for I := 0 to AExpr.Elements.Count - 1 do
    begin
      Elem    := TASTExpr(AExpr.Elements.Items[I]);
      ElemVal := EmitExpr(Elem);
      EmitLine(Format('  call $_SetInclude(l %s, w %s)', [Tmp, ElemVal]));
    end;
    Exit(Tmp);
  end;

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

  { 'array of const' literal: build an array of 16-byte TVarRec records
    (VType at +0, VValue at +8). }
  if AExpr.IsConstArray then
    Exit(EmitConstArrayLiteral(AExpr));

  { Empty literal with no resolved element type (an [] that never gained a
    context): emit a null data pointer rather than dereferencing a nil type. }
  if (AExpr.ResolvedType = nil) or (AExpr.Elements.Count = 0) then
  begin
    BufPtr := AllocTemp();
    EmitLine(Format('  %s =l copy 0', [BufPtr]));
    Exit(BufPtr);
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

{ Build an 'array of const' temporary: one 16-byte TVarRec per element
  (VType byte at +0, pointer-sized VValue at +8).  Borrow semantics — string
  and object values are stored without an AddRef; the callee must not retain
  them beyond the call.  Doubles are heap-boxed (a PDouble in the slot, tag
  vtExtended) because a double does not fit the integer value slot. }
function TCodeGenQBE.EmitConstArrayLiteral(AExpr: TArrayLiteralExpr): string;
var
  BufPtr:   string;
  Count:    Integer;
  I, Tag:   Integer;
  Elem:     TASTExpr;
  EK:       TTypeKind;
  SlotPtr:  string;
  ValPtr:   string;
  ElemVal:  string;
  BoxPtr:   string;
  Widened:  string;
begin
  Count := AExpr.Elements.Count;
  if Count < 1 then
  begin
    { Empty [] — no storage needed; pass a null data pointer (high = -1). }
    BufPtr := AllocTemp();
    EmitLine(Format('  %s =l copy 0', [BufPtr]));
    Exit(BufPtr);
  end;
  BufPtr := AllocTemp();
  EmitLine(Format('  %s =l alloc8 %d', [BufPtr, Count * 16]));
  for I := 0 to Count - 1 do
  begin
    Elem := TASTExpr(AExpr.Elements.Items[I]);
    EK   := Elem.ResolvedType.Kind;
    { Slot base = BufPtr + I*16; value pointer = slot + 8. }
    SlotPtr := AllocTemp();
    EmitLine(Format('  %s =l add %s, %d', [SlotPtr, BufPtr, I * 16]));
    ValPtr := AllocTemp();
    EmitLine(Format('  %s =l add %s, 8', [ValPtr, SlotPtr]));
    { Determine the vt tag and box the value into the 8-byte slot. }
    case EK of
      tyInteger, tyUInt32, tyByte, tySmallInt, tyWord:
        begin
          Tag := 0;   { vtInteger }
          ElemVal := EmitExpr(Elem);
          Widened := AllocTemp();
          EmitLine(Format('  %s =l extsw %s', [Widened, ElemVal]));
          EmitLine(Format('  storel %s, %s', [Widened, ValPtr]));
        end;
      tyBoolean:
        begin
          Tag := 1;   { vtBoolean }
          ElemVal := EmitExpr(Elem);
          Widened := AllocTemp();
          EmitLine(Format('  %s =l extub %s', [Widened, ElemVal]));
          EmitLine(Format('  storel %s, %s', [Widened, ValPtr]));
        end;
      tyEnum:
        begin
          Tag := 24;  { vtEnum }
          ElemVal := EmitExpr(Elem);
          Widened := AllocTemp();
          EmitLine(Format('  %s =l extsw %s', [Widened, ElemVal]));
          EmitLine(Format('  storel %s, %s', [Widened, ValPtr]));
        end;
      tyInt64, tyUInt64:
        begin
          Tag := 16;  { vtInt64 }
          ElemVal := EmitExpr(Elem);
          EmitLine(Format('  storel %s, %s', [ElemVal, ValPtr]));
        end;
      tyDouble, tySingle:
        begin
          Tag := 3;   { vtExtended — heap-box the double }
          ElemVal := EmitExpr(Elem);
          BoxPtr := AllocTemp();
          EmitLine(Format('  %s =l call $_BlaiseGetMem(w 8)', [BoxPtr]));
          EmitLine(Format('  stored %s, %s', [ElemVal, BoxPtr]));
          EmitLine(Format('  storel %s, %s', [BoxPtr, ValPtr]));
        end;
      tyString:
        begin
          Tag := 20;  { vtAnsiString — borrow the string data pointer }
          ElemVal := EmitExpr(Elem);
          EmitLine(Format('  storel %s, %s', [ElemVal, ValPtr]));
        end;
      tyClass, tyMetaClass:
        begin
          Tag := 7;   { vtObject — borrow the object pointer }
          ElemVal := EmitExpr(Elem);
          EmitLine(Format('  storel %s, %s', [ElemVal, ValPtr]));
        end;
    else
      { tyPointer, tyPChar, and anything else: store the pointer-sized value. }
      Tag := 5;     { vtPointer }
      ElemVal := EmitExpr(Elem);
      EmitLine(Format('  storel %s, %s', [ElemVal, ValPtr]));
    end;
    { Store the tag byte at slot +0. }
    EmitLine(Format('  storeb %d, %s', [Tag, SlotPtr]));
  end;
  Result := BufPtr;
end;

end.
