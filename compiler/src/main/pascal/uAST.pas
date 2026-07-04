{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uAST;

interface

uses
  Classes, SysUtils, contnrs, uSymbolTable;

type
  { Base node — all AST nodes carry source position. }
  TASTNode = class
  public
    Line: Integer;
    Col:  Integer;
  end;

  { ------------------------------------------------------------------ }
  {  Expressions                                                        }
  { ------------------------------------------------------------------ }

  { Semantic analyser fills ResolvedType on every expression node. }
  TASTExpr = class(TASTNode)
  public
    [Unretained] ResolvedType: TTypeDesc;  { not owned — points into the
                                              symbol table's type pool, which
                                              outlives the AST. }
  end;

  TIntLiteral = class(TASTExpr)
  public
    Value:    Int64;
    IsUInt64: Boolean;  { True when the source literal exceeds MaxInt64 and
                          must be interpreted as an unsigned 64-bit value.
                          Set by the parser; Value carries the bit pattern. }
  end;

  TFloatLiteral = class(TASTExpr)
  public
    Value: string;   { raw text e.g. '3.14' or '1.5E-3'; parsed at codegen }
  end;

  TStringLiteral = class(TASTExpr)
  public
    Value: string;
    IsCharCoerce: Boolean;  { set by uSemantic when used as Byte in a comparison }
    CharOrdValue: Integer;  { OrdAt(Value, 0) — valid only when IsCharCoerce = True }
  end;

  TStringSubscriptExpr = class(TASTExpr)
  public
    StrExpr:   TASTExpr;  { owned }
    IndexExpr: TASTExpr;  { owned }
    destructor Destroy; override;
  end;

  TArrayLiteralExpr = class(TASTExpr)
  public
    Elements: TObjectList;  { owned list of TASTExpr }
    IsConstArray: Boolean;  { set by uSemantic when this bracket literal is an
                              'array of const' argument — its elements are boxed
                              into TVarRec records at the call site rather than
                              forming a homogeneous open array. }
    constructor Create;
    destructor Destroy; override;
  end;

  { A `lo..hi` range appearing as an element of a set literal, e.g.
    [1..3] or [Red..Blue].  Both bounds must be compile-time constants;
    uSemantic.AnalyseSetLiteralExpr expands the range into individual
    member nodes (so codegen never sees this node), and rejects reversed
    or non-constant ranges.  Carried through the .bif serialiser because a
    generic template body may contain an unexpanded range. }
  TSetRangeExpr = class(TASTExpr)
  public
    LowExpr:  TASTExpr;  { owned }
    HighExpr: TASTExpr;  { owned }
    destructor Destroy; override;
  end;

  TNilLiteral = class(TASTExpr);  { nil keyword — type is tyNil }

  TParamMode = (
    pmNone,
    pmVar,
    pmRecordValue,
    pmStaticArrayValue,
    pmJumboSetValue       { by-value jumbo (>64) set param: by-ref aggregate ABI }
  );

  TIdentExpr = class(TASTExpr)
  public
    Name:              string;
    ParamMode:         TParamMode; { set by uSemantic — how the param slot is laid out }
    IsConstant:        Boolean;  { set by uSemantic — True if this ident is a skConstant symbol }
    ConstValue:        Int64;    { valid when IsConstant = True; integer/bool/enum value }
    ConstString:       string;   { valid when IsConstant = True and type is tyString }
    IsGlobal:          Boolean;  { set by uSemantic — this ident is a program-level global var }
    IsThreadVar:       Boolean;  { set by uSemantic — threadvar (TLS) global }
    IsImplicitSelf:    Boolean;  { set by uSemantic — bare field name implicitly referencing Self }
    [Unretained] ImplicitFieldInfo: TObject;  { TFieldInfo — not owned; valid when IsImplicitSelf }
    IsImplicitSelfMethod: Boolean; { set by uSemantic — bare zero-arg method call on Self }
    [Unretained] ImplicitMethodDecl:   TObject;  { TMethodDecl — not owned; set when IsImplicitSelfMethod }
    IsMetaclassRef:    Boolean;     { set by uSemantic — bare class type identifier used as
                                      metaclass value (typeinfo ptr); codegen emits
                                      $typeinfo_<Name> instead of loading a variable. }
    ConstArraySymbol:  string;      { set by uSemantic — non-empty when this ident resolves
                                      to an array const; the mangled QBE data-label codegen
                                      must reference instead of $Name. }
  end;

  TFieldAccessExpr = class(TASTExpr)
  public
    RecordName:        string;         { used when Base = nil (leaf access) }
    FieldName:         string;
    Base:              TASTExpr;       { owned — when non-nil, chained access (e.g. A.B.C) }
    FieldInfo:         TFieldInfo;    { set by uSemantic — nil for constructor calls }
    IsConstant:        Boolean;       { set by uSemantic — TypeName.ConstName resolves to a class constant }
    ConstValue:        Int64;         { valid when IsConstant = True }
    ConstString:       string;        { valid when IsConstant = True and type is tyString }
    ConstArraySymbol:  string;        { non-empty for class-level array const — global data label }
    [Unretained] ConstArrayType:    TObject;       { TStaticArrayTypeDesc — not owned; set when ConstArraySymbol is set }
    IsConstructorCall: Boolean;       { set by uSemantic — TypeName.Create }
    IsClassAccess:     Boolean;       { set by uSemantic — pointer deref needed }
    PropRead:          TPropertyInfo; { non-nil if this is a method-backed property read }
    PropOwnerType:     string;        { class type name for method-backed property calls }
    PropAccessorVSlot: Integer;       { set by uSemantic — getter vtable slot, -1 = static call }
    IsImplicitSelf:    Boolean;       { set by uSemantic — RecordName is a field of Self }
    [Unretained] ImplicitBaseInfo:  TFieldInfo;    { non-owned — the field of Self holding the record/class }
    IsMethodCall:        Boolean;     { set by uSemantic — FieldName is a zero-arg method }
    [Unretained] ResolvedMethod:      TObject;     { TMethodDecl — not owned; set when IsMethodCall }
    IsInterfaceCall:     Boolean;     { set by uSemantic — zero-arg method call through interface itab }
    [Unretained] ResolvedClassType:   TTypeDesc;  { not owned; set when IsInterfaceCall — the interface descriptor }
    IsGlobal:            Boolean;     { set by uSemantic — RecordName is a program-level global }
    IsClassNameAccess:   Boolean;     { set by uSemantic — .ClassName built-in on a class instance }
    IsClassTypeAccess:   Boolean;     { set by uSemantic — .ClassType built-in: returns metaclass (typeinfo ptr) }
    IsBuiltinToString:   Boolean;     { set by uSemantic — .ToString built-in: virtual dispatch via vtable slot 1 }
    IsVarParam:          Boolean;     { set by uSemantic — RecordName is a var parameter (record by-ref) }
    PropIndexExpr: TASTExpr;  { owned — non-nil = indexed property read (e.g. List.Items[i]) }
    IsCharAccess:  Boolean;   { set by uSemantic — PropIndexExpr indexes a string field: S.Field[N] }
    IsArrayAccess: Boolean;   { set by uSemantic — PropIndexExpr subscripts an array field: R.Arr[I] }
    destructor Destroy; override;
  end;

  TIsExpr = class(TASTExpr)
  public
    Obj:                TASTExpr;   { owned — left-hand side; must be class instance }
    TypeName:           string;     { right-hand side type name; resolved by uSemantic }
    [Unretained] ResolvedTargetType: TTypeDesc;  { set by uSemantic — class or interface descriptor }
    destructor Destroy; override;
  end;

  TAsExpr = class(TASTExpr)
  public
    Obj:      TASTExpr;  { owned — left-hand side; must be class instance }
    TypeName: string;    { right-hand side type name; resolved by uSemantic }
    destructor Destroy; override;
  end;

  { Supports(Obj, IFoo) — Boolean interface-membership test.
    Supports(Obj, IFoo, Ref) — test + assign fat pointer to Ref on success. }
  TSupportsExpr = class(TASTExpr)
  public
    Obj:                TASTExpr;  { owned — object being tested }
    IntfTypeName:       string;    { interface type name (second arg) }
    OutVarName:         string;    { variable to receive fat pointer (third arg; empty = 2-arg form) }
    [Unretained] ResolvedIntfType:   TTypeDesc; { set by uSemantic — must be tyInterface }
    OutVarIsGlobal:     Boolean;   { set by uSemantic }
    destructor Destroy; override;
  end;

  { `inherited Method(args)` used in EXPRESSION position (the value of the
    parent method's result is needed).  The statement form is
    TInheritedCallStmt; this is its expression sibling.  Resolved and lowered
    the same way (static dispatch to the parent slot), but yields a value. }
  TInheritedCallExpr = class(TASTExpr)
  public
    Name:               string;        { parent method name to call }
    Args:               TObjectList;   { owned TASTExpr items }
    { Set by uSemantic: }
    [Unretained] ResolvedParentType: TObject;   { TRecordTypeDesc — not owned }
    [Unretained] ResolvedMethod:     TObject;   { TMethodDecl — not owned }
    constructor Create;
    destructor Destroy; override;
  end;

  { boSlash is the `/` operator: real division, always yields a float.
    boDiv is the `div` operator: integer division between integer operands. }
  TBinaryOp = (boAdd, boSub, boMul, boSlash, boDiv, boMod,
               boEQ, boNE, boLT, boGT, boLE, boGE,
               boAnd, boOr, boXor, boIn, boShl, boShr, boSar);

  TBinaryExpr = class(TASTExpr)
  public
    Op:    TBinaryOp;
    Left:  TASTExpr;  { owned }
    Right: TASTExpr;  { owned }
    destructor Destroy; override;
  end;

  TNotExpr = class(TASTExpr)
  public
    Expr: TASTExpr;  { owned — must be Boolean }
    destructor Destroy; override;
  end;

  { ------------------------------------------------------------------ }
  {  Statements                                                         }
  { ------------------------------------------------------------------ }

  TASTStmt = class(TASTNode);

  TAssignment = class(TASTStmt)
  public
    Name:            string;
    Expr:            TASTExpr;   { owned }
    IsVarParam:      Boolean;    { set by uSemantic — True if target is a var parameter }
    IsGlobal:        Boolean;    { set by uSemantic — True if target is a program-level global }
    IsThreadVar:     Boolean;    { set by uSemantic — True if target is a threadvar }
    [Unretained] ResolvedLhsType: TTypeDesc;  { set by uSemantic — type of the target variable }
    IsWeakLhs:       Boolean;    { set by uSemantic — True if the LHS symbol
                                   was declared [Weak]; codegen emits a
                                   _WeakAssign in place of the strong
                                   addref/release pattern. }
    ImplicitSelfField: TObject;  { TFieldInfo — non-nil when LHS is bare field (implicit Self) }
    destructor Destroy; override;
  end;

  TIfStmt = class(TASTStmt)
  public
    Condition: TASTExpr;   { owned }
    ThenStmt:  TASTStmt;   { owned }
    ElseStmt:  TASTStmt;   { owned; nil if no else }
    destructor Destroy; override;
  end;

  TCompoundStmt = class(TASTStmt)
  public
    Stmts: TObjectList;  { owned TASTStmt }
    constructor Create;
    destructor Destroy; override;
  end;

  TWhileStmt = class(TASTStmt)
  public
    Condition: TASTExpr;  { owned }
    Body:      TASTStmt;  { owned }
    destructor Destroy; override;
  end;

  TRepeatStmt = class(TASTStmt)
  public
    Body:      TCompoundStmt;  { owned — statements between repeat and until }
    Condition: TASTExpr;       { owned — the until condition }
    destructor Destroy; override;
  end;

  TForStmt = class(TASTStmt)
  public
    VarName:   string;
    IsGlobal:  Boolean;   { set by uSemantic — VarName is a program-level global }
    StartExpr: TASTExpr;  { owned }
    EndExpr:   TASTExpr;  { owned }
    IsDownTo:  Boolean;
    Body:      TASTStmt;  { owned }
    destructor Destroy; override;
  end;

  TForInStmt = class(TASTStmt)
  public
    VarName:              string;
    VarIsGlobal:          Boolean;    { set by semantic — VarName is program-level global }
    CollExpr:             TASTExpr;   { owned — collection expression }
    Body:                 TASTStmt;   { owned }
    { Annotations set by the semantic pass }
    [Unretained] ResolvedVarType:      TTypeDesc;  { element type }
    { Class-enumerator path (IsArrayIter = False) }
    IsArrayIter:          Boolean;    { True when collection is a static array }
    EnumVarName:          string;     { synthetic enumerator slot, e.g. __forin_0 }
    ResolvedEnumTypeName: string;     { enumerator class type name }
    [Unretained] GetEnumDecl:          TObject;    { TMethodDecl — not owned }
    [Unretained] MoveNextDecl:         TObject;    { TMethodDecl — not owned }
    [Unretained] CurrentDecl:          TObject;    { TMethodDecl getter — not owned }
    { Static-array iteration path (IsArrayIter = True) }
    IdxVarName:           string;     { synthetic index slot — shared with string/dynarray path }
    ArrayLow:             Integer;    { compile-time lower bound }
    ArrayHigh:            Integer;    { compile-time upper bound }
    { Dynamic-array iteration path (IsDynArrayIter = True) }
    IsDynArrayIter:       Boolean;
    { String byte-iteration path (IsStringIter = True) }
    IsStringIter:         Boolean;
    { String codepoint-iteration path (IsCodePointIter = True) }
    IsCodePointIter:      Boolean;
    AdvVarName:           string;    { synthetic slot for byte-advance count }
    { Set iteration path (IsSetIter = True) }
    IsSetIter:            Boolean;
    SetBitCount:          Integer;   { number of bits in the set (= enum member count) }
    SetMaskVarName:       string;    { synthetic slot: holds the evaluated set mask
                                       (small set), or the set's ADDRESS (jumbo) }
    SetIsJumbo:           Boolean;   { True when the set is >64 members: the slot
                                       holds a pointer and membership is tested via
                                       the _SetIn RTL helper, not a register shift }
    destructor Destroy; override;
  end;

  TTryFinallyStmt = class(TASTStmt)
  public
    TryBody:     TCompoundStmt;  { owned }
    FinallyBody: TCompoundStmt;  { owned }
    destructor Destroy; override;
  end;

  { One 'on [VarName :] TypeName do Stmt' arm inside a try/except block.
    VarName is empty when the source uses the no-binding form 'on TFoo do'. }
  TExceptHandlerClause = class
  public
    VarName:  string;         { bound variable name, or '' }
    TypeName: string;         { exception class name }
    Body:     TCompoundStmt;  { owned }
    destructor Destroy; override;
  end;

  TTryExceptStmt = class(TASTStmt)
  public
    TryBody:    TCompoundStmt;  { owned }
    { Typed handlers (on E: T do): non-empty when the except block contains
      'on' clauses.  Mutually exclusive with ExceptBody. }
    Handlers:   TObjectList;    { owned list of TExceptHandlerClause }
    ElseBody:   TCompoundStmt;  { owned; catch-all after typed handlers, or nil }
    { Plain catch-all body: non-nil only when the except block has no 'on' clauses. }
    ExceptBody: TCompoundStmt;  { owned }
    constructor Create;
    destructor Destroy; override;
  end;

  TRaiseStmt = class(TASTStmt)
  public
    Expr: TASTExpr;  { owned; nil = bare re-raise }
    destructor Destroy; override;
  end;

  { 'exit' statement — returns from the current procedure/function.
    Value is the Exit(X) function-result shorthand: the parser stores the raw
    X here.  The semantic pass validates it and builds ResultAssign (a
    synthesised 'Result := X'); codegen emits ResultAssign before the exit
    jump.  Both nil = bare Exit. }
  TExitStmt = class(TASTStmt)
  public
    Value:        TASTExpr;     { owned; nil = bare exit; raw parsed expr }
    ResultAssign: TASTStmt;     { owned; synthesised 'Result := Value' (TAssignment) }
    destructor Destroy; override;
  end;

  { 'break' statement — exits the innermost loop. }
  TBreakStmt = class(TASTStmt);

  { 'continue' statement — jumps to next iteration of the innermost loop. }
  TContinueStmt = class(TASTStmt);

  { One arm of a case statement: one or more ordinal values → body }
  TCaseBranch = class
  public
    Values: TObjectList;  { owned list of TASTExpr (integer/enum literal values) }
    Stmt:   TASTStmt;     { owned }
    constructor Create;
    destructor Destroy; override;
  end;

  TCaseStmt = class(TASTStmt)
  public
    Selector: TASTExpr;    { owned — ordinal or string }
    Branches: TObjectList; { owned list of TCaseBranch }
    ElseStmt: TASTStmt;    { owned; nil if no else clause }
    IsStringCase: Boolean; { set by uSemantic when Selector resolves to string;
                             codegen uses _StringEquals instead of ceqw }
    constructor Create;
    destructor Destroy; override;
  end;

  TFieldAssignment = class(TASTStmt)
  public
    RecordName:    string;
    FieldName:     string;
    Expr:          TASTExpr;   { owned }
    ObjExpr:       TASTExpr;   { owned — when non-nil, receiver is this expression (e.g. typecast) }
    FieldInfo:     TFieldInfo; { set by uSemantic — carries offset + type }
    IsClassAccess: Boolean;    { set by uSemantic — pointer deref needed }
    IsImplicitSelf:    Boolean; { set by uSemantic — RecordName is a field of Self }
    [Unretained] ImplicitBaseInfo:  TFieldInfo; { non-owned — the field of Self that holds the record/class }
    IsGlobal:          Boolean; { set by uSemantic — RecordName is a program-level global }
    IsVarParam:        Boolean; { set by uSemantic — RecordName is a var parameter (record by-ref) }
    PropIndexExpr: TASTExpr;  { owned — non-nil = indexed property write via setter,
                                OR (IsElemWrite) the element index into an array-typed field }
    [Unretained] PropWriteInfo: TPropertyInfo;  { non-owned — set by semantic when PropIndexExpr is set }
    PropOwnerType: string;  { owner class name for setter call; valid when PropIndexExpr set }
    PropAccessorVSlot: Integer;  { set by uSemantic — setter vtable slot, -1 = static call }
    IsElemWrite: Boolean;   { set by uSemantic — FieldName is an array-typed field and
                              PropIndexExpr selects the element to store into }
    [Unretained] IntfWriteDesc: TTypeDesc;  { set by uSemantic — non-nil = interface
                              property write: RecordName is interface-typed and
                              FieldName has been rewritten to the SETTER method;
                              codegen dispatches it through the itab with Expr
                              as the single argument }
    destructor Destroy; override;
  end;

  { Static-array element write: 'ArrayName[IndexExpr] := ValueExpr' }
  TStaticSubscriptAssign = class(TASTStmt)
  public
    ArrayName: string;
    IndexExpr: TASTExpr;  { owned }
    ValueExpr: TASTExpr;  { owned }
    BaseExpr:  TASTExpr;  { owned — when non-nil, the element being written is
                            the IndexExpr-th element of the array yielded by
                            BaseExpr (an l-value subscript chain whose result
                            is an inner static-array address).  Used to lower
                            multi-dimensional / chained writes A[i][j] := v;
                            ArrayName is then unused for base resolution. }
    IsGlobal: Boolean;    { set by uSemantic }
    IsVarParam: Boolean;  { set by uSemantic — ArrayName is a var/out
                            parameter, so the local slot holds the ADDRESS
                            of the caller's variable; codegen needs one
                            extra dereference to reach the array }
    [Unretained] ResolvedArrayType: TTypeDesc;  { set by uSemantic; not owned }
    IsImplicitSelf: Boolean;  { set by uSemantic — ArrayName is an array-typed field of Self }
    [Unretained] ImplicitFieldInfo: TFieldInfo;  { non-owned — the Self field; set with IsImplicitSelf }
    { Default array property write: Obj[I] := V where Obj's class has a
      `default` indexed property — lowered to a setter call.  When
      PropWriteInfo is non-nil, ArrayName is the receiver variable, IndexExpr
      is the index arg, ValueExpr is the value arg. }
    [Unretained] PropWriteInfo: TObject;  { TPropertyInfo — non-owned; nil = plain array write }
    PropOwnerType:     string;  { declaring class of the setter }
    PropAccessorVSlot: Integer; { setter vtable slot, -1 = static call }
    destructor Destroy; override;
  end;

  { Write a value through a pointer: 'PtrExpr^ := ValueExpr' }
  TPointerWriteStmt = class(TASTStmt)
  public
    PtrExpr:  TASTExpr;  { owned — pointer expression }
    ValExpr:  TASTExpr;  { owned — value to store }
    [Unretained] BaseTy:   TTypeDesc; { non-owned — element type; set by uSemantic }
    destructor Destroy; override;
  end;

  TProcCall = class(TASTStmt)
  public
    Name:         string;
    Args:         TObjectList;  { owned TASTExpr items }
    [Unretained] ResolvedDecl: TObject;      { TMethodDecl — not owned; set by uSemantic for user-defined procs }
    IsImplicitSelfMethod: Boolean; { set by uSemantic — call is on Self }
    IsIndirectCall:       Boolean; { set by uSemantic — Name is a procedural-typed variable }
    IndirectCallIsGlobal: Boolean; { set by uSemantic — when IsIndirectCall, variable is global }
    [Unretained] ResolvedProcType:     TObject; { TProceduralTypeDesc — not owned; valid when IsIndirectCall }
    constructor Create;
    destructor Destroy; override;
  end;

  TFuncCallExpr = class(TASTExpr)
  public
    Name:         string;
    Args:         TObjectList;  { owned TASTExpr items }
    [Unretained] ResolvedDecl: TObject;      { TMethodDecl — not owned; set by uSemantic }
    IsImplicitSelfMethod: Boolean; { set by uSemantic — call is on Self }
    IsIndirectCall:       Boolean; { set by uSemantic — Name resolves to a
                                     variable of procedural type; codegen
                                     loads the function pointer and calls
                                     through it. ResolvedProcType holds
                                     the signature. }
    IndirectCallIsGlobal: Boolean; { set by uSemantic — when IsIndirectCall,
                                     True if the holding variable is a
                                     program-level global. }
    [Unretained] ResolvedProcType: TObject;     { TProceduralTypeDesc — not owned;
                                     valid when IsIndirectCall }
    IsBuiltinHasClassAttr: Boolean; { set by uSemantic — HasClassAttribute builtin }
    HasClassAttrClass:     string;  { class name for arg 1 (class being queried) }
    HasClassAttrAttr:      string;  { attribute class name for arg 2 }
    constructor Create;
    destructor Destroy; override;
  end;

  { Call through an arbitrary expression of procedural type: Expr(args).
    Used when the callee is not a simple identifier — e.g. an array element
    (Fns[I]()) or a field access result.  ResolvedProcType is set by uSemantic. }
  TIndirectFuncCallExpr = class(TASTExpr)
  public
    CalleeExpr:      TASTExpr;   { owned — the expression that yields the proc pointer }
    Args:            TObjectList; { owned TASTExpr items }
    [Unretained] ResolvedProcType: TObject;   { TProceduralTypeDesc — not owned; set by uSemantic }
    constructor Create;
    destructor Destroy; override;
  end;

  { Pointer dereference expression: 'PtrExpr^' — result type is BaseType of pointer }
  TDerefExpr = class(TASTExpr)
  public
    Expr: TASTExpr;  { owned — the pointer expression }
    destructor Destroy; override;
  end;

  { Address-of expression: '@Expr' — result type is ^ElemType }
  TAddrOfExpr = class(TASTExpr)
  public
    Expr: TASTExpr;  { owned — the inner expression whose address is taken }
    ResolvedFreeRoutine: TObject;  { TMethodDecl — not owned; populated by
                                    uSemantic when Expr is a bare identifier
                                    naming a standalone routine.  Lets codegen
                                    emit @<MDecl.ResolvedQbeName> instead of
                                    @<source-name>, which matters once routine
                                    names get unit-prefixed. }
    destructor Destroy; override;
  end;

  TMethodCallStmt = class(TASTStmt)
  public
    ObjectName: string;
    Name:       string;   { method name }
    Args:       TObjectList;   { owned TASTExpr items }
    ObjExpr:    TASTExpr;  { owned — when non-nil, receiver is this expression }
    { Set by uSemantic: }
    [Unretained] ResolvedClassType:  TTypeDesc;   { not owned }
    [Unretained] ResolvedMethod:     TObject;     { TMethodDecl — not owned; avoids forward ref }
    { Set by uSemantic for itab dispatch only: the method's resolved return
      type.  A discarded interface/record-returning call in statement
      position still needs the sret calling convention — codegen reads this
      to allocate a throwaway buffer. }
    [Unretained] ResolvedReturnTypeDesc: TTypeDesc;  { not owned; nil for procedures }
    IsImplicitSelf:     Boolean;     { ObjectName is a field of Self }
    [Unretained] ImplicitBaseInfo:   TFieldInfo;  { not owned — the field of Self }
    IsGlobal:           Boolean;     { set by uSemantic — ObjectName is a program-level global }
    IsVarParam:         Boolean;     { set by uSemantic — ObjectName is a var/out parameter }
    IsBuiltinToString:  Boolean;     { set by uSemantic — built-in TObject.ToString virtual dispatch }
    IsConstructorCall:  Boolean;     { set by uSemantic — metaclass-var Create in stmt position }
    IsMetaclassDispatch: Boolean;    { set by uSemantic — receiver is a metaclass var }
    IsProcFieldCall:    Boolean;     { set by uSemantic — Name is a procedural-typed field of
                                       the receiver, invoked directly (F.Handler;).  Codegen
                                       loads the (Code, Data) pair from the field slot and
                                       dispatches indirectly instead of calling a method. }
    [Unretained] ProcFieldInfo:      TFieldInfo;  { not owned — the procedural field, when IsProcFieldCall }
    [Unretained] ResolvedProcType:   TObject;     { TProceduralTypeDesc — not owned; the field's signature }
    constructor Create;
    destructor Destroy; override;
  end;

  { Static dispatch to the parent class's method: 'inherited MethodName(args)'.
    Legal only inside a method body; resolved by uSemantic using the enclosing
    class's parent chain. }
  TInheritedCallStmt = class(TASTStmt)
  public
    Name:               string;        { parent method name to call }
    Args:               TObjectList;   { owned TASTExpr items }
    { Set by uSemantic: }
    [Unretained] ResolvedParentType: TObject;       { TRecordTypeDesc — not owned }
    [Unretained] ResolvedMethod:     TObject;       { TMethodDecl — not owned }
    constructor Create;
    destructor Destroy; override;
  end;

  { ------------------------------------------------------------------ }
  {  Declarations                                                       }
  { ------------------------------------------------------------------ }

  { Constant declaration: const Name = Value; or const Name: Type = Value;
    or const Name: array[IndexType] of ElemType = (v0, v1, ...).
    Also carries a variable initialiser (var G: T = value) — see
    TVarDecl.InitConst — which is why it is declared ahead of TVarDecl. }
  TConstDecl = class(TASTNode)
  public
    Name:           string;
    TypeName:       string;   { non-empty when a type annotation was written }
    IntVal:         Int64;    { used when kind = integer (bit pattern when IsUInt64) }
    IsUInt64:       Boolean;  { value exceeded High(Int64): IntVal is the UInt64 bit pattern }
    StrVal:         string;   { used when IsString = True or IsFloat = True (raw text) }
    IsString:       Boolean;
    IsFloat:        Boolean;  { set when the rhs is a float literal }
    ConstParts:     TStringList; { non-nil when const expr has ident refs;
                                   Objects[i] = nil → string literal,
                                   Objects[i] <> nil → ident reference }
    { Array-typed constants — set when TypeName starts with 'array' }
    IsArrayConst:   Boolean;
    ArrayIndexType: string;   { enum type name used as index, e.g. 'TWeather' }
    ArrayElemType:  string;   { element type name, e.g. 'string', 'Integer' }
    ArrayElements:  TStringList; { ordered list of raw element values (strings or int literals) }
    ArrayIsRangeIndexed: Boolean; { True when index is Low..High integer range }
    ArrayLowBound:  Integer;
    ArrayHighBound: Integer;
    { Multi-dimensional range-indexed const arrays.  When the declaration is
      array[L0..H0, L1..H1, ...] of T (comma form) or the equivalent nested
      array[L0..H0] of array[L1..H1] of T, each dimension's bounds are pushed
      onto these parallel lists (one entry per dimension, integer text).  When
      non-nil and Count > 1 the constant is multi-dimensional; ArrayElements
      holds the values flattened in row-major order.  Count <= 1 (or nil) means
      single-dimension — ArrayLowBound/ArrayHighBound are authoritative. }
    ArrayDimLows:   TStringList;
    ArrayDimHighs:  TStringList;
    { Integer bit-op expression in the value position — non-nil when the
      RHS was a chain like 'FG_BLUE or 8' that couldn't be folded at
      parse time (because it references named constants).  Tokens are
      stored alternating operand/operator: tokens[0,2,4,...] are operands
      (Objects[i] = nil → integer literal, the string is the int;
      Objects[i] <> nil → ident reference); tokens[1,3,5,...] are
      operator names (one of 'or'/'and'/'xor'/'shl'/'shr').  Semantic
      resolves idents and folds to CD.IntVal. }
    IntExprTokens:  TStringList;
    { Integer constant expression in the value position — non-nil when the RHS
      is a compile-time arithmetic/bitwise expression with operator precedence
      and/or parentheses (e.g. '2 + 3 * 4', '(1 shl 8) or 7', 'BASE * 2').
      Stored as a normal expression AST so precedence and grouping are encoded
      structurally; the semantic pass folds it to CD.IntVal via EvalConstIntExpr
      (resolving any named-constant references after all consts are declared).
      Supersedes the flat IntExprTokens form for newly-parsed expressions; the
      token form is retained only for the legacy single-precedence bit-op path. }
    IntValueExpr:   TASTExpr;
    { Parallel to ArrayElements — each non-nil entry is an IntExprTokens-
      shaped TStringList describing the bit-op expression for that
      element.  Semantic folds it and overwrites ArrayElements[i] with
      the resolved integer.  Nil indicates the matching ArrayElements[i]
      is already a final scalar (literal, typecast, or ident). }
    ArrayElementParts: TObjectList;
    { Set-valued constant — set when the RHS is a set literal '[a, b, ...]'.
      SetElements holds the member identifier names (empty for '[]').
      Semantic resolves each to its enum ordinal, ORs (1 shl ord) into IntVal
      (the bitmask), and gives the symbol a tySet type — either CD.TypeName's
      declared set type or the set type inferred from the members' enum. }
    IsSet:       Boolean;
    SetElements: TStringList;   { non-nil when IsSet; member ident names }
    { JUMBO (>64-member) set constant: the bitmap as one decimal byte value per
      bitmap byte (RawByteSize entries).  Set by uSemantic when IsSet and the
      set type is jumbo, because the bitmask no longer fits in IntVal (Int64).
      Nil for small sets (which keep using IntVal). }
    ConstSetBytes: TStringList;
    { Canonical QBE data-label for an array const, set by uSemantic.  Mangled
      to a unique symbol so identically-named consts in different scopes (and
      RTL-internal consts) do not collide at link time.  Empty for non-array
      consts. }
    ResolvedQbeName: string;
    { Canonical, mangled QBE data-label for a JUMBO set const's byte blob
      (mirrors ResolvedQbeName for array consts). Empty otherwise. }
    ResolvedSetQbeName: string;
    destructor Destroy; override;
  end;

  TVarDecl = class(TASTNode)
  public
    Names:        TStringList;  { owned — one or more names: x, y: Integer }
    TypeName:     string;
    [Unretained] ResolvedType: TTypeDesc;    { set by uSemantic; nil until analysed }
    Attributes:   TStringList;  { owned — raw attribute names as written in
                                  source, e.g. 'Weak', 'SomeOther'; the
                                  Attribute suffix (if present) is preserved
                                  verbatim — normalisation happens in
                                  semantic analysis. }
    IsWeak:       Boolean;      { set by uSemantic when [Weak] is resolved
                                  on this declaration.  Codegen keys off
                                  this instead of walking Attributes. }
    IsUnretained: Boolean;      { set by uSemantic when [Unretained] is resolved.
                                  Non-owning reference, no ARC and no weak
                                  registry.  See TFieldInfo.IsUnretained. }
    IsGlobal:     Boolean;      { set by uSemantic when this is a program-level global variable }
    IsThreadVar:  Boolean;      { set by parser when declared in a threadvar section }
    InitConst:    TConstDecl;   { owned — optional initialiser for an initialised
                                  variable (var G: T = value).  nil when the
                                  declaration has no initialiser.  Reuses the
                                  const value/fold/data-emit pipeline; semantic
                                  type-checks it against ResolvedType and (for
                                  aggregates) mints InitConst.ResolvedQbeName. }
    constructor Create;
    destructor Destroy; override;
  end;

  { ------------------------------------------------------------------ }
  {  Type section                                                       }
  { ------------------------------------------------------------------ }

  { Abstract base for type definitions. }
  TASTTypeDef = class(TASTNode);

  { Type alias / pointer-type alias: type PFoo = ^TFoo; or type TMyInt = Integer;
    TypeName holds the right-hand side as parsed by ParseTypeName, e.g. '^TFoo'. }
  TTypeAliasDef = class(TASTTypeDef)
  public
    TypeName: string;
  end;

  { Set type definition: type TOptions = set of TEnum; }
  TSetTypeDef = class(TASTTypeDef)
  public
    BaseTypeName: string;  { element type name — must resolve to an enum }
  end;

  { Enum type definition: type TDir = (dNorth, dSouth, dEast, dWest);
    or with explicit ordinals: type TCode = (Idle=10, Running=20, Done=30);
    Members holds the member names; Members.Objects[I] carries the ordinal
    value as Pointer(PtrUInt(Value)).  When no explicit value is given for a
    member the parser assigns previous+1 (auto-increment), matching Delphi/FPC. }
  TEnumTypeDef = class(TASTTypeDef)
  public
    Members: TStringList;  { owned — ordered member names; Objects[I] = ordinal }
    constructor Create;
    destructor Destroy; override;
    procedure AddMember(const AName: string; AValue: Integer);
    function OrdinalAt(AIndex: Integer): Integer;
  end;

  TFieldDecl = class(TASTNode)
  public
    Names:        TStringList;  { owned — e.g. X, Y: Integer }
    TypeName:     string;
    [Unretained] ResolvedType: TTypeDesc;    { set by uSemantic }
    Attributes:   TStringList;  { owned — see TVarDecl.Attributes. }
    IsWeak:       Boolean;      { set by uSemantic when [Weak] is resolved. }
    IsUnretained: Boolean;      { set by uSemantic when [Unretained] is resolved. }
    constructor Create;
    destructor Destroy; override;
  end;

  TRecordTypeDef = class(TASTTypeDef)
  public
    Fields:   TObjectList;  { owned TFieldDecl }
    Methods:  TObjectList;  { owned TMethodDecl }
    IsPacked: Boolean;      { True iff declared `packed record` — disables
                              field alignment padding and tail padding;
                              ARC-managed fields (string/class/intf) still
                              retain 8-byte storage alignment }
    constructor Create;
    destructor Destroy; override;
  end;

  { Procedural type definition: type T = function(...): X;  or
                                 type T = procedure(...);
    Bare procedural pointers — not 'of object' (method pointers) and not
    'reference to' (anonymous methods); both are out of scope for this
    iteration. }
  TProceduralTypeDef = class(TASTTypeDef)
  public
    Params:         TObjectList;  { owned TMethodParam }
    ReturnTypeName: string;       { '' = procedure, non-empty = function }
    IsFunction:     Boolean;
    IsMethodPtr:    Boolean;       { True iff declared with the 'of object'
                                     suffix.  Method-pointer values carry a
                                     16-byte (Code, Data) pair instead of a
                                     bare code pointer. }
    constructor Create;
    destructor Destroy; override;
  end;

  TBlock = class(TASTNode)
  public
    TypeDecls:  TObjectList;  { owned TTypeDecl }
    ConstDecls: TObjectList;  { owned TConstDecl }
    Decls:      TObjectList;  { owned TVarDecl }
    ProcDecls:  TObjectList;  { owned TMethodDecl — standalone procs/funcs }
    Stmts:      TObjectList;  { owned TASTStmt }
    constructor Create;
    destructor Destroy; override;
  end;

  TMethodParam = class(TASTNode)
  public
    ParamName:    string;
    TypeName:     string;      { element type name when IsOpenArray = True }
    IsVarParam:   Boolean;    { True = passed by reference ('var' or 'out' keyword) }
    IsConstParam: Boolean;    { True = 'const' keyword present }
    IsOutParam:   Boolean;    { True = 'out' keyword (write-only by-reference); IsVarParam is also True }
    IsOpenArray:  Boolean;    { True = 'array of T'; TypeName is the element type }
    [Unretained] ResolvedType: TTypeDesc;  { set by uSemantic — TOpenArrayTypeDesc when IsOpenArray }
    DefaultValue: TASTExpr;   { owned — non-nil when the param has a default value
                                ('= expr' after the type); restricted to literal forms
                                (int/float/string/nil) and named-constant idents. }
    HasDefault:   Boolean;    { set when this param has a default value but the value
                                AST itself is unavailable — e.g. a method imported
                                from a cached .bif, which records only that a default
                                exists (so MinArity/overload resolution accept fewer
                                args) without serialising the default expression. }
    destructor Destroy; override;
  end;

  TMethodDecl = class(TASTNode)
  public
    Name:               string;      { method name }
    OwnerTypeName:      string;      { set by uSemantic — class that defines this method }
    Params:             TObjectList; { owned TMethodParam }
    ReturnTypeName:     string;      { empty = procedure }
    [Unretained] ResolvedReturnType: TTypeDesc;   { set by uSemantic; nil = procedure }
    Body:               TBlock;      { owned unless OwnBody = False }
    OwnBody:            Boolean;     { False for cloned generic method stubs that share the body }
    IsVirtual:          Boolean;     { declared with 'virtual' directive }
    IsOverride:         Boolean;     { declared with 'override' directive }
    IsAbstract:         Boolean;     { declared with 'abstract' directive; implies virtual }
    IsOverload:         Boolean;     { declared with 'overload' directive }
    IsPublished:        Boolean;     { declared inside a 'published' visibility
                                       section of a class.  Used by codegen to
                                       emit an entry in the published-method
                                       table, which TObject.MethodAddress
                                       walks at runtime. }
    ResolvedQbeName:    string;      { set by uSemantic — mangled QBE symbol name;
                                       empty string means use Name verbatim }
    OwningUnit:         string;      { name of the unit that exported this routine;
                                       empty for program-scope.  Set by uSemantic;
                                       consumed by codegen for cross-unit references. }
    IsExternal:         Boolean;     { declared with 'external' directive — no body }
    ExternalName:       string;      { C symbol name from 'external name ''c_foo'''; empty = use Pascal name }
    IsRecordMethod:     Boolean;     { set by uSemantic — owner type is a record (not a class) }
    VTableSlot:         Integer;     { -1 = static; >=0 = vtable index (set by uSemantic) }
    TypeParams:         TStringList; { non-nil = generic function template; owns param names }
    TypeParamConstraints: TStringList; { parallel to TypeParams; '' = unconstrained,
                                         'class', 'record', or a concrete type name }
    OwnerTypeParams:    TStringList; { non-nil = generic owner: 'T' in TList<T>.Add }
    IsInlineCandidate:  Boolean;     { set by uSemantic — body is small, leaf-only, primitive
                                       params and locals, no try/loops/raise/nested defs.
                                       Codegen may inline calls to this function at the call
                                       site instead of emitting a real call instruction. }
    { Nested procedures (procedure declared inside another procedure's var block):
      CapturedVars lists the names of outer-scope variables that this nested
      proc reads or writes (set by uSemantic).  Codegen passes each as an
      implicit leading 'var' (by-pointer) parameter so the nested function can
      share the outer variable's storage.  EnclosingDecl points to the directly
      enclosing standalone proc/function (nil for top-level decls). }
    CapturedVars:  TStringList; { owned; nil when no captures }
    [Unretained] EnclosingDecl: TMethodDecl; { not owned — enclosing standalone proc, or nil }
    IsInline: Boolean;    { set by uParser — 'inline' directive present }
    CallingConv: string;  { set by uParser — 'cdecl'/'stdcall'/'register'/'pascal'/
                            'safecall' directive (lowercased); '' = default }
    OwningUnit: string;   { set by uSemantic / uSemanticImport — unit that declares this routine }
    constructor Create;
    destructor Destroy; override;
  end;

  TMethodCallExpr = class(TASTExpr)
  public
    ObjectName:        string;
    Name:              string;     { method name }
    Args:              TObjectList; { owned TASTExpr }
    ObjExpr:           TASTExpr;   { owned — receiver expression when ObjectName = '' }
    [Unretained] ResolvedClassType:  TTypeDesc;   { not owned; set by uSemantic }
    [Unretained] ResolvedMethod:     TObject;     { TMethodDecl — not owned }
    IsConstructorCall:  Boolean;    { set by uSemantic — TypeName.Create(args) }
    IsMetaclassDispatch: Boolean;  { set by uSemantic — receiver is a metaclass var }
    IsGlobal:           Boolean;    { set by uSemantic — ObjectName is a program-level global }
    IsVarParam:         Boolean;    { set by uSemantic — ObjectName is a var/out parameter }
    IsBuiltinToString:    Boolean;  { set by uSemantic — built-in TObject.ToString virtual dispatch }
    IsBuiltinInheritsFrom: Boolean; { set by uSemantic — SomeClass.InheritsFrom(OtherClass) }
    IsProcFieldCall:    Boolean;    { set by uSemantic — Name is a procedural-typed field }
    [Unretained] ProcFieldInfo:      TFieldInfo;  { not owned — the procedural field }
    [Unretained] ResolvedProcType:   TObject;     { TProceduralTypeDesc — not owned }
    constructor Create;
    destructor Destroy; override;
  end;

  { One property declaration inside a class body. }
  TPropertyDecl = class(TASTNode)
  public
    Name:           string;  { property name }
    TypeName:       string;  { declared type }
    ReadName:       string;  { backing field or getter method; '' = no read accessor }
    WriteName:      string;  { backing field or setter method; '' = read-only }
    IndexParamName: string;  { '' = non-indexed property }
    IndexTypeName: string;  { type name of the index parameter; '' when non-indexed }
    IsDefault:      Boolean; { declared with the `default` directive (Obj[I] sugar) }
  end;

  TClassTypeDef = class(TASTTypeDef)
  public
    ParentName:      string;
    ImplementsNames: TStringList;  { owned — names of implemented interfaces }
    ConstDecls:      TObjectList;  { owned TConstDecl — class-level constants }
    Fields:          TObjectList;  { owned TFieldDecl }
    Methods:         TObjectList;  { owned TMethodDecl }
    Properties:      TObjectList;  { owned TPropertyDecl }
    Attributes:      TStringList;  { owned — class-level custom attribute names e.g. 'Threaded' }
    constructor Create;
    destructor Destroy; override;
  end;

  { Generic type template: type TBox<T> = class ... end }
  TGenericTypeDef = class(TASTTypeDef)
  public
    ParamNames:       TStringList;   { owned — type parameter names, e.g. ['T'] or ['K','V'] }
    ParamConstraints: TStringList;   { owned — parallel to ParamNames; '' = unconstrained }
    ClassDef:         TClassTypeDef; { owned — template class body with unresolved param types }
    DefUnitName:      string;        { set by uSemantic/uSemanticImport at registration —
                                       unit (or program) that declares the template; the
                                       Line fields of cloned method bodies refer to THIS
                                       unit's source, so codegen attributes allocation
                                       sites to it }
    constructor Create;
    destructor Destroy; override;
  end;

  { One concrete instantiation of a standalone generic function — stored on TProgram.
    Codegen iterates this list to emit function bodies. }
  TGenericFuncInstance = class
  public
    InstName:   string;       { raw name e.g. 'Identity<Integer>' }
    MethodDecl: TMethodDecl;  { owned — concrete method decl with substituted types }
    constructor Create;
    destructor Destroy; override;
  end;

  { A monomorphised generic METHOD instance (method-level <T>): a method that
    declares its own type parameters, instantiated at a call site.  OwnerType
    is the class/record the method belongs to; the instance keeps an implicit
    Self and is emitted as OwnerType_Method_<args>. }
  TGenericMethodInstance = class
  public
    OwnerType:  string;       { the class/record name }
    InstName:   string;       { method name with type args, e.g. 'Pick<Integer>' }
    MethodDecl: TMethodDecl;  { owned — concrete method decl with substituted types }
    constructor Create;
    destructor Destroy; override;
  end;

  { One concrete instantiation produced by monomorphization — stored on TProgram.
    Codegen iterates this list to emit typeinfo, vtables, and method bodies. }
  TGenericInstance = class
  public
    TypeName: string;        { raw e.g. 'TBox<Integer>' }
    ClassDef: TClassTypeDef; { owned — cloned class body with substituted type names }
    [Unretained] TypeDesc: TTypeDesc;     { non-owned — points to TRecordTypeDesc in SymbolTable }
    DefUnitName: string;     { set by uSemantic at instantiation — unit that DECLARES the
                               template; method-body Line fields refer to that unit's source }
    constructor Create;
    destructor Destroy; override;
  end;

  TInterfaceTypeDef = class(TASTTypeDef)
  public
    ParentName: string;
    Methods:    TObjectList;  { owned TMethodDecl — forward signatures only }
    Properties: TObjectList;  { owned TPropertyDecl — accessors are interface methods }
    constructor Create;
    destructor Destroy; override;
  end;

  { Generic interface template: type IFoo<T> = interface ... end }
  TGenericInterfaceDef = class(TASTTypeDef)
  public
    ParamNames:       TStringList;      { owned — type parameter names, e.g. ['T'] }
    ParamConstraints: TStringList;      { owned — parallel to ParamNames; '' = unconstrained }
    IntfDef:          TInterfaceTypeDef; { owned — template interface body with unresolved param types }
    constructor Create;
    destructor Destroy; override;
  end;

  { Generic record template: type TMyVal<T> = record ... end }
  TGenericRecordDef = class(TASTTypeDef)
  public
    ParamNames:       TStringList;      { owned — type parameter names, e.g. ['T'] }
    ParamConstraints: TStringList;      { owned — parallel to ParamNames; '' = unconstrained }
    RecordDef:        TRecordTypeDef;   { owned — template record body with unresolved param types }
    constructor Create;
    destructor Destroy; override;
  end;

  { One concrete instantiation of a generic record — stored on TProgram.
    Codegen iterates this list to emit method bodies and field cleanup. }
  TGenericRecordInstance = class
  public
    TypeName:  string;          { raw e.g. 'TMyVal<Integer>' }
    RecordDef: TRecordTypeDef;  { owned — cloned record body with substituted type names }
    [Unretained] TypeDesc: TTypeDesc;  { non-owned — points to TRecordTypeDesc in SymbolTable }
    constructor Create;
    destructor Destroy; override;
  end;

  { One concrete instantiation of a generic interface — stored on TProgram.
    Codegen iterates this list to emit typeinfo data. }
  TGenericInterfaceInstance = class
  public
    InstName: string;          { mangled name e.g. 'IEqualityComparer_Integer' }
    IntfDef:  TInterfaceTypeDef; { owned — cloned with substituted type names }
    [Unretained] TypeDesc: TTypeDesc;       { non-owned — points to TInterfaceTypeDesc in SymbolTable }
    constructor Create;
    destructor Destroy; override;
  end;

  TTypeDecl = class(TASTNode)
  public
    Name: string;
    Def:  TASTTypeDef;  { owned }
    destructor Destroy; override;
  end;

  { ------------------------------------------------------------------ }
  {  Block and Program                                                  }
  { ------------------------------------------------------------------ }

  TProgram = class(TASTNode)
  public
    Name:                 string;
    UsedUnits:            TStringList;    { owned }
    Block:                TBlock;         { owned }
    SymbolTable:          TSymbolTable;   { owned after semantic analysis; nil before }
    GenericInstances:       TObjectList;    { owned TGenericInstance — populated by uSemantic }
    GenericFuncInstances:   TObjectList;    { owned TGenericFuncInstance — populated by uSemantic }
    GenericMethodInstances: TObjectList;    { owned TGenericMethodInstance — populated by uSemantic }
    GenericIntfInstances:   TObjectList;    { owned TGenericInterfaceInstance — populated by uSemantic }
    GenericRecordInstances: TObjectList;    { owned TGenericRecordInstance — populated by uSemantic }
    constructor Create;
    destructor Destroy; override;
  end;

  TUnit = class(TASTNode)
  public
    Name:        string;
    SourceFile:  string;       { absolute path of the .pas file this unit was loaded from }
    UsedUnits:     TStringList; { owned — unit names from the interface uses clause }
    ImplUsedUnits: TStringList; { owned — unit names from the implementation
                                  uses clause (loaded but not re-exported) }
    IntfBlock:   TBlock;      { owned — forward decls + type decls }
    ImplBlock:   TBlock;      { owned — full implementations }
    InitStmts:   TObjectList; { owned — statements in the initialization section (may be nil) }
    FinalStmts:  TObjectList; { owned — statements in the finalization section (may be nil) }
    SymbolTable: TSymbolTable; { owned after standalone semantic analysis;
                                 nil when the unit is analysed as part of a
                                 program (program owns the table). }
    GenericInstances:       TObjectList;
    GenericFuncInstances:   TObjectList;
    GenericMethodInstances: TObjectList;
    GenericIntfInstances:   TObjectList;
    GenericRecordInstances: TObjectList;
    constructor Create;
    destructor Destroy; override;
  end;

function BinaryOpName(AOp: TBinaryOp): string;
function IsComparisonOp(AOp: TBinaryOp): Boolean;

{ Deep-clone helpers for generic-instance method body re-analysis.
  Clones structure + raw textual fields (names, type names, operators).
  Resolved* / FieldInfo / IsXxx semantic annotations are NOT copied: each
  instance must re-run semantic analysis to populate them correctly for
  its own concrete type arguments. }
function CloneExpr(AExpr: TASTExpr): TASTExpr;
function CloneStmt(AStmt: TASTStmt): TASTStmt;
function CloneBlock(ABlock: TBlock): TBlock;

{ Granular clone helpers — exposed for uSemanticExport to assemble
  TUnitInterface entries without re-implementing the cloning logic.
  Same deep-copy semantics as CloneBlock: structural + raw textual
  fields are copied, semantic Resolved* annotations are NOT. }
function CloneTypeDecl(ASrc: TTypeDecl): TTypeDecl;
function CloneConstDecl(ASrc: TConstDecl): TConstDecl;
function CloneMethodDecl(ASrc: TMethodDecl): TMethodDecl;
function CloneMethodParam(ASrc: TMethodParam): TMethodParam;
function CloneTypeDef(ASrc: TASTTypeDef): TASTTypeDef;
function CloneClassTypeDef(ASrc: TClassTypeDef): TClassTypeDef;

implementation

function BinaryOpName(AOp: TBinaryOp): string;
begin
  case AOp of
    boAdd: Result := '+';
    boSub: Result := '-';
    boMul: Result := '*';
    boSlash: Result := '/';
    boDiv: Result := 'div';
    boMod: Result := 'mod';
    boEQ:  Result := '=';
    boNE:  Result := '<>';
    boLT:  Result := '<';
    boGT:  Result := '>';
    boLE:  Result := '<=';
    boGE:  Result := '>=';
    boAnd: Result := 'and';
    boOr:  Result := 'or';
    boXor: Result := 'xor';
    boIn:  Result := 'in';
    boShl: Result := 'shl';
    boShr: Result := 'shr';
    boSar: Result := 'sar';
  else
    Result := '?';
  end;
end;

function IsComparisonOp(AOp: TBinaryOp): Boolean;
begin
  Result := AOp in [boEQ, boNE, boLT, boGT, boLE, boGE];
end;

{ TIfStmt }

destructor TIfStmt.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TCompoundStmt }

constructor TCompoundStmt.Create;
begin
  inherited Create();
  Stmts := TObjectList.Create(True);
end;

destructor TCompoundStmt.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TWhileStmt }

destructor TWhileStmt.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TRepeatStmt }

destructor TRepeatStmt.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TForStmt }

destructor TForStmt.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TForInStmt }

destructor TForInStmt.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TTryFinallyStmt }

destructor TTryFinallyStmt.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TExceptHandlerClause }

destructor TExceptHandlerClause.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TTryExceptStmt }

constructor TTryExceptStmt.Create;
begin
  inherited Create();
  Handlers := TObjectList.Create(True);
end;

destructor TTryExceptStmt.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TRaiseStmt }

destructor TRaiseStmt.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

destructor TExitStmt.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TFieldAccessExpr }

destructor TFieldAccessExpr.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TIsExpr }

destructor TIsExpr.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TAsExpr }

destructor TAsExpr.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TSupportsExpr }

destructor TSupportsExpr.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TBinaryExpr }

destructor TBinaryExpr.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TNotExpr }

destructor TNotExpr.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TAssignment }

destructor TAssignment.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TFieldAssignment }

destructor TFieldAssignment.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TStaticSubscriptAssign }

destructor TStaticSubscriptAssign.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TPointerWriteStmt }

destructor TPointerWriteStmt.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TDerefExpr }

destructor TDerefExpr.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

destructor TAddrOfExpr.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

destructor TStringSubscriptExpr.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TArrayLiteralExpr }

constructor TArrayLiteralExpr.Create;
begin
  inherited Create();
  Elements := TObjectList.Create(True);
end;

destructor TArrayLiteralExpr.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

destructor TSetRangeExpr.Destroy;
begin
  { LowExpr/HighExpr released by ARC field cleanup. }
  inherited Destroy();
end;

{ TProcCall }

constructor TProcCall.Create;
begin
  inherited Create();
  Args := TObjectList.Create(True);
end;

destructor TProcCall.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TFuncCallExpr }

constructor TFuncCallExpr.Create;
begin
  inherited Create();
  Args := TObjectList.Create(True);
end;

destructor TFuncCallExpr.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TIndirectFuncCallExpr }

constructor TIndirectFuncCallExpr.Create;
begin
  inherited Create();
  Args := TObjectList.Create(True);
end;

destructor TIndirectFuncCallExpr.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TMethodCallStmt }

constructor TMethodCallStmt.Create;
begin
  inherited Create();
  Args := TObjectList.Create(True);
end;

destructor TMethodCallStmt.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TInheritedCallStmt }

constructor TInheritedCallStmt.Create;
begin
  inherited Create();
  Args := TObjectList.Create(True);
end;

destructor TInheritedCallStmt.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TInheritedCallExpr }

constructor TInheritedCallExpr.Create;
begin
  inherited Create();
  Args := TObjectList.Create(True);
end;

destructor TInheritedCallExpr.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TMethodParam }

destructor TMethodParam.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TVarDecl }

constructor TVarDecl.Create;
begin
  inherited Create();
  Names      := TStringList.Create();
  Attributes := TStringList.Create();
  IsWeak     := False;
end;

destructor TVarDecl.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TFieldDecl }

constructor TFieldDecl.Create;
begin
  inherited Create();
  Names      := TStringList.Create();
  Attributes := TStringList.Create();
  IsWeak       := False;
  IsUnretained := False;
end;

destructor TFieldDecl.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TRecordTypeDef }

constructor TRecordTypeDef.Create;
begin
  inherited Create();
  Fields  := TObjectList.Create(True);
  Methods := TObjectList.Create(True);
end;

destructor TRecordTypeDef.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TProceduralTypeDef }

constructor TProceduralTypeDef.Create;
begin
  inherited Create();
  Params     := TObjectList.Create(True);
  IsFunction := False;
end;

destructor TProceduralTypeDef.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TMethodDecl }

constructor TMethodDecl.Create;
begin
  inherited Create();
  Params     := TObjectList.Create(True);
  VTableSlot := -1;
  OwnBody    := True;
end;

destructor TMethodDecl.Destroy;
begin
  Params.Free();
  TypeParams.Free();
  TypeParamConstraints.Free();
  OwnerTypeParams.Free();
  CapturedVars.Free();
  if OwnBody then Body.Free();
  inherited Destroy();
end;

{ TMethodCallExpr }

constructor TMethodCallExpr.Create;
begin
  inherited Create();
  Args := TObjectList.Create(True);
end;

destructor TMethodCallExpr.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TClassTypeDef }

constructor TClassTypeDef.Create;
begin
  inherited Create();
  ImplementsNames := TStringList.Create();
  ConstDecls      := TObjectList.Create(True);
  Fields          := TObjectList.Create(True);
  Methods         := TObjectList.Create(True);
  Properties      := TObjectList.Create(True);
  Attributes      := TStringList.Create();
end;

destructor TClassTypeDef.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TInterfaceTypeDef }

constructor TInterfaceTypeDef.Create;
begin
  inherited Create();
  Methods := TObjectList.Create(True);
  Properties := TObjectList.Create(True);
end;

destructor TInterfaceTypeDef.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TGenericTypeDef }

constructor TGenericTypeDef.Create;
begin
  inherited Create();
  ParamNames       := TStringList.Create();
  ParamConstraints := TStringList.Create();
  ClassDef         := TClassTypeDef.Create();
end;

destructor TGenericTypeDef.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TGenericInstance }

{ TGenericFuncInstance }

constructor TGenericFuncInstance.Create;
begin
  inherited Create();
end;

destructor TGenericFuncInstance.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

constructor TGenericMethodInstance.Create;
begin
  inherited Create();
end;

destructor TGenericMethodInstance.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TGenericInterfaceDef }

constructor TGenericInterfaceDef.Create;
begin
  inherited Create();
  ParamNames       := TStringList.Create();
  ParamConstraints := TStringList.Create();
  IntfDef          := TInterfaceTypeDef.Create();
end;

destructor TGenericInterfaceDef.Destroy;
begin
  inherited Destroy();
end;

{ TGenericRecordDef }

constructor TGenericRecordDef.Create;
begin
  inherited Create();
  ParamNames       := TStringList.Create();
  ParamConstraints := TStringList.Create();
  RecordDef        := TRecordTypeDef.Create();
end;

destructor TGenericRecordDef.Destroy;
begin
  inherited Destroy();
end;

{ TGenericRecordInstance }

constructor TGenericRecordInstance.Create;
begin
  inherited Create();
  RecordDef := TRecordTypeDef.Create();
end;

destructor TGenericRecordInstance.Destroy;
begin
  inherited Destroy();
end;

{ TGenericInterfaceInstance }

constructor TGenericInterfaceInstance.Create;
begin
  inherited Create();
  IntfDef := TInterfaceTypeDef.Create();
end;

destructor TGenericInterfaceInstance.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TGenericInstance }

constructor TGenericInstance.Create;
begin
  inherited Create();
  ClassDef := TClassTypeDef.Create();
end;

destructor TGenericInstance.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TTypeDecl }

destructor TTypeDecl.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TBlock }

constructor TBlock.Create;
begin
  inherited Create();
  TypeDecls  := TObjectList.Create(True);
  ConstDecls := TObjectList.Create(True);
  Decls      := TObjectList.Create(True);
  ProcDecls  := TObjectList.Create(True);
  Stmts      := TObjectList.Create(True);
end;

destructor TBlock.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TEnumTypeDef }

constructor TEnumTypeDef.Create;
begin
  inherited Create();
  Members := TStringList.Create();
end;

destructor TEnumTypeDef.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

procedure TEnumTypeDef.AddMember(const AName: string; AValue: Integer);
begin
  Members.AddObject(AName, TObject(Pointer(PtrUInt(AValue))));
end;

function TEnumTypeDef.OrdinalAt(AIndex: Integer): Integer;
begin
  Result := Integer(PtrUInt(Pointer(Members.Objects[AIndex])));
end;

{ TCaseBranch }

constructor TCaseBranch.Create;
begin
  inherited Create();
  Values := TObjectList.Create(True);
end;

destructor TCaseBranch.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TCaseStmt }

constructor TCaseStmt.Create;
begin
  inherited Create();
  Branches := TObjectList.Create(True);
end;

destructor TCaseStmt.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TProgram }

constructor TProgram.Create;
begin
  inherited Create();
  UsedUnits              := TStringList.Create();
  GenericInstances       := TObjectList.Create(True);
  GenericFuncInstances   := TObjectList.Create(True);
  GenericMethodInstances := TObjectList.Create(True);
  GenericIntfInstances   := TObjectList.Create(True);
  GenericRecordInstances := TObjectList.Create(True);
end;

destructor TConstDecl.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

destructor TProgram.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ TUnit }

constructor TUnit.Create;
begin
  inherited Create();
  UsedUnits     := TStringList.Create();
  ImplUsedUnits := TStringList.Create();
  IntfBlock  := TBlock.Create();
  ImplBlock  := TBlock.Create();
  InitStmts  := nil;
  FinalStmts := nil;
  GenericInstances       := TObjectList.Create(True);
  GenericFuncInstances   := TObjectList.Create(True);
  GenericMethodInstances := TObjectList.Create(True);
  GenericIntfInstances   := TObjectList.Create(True);
  GenericRecordInstances := TObjectList.Create(True);
end;

destructor TUnit.Destroy;
begin
  { Owned class fields released by ARC field cleanup. }
  inherited Destroy();
end;

{ ------------------------------------------------------------------ }
{ Deep clone for generic-instance method body re-analysis              }
{ ------------------------------------------------------------------ }

function CloneVarDecl(ASrc: TVarDecl): TVarDecl; forward;
function CloneFieldDecl(ASrc: TFieldDecl): TFieldDecl; forward;
function ClonePropertyDecl(ASrc: TPropertyDecl): TPropertyDecl; forward;
{ CloneTypeDecl, CloneConstDecl, CloneMethodDecl, CloneMethodParam,
  CloneTypeDef are now declared in the interface section. }
function CloneGenericTypeDef(ASrc: TGenericTypeDef): TGenericTypeDef; forward;
function CloneInterfaceTypeDef(ASrc: TInterfaceTypeDef): TInterfaceTypeDef; forward;
function CloneGenericInterfaceDef(ASrc: TGenericInterfaceDef): TGenericInterfaceDef; forward;
function CloneProceduralTypeDef(ASrc: TProceduralTypeDef): TProceduralTypeDef; forward;
function CloneExceptHandler(ASrc: TExceptHandlerClause): TExceptHandlerClause; forward;
function CloneCaseBranch(ASrc: TCaseBranch): TCaseBranch; forward;
function CloneCompound(ASrc: TCompoundStmt): TCompoundStmt; forward;

procedure CopyExprPos(ADst, ASrc: TASTExpr);
begin
  ADst.Line := ASrc.Line;
  ADst.Col  := ASrc.Col;
end;

procedure CopyStmtPos(ADst, ASrc: TASTStmt);
begin
  ADst.Line := ASrc.Line;
  ADst.Col  := ASrc.Col;
end;

function CloneExprList(ASrc: TObjectList): TObjectList;
var
  I: Integer;
begin
  Result := TObjectList.Create(True);
  for I := 0 to ASrc.Count - 1 do
    Result.Add(CloneExpr(TASTExpr(ASrc.Items[I])));
end;

function CloneExpr(AExpr: TASTExpr): TASTExpr;
var
  IL:  TIntLiteral;
  FL:  TFloatLiteral;
  SL:  TStringLiteral;
  SS:  TStringSubscriptExpr;
  AL:  TArrayLiteralExpr;
  SRE: TSetRangeExpr;
  IE:  TIdentExpr;
  FA:  TFieldAccessExpr;
  IsE: TIsExpr;
  InhE: TInheritedCallExpr;
  CloneI: Integer;
  AsE: TAsExpr;
  SuE: TSupportsExpr;
  BE:  TBinaryExpr;
  NE:  TNotExpr;
  FCE: TFuncCallExpr;
  DE:  TDerefExpr;
  AoE: TAddrOfExpr;
  MCE: TMethodCallExpr;
  I:   Integer;
begin
  if AExpr = nil then
  begin Result := nil; Exit; end;

  if AExpr is TIntLiteral then
  begin
    IL := TIntLiteral.Create();
    IL.Value := TIntLiteral(AExpr).Value;
    Result := IL;
  end
  else if AExpr is TFloatLiteral then
  begin
    FL := TFloatLiteral.Create();
    FL.Value := TFloatLiteral(AExpr).Value;
    Result := FL;
  end
  else if AExpr is TStringLiteral then
  begin
    SL := TStringLiteral.Create();
    SL.Value := TStringLiteral(AExpr).Value;
    Result := SL;
  end
  else if AExpr is TNilLiteral then
  begin
    Result := TNilLiteral.Create();
  end
  else if AExpr is TStringSubscriptExpr then
  begin
    SS := TStringSubscriptExpr.Create();
    SS.StrExpr   := CloneExpr(TStringSubscriptExpr(AExpr).StrExpr);
    SS.IndexExpr := CloneExpr(TStringSubscriptExpr(AExpr).IndexExpr);
    Result := SS;
  end
  else if AExpr is TArrayLiteralExpr then
  begin
    AL := TArrayLiteralExpr.Create();
    for I := 0 to TArrayLiteralExpr(AExpr).Elements.Count - 1 do
      AL.Elements.Add(CloneExpr(TASTExpr(TArrayLiteralExpr(AExpr).Elements.Items[I])));
    AL.IsConstArray := TArrayLiteralExpr(AExpr).IsConstArray;
    Result := AL;
  end
  else if AExpr is TSetRangeExpr then
  begin
    SRE := TSetRangeExpr.Create();
    SRE.LowExpr  := CloneExpr(TSetRangeExpr(AExpr).LowExpr);
    SRE.HighExpr := CloneExpr(TSetRangeExpr(AExpr).HighExpr);
    Result := SRE;
  end
  else if AExpr is TIdentExpr then
  begin
    IE := TIdentExpr.Create();
    IE.Name := TIdentExpr(AExpr).Name;
    { Note: leave IsConstant/ParamMode/IsImplicitSelf/etc. nil/false —
      semantic analyser must re-resolve in the new instance's scope. }
    Result := IE;
  end
  else if AExpr is TFieldAccessExpr then
  begin
    FA := TFieldAccessExpr.Create();
    FA.RecordName    := TFieldAccessExpr(AExpr).RecordName;
    FA.FieldName     := TFieldAccessExpr(AExpr).FieldName;
    FA.Base          := CloneExpr(TFieldAccessExpr(AExpr).Base);
    FA.PropIndexExpr := CloneExpr(TFieldAccessExpr(AExpr).PropIndexExpr);
    Result := FA;
  end
  else if AExpr is TIsExpr then
  begin
    IsE := TIsExpr.Create();
    IsE.Obj      := CloneExpr(TIsExpr(AExpr).Obj);
    IsE.TypeName := TIsExpr(AExpr).TypeName;
    Result := IsE;
  end
  else if AExpr is TInheritedCallExpr then
  begin
    InhE := TInheritedCallExpr.Create();
    InhE.Name := TInheritedCallExpr(AExpr).Name;
    for CloneI := 0 to TInheritedCallExpr(AExpr).Args.Count - 1 do
      InhE.Args.Add(CloneExpr(TASTExpr(TInheritedCallExpr(AExpr).Args.Items[CloneI])));
    Result := InhE;
  end
  else if AExpr is TAsExpr then
  begin
    AsE := TAsExpr.Create();
    AsE.Obj      := CloneExpr(TAsExpr(AExpr).Obj);
    AsE.TypeName := TAsExpr(AExpr).TypeName;
    Result := AsE;
  end
  else if AExpr is TSupportsExpr then
  begin
    SuE := TSupportsExpr.Create();
    SuE.Obj          := CloneExpr(TSupportsExpr(AExpr).Obj);
    SuE.IntfTypeName := TSupportsExpr(AExpr).IntfTypeName;
    SuE.OutVarName   := TSupportsExpr(AExpr).OutVarName;
    Result := SuE;
  end
  else if AExpr is TBinaryExpr then
  begin
    BE := TBinaryExpr.Create();
    BE.Op    := TBinaryExpr(AExpr).Op;
    BE.Left  := CloneExpr(TBinaryExpr(AExpr).Left);
    BE.Right := CloneExpr(TBinaryExpr(AExpr).Right);
    Result := BE;
  end
  else if AExpr is TNotExpr then
  begin
    NE := TNotExpr.Create();
    NE.Expr := CloneExpr(TNotExpr(AExpr).Expr);
    Result := NE;
  end
  else if AExpr is TFuncCallExpr then
  begin
    FCE := TFuncCallExpr.Create();
    FCE.Name := TFuncCallExpr(AExpr).Name;
    for I := 0 to TFuncCallExpr(AExpr).Args.Count - 1 do
      FCE.Args.Add(CloneExpr(TASTExpr(TFuncCallExpr(AExpr).Args.Items[I])));
    Result := FCE;
  end
  else if AExpr is TDerefExpr then
  begin
    DE := TDerefExpr.Create();
    DE.Expr := CloneExpr(TDerefExpr(AExpr).Expr);
    Result := DE;
  end
  else if AExpr is TAddrOfExpr then
  begin
    AoE := TAddrOfExpr.Create();
    AoE.Expr := CloneExpr(TAddrOfExpr(AExpr).Expr);
    Result := AoE;
  end
  else if AExpr is TMethodCallExpr then
  begin
    MCE := TMethodCallExpr.Create();
    MCE.ObjectName := TMethodCallExpr(AExpr).ObjectName;
    MCE.Name       := TMethodCallExpr(AExpr).Name;
    MCE.ObjExpr    := CloneExpr(TMethodCallExpr(AExpr).ObjExpr);
    for I := 0 to TMethodCallExpr(AExpr).Args.Count - 1 do
      MCE.Args.Add(CloneExpr(TASTExpr(TMethodCallExpr(AExpr).Args.Items[I])));
    Result := MCE;
  end
  else
    raise Exception.CreateFmt('CloneExpr: unhandled expression node %s',
      [AExpr.ClassName]);

  CopyExprPos(Result, AExpr);
end;

function CloneCompound(ASrc: TCompoundStmt): TCompoundStmt;
var
  I: Integer;
begin
  if ASrc = nil then
  begin Result := nil; Exit; end;
  Result := TCompoundStmt.Create();
  CopyStmtPos(Result, ASrc);
  for I := 0 to ASrc.Stmts.Count - 1 do
    Result.Stmts.Add(CloneStmt(TASTStmt(ASrc.Stmts.Items[I])));
end;

function CloneExceptHandler(ASrc: TExceptHandlerClause): TExceptHandlerClause;
begin
  Result := TExceptHandlerClause.Create();
  Result.VarName  := ASrc.VarName;
  Result.TypeName := ASrc.TypeName;
  Result.Body     := CloneCompound(ASrc.Body);
end;

function CloneCaseBranch(ASrc: TCaseBranch): TCaseBranch;
var
  I: Integer;
begin
  Result := TCaseBranch.Create();
  for I := 0 to ASrc.Values.Count - 1 do
    Result.Values.Add(CloneExpr(TASTExpr(ASrc.Values.Items[I])));
  Result.Stmt := CloneStmt(ASrc.Stmt);
end;

function CloneStmt(AStmt: TASTStmt): TASTStmt;
var
  AS_:  TAssignment;
  IF_:  TIfStmt;
  CS_:  TCompoundStmt;
  WS_:  TWhileStmt;
  RS_:  TRepeatStmt;
  FS_:  TForStmt;
  FIS_: TForInStmt;
  TFS_: TTryFinallyStmt;
  TES_: TTryExceptStmt;
  RaS_: TRaiseStmt;
  ExS_: TExitStmt;
  CSS_: TCaseStmt;
  FAS_: TFieldAssignment;
  SSA_: TStaticSubscriptAssign;
  PWS_: TPointerWriteStmt;
  PC_:  TProcCall;
  MCS_: TMethodCallStmt;
  ICS_: TInheritedCallStmt;
  I:    Integer;
begin
  if AStmt = nil then
  begin Result := nil; Exit; end;

  if AStmt is TAssignment then
  begin
    AS_ := TAssignment.Create();
    AS_.Name := TAssignment(AStmt).Name;
    AS_.Expr := CloneExpr(TAssignment(AStmt).Expr);
    Result := AS_;
  end
  else if AStmt is TIfStmt then
  begin
    IF_ := TIfStmt.Create();
    IF_.Condition := CloneExpr(TIfStmt(AStmt).Condition);
    IF_.ThenStmt  := CloneStmt(TIfStmt(AStmt).ThenStmt);
    IF_.ElseStmt  := CloneStmt(TIfStmt(AStmt).ElseStmt);
    Result := IF_;
  end
  else if AStmt is TCompoundStmt then
  begin
    CS_ := TCompoundStmt.Create();
    for I := 0 to TCompoundStmt(AStmt).Stmts.Count - 1 do
      CS_.Stmts.Add(CloneStmt(TASTStmt(TCompoundStmt(AStmt).Stmts.Items[I])));
    Result := CS_;
  end
  else if AStmt is TWhileStmt then
  begin
    WS_ := TWhileStmt.Create();
    WS_.Condition := CloneExpr(TWhileStmt(AStmt).Condition);
    WS_.Body      := CloneStmt(TWhileStmt(AStmt).Body);
    Result := WS_;
  end
  else if AStmt is TRepeatStmt then
  begin
    RS_ := TRepeatStmt.Create();
    RS_.Body      := CloneCompound(TRepeatStmt(AStmt).Body);
    RS_.Condition := CloneExpr(TRepeatStmt(AStmt).Condition);
    Result := RS_;
  end
  else if AStmt is TForStmt then
  begin
    FS_ := TForStmt.Create();
    FS_.VarName   := TForStmt(AStmt).VarName;
    FS_.StartExpr := CloneExpr(TForStmt(AStmt).StartExpr);
    FS_.EndExpr   := CloneExpr(TForStmt(AStmt).EndExpr);
    FS_.IsDownTo  := TForStmt(AStmt).IsDownTo;
    FS_.Body      := CloneStmt(TForStmt(AStmt).Body);
    Result := FS_;
  end
  else if AStmt is TForInStmt then
  begin
    FIS_ := TForInStmt.Create();
    FIS_.VarName  := TForInStmt(AStmt).VarName;
    FIS_.CollExpr := CloneExpr(TForInStmt(AStmt).CollExpr);
    FIS_.Body     := CloneStmt(TForInStmt(AStmt).Body);
    Result := FIS_;
  end
  else if AStmt is TTryFinallyStmt then
  begin
    TFS_ := TTryFinallyStmt.Create();
    TFS_.TryBody     := CloneCompound(TTryFinallyStmt(AStmt).TryBody);
    TFS_.FinallyBody := CloneCompound(TTryFinallyStmt(AStmt).FinallyBody);
    Result := TFS_;
  end
  else if AStmt is TTryExceptStmt then
  begin
    TES_ := TTryExceptStmt.Create();
    TES_.TryBody := CloneCompound(TTryExceptStmt(AStmt).TryBody);
    for I := 0 to TTryExceptStmt(AStmt).Handlers.Count - 1 do
      TES_.Handlers.Add(
        CloneExceptHandler(
          TExceptHandlerClause(TTryExceptStmt(AStmt).Handlers.Items[I])));
    TES_.ElseBody   := CloneCompound(TTryExceptStmt(AStmt).ElseBody);
    TES_.ExceptBody := CloneCompound(TTryExceptStmt(AStmt).ExceptBody);
    Result := TES_;
  end
  else if AStmt is TRaiseStmt then
  begin
    RaS_ := TRaiseStmt.Create();
    RaS_.Expr := CloneExpr(TRaiseStmt(AStmt).Expr);
    Result := RaS_;
  end
  else if AStmt is TExitStmt then
  begin
    ExS_       := TExitStmt.Create();
    ExS_.Value := CloneExpr(TExitStmt(AStmt).Value);
    Result     := ExS_;
  end
  else if AStmt is TBreakStmt then
    Result := TBreakStmt.Create()
  else if AStmt is TContinueStmt then
    Result := TContinueStmt.Create()
  else if AStmt is TCaseStmt then
  begin
    CSS_ := TCaseStmt.Create();
    CSS_.Selector := CloneExpr(TCaseStmt(AStmt).Selector);
    for I := 0 to TCaseStmt(AStmt).Branches.Count - 1 do
      CSS_.Branches.Add(
        CloneCaseBranch(TCaseBranch(TCaseStmt(AStmt).Branches.Items[I])));
    CSS_.ElseStmt := CloneStmt(TCaseStmt(AStmt).ElseStmt);
    Result := CSS_;
  end
  else if AStmt is TFieldAssignment then
  begin
    FAS_ := TFieldAssignment.Create();
    FAS_.RecordName    := TFieldAssignment(AStmt).RecordName;
    FAS_.FieldName     := TFieldAssignment(AStmt).FieldName;
    FAS_.Expr          := CloneExpr(TFieldAssignment(AStmt).Expr);
    FAS_.ObjExpr       := CloneExpr(TFieldAssignment(AStmt).ObjExpr);
    FAS_.PropIndexExpr := CloneExpr(TFieldAssignment(AStmt).PropIndexExpr);
    Result := FAS_;
  end
  else if AStmt is TStaticSubscriptAssign then
  begin
    SSA_ := TStaticSubscriptAssign.Create();
    SSA_.ArrayName := TStaticSubscriptAssign(AStmt).ArrayName;
    SSA_.IndexExpr := CloneExpr(TStaticSubscriptAssign(AStmt).IndexExpr);
    SSA_.ValueExpr := CloneExpr(TStaticSubscriptAssign(AStmt).ValueExpr);
    SSA_.BaseExpr  := CloneExpr(TStaticSubscriptAssign(AStmt).BaseExpr);
    Result := SSA_;
  end
  else if AStmt is TPointerWriteStmt then
  begin
    PWS_ := TPointerWriteStmt.Create();
    PWS_.PtrExpr := CloneExpr(TPointerWriteStmt(AStmt).PtrExpr);
    PWS_.ValExpr := CloneExpr(TPointerWriteStmt(AStmt).ValExpr);
    Result := PWS_;
  end
  else if AStmt is TProcCall then
  begin
    PC_ := TProcCall.Create();
    PC_.Name := TProcCall(AStmt).Name;
    for I := 0 to TProcCall(AStmt).Args.Count - 1 do
      PC_.Args.Add(CloneExpr(TASTExpr(TProcCall(AStmt).Args.Items[I])));
    Result := PC_;
  end
  else if AStmt is TMethodCallStmt then
  begin
    MCS_ := TMethodCallStmt.Create();
    MCS_.ObjectName := TMethodCallStmt(AStmt).ObjectName;
    MCS_.Name       := TMethodCallStmt(AStmt).Name;
    MCS_.ObjExpr    := CloneExpr(TMethodCallStmt(AStmt).ObjExpr);
    for I := 0 to TMethodCallStmt(AStmt).Args.Count - 1 do
      MCS_.Args.Add(CloneExpr(TASTExpr(TMethodCallStmt(AStmt).Args.Items[I])));
    Result := MCS_;
  end
  else if AStmt is TInheritedCallStmt then
  begin
    ICS_ := TInheritedCallStmt.Create();
    ICS_.Name := TInheritedCallStmt(AStmt).Name;
    for I := 0 to TInheritedCallStmt(AStmt).Args.Count - 1 do
      ICS_.Args.Add(CloneExpr(TASTExpr(TInheritedCallStmt(AStmt).Args.Items[I])));
    Result := ICS_;
  end
  else
    raise Exception.CreateFmt('CloneStmt: unhandled statement node %s',
      [AStmt.ClassName]);

  CopyStmtPos(Result, AStmt);
end;

function CloneVarDecl(ASrc: TVarDecl): TVarDecl;
var
  I: Integer;
begin
  Result := TVarDecl.Create();
  Result.Line     := ASrc.Line;
  Result.Col      := ASrc.Col;
  Result.TypeName := ASrc.TypeName;
  for I := 0 to ASrc.Names.Count - 1 do
    Result.Names.Add(ASrc.Names.Strings[I]);
  for I := 0 to ASrc.Attributes.Count - 1 do
    Result.Attributes.Add(ASrc.Attributes.Strings[I]);
  if ASrc.InitConst <> nil then
    Result.InitConst := CloneConstDecl(ASrc.InitConst);
end;

function CloneFieldDecl(ASrc: TFieldDecl): TFieldDecl;
var
  I: Integer;
begin
  Result := TFieldDecl.Create();
  Result.Line     := ASrc.Line;
  Result.Col      := ASrc.Col;
  Result.TypeName := ASrc.TypeName;
  for I := 0 to ASrc.Names.Count - 1 do
    Result.Names.Add(ASrc.Names.Strings[I]);
  for I := 0 to ASrc.Attributes.Count - 1 do
    Result.Attributes.Add(ASrc.Attributes.Strings[I]);
end;

function ClonePropertyDecl(ASrc: TPropertyDecl): TPropertyDecl;
begin
  Result := TPropertyDecl.Create();
  Result.Name           := ASrc.Name;
  Result.TypeName       := ASrc.TypeName;
  Result.ReadName       := ASrc.ReadName;
  Result.WriteName      := ASrc.WriteName;
  Result.IndexParamName := ASrc.IndexParamName;
  Result.IndexTypeName  := ASrc.IndexTypeName;
end;

function CloneTypeDecl(ASrc: TTypeDecl): TTypeDecl;
begin
  Result := TTypeDecl.Create();
  Result.Line := ASrc.Line;
  Result.Col  := ASrc.Col;
  Result.Name := ASrc.Name;
  Result.Def  := CloneTypeDef(ASrc.Def);
end;

function CloneConstDecl(ASrc: TConstDecl): TConstDecl;
var
  I: Integer;
begin
  Result := TConstDecl.Create();
  Result.Line     := ASrc.Line;
  Result.Col      := ASrc.Col;
  Result.Name     := ASrc.Name;
  Result.TypeName := ASrc.TypeName;
  Result.IntVal   := ASrc.IntVal;
  Result.StrVal   := ASrc.StrVal;
  Result.IsString := ASrc.IsString;
  Result.IsFloat  := ASrc.IsFloat;
  if ASrc.ConstParts <> nil then
  begin
    Result.ConstParts := TStringList.Create();
    for I := 0 to ASrc.ConstParts.Count - 1 do
      Result.ConstParts.AddObject(
        ASrc.ConstParts.Strings[I], ASrc.ConstParts.Objects[I]);
  end;
  Result.IsArrayConst        := ASrc.IsArrayConst;
  Result.ArrayIndexType      := ASrc.ArrayIndexType;
  Result.ArrayElemType       := ASrc.ArrayElemType;
  Result.ArrayIsRangeIndexed := ASrc.ArrayIsRangeIndexed;
  Result.ArrayLowBound       := ASrc.ArrayLowBound;
  Result.ArrayHighBound      := ASrc.ArrayHighBound;
  if ASrc.ArrayDimLows <> nil then
  begin
    Result.ArrayDimLows := TStringList.Create();
    for I := 0 to ASrc.ArrayDimLows.Count - 1 do
      Result.ArrayDimLows.Add(ASrc.ArrayDimLows.Strings[I]);
  end;
  if ASrc.ArrayDimHighs <> nil then
  begin
    Result.ArrayDimHighs := TStringList.Create();
    for I := 0 to ASrc.ArrayDimHighs.Count - 1 do
      Result.ArrayDimHighs.Add(ASrc.ArrayDimHighs.Strings[I]);
  end;
  if ASrc.ArrayElements <> nil then
  begin
    Result.ArrayElements := TStringList.Create();
    for I := 0 to ASrc.ArrayElements.Count - 1 do
      Result.ArrayElements.Add(ASrc.ArrayElements.Strings[I]);
  end;
  if ASrc.IntExprTokens <> nil then
  begin
    Result.IntExprTokens := TStringList.Create();
    for I := 0 to ASrc.IntExprTokens.Count - 1 do
      Result.IntExprTokens.AddObject(
        ASrc.IntExprTokens.Strings[I], ASrc.IntExprTokens.Objects[I]);
  end;
  if ASrc.IntValueExpr <> nil then
    Result.IntValueExpr := CloneExpr(ASrc.IntValueExpr);
  Result.IsSet := ASrc.IsSet;
  if ASrc.SetElements <> nil then
  begin
    Result.SetElements := TStringList.Create();
    for I := 0 to ASrc.SetElements.Count - 1 do
      Result.SetElements.Add(ASrc.SetElements.Strings[I]);
  end;
  if ASrc.ConstSetBytes <> nil then
  begin
    Result.ConstSetBytes := TStringList.Create();
    for I := 0 to ASrc.ConstSetBytes.Count - 1 do
      Result.ConstSetBytes.Add(ASrc.ConstSetBytes.Strings[I]);
  end;
  Result.ResolvedSetQbeName := ASrc.ResolvedSetQbeName;
end;

function CloneMethodParam(ASrc: TMethodParam): TMethodParam;
begin
  Result := TMethodParam.Create();
  Result.Line         := ASrc.Line;
  Result.Col          := ASrc.Col;
  Result.ParamName    := ASrc.ParamName;
  Result.TypeName     := ASrc.TypeName;
  Result.IsVarParam   := ASrc.IsVarParam;
  Result.IsConstParam := ASrc.IsConstParam;
  Result.IsOutParam   := ASrc.IsOutParam;
  Result.IsOpenArray  := ASrc.IsOpenArray;
  Result.DefaultValue := CloneExpr(ASrc.DefaultValue);
  Result.HasDefault   := ASrc.HasDefault;
end;

function CloneMethodDecl(ASrc: TMethodDecl): TMethodDecl;
var
  I: Integer;
begin
  Result := TMethodDecl.Create();
  Result.Line           := ASrc.Line;
  Result.Col            := ASrc.Col;
  Result.Name           := ASrc.Name;
  Result.OwnerTypeName  := ASrc.OwnerTypeName;
  Result.ReturnTypeName := ASrc.ReturnTypeName;
  Result.IsVirtual      := ASrc.IsVirtual;
  Result.IsOverride     := ASrc.IsOverride;
  Result.IsAbstract     := ASrc.IsAbstract;
  Result.IsOverload     := ASrc.IsOverload;
  Result.IsPublished    := ASrc.IsPublished;
  Result.IsExternal     := ASrc.IsExternal;
  Result.ExternalName   := ASrc.ExternalName;
  Result.CallingConv    := ASrc.CallingConv;
  Result.IsRecordMethod := ASrc.IsRecordMethod;
  for I := 0 to ASrc.Params.Count - 1 do
    Result.Params.Add(CloneMethodParam(TMethodParam(ASrc.Params.Items[I])));
  if ASrc.TypeParams <> nil then
  begin
    Result.TypeParams := TStringList.Create();
    for I := 0 to ASrc.TypeParams.Count - 1 do
      Result.TypeParams.Add(ASrc.TypeParams.Strings[I]);
  end;
  if ASrc.TypeParamConstraints <> nil then
  begin
    Result.TypeParamConstraints := TStringList.Create();
    for I := 0 to ASrc.TypeParamConstraints.Count - 1 do
      Result.TypeParamConstraints.Add(ASrc.TypeParamConstraints.Strings[I]);
  end;
  if ASrc.OwnerTypeParams <> nil then
  begin
    Result.OwnerTypeParams := TStringList.Create();
    for I := 0 to ASrc.OwnerTypeParams.Count - 1 do
      Result.OwnerTypeParams.Add(ASrc.OwnerTypeParams.Strings[I]);
  end;
  if (ASrc.Body <> nil) and ASrc.OwnBody then
  begin
    Result.Body    := CloneBlock(ASrc.Body);
    Result.OwnBody := True;
  end
  else
  begin
    Result.Body    := ASrc.Body;
    Result.OwnBody := False;
  end;
end;

function CloneTypeDef(ASrc: TASTTypeDef): TASTTypeDef;
var
  TA: TTypeAliasDef;
  ST: TSetTypeDef;
  RT: TRecordTypeDef;
  ET: TEnumTypeDef;
  I:  Integer;
begin
  if ASrc = nil then
  begin Result := nil; Exit; end;
  if ASrc is TTypeAliasDef then
  begin
    TA := TTypeAliasDef.Create();
    TA.TypeName := TTypeAliasDef(ASrc).TypeName;
    Result := TA;
  end
  else if ASrc is TSetTypeDef then
  begin
    ST := TSetTypeDef.Create();
    ST.BaseTypeName := TSetTypeDef(ASrc).BaseTypeName;
    Result := ST;
  end
  else if ASrc is TEnumTypeDef then
  begin
    ET := TEnumTypeDef.Create();
    for I := 0 to TEnumTypeDef(ASrc).Members.Count - 1 do
      ET.Members.AddObject(
        TEnumTypeDef(ASrc).Members.Strings[I],
        TEnumTypeDef(ASrc).Members.Objects[I]);
    Result := ET;
  end
  else if ASrc is TRecordTypeDef then
  begin
    RT := TRecordTypeDef.Create();
    RT.IsPacked := TRecordTypeDef(ASrc).IsPacked;
    for I := 0 to TRecordTypeDef(ASrc).Fields.Count - 1 do
      RT.Fields.Add(CloneFieldDecl(TFieldDecl(TRecordTypeDef(ASrc).Fields.Items[I])));
    for I := 0 to TRecordTypeDef(ASrc).Methods.Count - 1 do
      RT.Methods.Add(CloneMethodDecl(TMethodDecl(TRecordTypeDef(ASrc).Methods.Items[I])));
    Result := RT;
  end
  else if ASrc is TClassTypeDef then
  begin
    Result := CloneClassTypeDef(TClassTypeDef(ASrc));
  end
  else if ASrc is TGenericTypeDef then
  begin
    Result := CloneGenericTypeDef(TGenericTypeDef(ASrc));
  end
  else if ASrc is TGenericInterfaceDef then
  begin
    Result := CloneGenericInterfaceDef(TGenericInterfaceDef(ASrc));
  end
  else if ASrc is TInterfaceTypeDef then
  begin
    Result := CloneInterfaceTypeDef(TInterfaceTypeDef(ASrc));
  end
  else if ASrc is TProceduralTypeDef then
  begin
    Result := CloneProceduralTypeDef(TProceduralTypeDef(ASrc));
  end
  else
    raise Exception.CreateFmt(
      'CloneTypeDef: unsupported type def %s', [ASrc.ClassName]);

  Result.Line := ASrc.Line;
  Result.Col  := ASrc.Col;
end;

function CloneClassTypeDef(ASrc: TClassTypeDef): TClassTypeDef;
var
  I: Integer;
begin
  if ASrc = nil then begin Result := nil; Exit; end;
  Result := TClassTypeDef.Create();
  Result.ParentName := ASrc.ParentName;
  for I := 0 to ASrc.ImplementsNames.Count - 1 do
    Result.ImplementsNames.Add(ASrc.ImplementsNames.Strings[I]);
  for I := 0 to ASrc.ConstDecls.Count - 1 do
    Result.ConstDecls.Add(CloneConstDecl(TConstDecl(ASrc.ConstDecls.Items[I])));
  for I := 0 to ASrc.Fields.Count - 1 do
    Result.Fields.Add(CloneFieldDecl(TFieldDecl(ASrc.Fields.Items[I])));
  for I := 0 to ASrc.Methods.Count - 1 do
    Result.Methods.Add(CloneMethodDecl(TMethodDecl(ASrc.Methods.Items[I])));
  for I := 0 to ASrc.Attributes.Count - 1 do
    Result.Attributes.Add(ASrc.Attributes.Strings[I]);
  for I := 0 to ASrc.Properties.Count - 1 do
    Result.Properties.Add(ClonePropertyDecl(TPropertyDecl(ASrc.Properties.Items[I])));
end;

function CloneGenericTypeDef(ASrc: TGenericTypeDef): TGenericTypeDef;
var
  I: Integer;
begin
  if ASrc = nil then begin Result := nil; Exit; end;
  Result := TGenericTypeDef.Create();
  for I := 0 to ASrc.ParamNames.Count - 1 do
  begin
    Result.ParamNames.Add(ASrc.ParamNames.Strings[I]);
    if I < ASrc.ParamConstraints.Count then
      Result.ParamConstraints.Add(ASrc.ParamConstraints.Strings[I])
    else
      Result.ParamConstraints.Add('');
  end;
  { Replace the autoctor's blank ClassDef with a real clone. }
  Result.ClassDef.Free();
  Result.ClassDef := CloneClassTypeDef(ASrc.ClassDef);
end;

function CloneInterfaceTypeDef(ASrc: TInterfaceTypeDef): TInterfaceTypeDef;
var
  I: Integer;
begin
  if ASrc = nil then begin Result := nil; Exit; end;
  Result := TInterfaceTypeDef.Create();
  Result.ParentName := ASrc.ParentName;
  for I := 0 to ASrc.Methods.Count - 1 do
    Result.Methods.Add(CloneMethodDecl(TMethodDecl(ASrc.Methods.Items[I])));
  for I := 0 to ASrc.Properties.Count - 1 do
    Result.Properties.Add(ClonePropertyDecl(TPropertyDecl(ASrc.Properties.Items[I])));
end;

function CloneGenericInterfaceDef(ASrc: TGenericInterfaceDef): TGenericInterfaceDef;
var
  I: Integer;
begin
  if ASrc = nil then begin Result := nil; Exit; end;
  Result := TGenericInterfaceDef.Create();
  for I := 0 to ASrc.ParamNames.Count - 1 do
  begin
    Result.ParamNames.Add(ASrc.ParamNames.Strings[I]);
    if I < ASrc.ParamConstraints.Count then
      Result.ParamConstraints.Add(ASrc.ParamConstraints.Strings[I])
    else
      Result.ParamConstraints.Add('');
  end;
  Result.IntfDef.Free();
  Result.IntfDef := CloneInterfaceTypeDef(ASrc.IntfDef);
end;

function CloneProceduralTypeDef(ASrc: TProceduralTypeDef): TProceduralTypeDef;
var
  I: Integer;
begin
  if ASrc = nil then begin Result := nil; Exit; end;
  Result := TProceduralTypeDef.Create();
  Result.ReturnTypeName := ASrc.ReturnTypeName;
  Result.IsFunction     := ASrc.IsFunction;
  Result.IsMethodPtr    := ASrc.IsMethodPtr;
  for I := 0 to ASrc.Params.Count - 1 do
    Result.Params.Add(CloneMethodParam(TMethodParam(ASrc.Params.Items[I])));
end;

function CloneBlock(ABlock: TBlock): TBlock;
var
  I: Integer;
begin
  if ABlock = nil then
  begin Result := nil; Exit; end;
  Result := TBlock.Create();
  Result.Line := ABlock.Line;
  Result.Col  := ABlock.Col;
  for I := 0 to ABlock.TypeDecls.Count - 1 do
    Result.TypeDecls.Add(CloneTypeDecl(TTypeDecl(ABlock.TypeDecls.Items[I])));
  for I := 0 to ABlock.ConstDecls.Count - 1 do
    Result.ConstDecls.Add(CloneConstDecl(TConstDecl(ABlock.ConstDecls.Items[I])));
  for I := 0 to ABlock.Decls.Count - 1 do
    Result.Decls.Add(CloneVarDecl(TVarDecl(ABlock.Decls.Items[I])));
  for I := 0 to ABlock.ProcDecls.Count - 1 do
    Result.ProcDecls.Add(CloneMethodDecl(TMethodDecl(ABlock.ProcDecls.Items[I])));
  for I := 0 to ABlock.Stmts.Count - 1 do
    Result.Stmts.Add(CloneStmt(TASTStmt(ABlock.Stmts.Items[I])));
end;

end.
