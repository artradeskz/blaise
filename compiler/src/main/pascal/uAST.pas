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
    ResolvedType: TTypeDesc;  { set by uSemantic; nil until analysed }
  end;

  TIntLiteral = class(TASTExpr)
  public
    Value: Int64;
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
    constructor Create;
    destructor Destroy; override;
  end;

  TNilLiteral = class(TASTExpr);  { nil keyword — type is tyNil }

  TIdentExpr = class(TASTExpr)
  public
    Name:              string;
    IsVarParam:        Boolean;  { set by uSemantic — True if this ident is a var parameter }
    IsConstant:        Boolean;  { set by uSemantic — True if this ident is a skConstant symbol }
    ConstValue:        Int64;    { valid when IsConstant = True; integer/bool/enum value }
    ConstString:       string;   { valid when IsConstant = True and type is tyString }
    IsNoArgFuncCall:   Boolean;  { set by uSemantic — bare ident that resolves to a 0-arg function }
    NoArgFuncDecl:     TObject;  { TMethodDecl — not owned; valid when IsNoArgFuncCall and user-defined }
    IsGlobal:          Boolean;  { set by uSemantic — this ident is a program-level global var }
    IsImplicitSelf:    Boolean;  { set by uSemantic — bare field name implicitly referencing Self }
    ImplicitFieldInfo: TObject;  { TFieldInfo — not owned; valid when IsImplicitSelf }
    IsImplicitSelfMethod: Boolean; { set by uSemantic — bare zero-arg method call on Self }
    ImplicitMethodDecl:   TObject;  { TMethodDecl — not owned; set when IsImplicitSelfMethod }
    IsMetaclassRef:    Boolean;     { set by uSemantic — bare class type identifier used as
                                      metaclass value (typeinfo ptr); codegen emits
                                      $typeinfo_<Name> instead of loading a variable. }
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
    IsConstructorCall: Boolean;       { set by uSemantic — TypeName.Create }
    IsClassAccess:     Boolean;       { set by uSemantic — pointer deref needed }
    PropRead:          TPropertyInfo; { non-nil if this is a method-backed property read }
    PropOwnerType:     string;        { class type name for method-backed property calls }
    IsImplicitSelf:    Boolean;       { set by uSemantic — RecordName is a field of Self }
    ImplicitBaseInfo:  TFieldInfo;    { non-owned — the field of Self holding the record/class }
    IsMethodCall:        Boolean;     { set by uSemantic — FieldName is a zero-arg method }
    ResolvedMethod:      TObject;     { TMethodDecl — not owned; set when IsMethodCall }
    IsInterfaceCall:     Boolean;     { set by uSemantic — zero-arg method call through interface itab }
    ResolvedClassType:   TTypeDesc;  { not owned; set when IsInterfaceCall — the interface descriptor }
    IsGlobal:            Boolean;     { set by uSemantic — RecordName is a program-level global }
    IsClassNameAccess:   Boolean;     { set by uSemantic — .ClassName built-in on a class instance }
    IsClassTypeAccess:   Boolean;     { set by uSemantic — .ClassType built-in: returns metaclass (typeinfo ptr) }
    IsBuiltinToString:   Boolean;     { set by uSemantic — .ToString built-in: virtual dispatch via vtable slot 1 }
    IsVarParam:          Boolean;     { set by uSemantic — RecordName is a var parameter (record by-ref) }
    PropIndexExpr: TASTExpr;  { owned — non-nil = indexed property read (e.g. List.Items[i]) }
    IsCharAccess:  Boolean;   { set by uSemantic — PropIndexExpr indexes a string field: S.Field[N] }
    destructor Destroy; override;
  end;

  TIsExpr = class(TASTExpr)
  public
    Obj:                TASTExpr;   { owned — left-hand side; must be class instance }
    TypeName:           string;     { right-hand side type name; resolved by uSemantic }
    ResolvedTargetType: TTypeDesc;  { set by uSemantic — class or interface descriptor }
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
    ResolvedIntfType:   TTypeDesc; { set by uSemantic — must be tyInterface }
    OutVarIsGlobal:     Boolean;   { set by uSemantic }
    destructor Destroy; override;
  end;

  TBinaryOp = (boAdd, boSub, boMul, boDiv, boMod, boEQ, boNE, boLT, boGT, boLE, boGE,
               boAnd, boOr, boXor, boIn, boShl, boShr);

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
    ResolvedLhsType: TTypeDesc;  { set by uSemantic — type of the target variable }
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
    ResolvedVarType:      TTypeDesc;  { element type }
    { Class-enumerator path (IsArrayIter = False) }
    IsArrayIter:          Boolean;    { True when collection is a static array }
    EnumVarName:          string;     { synthetic enumerator slot, e.g. __forin_0 }
    ResolvedEnumTypeName: string;     { enumerator class type name }
    GetEnumDecl:          TObject;    { TMethodDecl — not owned }
    MoveNextDecl:         TObject;    { TMethodDecl — not owned }
    CurrentDecl:          TObject;    { TMethodDecl getter — not owned }
    { Static-array iteration path (IsArrayIter = True) }
    IdxVarName:           string;     { synthetic index slot — shared with string path }
    ArrayLow:             Integer;    { compile-time lower bound }
    ArrayHigh:            Integer;    { compile-time upper bound }
    { String byte-iteration path (IsStringIter = True) }
    IsStringIter:         Boolean;
    { Set iteration path (IsSetIter = True) }
    IsSetIter:            Boolean;
    SetBitCount:          Integer;   { number of bits in the set (= enum member count) }
    SetMaskVarName:       string;    { synthetic slot holding the evaluated set mask }
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

  { 'exit' statement — returns from the current procedure/function. }
  TExitStmt = class(TASTStmt);

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
    ImplicitBaseInfo:  TFieldInfo; { non-owned — the field of Self that holds the record/class }
    IsGlobal:          Boolean; { set by uSemantic — RecordName is a program-level global }
    IsVarParam:        Boolean; { set by uSemantic — RecordName is a var parameter (record by-ref) }
    PropIndexExpr: TASTExpr;  { owned — non-nil = indexed property write via setter }
    PropWriteInfo: TPropertyInfo;  { non-owned — set by semantic when PropIndexExpr is set }
    PropOwnerType: string;  { owner class name for setter call; valid when PropIndexExpr set }
    destructor Destroy; override;
  end;

  { Static-array element write: 'ArrayName[IndexExpr] := ValueExpr' }
  TStaticSubscriptAssign = class(TASTStmt)
  public
    ArrayName: string;
    IndexExpr: TASTExpr;  { owned }
    ValueExpr: TASTExpr;  { owned }
    IsGlobal: Boolean;    { set by uSemantic }
    ResolvedArrayType: TTypeDesc;  { set by uSemantic; not owned }
    destructor Destroy; override;
  end;

  { Write a value through a pointer: 'PtrExpr^ := ValueExpr' }
  TPointerWriteStmt = class(TASTStmt)
  public
    PtrExpr:  TASTExpr;  { owned — pointer expression }
    ValExpr:  TASTExpr;  { owned — value to store }
    BaseTy:   TTypeDesc; { non-owned — element type; set by uSemantic }
    destructor Destroy; override;
  end;

  TProcCall = class(TASTStmt)
  public
    Name:         string;
    Args:         TObjectList;  { owned TASTExpr items }
    ResolvedDecl: TObject;      { TMethodDecl — not owned; set by uSemantic for user-defined procs }
    IsImplicitSelfMethod: Boolean; { set by uSemantic — call is on Self }
    IsIndirectCall:       Boolean; { set by uSemantic — Name is a procedural-typed variable }
    IndirectCallIsGlobal: Boolean; { set by uSemantic — when IsIndirectCall, variable is global }
    ResolvedProcType:     TObject; { TProceduralTypeDesc — not owned; valid when IsIndirectCall }
    constructor Create;
    destructor Destroy; override;
  end;

  TFuncCallExpr = class(TASTExpr)
  public
    Name:         string;
    Args:         TObjectList;  { owned TASTExpr items }
    ResolvedDecl: TObject;      { TMethodDecl — not owned; set by uSemantic }
    IsImplicitSelfMethod: Boolean; { set by uSemantic — call is on Self }
    IsIndirectCall:       Boolean; { set by uSemantic — Name resolves to a
                                     variable of procedural type; codegen
                                     loads the function pointer and calls
                                     through it. ResolvedProcType holds
                                     the signature. }
    IndirectCallIsGlobal: Boolean; { set by uSemantic — when IsIndirectCall,
                                     True if the holding variable is a
                                     program-level global. }
    ResolvedProcType: TObject;     { TProceduralTypeDesc — not owned;
                                     valid when IsIndirectCall }
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
    destructor Destroy; override;
  end;

  TMethodCallStmt = class(TASTStmt)
  public
    ObjectName: string;
    Name:       string;   { method name }
    Args:       TObjectList;   { owned TASTExpr items }
    ObjExpr:    TASTExpr;  { owned — when non-nil, receiver is this expression }
    { Set by uSemantic: }
    ResolvedClassType:  TTypeDesc;   { not owned }
    ResolvedMethod:     TObject;     { TMethodDecl — not owned; avoids forward ref }
    IsImplicitSelf:     Boolean;     { ObjectName is a field of Self }
    ImplicitBaseInfo:   TFieldInfo;  { not owned — the field of Self }
    IsGlobal:           Boolean;     { set by uSemantic — ObjectName is a program-level global }
    IsVarParam:         Boolean;     { set by uSemantic — ObjectName is a var/out parameter }
    IsBuiltinToString:  Boolean;     { set by uSemantic — built-in TObject.ToString virtual dispatch }
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
    ResolvedParentType: TObject;       { TRecordTypeDesc — not owned }
    ResolvedMethod:     TObject;       { TMethodDecl — not owned }
    constructor Create;
    destructor Destroy; override;
  end;

  { ------------------------------------------------------------------ }
  {  Declarations                                                       }
  { ------------------------------------------------------------------ }

  TVarDecl = class(TASTNode)
  public
    Names:        TStringList;  { owned — one or more names: x, y: Integer }
    TypeName:     string;
    ResolvedType: TTypeDesc;    { set by uSemantic; nil until analysed }
    Attributes:   TStringList;  { owned — raw attribute names as written in
                                  source, e.g. 'Weak', 'SomeOther'; the
                                  Attribute suffix (if present) is preserved
                                  verbatim — normalisation happens in
                                  semantic analysis. }
    IsWeak:       Boolean;      { set by uSemantic when [Weak] is resolved
                                  on this declaration.  Codegen keys off
                                  this instead of walking Attributes. }
    IsGlobal:     Boolean;      { set by uSemantic when this is a program-level global variable }
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
    ResolvedType: TTypeDesc;    { set by uSemantic }
    Attributes:   TStringList;  { owned — see TVarDecl.Attributes. }
    IsWeak:       Boolean;      { set by uSemantic when [Weak] is resolved. }
    constructor Create;
    destructor Destroy; override;
  end;

  TRecordTypeDef = class(TASTTypeDef)
  public
    Fields: TObjectList;  { owned TFieldDecl }
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
    IsVarParam:   Boolean;    { True = passed by reference (var keyword) }
    IsConstParam: Boolean;    { True = 'const' keyword present }
    IsOpenArray:  Boolean;    { True = 'array of T'; TypeName is the element type }
    ResolvedType: TTypeDesc;  { set by uSemantic — TOpenArrayTypeDesc when IsOpenArray }
    DefaultValue: TASTExpr;   { owned — non-nil when the param has a default value
                                ('= expr' after the type); restricted to literal forms
                                (int/float/string/nil) and named-constant idents. }
    destructor Destroy; override;
  end;

  TMethodDecl = class(TASTNode)
  public
    Name:               string;      { method name }
    OwnerTypeName:      string;      { set by uSemantic — class that defines this method }
    Params:             TObjectList; { owned TMethodParam }
    ReturnTypeName:     string;      { empty = procedure }
    ResolvedReturnType: TTypeDesc;   { set by uSemantic; nil = procedure }
    Body:               TBlock;      { owned unless OwnBody = False }
    OwnBody:            Boolean;     { False for cloned generic method stubs that share the body }
    IsVirtual:          Boolean;     { declared with 'virtual' directive }
    IsOverride:         Boolean;     { declared with 'override' directive }
    IsOverload:         Boolean;     { declared with 'overload' directive }
    IsPublished:        Boolean;     { declared inside a 'published' visibility
                                       section of a class.  Used by codegen to
                                       emit an entry in the published-method
                                       table, which TObject.MethodAddress
                                       walks at runtime. }
    ResolvedQbeName:    string;      { set by uSemantic — mangled QBE symbol name;
                                       empty string means use Name verbatim }
    IsExternal:         Boolean;     { declared with 'external' directive — no body }
    ExternalName:       string;      { C symbol name from 'external name ''c_foo'''; empty = use Pascal name }
    VTableSlot:         Integer;     { -1 = static; >=0 = vtable index (set by uSemantic) }
    TypeParams:         TStringList; { non-nil = generic function template; owns param names }
    TypeParamConstraints: TStringList; { parallel to TypeParams; '' = unconstrained,
                                         'class', 'record', or a concrete type name }
    OwnerTypeParams:    TStringList; { non-nil = generic owner: 'T' in TList<T>.Add }
    constructor Create;
    destructor Destroy; override;
  end;

  TMethodCallExpr = class(TASTExpr)
  public
    ObjectName:        string;
    Name:              string;     { method name }
    Args:              TObjectList; { owned TASTExpr }
    ObjExpr:           TASTExpr;   { owned — receiver expression when ObjectName = '' }
    ResolvedClassType:  TTypeDesc;   { not owned; set by uSemantic }
    ResolvedMethod:     TObject;     { TMethodDecl — not owned }
    IsConstructorCall:  Boolean;    { set by uSemantic — TypeName.Create(args) }
    IsGlobal:           Boolean;    { set by uSemantic — ObjectName is a program-level global }
    IsVarParam:         Boolean;    { set by uSemantic — ObjectName is a var/out parameter }
    IsBuiltinToString:    Boolean;  { set by uSemantic — built-in TObject.ToString virtual dispatch }
    IsBuiltinInheritsFrom: Boolean; { set by uSemantic — SomeClass.InheritsFrom(OtherClass) }
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
  end;

  TClassTypeDef = class(TASTTypeDef)
  public
    ParentName:      string;
    ImplementsNames: TStringList;  { owned — names of implemented interfaces }
    ConstDecls:      TObjectList;  { owned TConstDecl — class-level constants }
    Fields:          TObjectList;  { owned TFieldDecl }
    Methods:         TObjectList;  { owned TMethodDecl }
    Properties:      TObjectList;  { owned TPropertyDecl }
    constructor Create;
    destructor Destroy; override;
  end;

  { Generic type template: type TBox<T> = class ... end }
  TGenericTypeDef = class(TASTTypeDef)
  public
    ParamNames:       TStringList;   { owned — type parameter names, e.g. ['T'] or ['K','V'] }
    ParamConstraints: TStringList;   { owned — parallel to ParamNames; '' = unconstrained }
    ClassDef:         TClassTypeDef; { owned — template class body with unresolved param types }
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

  { One concrete instantiation produced by monomorphization — stored on TProgram.
    Codegen iterates this list to emit typeinfo, vtables, and method bodies. }
  TGenericInstance = class
  public
    TypeName: string;        { raw e.g. 'TBox<Integer>' }
    ClassDef: TClassTypeDef; { owned — cloned class body with substituted type names }
    TypeDesc: TTypeDesc;     { non-owned — points to TRecordTypeDesc in SymbolTable }
    constructor Create;
    destructor Destroy; override;
  end;

  TInterfaceTypeDef = class(TASTTypeDef)
  public
    ParentName: string;
    Methods:    TObjectList;  { owned TMethodDecl — forward signatures only }
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

  { One concrete instantiation of a generic interface — stored on TProgram.
    Codegen iterates this list to emit typeinfo data. }
  TGenericInterfaceInstance = class
  public
    InstName: string;          { mangled name e.g. 'IEqualityComparer_Integer' }
    IntfDef:  TInterfaceTypeDef; { owned — cloned with substituted type names }
    TypeDesc: TTypeDesc;       { non-owned — points to TInterfaceTypeDesc in SymbolTable }
    constructor Create;
    destructor Destroy; override;
  end;

  TTypeDecl = class(TASTNode)
  public
    Name: string;
    Def:  TASTTypeDef;  { owned }
    destructor Destroy; override;
  end;

  { Constant declaration: const Name = Value; }
  TConstDecl = class(TASTNode)
  public
    Name:       string;
    IntVal:     Int64;    { used when kind = integer }
    StrVal:     string;   { used when IsString = True or IsFloat = True (raw text) }
    IsString:   Boolean;
    IsFloat:    Boolean;  { set when the rhs is a float literal }
    ConstParts: TStringList; { non-nil when const expr has ident refs;
                               Objects[i] = nil → string literal,
                               Objects[i] <> nil → ident reference }
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
    GenericInstances:     TObjectList;    { owned TGenericInstance — populated by uSemantic }
    GenericFuncInstances: TObjectList;    { owned TGenericFuncInstance — populated by uSemantic }
    GenericIntfInstances: TObjectList;    { owned TGenericInterfaceInstance — populated by uSemantic }
    constructor Create;
    destructor Destroy; override;
  end;

  TUnit = class(TASTNode)
  public
    Name:        string;
    SourceFile:  string;       { absolute path of the .pas file this unit was loaded from }
    UsedUnits:   TStringList; { owned — unit names from the interface uses clause }
    IntfBlock:   TBlock;      { owned — forward decls + type decls }
    ImplBlock:   TBlock;      { owned — full implementations }
    InitStmts:   TObjectList; { owned — statements in the initialization section (may be nil) }
    FinalStmts:  TObjectList; { owned — statements in the finalization section (may be nil) }
    SymbolTable: TSymbolTable; { owned after standalone semantic analysis;
                                 nil when the unit is analysed as part of a
                                 program (program owns the table). }
    constructor Create;
    destructor Destroy; override;
  end;

function BinaryOpName(AOp: TBinaryOp): string;
function IsComparisonOp(AOp: TBinaryOp): Boolean;

implementation

function BinaryOpName(AOp: TBinaryOp): string;
begin
  case AOp of
    boAdd: Result := '+';
    boSub: Result := '-';
    boMul: Result := '*';
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
  Condition.Free;
  ThenStmt.Free;
  ElseStmt.Free;
  inherited Destroy;
end;

{ TCompoundStmt }

constructor TCompoundStmt.Create;
begin
  inherited Create;
  Stmts := TObjectList.Create(True);
end;

destructor TCompoundStmt.Destroy;
begin
  Stmts.Free;
  inherited Destroy;
end;

{ TWhileStmt }

destructor TWhileStmt.Destroy;
begin
  Condition.Free;
  Body.Free;
  inherited Destroy;
end;

{ TRepeatStmt }

destructor TRepeatStmt.Destroy;
begin
  Body.Free;
  Condition.Free;
  inherited Destroy;
end;

{ TForStmt }

destructor TForStmt.Destroy;
begin
  StartExpr.Free;
  EndExpr.Free;
  Body.Free;
  inherited Destroy;
end;

{ TForInStmt }

destructor TForInStmt.Destroy;
begin
  CollExpr.Free;
  Body.Free;
  inherited Destroy;
end;

{ TTryFinallyStmt }

destructor TTryFinallyStmt.Destroy;
begin
  TryBody.Free;
  FinallyBody.Free;
  inherited Destroy;
end;

{ TExceptHandlerClause }

destructor TExceptHandlerClause.Destroy;
begin
  Body.Free;
  inherited Destroy;
end;

{ TTryExceptStmt }

constructor TTryExceptStmt.Create;
begin
  inherited Create;
  Handlers := TObjectList.Create(True);
end;

destructor TTryExceptStmt.Destroy;
begin
  TryBody.Free;
  Handlers.Free;
  ElseBody.Free;
  ExceptBody.Free;
  inherited Destroy;
end;

{ TRaiseStmt }

destructor TRaiseStmt.Destroy;
begin
  Expr.Free;
  inherited Destroy;
end;

{ TFieldAccessExpr }

destructor TFieldAccessExpr.Destroy;
begin
  Base.Free;
  PropIndexExpr.Free;
  inherited Destroy;
end;

{ TIsExpr }

destructor TIsExpr.Destroy;
begin
  Obj.Free;
  inherited Destroy;
end;

{ TAsExpr }

destructor TAsExpr.Destroy;
begin
  Obj.Free;
  inherited Destroy;
end;

{ TSupportsExpr }

destructor TSupportsExpr.Destroy;
begin
  Obj.Free;
  inherited Destroy;
end;

{ TBinaryExpr }

destructor TBinaryExpr.Destroy;
begin
  Left.Free;
  Right.Free;
  inherited Destroy;
end;

{ TNotExpr }

destructor TNotExpr.Destroy;
begin
  Expr.Free;
  inherited Destroy;
end;

{ TAssignment }

destructor TAssignment.Destroy;
begin
  Expr.Free;
  inherited Destroy;
end;

{ TFieldAssignment }

destructor TFieldAssignment.Destroy;
begin
  Expr.Free;
  ObjExpr.Free;
  PropIndexExpr.Free;
  inherited Destroy;
end;

{ TStaticSubscriptAssign }

destructor TStaticSubscriptAssign.Destroy;
begin
  IndexExpr.Free;
  ValueExpr.Free;
  inherited Destroy;
end;

{ TPointerWriteStmt }

destructor TPointerWriteStmt.Destroy;
begin
  PtrExpr.Free;
  ValExpr.Free;
  inherited Destroy;
end;

{ TDerefExpr }

destructor TDerefExpr.Destroy;
begin
  Expr.Free;
  inherited Destroy;
end;

destructor TAddrOfExpr.Destroy;
begin
  Expr.Free;
  inherited Destroy;
end;

destructor TStringSubscriptExpr.Destroy;
begin
  StrExpr.Free;
  IndexExpr.Free;
  inherited Destroy;
end;

{ TArrayLiteralExpr }

constructor TArrayLiteralExpr.Create;
begin
  inherited Create;
  Elements := TObjectList.Create(True);
end;

destructor TArrayLiteralExpr.Destroy;
begin
  Elements.Free;
  inherited Destroy;
end;

{ TProcCall }

constructor TProcCall.Create;
begin
  inherited Create;
  Args := TObjectList.Create(True);
end;

destructor TProcCall.Destroy;
begin
  Args.Free;
  inherited Destroy;
end;

{ TFuncCallExpr }

constructor TFuncCallExpr.Create;
begin
  inherited Create;
  Args := TObjectList.Create(True);
end;

destructor TFuncCallExpr.Destroy;
begin
  Args.Free;
  inherited Destroy;
end;

{ TMethodCallStmt }

constructor TMethodCallStmt.Create;
begin
  inherited Create;
  Args := TObjectList.Create(True);
end;

destructor TMethodCallStmt.Destroy;
begin
  Args.Free;
  ObjExpr.Free;
  inherited Destroy;
end;

{ TInheritedCallStmt }

constructor TInheritedCallStmt.Create;
begin
  inherited Create;
  Args := TObjectList.Create(True);
end;

destructor TInheritedCallStmt.Destroy;
begin
  Args.Free;
  inherited Destroy;
end;

{ TMethodParam }

destructor TMethodParam.Destroy;
begin
  DefaultValue.Free;
  inherited Destroy;
end;

{ TVarDecl }

constructor TVarDecl.Create;
begin
  inherited Create;
  Names      := TStringList.Create;
  Attributes := TStringList.Create;
  IsWeak     := False;
end;

destructor TVarDecl.Destroy;
begin
  Attributes.Free;
  Names.Free;
  inherited Destroy;
end;

{ TFieldDecl }

constructor TFieldDecl.Create;
begin
  inherited Create;
  Names      := TStringList.Create;
  Attributes := TStringList.Create;
  IsWeak     := False;
end;

destructor TFieldDecl.Destroy;
begin
  Attributes.Free;
  Names.Free;
  inherited Destroy;
end;

{ TRecordTypeDef }

constructor TRecordTypeDef.Create;
begin
  inherited Create;
  Fields := TObjectList.Create(True);
end;

destructor TRecordTypeDef.Destroy;
begin
  Fields.Free;
  inherited Destroy;
end;

{ TProceduralTypeDef }

constructor TProceduralTypeDef.Create;
begin
  inherited Create;
  Params     := TObjectList.Create(True);
  IsFunction := False;
end;

destructor TProceduralTypeDef.Destroy;
begin
  Params.Free;
  inherited Destroy;
end;

{ TMethodDecl }

constructor TMethodDecl.Create;
begin
  inherited Create;
  Params     := TObjectList.Create(True);
  VTableSlot := -1;
  OwnBody    := True;
end;

destructor TMethodDecl.Destroy;
begin
  Params.Free;
  TypeParams.Free;
  TypeParamConstraints.Free;
  OwnerTypeParams.Free;
  if OwnBody then Body.Free;
  inherited Destroy;
end;

{ TMethodCallExpr }

constructor TMethodCallExpr.Create;
begin
  inherited Create;
  Args := TObjectList.Create(True);
end;

destructor TMethodCallExpr.Destroy;
begin
  Args.Free;
  ObjExpr.Free;
  inherited Destroy;
end;

{ TClassTypeDef }

constructor TClassTypeDef.Create;
begin
  inherited Create;
  ImplementsNames := TStringList.Create;
  ConstDecls      := TObjectList.Create(True);
  Fields          := TObjectList.Create(True);
  Methods         := TObjectList.Create(True);
  Properties      := TObjectList.Create(True);
end;

destructor TClassTypeDef.Destroy;
begin
  Properties.Free;
  Methods.Free;
  Fields.Free;
  ConstDecls.Free;
  ImplementsNames.Free;
  inherited Destroy;
end;

{ TInterfaceTypeDef }

constructor TInterfaceTypeDef.Create;
begin
  inherited Create;
  Methods := TObjectList.Create(True);
end;

destructor TInterfaceTypeDef.Destroy;
begin
  Methods.Free;
  inherited Destroy;
end;

{ TGenericTypeDef }

constructor TGenericTypeDef.Create;
begin
  inherited Create;
  ParamNames       := TStringList.Create;
  ParamConstraints := TStringList.Create;
  ClassDef         := TClassTypeDef.Create;
end;

destructor TGenericTypeDef.Destroy;
begin
  ClassDef.Free;
  ParamConstraints.Free;
  ParamNames.Free;
  inherited Destroy;
end;

{ TGenericInstance }

{ TGenericFuncInstance }

constructor TGenericFuncInstance.Create;
begin
  inherited Create;
end;

destructor TGenericFuncInstance.Destroy;
begin
  MethodDecl.Free;
  inherited Destroy;
end;

{ TGenericInterfaceDef }

constructor TGenericInterfaceDef.Create;
begin
  inherited Create;
  ParamNames       := TStringList.Create;
  ParamConstraints := TStringList.Create;
  IntfDef          := TInterfaceTypeDef.Create;
end;

destructor TGenericInterfaceDef.Destroy;
begin
  IntfDef.Free;
  ParamConstraints.Free;
  ParamNames.Free;
  inherited Destroy;
end;

{ TGenericInterfaceInstance }

constructor TGenericInterfaceInstance.Create;
begin
  inherited Create;
  IntfDef := TInterfaceTypeDef.Create;
end;

destructor TGenericInterfaceInstance.Destroy;
begin
  IntfDef.Free;
  inherited Destroy;
end;

{ TGenericInstance }

constructor TGenericInstance.Create;
begin
  inherited Create;
  ClassDef := TClassTypeDef.Create;
end;

destructor TGenericInstance.Destroy;
begin
  ClassDef.Free;
  inherited Destroy;
end;

{ TTypeDecl }

destructor TTypeDecl.Destroy;
begin
  Def.Free;
  inherited Destroy;
end;

{ TBlock }

constructor TBlock.Create;
begin
  inherited Create;
  TypeDecls  := TObjectList.Create(True);
  ConstDecls := TObjectList.Create(True);
  Decls      := TObjectList.Create(True);
  ProcDecls  := TObjectList.Create(True);
  Stmts      := TObjectList.Create(True);
end;

destructor TBlock.Destroy;
begin
  TypeDecls.Free;
  ConstDecls.Free;
  Decls.Free;
  ProcDecls.Free;
  Stmts.Free;
  inherited Destroy;
end;

{ TEnumTypeDef }

constructor TEnumTypeDef.Create;
begin
  inherited Create;
  Members := TStringList.Create;
end;

destructor TEnumTypeDef.Destroy;
begin
  Members.Free;
  inherited Destroy;
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
  inherited Create;
  Values := TObjectList.Create(True);
end;

destructor TCaseBranch.Destroy;
begin
  Stmt.Free;
  Values.Free;
  inherited Destroy;
end;

{ TCaseStmt }

constructor TCaseStmt.Create;
begin
  inherited Create;
  Branches := TObjectList.Create(True);
end;

destructor TCaseStmt.Destroy;
begin
  ElseStmt.Free;
  Branches.Free;
  Selector.Free;
  inherited Destroy;
end;

{ TProgram }

constructor TProgram.Create;
begin
  inherited Create;
  UsedUnits            := TStringList.Create;
  GenericInstances     := TObjectList.Create(True);
  GenericFuncInstances := TObjectList.Create(True);
  GenericIntfInstances := TObjectList.Create(True);
end;

destructor TConstDecl.Destroy;
begin
  ConstParts.Free;
  inherited Destroy;
end;

destructor TProgram.Destroy;
begin
  GenericIntfInstances.Free;
  GenericFuncInstances.Free;
  GenericInstances.Free;
  SymbolTable.Free;
  UsedUnits.Free;
  Block.Free;
  inherited Destroy;
end;

{ TUnit }

constructor TUnit.Create;
begin
  inherited Create;
  UsedUnits  := TStringList.Create;
  IntfBlock  := TBlock.Create;
  ImplBlock  := TBlock.Create;
  InitStmts  := nil;
  FinalStmts := nil;
end;

destructor TUnit.Destroy;
begin
  IntfBlock.Free;
  ImplBlock.Free;
  InitStmts.Free;
  FinalStmts.Free;
  UsedUnits.Free;
  { Transferred from TSemanticAnalyser when the unit is analysed standalone;
    nil when the unit is analysed as a dependency of a program (program owns
    the shared symbol table in that case). }
  SymbolTable.Free;
  inherited Destroy;
end;

end.
