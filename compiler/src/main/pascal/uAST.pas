{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

unit uAST;

{$mode objfpc}{$H+}

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

  TStringLiteral = class(TASTExpr)
  public
    Value: string;
  end;

  TNilLiteral = class(TASTExpr);  { nil keyword — type is tyNil }

  TIdentExpr = class(TASTExpr)
  public
    Name:              string;
    IsVarParam:        Boolean;  { set by uSemantic — True if this ident is a var parameter }
    IsConstant:        Boolean;  { set by uSemantic — True if this ident is a skConstant symbol }
    ConstValue:        Int64;    { valid when IsConstant = True }
    IsNoArgFuncCall:   Boolean;  { set by uSemantic — bare ident that resolves to a 0-arg function }
  end;

  TFieldAccessExpr = class(TASTExpr)
  public
    RecordName:        string;         { used when Base = nil (leaf access) }
    FieldName:         string;
    Base:              TASTExpr;       { owned — when non-nil, chained access (e.g. A.B.C) }
    FieldInfo:         TFieldInfo;    { set by uSemantic — nil for constructor calls }
    IsConstructorCall: Boolean;       { set by uSemantic — TypeName.Create }
    IsClassAccess:     Boolean;       { set by uSemantic — pointer deref needed }
    PropRead:          TPropertyInfo; { non-nil if this is a method-backed property read }
    PropOwnerType:     string;        { class type name for method-backed property calls }
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

  TBinaryOp = (boAdd, boSub, boMul, boDiv, boEQ, boNE, boLT, boGT, boLE, boGE,
               boAnd, boOr);

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
    ResolvedLhsType: TTypeDesc;  { set by uSemantic — type of the target variable }
    IsWeakLhs:       Boolean;    { set by uSemantic — True if the LHS symbol
                                   was declared [Weak]; codegen emits a
                                   _WeakAssign in place of the strong
                                   addref/release pattern. }
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

  TForStmt = class(TASTStmt)
  public
    VarName:   string;
    StartExpr: TASTExpr;  { owned }
    EndExpr:   TASTExpr;  { owned }
    IsDownTo:  Boolean;
    Body:      TASTStmt;  { owned }
    destructor Destroy; override;
  end;

  TTryFinallyStmt = class(TASTStmt)
  public
    TryBody:     TCompoundStmt;  { owned }
    FinallyBody: TCompoundStmt;  { owned }
    destructor Destroy; override;
  end;

  TTryExceptStmt = class(TASTStmt)
  public
    TryBody:    TCompoundStmt;  { owned }
    ExceptBody: TCompoundStmt;  { owned }
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
    Selector: TASTExpr;    { owned — must be ordinal type }
    Branches: TObjectList; { owned list of TCaseBranch }
    ElseStmt: TASTStmt;    { owned; nil if no else clause }
    constructor Create;
    destructor Destroy; override;
  end;

  TFieldAssignment = class(TASTStmt)
  public
    RecordName:    string;
    FieldName:     string;
    Expr:          TASTExpr;   { owned }
    FieldInfo:     TFieldInfo; { set by uSemantic — carries offset + type }
    IsClassAccess: Boolean;    { set by uSemantic — pointer deref needed }
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
    constructor Create;
    destructor Destroy; override;
  end;

  TFuncCallExpr = class(TASTExpr)
  public
    Name:         string;
    Args:         TObjectList;  { owned TASTExpr items }
    ResolvedDecl: TObject;      { TMethodDecl — not owned; set by uSemantic }
    constructor Create;
    destructor Destroy; override;
  end;

  { Pointer dereference expression: 'PtrExpr^' — result type is BaseType of pointer }
  TDerefExpr = class(TASTExpr)
  public
    Expr: TASTExpr;  { owned — the pointer expression }
    destructor Destroy; override;
  end;

  TMethodCallStmt = class(TASTStmt)
  public
    ObjectName: string;
    Name:       string;   { method name }
    Args:       TObjectList;   { owned TASTExpr items }
    { Set by uSemantic: }
    ResolvedClassType: TTypeDesc;   { not owned }
    ResolvedMethod:    TObject;     { TMethodDecl — not owned; avoids forward ref }
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
    constructor Create;
    destructor Destroy; override;
  end;

  { ------------------------------------------------------------------ }
  {  Type section                                                       }
  { ------------------------------------------------------------------ }

  { Abstract base for type definitions. }
  TASTTypeDef = class(TASTNode);

  { Enum type definition: type TDir = (dNorth, dSouth, dEast, dWest); }
  TEnumTypeDef = class(TASTTypeDef)
  public
    Members: TStringList;  { owned — ordered member names }
    constructor Create;
    destructor Destroy; override;
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

  TBlock = class;  { forward — defined below after all declarations }

  TMethodParam = class(TASTNode)
  public
    ParamName:    string;
    TypeName:     string;
    IsVarParam:   Boolean;    { True = passed by reference (var keyword) }
    ResolvedType: TTypeDesc;  { set by uSemantic }
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
    ResolvedClassType: TTypeDesc;   { not owned; set by uSemantic }
    ResolvedMethod:    TObject;     { TMethodDecl — not owned }
    constructor Create;
    destructor Destroy; override;
  end;

  { One property declaration inside a class body. }
  TPropertyDecl = class(TASTNode)
  public
    Name:      string;  { property name }
    TypeName:  string;  { declared type }
    ReadName:  string;  { backing field or getter method; '' = no read accessor }
    WriteName: string;  { backing field or setter method; '' = read-only }
  end;

  TClassTypeDef = class(TASTTypeDef)
  public
    ParentName:      string;
    ImplementsNames: TStringList;  { owned — names of implemented interfaces }
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

  { Constant declaration: const Name = Value; — integer or string literal }
  TConstDecl = class(TASTNode)
  public
    Name:    string;
    IntVal:  Int64;    { used when IsString = False }
    StrVal:  string;   { used when IsString = True }
    IsString: Boolean;
  end;

  { ------------------------------------------------------------------ }
  {  Block and Program                                                  }
  { ------------------------------------------------------------------ }

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
    Name:      string;
    IntfBlock: TBlock;  { owned — forward decls + type decls }
    ImplBlock: TBlock;  { owned — full implementations }
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
    boEQ:  Result := '=';
    boNE:  Result := '<>';
    boLT:  Result := '<';
    boGT:  Result := '>';
    boLE:  Result := '<=';
    boGE:  Result := '>=';
    boAnd: Result := 'and';
    boOr:  Result := 'or';
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

{ TForStmt }

destructor TForStmt.Destroy;
begin
  StartExpr.Free;
  EndExpr.Free;
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

{ TTryExceptStmt }

destructor TTryExceptStmt.Destroy;
begin
  TryBody.Free;
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
  inherited Destroy;
end;

{ TClassTypeDef }

constructor TClassTypeDef.Create;
begin
  inherited Create;
  ImplementsNames := TStringList.Create;
  Fields          := TObjectList.Create(True);
  Methods         := TObjectList.Create(True);
  Properties      := TObjectList.Create(True);
end;

destructor TClassTypeDef.Destroy;
begin
  Properties.Free;
  Methods.Free;
  Fields.Free;
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
  IntfBlock := TBlock.Create;
  ImplBlock := TBlock.Create;
end;

destructor TUnit.Destroy;
begin
  IntfBlock.Free;
  ImplBlock.Free;
  inherited Destroy;
end;

end.
