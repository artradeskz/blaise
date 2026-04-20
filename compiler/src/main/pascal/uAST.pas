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

  TIdentExpr = class(TASTExpr)
  public
    Name: string;
  end;

  TFieldAccessExpr = class(TASTExpr)
  public
    RecordName:        string;
    FieldName:         string;
    FieldInfo:         TFieldInfo;  { set by uSemantic — nil for constructor calls }
    IsConstructorCall: Boolean;     { set by uSemantic — TypeName.Create }
    IsClassAccess:     Boolean;     { set by uSemantic — pointer deref needed }
  end;

  TBinaryOp = (boAdd, boSub, boMul, boDiv);

  TBinaryExpr = class(TASTExpr)
  public
    Op:    TBinaryOp;
    Left:  TASTExpr;  { owned }
    Right: TASTExpr;  { owned }
    destructor Destroy; override;
  end;

  { ------------------------------------------------------------------ }
  {  Statements                                                         }
  { ------------------------------------------------------------------ }

  TASTStmt = class(TASTNode);

  TAssignment = class(TASTStmt)
  public
    Name: string;
    Expr: TASTExpr;  { owned }
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

  TProcCall = class(TASTStmt)
  public
    Name: string;
    Args: TObjectList;  { owned TASTExpr items }
    constructor Create;
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

  { ------------------------------------------------------------------ }
  {  Declarations                                                       }
  { ------------------------------------------------------------------ }

  TVarDecl = class(TASTNode)
  public
    Names:        TStringList;  { owned — one or more names: x, y: Integer }
    TypeName:     string;
    ResolvedType: TTypeDesc;    { set by uSemantic; nil until analysed }
    constructor Create;
    destructor Destroy; override;
  end;

  { ------------------------------------------------------------------ }
  {  Type section                                                       }
  { ------------------------------------------------------------------ }

  { Abstract base for type definitions (currently only TRecordTypeDef). }
  TASTTypeDef = class(TASTNode);

  TFieldDecl = class(TASTNode)
  public
    Names:        TStringList;  { owned — e.g. X, Y: Integer }
    TypeName:     string;
    ResolvedType: TTypeDesc;    { set by uSemantic }
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
    ResolvedType: TTypeDesc;  { set by uSemantic }
  end;

  TMethodDecl = class(TASTNode)
  public
    Name:               string;      { method name }
    Params:             TObjectList; { owned TMethodParam }
    ReturnTypeName:     string;      { empty = procedure }
    ResolvedReturnType: TTypeDesc;   { set by uSemantic; nil = procedure }
    Body:               TBlock;      { owned }
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

  TClassTypeDef = class(TASTTypeDef)
  public
    ParentName: string;
    Fields:     TObjectList;  { owned TFieldDecl }
    Methods:    TObjectList;  { owned TMethodDecl }
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

  TBlock = class(TASTNode)
  public
    TypeDecls: TObjectList;  { owned TTypeDecl }
    Decls:     TObjectList;  { owned TVarDecl }
    Stmts:     TObjectList;  { owned TASTStmt }
    constructor Create;
    destructor Destroy; override;
  end;

  TProgram = class(TASTNode)
  public
    Name:        string;
    UsedUnits:   TStringList;   { owned }
    Block:       TBlock;        { owned }
    SymbolTable: TSymbolTable;  { owned after semantic analysis; nil before }
    constructor Create;
    destructor Destroy; override;
  end;

function BinaryOpName(AOp: TBinaryOp): string;

implementation

function BinaryOpName(AOp: TBinaryOp): string;
begin
  case AOp of
    boAdd: Result := '+';
    boSub: Result := '-';
    boMul: Result := '*';
    boDiv: Result := 'div';
  else
    Result := '?';
  end;
end;

{ TBinaryExpr }

destructor TBinaryExpr.Destroy;
begin
  Left.Free;
  Right.Free;
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

{ TVarDecl }

constructor TVarDecl.Create;
begin
  inherited Create;
  Names := TStringList.Create;
end;

destructor TVarDecl.Destroy;
begin
  Names.Free;
  inherited Destroy;
end;

{ TFieldDecl }

constructor TFieldDecl.Create;
begin
  inherited Create;
  Names := TStringList.Create;
end;

destructor TFieldDecl.Destroy;
begin
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
  Params := TObjectList.Create(True);
end;

destructor TMethodDecl.Destroy;
begin
  Params.Free;
  Body.Free;
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
  Fields  := TObjectList.Create(True);
  Methods := TObjectList.Create(True);
end;

destructor TClassTypeDef.Destroy;
begin
  Methods.Free;
  Fields.Free;
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
  TypeDecls := TObjectList.Create(True);
  Decls     := TObjectList.Create(True);
  Stmts     := TObjectList.Create(True);
end;

destructor TBlock.Destroy;
begin
  TypeDecls.Free;
  Decls.Free;
  Stmts.Free;
  inherited Destroy;
end;

{ TProgram }

constructor TProgram.Create;
begin
  inherited Create;
  UsedUnits := TStringList.Create;
end;

destructor TProgram.Destroy;
begin
  SymbolTable.Free;
  UsedUnits.Free;
  Block.Free;
  inherited Destroy;
end;

end.
