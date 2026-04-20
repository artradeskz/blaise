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

  TProcCall = class(TASTStmt)
  public
    Name: string;
    Args: TObjectList;  { owned TASTExpr items }
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
  {  Block and Program                                                  }
  { ------------------------------------------------------------------ }

  TBlock = class(TASTNode)
  public
    Decls: TObjectList;  { owned TVarDecl }
    Stmts: TObjectList;  { owned TASTStmt }
    constructor Create;
    destructor Destroy; override;
  end;

  TProgram = class(TASTNode)
  public
    Name:        string;
    UsedUnits:   TStringList;   { owned — unit names from uses clause }
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

{ TBlock }

constructor TBlock.Create;
begin
  inherited Create;
  Decls := TObjectList.Create(True);
  Stmts := TObjectList.Create(True);
end;

destructor TBlock.Destroy;
begin
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
