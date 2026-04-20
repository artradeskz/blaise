unit uParser;

{$mode objfpc}{$H+}

// Recursive-descent parser for the Phase 1 grammar:
//   Program    ::= 'program' Ident ';' [Uses] Block '.'
//   Uses       ::= 'uses' Ident {',' Ident} ';'
//   Block      ::= ['var' VarBlock] 'begin' StmtList 'end'
//   VarBlock   ::= VarDecl {VarDecl}
//   VarDecl    ::= IdentList ':' TypeName ';'
//   StmtList   ::= Stmt {';' Stmt} [';']
//   Stmt       ::= Assignment | ProcCall | empty
//   Assignment ::= Ident ':=' Expr
//   ProcCall   ::= Ident ['(' [ExprList] ')']
//   ExprList   ::= Expr {',' Expr}
//   Expr       ::= Term (('+' | '-') Term)*
//   Term       ::= Factor (('*' | '/') Factor)*
//   Factor     ::= IntLit | StringLit | Ident | '(' Expr ')'
//   TypeName   ::= 'Integer' | 'Boolean' | 'string'

interface

uses
  SysUtils, uLexer, uAST;

type
  EParseError = class(Exception);

  TParser = class
  private
    FLexer:   TLexer;
    FCurrent: TToken;

    procedure Advance;
    procedure Expect(AKind: TTokenKind);
    function  Check(AKind: TTokenKind): Boolean;

    function  ParseProgram: TProgram;
    procedure ParseUses(AProg: TProgram);
    function  ParseBlock: TBlock;
    procedure ParseVarBlock(ABlock: TBlock);
    procedure ParseVarDecl(ABlock: TBlock);
    procedure ParseStmtList(ABlock: TBlock);
    function  ParseStmt: TASTStmt;
    function  ParseExpr: TASTExpr;
    function  ParseTerm: TASTExpr;
    function  ParseFactor: TASTExpr;
    procedure ParseArgList(ACall: TProcCall);
  public
    constructor Create(ALexer: TLexer);
    function Parse: TProgram;
  end;

implementation

constructor TParser.Create(ALexer: TLexer);
begin
  inherited Create;
  FLexer := ALexer;
  FCurrent := FLexer.Next;
end;

procedure TParser.Advance;
begin
  FCurrent := FLexer.Next;
end;

procedure TParser.Expect(AKind: TTokenKind);
begin
  if FCurrent.Kind <> AKind then
    raise EParseError.CreateFmt(
      'Expected token %d but got %d (''%s'') at line %d col %d',
      [Ord(AKind), Ord(FCurrent.Kind), FCurrent.Value,
       FCurrent.Line, FCurrent.Col]);
  Advance;
end;

function TParser.Check(AKind: TTokenKind): Boolean;
begin
  Result := FCurrent.Kind = AKind;
end;

{ ------------------------------------------------------------------ }

function TParser.Parse: TProgram;
begin
  Result := ParseProgram;
end;

function TParser.ParseProgram: TProgram;
begin
  Result := TProgram.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;

    Expect(tkProgram);

    if not Check(tkIdent) then
      raise EParseError.CreateFmt('Expected program name at line %d col %d',
        [FCurrent.Line, FCurrent.Col]);
    Result.Name := FCurrent.Value;
    Advance;

    Expect(tkSemicolon);

    if Check(tkUses) then
      ParseUses(Result);

    Result.Block := ParseBlock;

    Expect(tkDot);

    if not Check(tkEOF) then
      raise EParseError.CreateFmt(
        'Unexpected tokens after program end at line %d col %d',
        [FCurrent.Line, FCurrent.Col]);
  except
    Result.Free;
    raise;
  end;
end;

procedure TParser.ParseUses(AProg: TProgram);
begin
  Expect(tkUses);
  if not Check(tkIdent) then
    raise EParseError.CreateFmt('Expected unit name after ''uses'' at line %d col %d',
      [FCurrent.Line, FCurrent.Col]);
  AProg.UsedUnits.Add(FCurrent.Value);
  Advance;
  while Check(tkComma) do
  begin
    Advance;
    if not Check(tkIdent) then
      raise EParseError.CreateFmt('Expected unit name after '','' at line %d col %d',
        [FCurrent.Line, FCurrent.Col]);
    AProg.UsedUnits.Add(FCurrent.Value);
    Advance;
  end;
  Expect(tkSemicolon);
end;

function TParser.ParseBlock: TBlock;
begin
  Result := TBlock.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;

    if Check(tkVar) then
      ParseVarBlock(Result);

    Expect(tkBegin);
    ParseStmtList(Result);
    Expect(tkEnd);
  except
    Result.Free;
    raise;
  end;
end;

procedure TParser.ParseVarBlock(ABlock: TBlock);
begin
  Expect(tkVar);
  { At least one declaration required after 'var' }
  while Check(tkIdent) do
    ParseVarDecl(ABlock);
end;

procedure TParser.ParseVarDecl(ABlock: TBlock);
var
  Decl: TVarDecl;
begin
  Decl := TVarDecl.Create;
  Decl.Line := FCurrent.Line;
  Decl.Col  := FCurrent.Col;
  try
    { IdentList: one or more names separated by commas }
    if not Check(tkIdent) then
      raise EParseError.CreateFmt('Expected variable name at line %d col %d',
        [FCurrent.Line, FCurrent.Col]);
    Decl.Names.Add(FCurrent.Value);
    Advance;
    while Check(tkComma) do
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.CreateFmt('Expected variable name at line %d col %d',
          [FCurrent.Line, FCurrent.Col]);
      Decl.Names.Add(FCurrent.Value);
      Advance;
    end;
    Expect(tkColon);
    if not Check(tkIdent) then
      raise EParseError.CreateFmt('Expected type name at line %d col %d',
        [FCurrent.Line, FCurrent.Col]);
    Decl.TypeName := FCurrent.Value;
    Advance;
    Expect(tkSemicolon);
    ABlock.Decls.Add(Decl);
  except
    Decl.Free;
    raise;
  end;
end;

procedure TParser.ParseStmtList(ABlock: TBlock);
var
  Stmt: TASTStmt;
begin
  { Parse zero or more statements separated (or terminated) by semicolons }
  while not (Check(tkEnd) or Check(tkEOF)) do
  begin
    Stmt := ParseStmt;
    if Stmt <> nil then
      ABlock.Stmts.Add(Stmt);
    if Check(tkSemicolon) then
      Advance
    else
      Break;
  end;
end;

function TParser.ParseStmt: TASTStmt;
var
  Name: string;
  Line, Col: Integer;
  Call: TProcCall;
  Assign: TAssignment;
begin
  Result := nil;

  { Empty statement }
  if Check(tkEnd) or Check(tkEOF) or Check(tkSemicolon) then
    Exit;

  if not Check(tkIdent) then
    raise EParseError.CreateFmt(
      'Expected statement at line %d col %d',
      [FCurrent.Line, FCurrent.Col]);

  Name := FCurrent.Value;
  Line := FCurrent.Line;
  Col  := FCurrent.Col;
  Advance;

  if Check(tkAssign) then
  begin
    { Assignment }
    Advance;
    Assign := TAssignment.Create;
    Assign.Line := Line;
    Assign.Col  := Col;
    Assign.Name := Name;
    Assign.Expr := ParseExpr;
    Result := Assign;
  end
  else
  begin
    { Procedure call — parentheses optional for zero-arg calls }
    Call := TProcCall.Create;
    Call.Line := Line;
    Call.Col  := Col;
    Call.Name := Name;
    if Check(tkLParen) then
    begin
      Advance;
      if not Check(tkRParen) then
        ParseArgList(Call);
      Expect(tkRParen);
    end;
    Result := Call;
  end;
end;

procedure TParser.ParseArgList(ACall: TProcCall);
begin
  ACall.Args.Add(ParseExpr);
  while Check(tkComma) do
  begin
    Advance;
    ACall.Args.Add(ParseExpr);
  end;
end;

{ Expression parsing — standard precedence climbing }

function TParser.ParseExpr: TASTExpr;
var
  Right: TASTExpr;
  Op:    TBinaryOp;
  Node:  TBinaryExpr;
begin
  Result := ParseTerm;
  while Check(tkPlus) or Check(tkMinus) do
  begin
    if Check(tkPlus) then Op := boAdd else Op := boSub;
    Advance;
    Right := ParseTerm;
    Node := TBinaryExpr.Create;
    Node.Op    := Op;
    Node.Left  := Result;
    Node.Right := Right;
    Result := Node;
  end;
end;

function TParser.ParseTerm: TASTExpr;
var
  Right: TASTExpr;
  Op:    TBinaryOp;
  Node:  TBinaryExpr;
begin
  Result := ParseFactor;
  while Check(tkStar) or Check(tkSlash) or Check(tkDiv) do
  begin
    if Check(tkStar) then Op := boMul else Op := boDiv;
    Advance;
    Right := ParseFactor;
    Node := TBinaryExpr.Create;
    Node.Op    := Op;
    Node.Left  := Result;
    Node.Right := Right;
    Result := Node;
  end;
end;

function TParser.ParseFactor: TASTExpr;
var
  IntNode: TIntLiteral;
  StrNode: TStringLiteral;
  IdNode:  TIdentExpr;
  Inner:   TASTExpr;
begin
  case FCurrent.Kind of
    tkIntLit:
      begin
        IntNode := TIntLiteral.Create;
        IntNode.Line  := FCurrent.Line;
        IntNode.Col   := FCurrent.Col;
        IntNode.Value := StrToInt64(FCurrent.Value);
        Advance;
        Result := IntNode;
      end;
    tkStringLit:
      begin
        StrNode := TStringLiteral.Create;
        StrNode.Line  := FCurrent.Line;
        StrNode.Col   := FCurrent.Col;
        StrNode.Value := FCurrent.Value;
        Advance;
        Result := StrNode;
      end;
    tkIdent:
      begin
        IdNode := TIdentExpr.Create;
        IdNode.Line := FCurrent.Line;
        IdNode.Col  := FCurrent.Col;
        IdNode.Name := FCurrent.Value;
        Advance;
        Result := IdNode;
      end;
    tkLParen:
      begin
        Advance;
        Inner := ParseExpr;
        Expect(tkRParen);
        Result := Inner;
      end;
  else
    raise EParseError.CreateFmt(
      'Expected expression at line %d col %d',
      [FCurrent.Line, FCurrent.Col]);
  end;
end;

end.
