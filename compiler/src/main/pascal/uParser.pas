unit uParser;

{$mode objfpc}{$H+}

// Recursive-descent parser for the Blaise grammar:
//   Program        ::= 'program' Ident ';' [Uses] Block '.'
//   Uses           ::= 'uses' Ident {',' Ident} ';'
//   Block          ::= [TypeSection] [VarSection] 'begin' StmtList 'end'
//   TypeSection    ::= 'type' TypeDecl {TypeDecl}
//   TypeDecl       ::= Ident '=' (RecordDef | ClassDef) ';'
//   RecordDef      ::= 'record' FieldList 'end'
//   ClassDef       ::= 'class' ['(' Ident ')'] FieldList MethodList 'end'
//   FieldList      ::= {FieldDecl}
//   FieldDecl      ::= IdentList ':' TypeName ';'
//   MethodList     ::= {MethodDecl}
//   MethodDecl     ::= 'procedure' Ident ['(' ParamList ')'] ';' Block ';'
//   ParamList      ::= ParamGroup {';' ParamGroup}
//   ParamGroup     ::= IdentList ':' TypeName
//   VarSection     ::= 'var' VarDecl {VarDecl}
//   VarDecl        ::= IdentList ':' TypeName ';'
//   StmtList       ::= Stmt {';' Stmt} [';']
//   Stmt           ::= FieldAssignment | MethodCall | Assignment | ProcCall | empty
//   FieldAssign    ::= Ident '.' Ident ':=' Expr
//   MethodCall     ::= Ident '.' Ident ['(' [ExprList] ')']
//   Assignment     ::= Ident ':=' Expr
//   ProcCall       ::= Ident ['(' [ExprList] ')']
//   ExprList       ::= Expr {',' Expr}
//   Expr           ::= Term (('+' | '-') Term)*
//   Term           ::= Factor (('*' | '/' | 'div') Factor)*
//   Factor         ::= IntLit | StringLit | Ident '.' Ident | Ident | '(' Expr ')'
//   TypeName       ::= Ident

interface

uses
  SysUtils, Classes, contnrs, uLexer, uAST;

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
    procedure ParseTypeSection(ABlock: TBlock);
    procedure ParseTypeDecl(ABlock: TBlock);
    function  ParseRecordDef: TRecordTypeDef;
    function  ParseClassDef: TClassTypeDef;
    procedure ParseFieldDecl(AFields: TObjectList);
    function  ParseMethodDecl(IsFunction: Boolean): TMethodDecl;
    procedure ParseParamList(AParams: TObjectList);
    procedure ParseVarBlock(ABlock: TBlock);
    procedure ParseVarDecl(ABlock: TBlock);
    procedure ParseStmtList(ABlock: TBlock);
    function  ParseStmt: TASTStmt;
    function  ParseExpr: TASTExpr;
    function  ParseTerm: TASTExpr;
    function  ParseFactor: TASTExpr;
    procedure ParseArgList(ACall: TProcCall);
    procedure ParseMethodCallArgList(ACall: TMethodCallStmt);
  public
    constructor Create(ALexer: TLexer);
    function Parse: TProgram;
  end;

implementation

constructor TParser.Create(ALexer: TLexer);
begin
  inherited Create;
  FLexer   := ALexer;
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

    if Check(tkType) then
      ParseTypeSection(Result);

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

{ ------------------------------------------------------------------ }
{ Type section                                                        }
{ ------------------------------------------------------------------ }

procedure TParser.ParseTypeSection(ABlock: TBlock);
begin
  Expect(tkType);
  { At least one declaration required after 'type' }
  while Check(tkIdent) do
    ParseTypeDecl(ABlock);
end;

procedure TParser.ParseTypeDecl(ABlock: TBlock);
var
  TD: TTypeDecl;
begin
  TD := TTypeDecl.Create;
  TD.Line := FCurrent.Line;
  TD.Col  := FCurrent.Col;
  try
    if not Check(tkIdent) then
      raise EParseError.CreateFmt('Expected type name at line %d col %d',
        [FCurrent.Line, FCurrent.Col]);
    TD.Name := FCurrent.Value;
    Advance;
    Expect(tkEquals);
    if Check(tkRecord) then
      TD.Def := ParseRecordDef
    else if Check(tkClass) then
      TD.Def := ParseClassDef
    else
      raise EParseError.CreateFmt(
        'Expected ''record'' or ''class'' at line %d col %d',
        [FCurrent.Line, FCurrent.Col]);
    Expect(tkSemicolon);
    ABlock.TypeDecls.Add(TD);
  except
    TD.Free;
    raise;
  end;
end;

function TParser.ParseRecordDef: TRecordTypeDef;
begin
  Result := TRecordTypeDef.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkRecord);
    while Check(tkIdent) do
      ParseFieldDecl(Result.Fields);
    Expect(tkEnd);
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseClassDef: TClassTypeDef;
begin
  Result := TClassTypeDef.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkClass);
    if Check(tkLParen) then
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.CreateFmt('Expected parent class name at line %d col %d',
          [FCurrent.Line, FCurrent.Col]);
      Result.ParentName := FCurrent.Value;
      Advance;
      Expect(tkRParen);
    end;
    while Check(tkIdent) do
      ParseFieldDecl(Result.Fields);
    while Check(tkProcedure) or Check(tkFunction) do
    begin
      if Check(tkFunction) then
        Result.Methods.Add(ParseMethodDecl(True))
      else
        Result.Methods.Add(ParseMethodDecl(False));
    end;
    Expect(tkEnd);
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseMethodDecl(IsFunction: Boolean): TMethodDecl;
begin
  Result := TMethodDecl.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    if IsFunction then
      Expect(tkFunction)
    else
      Expect(tkProcedure);
    if not Check(tkIdent) then
      raise EParseError.CreateFmt('Expected method name at line %d col %d',
        [FCurrent.Line, FCurrent.Col]);
    Result.Name := FCurrent.Value;
    Advance;
    if Check(tkLParen) then
    begin
      Advance;
      if not Check(tkRParen) then
        ParseParamList(Result.Params);
      Expect(tkRParen);
    end;
    if IsFunction then
    begin
      Expect(tkColon);
      if not Check(tkIdent) then
        raise EParseError.CreateFmt('Expected return type at line %d col %d',
          [FCurrent.Line, FCurrent.Col]);
      Result.ReturnTypeName := FCurrent.Value;
      Advance;
    end;
    Expect(tkSemicolon);
    Result.Body := ParseBlock;
    Expect(tkSemicolon);
  except
    Result.Free;
    raise;
  end;
end;

procedure TParser.ParseParamList(AParams: TObjectList);
var
  Par:   TMethodParam;
  I:     Integer;
  Names: TStringList;
  TypeN: string;
begin
  repeat
    Names := TStringList.Create;
    try
      if not Check(tkIdent) then
        raise EParseError.CreateFmt('Expected parameter name at line %d col %d',
          [FCurrent.Line, FCurrent.Col]);
      Names.Add(FCurrent.Value);
      Advance;
      while Check(tkComma) do
      begin
        Advance;
        if not Check(tkIdent) then
          raise EParseError.CreateFmt('Expected parameter name at line %d col %d',
            [FCurrent.Line, FCurrent.Col]);
        Names.Add(FCurrent.Value);
        Advance;
      end;
      Expect(tkColon);
      if not Check(tkIdent) then
        raise EParseError.CreateFmt('Expected type name at line %d col %d',
          [FCurrent.Line, FCurrent.Col]);
      TypeN := FCurrent.Value;
      Advance;
      for I := 0 to Names.Count - 1 do
      begin
        Par           := TMethodParam.Create;
        Par.ParamName := Names[I];
        Par.TypeName  := TypeN;
        AParams.Add(Par);
      end;
    finally
      Names.Free;
    end;
    if Check(tkSemicolon) then
      Advance
    else
      Break;
  until False;
end;

procedure TParser.ParseFieldDecl(AFields: TObjectList);
var
  Fld: TFieldDecl;
begin
  Fld := TFieldDecl.Create;
  Fld.Line := FCurrent.Line;
  Fld.Col  := FCurrent.Col;
  try
    if not Check(tkIdent) then
      raise EParseError.CreateFmt('Expected field name at line %d col %d',
        [FCurrent.Line, FCurrent.Col]);
    Fld.Names.Add(FCurrent.Value);
    Advance;
    while Check(tkComma) do
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.CreateFmt('Expected field name at line %d col %d',
          [FCurrent.Line, FCurrent.Col]);
      Fld.Names.Add(FCurrent.Value);
      Advance;
    end;
    Expect(tkColon);
    if not Check(tkIdent) then
      raise EParseError.CreateFmt('Expected type name at line %d col %d',
        [FCurrent.Line, FCurrent.Col]);
    Fld.TypeName := FCurrent.Value;
    Advance;
    Expect(tkSemicolon);
    AFields.Add(Fld);
  except
    Fld.Free;
    raise;
  end;
end;

{ ------------------------------------------------------------------ }
{ Var section                                                         }
{ ------------------------------------------------------------------ }

procedure TParser.ParseVarBlock(ABlock: TBlock);
begin
  Expect(tkVar);
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

{ ------------------------------------------------------------------ }
{ Statements                                                          }
{ ------------------------------------------------------------------ }

procedure TParser.ParseStmtList(ABlock: TBlock);
var
  Stmt: TASTStmt;
begin
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
  Name:        string;
  Line, Col:   Integer;
  Call:        TProcCall;
  Assign:      TAssignment;
  FldAssign:   TFieldAssignment;
  MCall:       TMethodCallStmt;
  SecondIdent: string;
begin
  Result := nil;

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

  if Check(tkDot) then
  begin
    Advance;
    if not Check(tkIdent) then
      raise EParseError.CreateFmt('Expected field or method name at line %d col %d',
        [FCurrent.Line, FCurrent.Col]);
    SecondIdent := FCurrent.Value;
    Advance;

    if Check(tkAssign) then
    begin
      { Field assignment: Ident '.' Ident ':=' Expr }
      FldAssign            := TFieldAssignment.Create;
      FldAssign.Line       := Line;
      FldAssign.Col        := Col;
      FldAssign.RecordName := Name;
      FldAssign.FieldName  := SecondIdent;
      Expect(tkAssign);
      FldAssign.Expr := ParseExpr;
      Result := FldAssign;
    end
    else
    begin
      { Method call: Ident '.' Ident ['(' [args] ')'] }
      MCall            := TMethodCallStmt.Create;
      MCall.Line       := Line;
      MCall.Col        := Col;
      MCall.ObjectName := Name;
      MCall.Name := SecondIdent;
      if Check(tkLParen) then
      begin
        Advance;
        if not Check(tkRParen) then
          ParseMethodCallArgList(MCall);
        Expect(tkRParen);
      end;
      Result := MCall;
    end;
  end
  else if Check(tkAssign) then
  begin
    Advance;
    Assign      := TAssignment.Create;
    Assign.Line := Line;
    Assign.Col  := Col;
    Assign.Name := Name;
    Assign.Expr := ParseExpr;
    Result := Assign;
  end
  else
  begin
    Call      := TProcCall.Create;
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

procedure TParser.ParseMethodCallArgList(ACall: TMethodCallStmt);
begin
  ACall.Args.Add(ParseExpr);
  while Check(tkComma) do
  begin
    Advance;
    ACall.Args.Add(ParseExpr);
  end;
end;

{ ------------------------------------------------------------------ }
{ Expression parsing — standard precedence climbing                   }
{ ------------------------------------------------------------------ }

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
  IntNode:    TIntLiteral;
  StrNode:    TStringLiteral;
  IdNode:     TIdentExpr;
  FldNode:    TFieldAccessExpr;
  MCallNode:  TMethodCallExpr;
  Inner:      TASTExpr;
  Name:       string;
  SecondName: string;
  Line, Col:  Integer;
begin
  case FCurrent.Kind of
    tkIntLit:
      begin
        IntNode       := TIntLiteral.Create;
        IntNode.Line  := FCurrent.Line;
        IntNode.Col   := FCurrent.Col;
        IntNode.Value := StrToInt64(FCurrent.Value);
        Advance;
        Result := IntNode;
      end;
    tkStringLit:
      begin
        StrNode       := TStringLiteral.Create;
        StrNode.Line  := FCurrent.Line;
        StrNode.Col   := FCurrent.Col;
        StrNode.Value := FCurrent.Value;
        Advance;
        Result := StrNode;
      end;
    tkIdent:
      begin
        Name := FCurrent.Value;
        Line := FCurrent.Line;
        Col  := FCurrent.Col;
        Advance;
        if Check(tkDot) then
        begin
          Advance;
          if not Check(tkIdent) then
            raise EParseError.CreateFmt('Expected field or method name at line %d col %d',
              [FCurrent.Line, FCurrent.Col]);
          SecondName := FCurrent.Value;
          Advance;
          if Check(tkLParen) then
          begin
            { IDENT '.' IDENT '(' ... ')' — method call expression }
            MCallNode            := TMethodCallExpr.Create;
            MCallNode.Line       := Line;
            MCallNode.Col        := Col;
            MCallNode.ObjectName := Name;
            MCallNode.Name       := SecondName;
            Advance;
            if not Check(tkRParen) then
            begin
              MCallNode.Args.Add(ParseExpr);
              while Check(tkComma) do
              begin
                Advance;
                MCallNode.Args.Add(ParseExpr);
              end;
            end;
            Expect(tkRParen);
            Result := MCallNode;
          end
          else
          begin
            { IDENT '.' IDENT — field access or constructor call }
            FldNode            := TFieldAccessExpr.Create;
            FldNode.Line       := Line;
            FldNode.Col        := Col;
            FldNode.RecordName := Name;
            FldNode.FieldName  := SecondName;
            Result := FldNode;
          end;
        end
        else
        begin
          IdNode      := TIdentExpr.Create;
          IdNode.Line := Line;
          IdNode.Col  := Col;
          IdNode.Name := Name;
          Result := IdNode;
        end;
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
