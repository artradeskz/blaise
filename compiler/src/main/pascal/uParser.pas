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
    FLexer:     TLexer;
    FCurrent:   TToken;
    FLookahead: TToken;  { one-token lookahead for generic disambiguation }

    procedure Advance;
    function  PeekKind: TTokenKind;
    procedure Expect(AKind: TTokenKind);
    function  Check(AKind: TTokenKind): Boolean;
    function  ParseTypeName: string;  { reads Ident optionally followed by '<' ArgList '>' }

    function  ParseProgram: TProgram;
    procedure ParseUses(AProg: TProgram);
    function  ParseBlock: TBlock;
    procedure ParseTypeSection(ABlock: TBlock);
    procedure ParseTypeDecl(ABlock: TBlock);
    function  ParseRecordDef: TRecordTypeDef;
    function  ParseClassDef: TClassTypeDef;
    function  ParseInterfaceDef: TInterfaceTypeDef;
    procedure ParseFieldDecl(AFields: TObjectList);
    function  ParseMethodDecl(IsFunction: Boolean): TMethodDecl;
    procedure ParseParamList(AParams: TObjectList);
    procedure ParseStandaloneDecl(ABlock: TBlock);
    procedure ParseVarBlock(ABlock: TBlock);
    procedure ParseVarDecl(ABlock: TBlock);
    procedure ParseStmtList(ABlock: TBlock);
    function  ParseStmt: TASTStmt;
    function  ParseIfStmt: TIfStmt;
    function  ParseWhileStmt: TWhileStmt;
    function  ParseForStmt: TForStmt;
    function  ParseTryStmt: TASTStmt;
    function  ParseRaiseStmt: TRaiseStmt;
    function  ParseForwardDecl(IsFunction: Boolean): TMethodDecl;
    function  ParseCompoundStmt: TCompoundStmt;
    function  ParseExpr: TASTExpr;
    function  ParseAddSub: TASTExpr;
    function  ParseTerm: TASTExpr;
    function  ParseFactor: TASTExpr;
    procedure ParseArgList(ACall: TProcCall);
    procedure ParseMethodCallArgList(ACall: TMethodCallStmt);
  public
    constructor Create(ALexer: TLexer);
    function Parse: TProgram;
    function ParseUnit: TUnit;
  end;

implementation

constructor TParser.Create(ALexer: TLexer);
begin
  inherited Create;
  FLexer     := ALexer;
  FCurrent   := FLexer.Next;
  FLookahead := FLexer.Next;
end;

procedure TParser.Advance;
begin
  FCurrent   := FLookahead;
  FLookahead := FLexer.Next;
end;

function TParser.PeekKind: TTokenKind;
begin
  Result := FLookahead.Kind;
end;

{ Parse a type name, including generic instantiations.
  Returns 'Integer', 'TBox<Integer>', 'TPair<string,Integer>', etc.
  Spaces around commas are stripped for a canonical representation. }
function TParser.ParseTypeName: string;
begin
  if not Check(tkIdent) then
    raise EParseError.CreateFmt('Expected type name at line %d col %d',
      [FCurrent.Line, FCurrent.Col]);
  Result := FCurrent.Value;
  Advance;
  if Check(tkLessThan) then
  begin
    Advance;  { consume '<' }
    Result := Result + '<';
    if not Check(tkIdent) then
      raise EParseError.CreateFmt(
        'Expected type argument after ''<'' at line %d col %d',
        [FCurrent.Line, FCurrent.Col]);
    Result := Result + FCurrent.Value;
    Advance;
    while Check(tkComma) do
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.CreateFmt(
          'Expected type argument after '','' at line %d col %d',
          [FCurrent.Line, FCurrent.Col]);
      Result := Result + ',' + FCurrent.Value;
      Advance;
    end;
    Expect(tkGreaterThan);
    Result := Result + '>';
  end;
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

    while Check(tkVar) or Check(tkProcedure) or Check(tkFunction) do
    begin
      if Check(tkVar) then
        ParseVarBlock(Result)
      else
        ParseStandaloneDecl(Result);
    end;

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
  TD:         TTypeDecl;
  GD:         TGenericTypeDef;
  ParamNames: TStringList;
  IsGeneric:  Boolean;
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
    { Check for generic type parameters: TBox<T> or TPair<K, V> }
    IsGeneric := Check(tkLessThan);
    if IsGeneric then
    begin
      Advance;  { consume '<' }
      ParamNames := TStringList.Create;
      try
        if not Check(tkIdent) then
          raise EParseError.CreateFmt(
            'Expected type parameter name at line %d col %d',
            [FCurrent.Line, FCurrent.Col]);
        ParamNames.Add(FCurrent.Value);
        Advance;
        while Check(tkComma) do
        begin
          Advance;
          if not Check(tkIdent) then
            raise EParseError.CreateFmt(
              'Expected type parameter name at line %d col %d',
              [FCurrent.Line, FCurrent.Col]);
          ParamNames.Add(FCurrent.Value);
          Advance;
        end;
        Expect(tkGreaterThan);
        Expect(tkEquals);
        if not Check(tkClass) then
          raise EParseError.CreateFmt(
            'Generic type must be a class at line %d col %d',
            [FCurrent.Line, FCurrent.Col]);
        GD            := TGenericTypeDef.Create;
        GD.Line       := TD.Line;
        GD.Col        := TD.Col;
        GD.ParamNames.AddStrings(ParamNames);
        GD.ClassDef.Free;
        GD.ClassDef := ParseClassDef;
        TD.Def := GD;
      finally
        ParamNames.Free;
      end;
    end
    else
    begin
      Expect(tkEquals);
      if Check(tkRecord) then
        TD.Def := ParseRecordDef
      else if Check(tkClass) then
        TD.Def := ParseClassDef
      else if Check(tkIntf) then
        TD.Def := ParseInterfaceDef
      else
        raise EParseError.CreateFmt(
          'Expected ''record'', ''class'', or ''interface'' at line %d col %d',
          [FCurrent.Line, FCurrent.Col]);
    end;
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
      { Additional names after a comma are implemented interface names }
      while Check(tkComma) do
      begin
        Advance;
        if not Check(tkIdent) then
          raise EParseError.CreateFmt('Expected interface name at line %d col %d',
            [FCurrent.Line, FCurrent.Col]);
        Result.ImplementsNames.Add(FCurrent.Value);
        Advance;
      end;
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

function TParser.ParseInterfaceDef: TInterfaceTypeDef;
begin
  Result := TInterfaceTypeDef.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkIntf);
    if Check(tkLParen) then
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.CreateFmt('Expected parent interface name at line %d col %d',
          [FCurrent.Line, FCurrent.Col]);
      Result.ParentName := FCurrent.Value;
      Advance;
      Expect(tkRParen);
    end;
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
    { Qualified name: TypeName.MethodName (standalone class method implementation) }
    if Check(tkDot) then
    begin
      Advance;
      if not Check(tkIdent) then
        raise EParseError.CreateFmt('Expected method name after ''.'' at line %d col %d',
          [FCurrent.Line, FCurrent.Col]);
      Result.OwnerTypeName := Result.Name;
      Result.Name          := FCurrent.Value;
      Advance;
    end;
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
      Result.ReturnTypeName := ParseTypeName;
    end;
    Expect(tkSemicolon);
    if Check(tkVirtual) then
    begin
      Result.IsVirtual := True;
      Advance;
      Expect(tkSemicolon);
    end
    else if Check(tkOverride) then
    begin
      Result.IsOverride := True;
      Advance;
      Expect(tkSemicolon);
    end;
    { Body is optional — present for standalone impls and inline class methods,
      absent for class forward declarations (no begin/var/type follows) }
    if Check(tkBegin) or Check(tkVar) or Check(tkType) then
    begin
      Result.Body := ParseBlock;
      Expect(tkSemicolon);
    end;
  except
    Result.Free;
    raise;
  end;
end;

procedure TParser.ParseParamList(AParams: TObjectList);
var
  Par:      TMethodParam;
  I:        Integer;
  Names:    TStringList;
  TypeN:    string;
  IsVarGrp: Boolean;
begin
  repeat
    IsVarGrp := Check(tkVar);
    if IsVarGrp then Advance;
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
      TypeN := ParseTypeName;
      for I := 0 to Names.Count - 1 do
      begin
        Par            := TMethodParam.Create;
        Par.ParamName  := Names[I];
        Par.TypeName   := TypeN;
        Par.IsVarParam := IsVarGrp;
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

procedure TParser.ParseStandaloneDecl(ABlock: TBlock);
var
  IsFunc: Boolean;
  MD:     TMethodDecl;
begin
  IsFunc := Check(tkFunction);
  MD     := ParseMethodDecl(IsFunc);
  ABlock.ProcDecls.Add(MD);
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
    Fld.TypeName := ParseTypeName;
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
    Decl.TypeName := ParseTypeName;
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
  while not (Check(tkEnd) or Check(tkEOF) or Check(tkElse)) do
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

  if Check(tkEnd) or Check(tkEOF) or Check(tkSemicolon) or Check(tkElse) then
    Exit;

  if Check(tkIf) then
  begin
    Result := ParseIfStmt;
    Exit;
  end;

  if Check(tkWhile) then
  begin
    Result := ParseWhileStmt;
    Exit;
  end;

  if Check(tkFor) then
  begin
    Result := ParseForStmt;
    Exit;
  end;

  if Check(tkTry) then
  begin
    Result := ParseTryStmt;
    Exit;
  end;

  if Check(tkRaise) then
  begin
    Result := ParseRaiseStmt;
    Exit;
  end;

  if Check(tkBegin) then
  begin
    Result := ParseCompoundStmt;
    Exit;
  end;

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

function TParser.ParseWhileStmt: TWhileStmt;
begin
  Result := TWhileStmt.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkWhile);
    Result.Condition := ParseExpr;
    Expect(tkDo);
    Result.Body := ParseStmt;
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseIfStmt: TIfStmt;
begin
  Result := TIfStmt.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkIf);
    Result.Condition := ParseExpr;
    Expect(tkThen);
    Result.ThenStmt := ParseStmt;
    if Check(tkElse) then
    begin
      Advance;
      Result.ElseStmt := ParseStmt;
    end;
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseForStmt: TForStmt;
begin
  Result := TForStmt.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkFor);
    if not Check(tkIdent) then
      raise EParseError.CreateFmt('Expected loop variable at line %d col %d',
        [FCurrent.Line, FCurrent.Col]);
    Result.VarName := FCurrent.Value;
    Advance;
    Expect(tkAssign);
    Result.StartExpr := ParseExpr;
    if Check(tkTo) then
    begin
      Result.IsDownTo := False;
      Advance;
    end
    else if Check(tkDownto) then
    begin
      Result.IsDownTo := True;
      Advance;
    end
    else
      raise EParseError.CreateFmt(
        'Expected ''to'' or ''downto'' at line %d col %d',
        [FCurrent.Line, FCurrent.Col]);
    Result.EndExpr := ParseExpr;
    Expect(tkDo);
    Result.Body := ParseStmt;
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseTryStmt: TASTStmt;
var
  TryBody:     TCompoundStmt;
  FinallyBody: TCompoundStmt;
  ExceptBody:  TCompoundStmt;
  Stmt:        TASTStmt;
  TFS:         TTryFinallyStmt;
  TES:         TTryExceptStmt;
  Line, Col:   Integer;

  procedure ParseBodyInto(ATarget: TCompoundStmt;
    AStop1, AStop2: TTokenKind);
  var S: TASTStmt;
  begin
    while not (Check(AStop1) or Check(AStop2) or
               Check(tkEnd) or Check(tkEOF)) do
    begin
      S := ParseStmt;
      if S <> nil then
        ATarget.Stmts.Add(S);
      if Check(tkSemicolon) then
        Advance
      else
        Break;
    end;
  end;

begin
  Line := FCurrent.Line;
  Col  := FCurrent.Col;
  Expect(tkTry);

  TryBody := TCompoundStmt.Create;
  TryBody.Line := Line;
  TryBody.Col  := Col;
  try
    ParseBodyInto(TryBody, tkFinally, tkExcept);

    if Check(tkFinally) then
    begin
      Advance;
      FinallyBody := TCompoundStmt.Create;
      try
        ParseBodyInto(FinallyBody, tkEnd, tkEnd);
        Expect(tkEnd);
        TFS             := TTryFinallyStmt.Create;
        TFS.Line        := Line;
        TFS.Col         := Col;
        TFS.TryBody     := TryBody;
        TFS.FinallyBody := FinallyBody;
        TryBody     := nil;
        FinallyBody := nil;
        Result := TFS;
      except
        FinallyBody.Free;
        raise;
      end;
    end
    else if Check(tkExcept) then
    begin
      Advance;
      ExceptBody := TCompoundStmt.Create;
      try
        ParseBodyInto(ExceptBody, tkEnd, tkEnd);
        Expect(tkEnd);
        TES            := TTryExceptStmt.Create;
        TES.Line       := Line;
        TES.Col        := Col;
        TES.TryBody    := TryBody;
        TES.ExceptBody := ExceptBody;
        TryBody    := nil;
        ExceptBody := nil;
        Result := TES;
      except
        ExceptBody.Free;
        raise;
      end;
    end
    else
    begin
      raise EParseError.CreateFmt(
        'Expected ''finally'' or ''except'' after try body at line %d col %d',
        [FCurrent.Line, FCurrent.Col]);
    end;
  except
    TryBody.Free;
    raise;
  end;
end;

function TParser.ParseRaiseStmt: TRaiseStmt;
begin
  Result := TRaiseStmt.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkRaise);
    { Bare raise has no expression; detect by checking statement terminators }
    if not (Check(tkSemicolon) or Check(tkEnd) or Check(tkEOF) or
            Check(tkFinally) or Check(tkExcept) or Check(tkElse)) then
      Result.Expr := ParseExpr;
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseCompoundStmt: TCompoundStmt;
var
  Stmt: TASTStmt;
begin
  Result := TCompoundStmt.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkBegin);
    while not (Check(tkEnd) or Check(tkEOF)) do
    begin
      Stmt := ParseStmt;
      if Stmt <> nil then
        Result.Stmts.Add(Stmt);
      if Check(tkSemicolon) then
        Advance
      else
        Break;
    end;
    Expect(tkEnd);
  except
    Result.Free;
    raise;
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
{ Unit parsing                                                        }
{ ------------------------------------------------------------------ }

function TParser.ParseForwardDecl(IsFunction: Boolean): TMethodDecl;
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
      raise EParseError.CreateFmt('Expected name at line %d col %d',
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
      Result.ReturnTypeName := ParseTypeName;
    end;
    Expect(tkSemicolon);
    { Body remains nil — forward declaration }
  except
    Result.Free;
    raise;
  end;
end;

function TParser.ParseUnit: TUnit;
begin
  Result := TUnit.Create;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;

    Expect(tkUnit);
    if not Check(tkIdent) then
      raise EParseError.CreateFmt('Expected unit name at line %d col %d',
        [FCurrent.Line, FCurrent.Col]);
    Result.Name := FCurrent.Value;
    Advance;
    Expect(tkSemicolon);

    { Interface section }
    Expect(tkIntf);
    if Check(tkType) then
      ParseTypeSection(Result.IntfBlock);
    while Check(tkProcedure) or Check(tkFunction) do
    begin
      if Check(tkFunction) then
        Result.IntfBlock.ProcDecls.Add(ParseForwardDecl(True))
      else
        Result.IntfBlock.ProcDecls.Add(ParseForwardDecl(False));
    end;

    { Implementation section }
    Expect(tkImplementation);
    while Check(tkProcedure) or Check(tkFunction) do
    begin
      if Check(tkFunction) then
        Result.ImplBlock.ProcDecls.Add(ParseMethodDecl(True))
      else
        Result.ImplBlock.ProcDecls.Add(ParseMethodDecl(False));
    end;

    Expect(tkEnd);
    Expect(tkDot);

    if not Check(tkEOF) then
      raise EParseError.CreateFmt(
        'Unexpected tokens after unit end at line %d col %d',
        [FCurrent.Line, FCurrent.Col]);
  except
    Result.Free;
    raise;
  end;
end;

{ ------------------------------------------------------------------ }
{ Expression parsing — standard precedence climbing                   }
{ ------------------------------------------------------------------ }

function TParser.ParseExpr: TASTExpr;
var
  Right:  TASTExpr;
  CmpOp:  TBinaryOp;
  Node:   TBinaryExpr;
  IsNode: TIsExpr;
  AsNode: TAsExpr;
begin
  Result := ParseAddSub;

  { Comparison — non-associative, one level only }
  if Check(tkEquals) or Check(tkNotEquals) or
     Check(tkLessThan) or Check(tkGreaterThan) or
     Check(tkLessEqual) or Check(tkGreaterEqual) then
  begin
    if      Check(tkEquals)      then CmpOp := boEQ
    else if Check(tkNotEquals)   then CmpOp := boNE
    else if Check(tkLessThan)    then CmpOp := boLT
    else if Check(tkGreaterThan) then CmpOp := boGT
    else if Check(tkLessEqual)   then CmpOp := boLE
    else                              CmpOp := boGE;
    Advance;
    Right       := ParseAddSub;
    Node        := TBinaryExpr.Create;
    Node.Op     := CmpOp;
    Node.Left   := Result;
    Node.Right  := Right;
    Result      := Node;
  end
  else if Check(tkIs) then
  begin
    Advance;
    IsNode          := TIsExpr.Create;
    IsNode.Obj      := Result;
    IsNode.TypeName := FCurrent.Value;
    Expect(tkIdent);
    Result := IsNode;
  end
  else if Check(tkAs) then
  begin
    Advance;
    AsNode          := TAsExpr.Create;
    AsNode.Obj      := Result;
    AsNode.TypeName := FCurrent.Value;
    Expect(tkIdent);
    Result := AsNode;
  end;
end;

function TParser.ParseAddSub: TASTExpr;
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
  NilNode:    TNilLiteral;
  IdNode:     TIdentExpr;
  FldNode:    TFieldAccessExpr;
  MCallNode:  TMethodCallExpr;
  FCallNode:  TFuncCallExpr;
  Inner:      TASTExpr;
  Name:       string;
  SecondName: string;
  Line, Col:  Integer;
begin
  case FCurrent.Kind of
    tkNil:
      begin
        NilNode      := TNilLiteral.Create;
        NilNode.Line := FCurrent.Line;
        NilNode.Col  := FCurrent.Col;
        Advance;
        Result := NilNode;
      end;
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
        { Generic constructor: TypeName<Args>.Method
          Heuristic: '<' followed by identifier is treated as generic type args.
          This means 'A < SomeName > .X' cannot appear as a comparison in expressions,
          which is a known Phase 3 limitation. }
        if Check(tkLessThan) and (PeekKind = tkIdent) then
        begin
          Advance;  { consume '<' }
          Name := Name + '<' + FCurrent.Value;
          Advance;
          while Check(tkComma) do
          begin
            Advance;
            Name := Name + ',' + FCurrent.Value;
            Advance;
          end;
          Expect(tkGreaterThan);
          Name := Name + '>';
          { Generic type args must be followed by '.' (constructor or class method) }
          if not Check(tkDot) then
            raise EParseError.CreateFmt(
              'Expected ''.'' after generic type arguments at line %d col %d',
              [FCurrent.Line, FCurrent.Col]);
        end;
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
        else if Check(tkLParen) then
        begin
          { Standalone function call expression: Ident '(' [args] ')' }
          FCallNode      := TFuncCallExpr.Create;
          FCallNode.Line := Line;
          FCallNode.Col  := Col;
          FCallNode.Name := Name;
          Advance;  { consume '(' }
          if not Check(tkRParen) then
          begin
            FCallNode.Args.Add(ParseExpr);
            while Check(tkComma) do
            begin
              Advance;
              FCallNode.Args.Add(ParseExpr);
            end;
          end;
          Expect(tkRParen);
          Result := FCallNode;
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
