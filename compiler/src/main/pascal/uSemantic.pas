unit uSemantic;

{$mode objfpc}{$H+}

// Semantic analysis pass — walks the AST produced by uParser and:
//   1. Resolves every identifier to a TSymbol in the symbol table.
//   2. Infers and annotates every expression node with ResolvedType.
//   3. Type-checks assignments (lhs type == rhs type).
//   4. Validates procedure/function calls (callee exists, arg types valid).
//   5. Raises ESemanticError with source position on any violation.

interface

uses
  SysUtils, uAST, uSymbolTable;

type
  ESemanticError = class(Exception);

  TSemanticAnalyser = class
  private
    FTable: TSymbolTable;

    procedure AnalyseBlock(ABlock: TBlock);
    procedure AnalyseVarDecls(ABlock: TBlock);
    procedure AnalyseStmts(ABlock: TBlock);
    procedure AnalyseStmt(AStmt: TASTStmt);
    procedure AnalyseAssignment(AAssign: TAssignment);
    procedure AnalyseProcCall(ACall: TProcCall);
    function  AnalyseExpr(AExpr: TASTExpr): TTypeDesc;
    function  AnalyseBinaryExpr(ABin: TBinaryExpr): TTypeDesc;

    procedure SemanticError(const AMsg: string; ALine, ACol: Integer);
    procedure CheckTypesMatch(AExpected, AActual: TTypeDesc;
      const AContext: string; ALine, ACol: Integer);
  public
    constructor Create;
    destructor Destroy; override;
    procedure Analyse(AProg: TProgram);
  end;

implementation

constructor TSemanticAnalyser.Create;
begin
  inherited Create;
  FTable := TSymbolTable.Create;
end;

destructor TSemanticAnalyser.Destroy;
begin
  FTable.Free;
  inherited Destroy;
end;

procedure TSemanticAnalyser.SemanticError(const AMsg: string; ALine, ACol: Integer);
begin
  raise ESemanticError.CreateFmt('%s at line %d col %d', [AMsg, ALine, ACol]);
end;

procedure TSemanticAnalyser.CheckTypesMatch(AExpected, AActual: TTypeDesc;
  const AContext: string; ALine, ACol: Integer);
begin
  if AExpected <> AActual then
    SemanticError(
      Format('Type mismatch in %s: expected ''%s'' but got ''%s''',
        [AContext, AExpected.Name, AActual.Name]),
      ALine, ACol);
end;

procedure TSemanticAnalyser.Analyse(AProg: TProgram);
begin
  AnalyseBlock(AProg.Block);
  { Transfer symbol table ownership to the program so that TTypeDesc
    objects (referenced by ResolvedType pointers on AST nodes) outlive
    this analyser. }
  AProg.SymbolTable := FTable;
  FTable := nil;
end;

procedure TSemanticAnalyser.AnalyseBlock(ABlock: TBlock);
begin
  FTable.PushScope;
  try
    AnalyseVarDecls(ABlock);
    AnalyseStmts(ABlock);
  finally
    FTable.PopScope;
  end;
end;

procedure TSemanticAnalyser.AnalyseVarDecls(ABlock: TBlock);
var
  I, J:    Integer;
  Decl:    TVarDecl;
  Typ:     TTypeDesc;
  VarName: string;
  Sym:     TSymbol;
begin
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(ABlock.Decls[I]);

    Typ := FTable.FindType(Decl.TypeName);
    if Typ = nil then
      SemanticError(
        Format('Unknown type ''%s''', [Decl.TypeName]),
        Decl.Line, Decl.Col);

    Decl.ResolvedType := Typ;

    for J := 0 to Decl.Names.Count - 1 do
    begin
      VarName := Decl.Names[J];
      Sym := TSymbol.Create(VarName, skVariable, Typ);
      if not FTable.Define(Sym) then
      begin
        Sym.Free;
        SemanticError(
          Format('Duplicate identifier ''%s''', [VarName]),
          Decl.Line, Decl.Col);
      end;
    end;
  end;
end;

procedure TSemanticAnalyser.AnalyseStmts(ABlock: TBlock);
var
  I: Integer;
begin
  for I := 0 to ABlock.Stmts.Count - 1 do
    AnalyseStmt(TASTStmt(ABlock.Stmts[I]));
end;

procedure TSemanticAnalyser.AnalyseStmt(AStmt: TASTStmt);
begin
  if AStmt is TAssignment then
    AnalyseAssignment(TAssignment(AStmt))
  else if AStmt is TProcCall then
    AnalyseProcCall(TProcCall(AStmt));
end;

procedure TSemanticAnalyser.AnalyseAssignment(AAssign: TAssignment);
var
  VarSym:   TSymbol;
  ExprType: TTypeDesc;
begin
  VarSym := FTable.Lookup(AAssign.Name);
  if VarSym = nil then
    SemanticError(
      Format('Undeclared variable ''%s''', [AAssign.Name]),
      AAssign.Line, AAssign.Col);
  if VarSym.Kind <> skVariable then
    SemanticError(
      Format('''%s'' is not a variable', [AAssign.Name]),
      AAssign.Line, AAssign.Col);

  ExprType := AnalyseExpr(AAssign.Expr);
  CheckTypesMatch(VarSym.TypeDesc, ExprType, 'assignment', AAssign.Line, AAssign.Col);
end;

procedure TSemanticAnalyser.AnalyseProcCall(ACall: TProcCall);
var
  Sym: TSymbol;
  I:   Integer;
begin
  Sym := FTable.Lookup(ACall.Name);
  if Sym = nil then
    SemanticError(
      Format('Undeclared procedure ''%s''', [ACall.Name]),
      ACall.Line, ACall.Col);
  if not (Sym.Kind in [skProcedure, skFunction]) then
    SemanticError(
      Format('''%s'' is not a procedure or function', [ACall.Name]),
      ACall.Line, ACall.Col);

  { Analyse argument expressions for type correctness.
    Phase 1 built-ins (Write/WriteLn) accept any single argument —
    detailed overload resolution is a Phase 2 enhancement. }
  for I := 0 to ACall.Args.Count - 1 do
    AnalyseExpr(TASTExpr(ACall.Args[I]));
end;

function TSemanticAnalyser.AnalyseExpr(AExpr: TASTExpr): TTypeDesc;
var
  Sym: TSymbol;
begin
  if AExpr is TIntLiteral then
    Result := FTable.TypeInteger
  else if AExpr is TStringLiteral then
    Result := FTable.TypeString
  else if AExpr is TIdentExpr then
  begin
    Sym := FTable.Lookup(TIdentExpr(AExpr).Name);
    if Sym = nil then
      SemanticError(
        Format('Undeclared identifier ''%s''', [TIdentExpr(AExpr).Name]),
        AExpr.Line, AExpr.Col);
    Result := Sym.TypeDesc;
  end
  else if AExpr is TBinaryExpr then
    Result := AnalyseBinaryExpr(TBinaryExpr(AExpr))
  else
    SemanticError('Unknown expression node', AExpr.Line, AExpr.Col);

  AExpr.ResolvedType := Result;
end;

function TSemanticAnalyser.AnalyseBinaryExpr(ABin: TBinaryExpr): TTypeDesc;
var
  LType, RType: TTypeDesc;
begin
  LType := AnalyseExpr(ABin.Left);
  RType := AnalyseExpr(ABin.Right);

  { Arithmetic operators require both operands to be numeric. }
  if not LType.IsNumeric then
    SemanticError(
      Format('Left operand of ''%s'' must be numeric, got ''%s''',
        [BinaryOpName(ABin.Op), LType.Name]),
      ABin.Line, ABin.Col);
  if not RType.IsNumeric then
    SemanticError(
      Format('Right operand of ''%s'' must be numeric, got ''%s''',
        [BinaryOpName(ABin.Op), RType.Name]),
      ABin.Line, ABin.Col);

  CheckTypesMatch(LType, RType, 'binary expression', ABin.Line, ABin.Col);

  Result := LType;
end;

end.
