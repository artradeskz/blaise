unit cp.test.semantic;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TSemanticTests = class(TTestCase)
  private
    function Analyse(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { Variable declarations are added to the symbol table }
    procedure TestVarDecl_RegistersSymbol;
    procedure TestVarDecl_Type_Integer;
    procedure TestVarDecl_Type_String;
    procedure TestVarDecl_MultiName_BothRegistered;
    procedure TestVarDecl_UnknownType_RaisesError;
    procedure TestVarDecl_Duplicate_RaisesError;

    { Expression type inference }
    procedure TestExpr_IntLiteral_TypeIsInteger;
    procedure TestExpr_StringLiteral_TypeIsString;
    procedure TestExpr_Ident_ResolvesToVarType;
    procedure TestExpr_Ident_Undeclared_RaisesError;
    procedure TestExpr_Add_TwoIntegers_TypeIsInteger;
    procedure TestExpr_Add_IntAndString_RaisesError;
    procedure TestExpr_Sub_TypeIsInteger;
    procedure TestExpr_Mul_TypeIsInteger;
    procedure TestExpr_Div_TypeIsInteger;

    { Assignment type checking }
    procedure TestAssign_IntToInt_OK;
    procedure TestAssign_StringToString_OK;
    procedure TestAssign_IntToString_RaisesError;
    procedure TestAssign_StringToInt_RaisesError;
    procedure TestAssign_UndeclaredVar_RaisesError;

    { Procedure calls }
    procedure TestProcCall_WriteLn_NoArgs_OK;
    procedure TestProcCall_WriteLn_StringArg_OK;
    procedure TestProcCall_WriteLn_IntArg_OK;
    procedure TestProcCall_UndeclaredProc_RaisesError;

    { Full program analysis }
    procedure TestProgram_HelloWorld_OK;
    procedure TestProgram_ArithmeticAndPrint_OK;
  end;

implementation

function TSemanticTests.Analyse(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
  A: TSemanticAnalyser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse;
  finally
    P.Free;
    L.Free;
  end;
  A := TSemanticAnalyser.Create;
  try
    A.Analyse(Result);
  finally
    A.Free;
  end;
end;

procedure TSemanticTests.AnalyseExpectError(const ASrc: string);
var
  Prog: TProgram;
begin
  try
    Prog := Analyse(ASrc);
    Prog.Free;
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ; { expected }
  end;
end;

{ ------------------------------------------------------------------ }
{ Var declarations                                                    }
{ ------------------------------------------------------------------ }

procedure TSemanticTests.TestVarDecl_RegistersSymbol;
var
  Prog: TProgram;
  Decl: TVarDecl;
begin
  Prog := Analyse('program P; var x: Integer; begin end.');
  try
    AssertEquals('1 decl', 1, Prog.Block.Decls.Count);
    Decl := TVarDecl(Prog.Block.Decls[0]);
    AssertNotNull('ResolvedType set', Decl.ResolvedType);
  finally
    Prog.Free;
  end;
end;

procedure TSemanticTests.TestVarDecl_Type_Integer;
var
  Prog: TProgram;
begin
  Prog := Analyse('program P; var n: Integer; begin end.');
  try
    AssertEquals('Integer kind',
      Ord(tyInteger),
      Ord(TVarDecl(Prog.Block.Decls[0]).ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TSemanticTests.TestVarDecl_Type_String;
var
  Prog: TProgram;
begin
  Prog := Analyse('program P; var s: string; begin end.');
  try
    AssertEquals('string kind',
      Ord(tyString),
      Ord(TVarDecl(Prog.Block.Decls[0]).ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TSemanticTests.TestVarDecl_MultiName_BothRegistered;
var
  Prog: TProgram;
  Decl: TVarDecl;
begin
  Prog := Analyse('program P; var x, y: Integer; begin end.');
  try
    Decl := TVarDecl(Prog.Block.Decls[0]);
    AssertNotNull('ResolvedType', Decl.ResolvedType);
    AssertEquals('Integer', Ord(tyInteger), Ord(Decl.ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TSemanticTests.TestVarDecl_UnknownType_RaisesError;
begin
  AnalyseExpectError('program P; var x: Foobar; begin end.');
end;

procedure TSemanticTests.TestVarDecl_Duplicate_RaisesError;
begin
  AnalyseExpectError(
    'program P; var x: Integer; x: string; begin end.');
end;

{ ------------------------------------------------------------------ }
{ Expression type inference                                           }
{ ------------------------------------------------------------------ }

procedure TSemanticTests.TestExpr_IntLiteral_TypeIsInteger;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Prog := Analyse('program P; var n: Integer; begin n := 42 end.');
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertNotNull('Expr type', Assign.Expr.ResolvedType);
    AssertEquals('Integer',
      Ord(tyInteger), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TSemanticTests.TestExpr_StringLiteral_TypeIsString;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Prog := Analyse(
    'program P; var s: string; begin s := ''hello'' end.');
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertEquals('string',
      Ord(tyString), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TSemanticTests.TestExpr_Ident_ResolvesToVarType;
var
  Prog: TProgram;
  Bin:  TBinaryExpr;
begin
  Prog := Analyse(
    'program P; var x, y: Integer; begin y := x + 1 end.');
  try
    Bin := TBinaryExpr(TAssignment(Prog.Block.Stmts[0]).Expr);
    AssertNotNull('Left type', Bin.Left.ResolvedType);
    AssertEquals('x is Integer',
      Ord(tyInteger), Ord(Bin.Left.ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TSemanticTests.TestExpr_Ident_Undeclared_RaisesError;
begin
  AnalyseExpectError(
    'program P; var n: Integer; begin n := undeclared end.');
end;

procedure TSemanticTests.TestExpr_Add_TwoIntegers_TypeIsInteger;
var
  Prog: TProgram;
  Bin:  TBinaryExpr;
begin
  Prog := Analyse(
    'program P; var n: Integer; begin n := 1 + 2 end.');
  try
    Bin := TBinaryExpr(TAssignment(Prog.Block.Stmts[0]).Expr);
    AssertEquals('Add result is Integer',
      Ord(tyInteger), Ord(Bin.ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TSemanticTests.TestExpr_Add_IntAndString_RaisesError;
begin
  AnalyseExpectError(
    'program P; var n: Integer; s: string; begin n := n + s end.');
end;

procedure TSemanticTests.TestExpr_Sub_TypeIsInteger;
var
  Prog: TProgram;
  Bin:  TBinaryExpr;
begin
  Prog := Analyse(
    'program P; var n: Integer; begin n := 10 - 3 end.');
  try
    Bin := TBinaryExpr(TAssignment(Prog.Block.Stmts[0]).Expr);
    AssertEquals('Sub is Integer',
      Ord(tyInteger), Ord(Bin.ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TSemanticTests.TestExpr_Mul_TypeIsInteger;
var
  Prog: TProgram;
  Bin:  TBinaryExpr;
begin
  Prog := Analyse(
    'program P; var n: Integer; begin n := 3 * 4 end.');
  try
    Bin := TBinaryExpr(TAssignment(Prog.Block.Stmts[0]).Expr);
    AssertEquals('Mul is Integer',
      Ord(tyInteger), Ord(Bin.ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TSemanticTests.TestExpr_Div_TypeIsInteger;
var
  Prog: TProgram;
  Bin:  TBinaryExpr;
begin
  Prog := Analyse(
    'program P; var n: Integer; begin n := 8 div 2 end.');
  try
    Bin := TBinaryExpr(TAssignment(Prog.Block.Stmts[0]).Expr);
    AssertEquals('Div is Integer',
      Ord(tyInteger), Ord(Bin.ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Assignment type checking                                            }
{ ------------------------------------------------------------------ }

procedure TSemanticTests.TestAssign_IntToInt_OK;
begin
  Analyse('program P; var n: Integer; begin n := 5 end.').Free;
end;

procedure TSemanticTests.TestAssign_StringToString_OK;
begin
  Analyse(
    'program P; var s: string; begin s := ''hi'' end.').Free;
end;

procedure TSemanticTests.TestAssign_IntToString_RaisesError;
begin
  AnalyseExpectError(
    'program P; var s: string; begin s := 42 end.');
end;

procedure TSemanticTests.TestAssign_StringToInt_RaisesError;
begin
  AnalyseExpectError(
    'program P; var n: Integer; begin n := ''hello'' end.');
end;

procedure TSemanticTests.TestAssign_UndeclaredVar_RaisesError;
begin
  AnalyseExpectError(
    'program P; begin ghost := 1 end.');
end;

{ ------------------------------------------------------------------ }
{ Procedure calls                                                     }
{ ------------------------------------------------------------------ }

procedure TSemanticTests.TestProcCall_WriteLn_NoArgs_OK;
begin
  Analyse('program P; begin WriteLn end.').Free;
end;

procedure TSemanticTests.TestProcCall_WriteLn_StringArg_OK;
begin
  Analyse('program P; begin WriteLn(''Hello'') end.').Free;
end;

procedure TSemanticTests.TestProcCall_WriteLn_IntArg_OK;
begin
  Analyse('program P; begin WriteLn(99) end.').Free;
end;

procedure TSemanticTests.TestProcCall_UndeclaredProc_RaisesError;
begin
  AnalyseExpectError('program P; begin NoSuchProc end.');
end;

{ ------------------------------------------------------------------ }
{ Full programs                                                       }
{ ------------------------------------------------------------------ }

procedure TSemanticTests.TestProgram_HelloWorld_OK;
begin
  Analyse(
    'program Hello;'            + LineEnding +
    'begin'                     + LineEnding +
    '  WriteLn(''Hello!'');'    + LineEnding +
    'end.'
  ).Free;
end;

procedure TSemanticTests.TestProgram_ArithmeticAndPrint_OK;
begin
  Analyse(
    'program Arith;'                        + LineEnding +
    'var n: Integer;'                       + LineEnding +
    'begin'                                 + LineEnding +
    '  n := 3 * 4 + 2;'                    + LineEnding +
    '  WriteLn(n);'                         + LineEnding +
    'end.'
  ).Free;
end;

initialization
  RegisterTest(TSemanticTests);

end.
