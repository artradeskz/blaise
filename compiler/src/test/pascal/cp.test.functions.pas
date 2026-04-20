unit cp.test.functions;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TFunctionTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Lexer                                                                }
    { ------------------------------------------------------------------ }
    procedure TestLexer_Function_Keyword;

    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_FunctionMethod_InClass;
    procedure TestParse_FunctionMethod_Name;
    procedure TestParse_FunctionMethod_ReturnTypeName;
    procedure TestParse_FunctionMethod_WithParams;
    procedure TestParse_FunctionCall_Expr;
    procedure TestParse_FunctionCall_Expr_ObjectName;
    procedure TestParse_FunctionCall_Expr_WithArgs;
    procedure TestParse_FunctionCall_Expr_ArgCount;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_FunctionReturn_TypeResolved;
    procedure TestSemantic_FunctionCall_Resolves;
    procedure TestSemantic_FunctionCall_ReturnTypeAssign_OK;
    procedure TestSemantic_FunctionCall_ReturnTypeMismatch_RaisesError;
    procedure TestSemantic_FunctionCall_WrongArgCount_RaisesError;
    procedure TestSemantic_Result_AvailableInBody;
    procedure TestSemantic_Result_WrongType_RaisesError;

    { ------------------------------------------------------------------ }
    { Code generation                                                      }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_Function_EmitsReturnType;
    procedure TestCodegen_Function_ReturnTypeW;
    procedure TestCodegen_Function_HasResultVar;
    procedure TestCodegen_FunctionCall_EmitsCall;
    procedure TestCodegen_FunctionCall_ResultLoaded;
    procedure TestCodegen_Function_ReturnsResult;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TFunctionTests.ParseSrc(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse;
  finally
    P.Free;
    L.Free;
  end;
end;

function TFunctionTests.AnalyseSrc(const ASrc: string): TProgram;
var
  A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create;
  try
    A.Analyse(Result);
  finally
    A.Free;
  end;
end;

function TFunctionTests.GenIR(const ASrc: string): string;
var
  Prog: TProgram;
  CG:   TCodeGenQBE;
begin
  Prog := AnalyseSrc(ASrc);
  try
    CG := TCodeGenQBE.Create;
    try
      CG.Generate(Prog);
      Result := CG.GetOutput;
    finally
      CG.Free;
    end;
  finally
    Prog.Free;
  end;
end;

procedure TFunctionTests.AnalyseExpectError(const ASrc: string);
var
  Prog: TProgram;
begin
  try
    Prog := AnalyseSrc(ASrc);
    Prog.Free;
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ;
  end;
end;

{ ------------------------------------------------------------------ }
{ Shared source snippets                                              }
{ ------------------------------------------------------------------ }

const
  SrcGetterClass =
    'program P;'                               + LineEnding +
    'type'                                     + LineEnding +
    '  TBox = class'                           + LineEnding +
    '    Value: Integer;'                      + LineEnding +
    '    procedure SetValue(AVal: Integer);'   + LineEnding +
    '    begin'                                + LineEnding +
    '      Self.Value := AVal'                 + LineEnding +
    '    end;'                                 + LineEnding +
    '    function GetValue: Integer;'          + LineEnding +
    '    begin'                                + LineEnding +
    '      Result := Self.Value'               + LineEnding +
    '    end;'                                 + LineEnding +
    '  end;'                                   + LineEnding +
    'var B: TBox; N: Integer;'                 + LineEnding +
    'begin'                                    + LineEnding +
    '  B := TBox.Create;'                      + LineEnding +
    '  B.SetValue(42);'                        + LineEnding +
    '  N := B.GetValue()'                      + LineEnding +
    'end.';

  SrcAdderClass =
    'program P;'                               + LineEnding +
    'type'                                     + LineEnding +
    '  TCalc = class'                          + LineEnding +
    '    function Add(A: Integer; B: Integer): Integer;' + LineEnding +
    '    begin'                                + LineEnding +
    '      Result := A + B'                   + LineEnding +
    '    end;'                                 + LineEnding +
    '  end;'                                   + LineEnding +
    'var C: TCalc; N: Integer;'                + LineEnding +
    'begin'                                    + LineEnding +
    '  C := TCalc.Create;'                     + LineEnding +
    '  N := C.Add(3, 4)'                       + LineEnding +
    'end.';

{ ------------------------------------------------------------------ }
{ Lexer                                                               }
{ ------------------------------------------------------------------ }

procedure TFunctionTests.TestLexer_Function_Keyword;
var
  L: TLexer;
  T: TToken;
begin
  L := TLexer.Create('function');
  try
    T := L.Next;
    AssertEquals('function token', Ord(tkFunction), Ord(T.Kind));
  finally
    L.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser                                                              }
{ ------------------------------------------------------------------ }

procedure TFunctionTests.TestParse_FunctionMethod_InClass;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(SrcGetterClass);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('two methods (proc + func)', 2, CD.Methods.Count);
  finally
    Prog.Free;
  end;
end;

procedure TFunctionTests.TestParse_FunctionMethod_Name;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcGetterClass);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MD := TMethodDecl(CD.Methods[1]);  { second method = GetValue }
    AssertEquals('func name', 'GetValue', MD.Name);
  finally
    Prog.Free;
  end;
end;

procedure TFunctionTests.TestParse_FunctionMethod_ReturnTypeName;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcGetterClass);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MD := TMethodDecl(CD.Methods[1]);
    AssertEquals('return type name', 'Integer', MD.ReturnTypeName);
  finally
    Prog.Free;
  end;
end;

procedure TFunctionTests.TestParse_FunctionMethod_WithParams;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcAdderClass);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MD := TMethodDecl(CD.Methods[0]);
    AssertEquals('two params', 2, MD.Params.Count);
    AssertEquals('return type', 'Integer', MD.ReturnTypeName);
  finally
    Prog.Free;
  end;
end;

procedure TFunctionTests.TestParse_FunctionCall_Expr;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Prog := ParseSrc(SrcGetterClass);
  try
    { third stmt: N := B.GetValue() }
    Assign := TAssignment(Prog.Block.Stmts[2]);
    AssertTrue('RHS is TMethodCallExpr', Assign.Expr is TMethodCallExpr);
  finally
    Prog.Free;
  end;
end;

procedure TFunctionTests.TestParse_FunctionCall_Expr_ObjectName;
var
  Prog: TProgram;
  Expr: TMethodCallExpr;
begin
  Prog := ParseSrc(SrcGetterClass);
  try
    Expr := TMethodCallExpr(TAssignment(Prog.Block.Stmts[2]).Expr);
    AssertEquals('object name', 'B', Expr.ObjectName);
    AssertEquals('method name', 'GetValue', Expr.Name);
  finally
    Prog.Free;
  end;
end;

procedure TFunctionTests.TestParse_FunctionCall_Expr_WithArgs;
var
  Prog:   TProgram;
  Assign: TAssignment;
  Expr:   TMethodCallExpr;
begin
  Prog := ParseSrc(SrcAdderClass);
  try
    { second stmt: N := C.Add(3, 4) }
    Assign := TAssignment(Prog.Block.Stmts[1]);
    AssertTrue('RHS is TMethodCallExpr', Assign.Expr is TMethodCallExpr);
    Expr := TMethodCallExpr(Assign.Expr);
    AssertEquals('object', 'C', Expr.ObjectName);
    AssertEquals('method', 'Add', Expr.Name);
  finally
    Prog.Free;
  end;
end;

procedure TFunctionTests.TestParse_FunctionCall_Expr_ArgCount;
var
  Prog: TProgram;
  Expr: TMethodCallExpr;
begin
  Prog := ParseSrc(SrcAdderClass);
  try
    Expr := TMethodCallExpr(TAssignment(Prog.Block.Stmts[1]).Expr);
    AssertEquals('two args', 2, Expr.Args.Count);
  finally
    Prog.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic                                                            }
{ ------------------------------------------------------------------ }

procedure TFunctionTests.TestSemantic_FunctionReturn_TypeResolved;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  MD:   TMethodDecl;
begin
  Prog := AnalyseSrc(SrcGetterClass);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MD := TMethodDecl(CD.Methods[1]);
    AssertNotNull('return type resolved', MD.ResolvedReturnType);
    AssertEquals('return type is Integer',
      Ord(tyInteger), Ord(MD.ResolvedReturnType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TFunctionTests.TestSemantic_FunctionCall_Resolves;
begin
  AnalyseSrc(SrcGetterClass).Free;
end;

procedure TFunctionTests.TestSemantic_FunctionCall_ReturnTypeAssign_OK;
begin
  AnalyseSrc(SrcGetterClass).Free;
end;

procedure TFunctionTests.TestSemantic_FunctionCall_ReturnTypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    'program P;'                              + LineEnding +
    'type'                                    + LineEnding +
    '  TFoo = class'                          + LineEnding +
    '    function GetVal: Integer;'           + LineEnding +
    '    begin'                               + LineEnding +
    '      Result := 1'                       + LineEnding +
    '    end;'                                + LineEnding +
    '  end;'                                  + LineEnding +
    'var F: TFoo; S: string;'                 + LineEnding +
    'begin'                                   + LineEnding +
    '  F := TFoo.Create;'                     + LineEnding +
    '  S := F.GetVal()'                       + LineEnding +
    'end.');
end;

procedure TFunctionTests.TestSemantic_FunctionCall_WrongArgCount_RaisesError;
begin
  AnalyseExpectError(
    'program P;'                              + LineEnding +
    'type'                                    + LineEnding +
    '  TFoo = class'                          + LineEnding +
    '    function GetVal: Integer;'           + LineEnding +
    '    begin'                               + LineEnding +
    '      Result := 0'                       + LineEnding +
    '    end;'                                + LineEnding +
    '  end;'                                  + LineEnding +
    'var F: TFoo; N: Integer;'                + LineEnding +
    'begin'                                   + LineEnding +
    '  F := TFoo.Create;'                     + LineEnding +
    '  N := F.GetVal(1)'                      + LineEnding +
    'end.');
end;

procedure TFunctionTests.TestSemantic_Result_AvailableInBody;
begin
  { If Result is not in scope, analysing it as an identifier would raise
    an ESemanticError. A clean pass proves Result is defined. }
  AnalyseSrc(
    'program P;'                              + LineEnding +
    'type'                                    + LineEnding +
    '  TFoo = class'                          + LineEnding +
    '    function GetOne: Integer;'           + LineEnding +
    '    begin'                               + LineEnding +
    '      Result := 1'                       + LineEnding +
    '    end;'                                + LineEnding +
    '  end;'                                  + LineEnding +
    'var F: TFoo; N: Integer;'                + LineEnding +
    'begin'                                   + LineEnding +
    '  F := TFoo.Create;'                     + LineEnding +
    '  N := F.GetOne()'                       + LineEnding +
    'end.'
  ).Free;
end;

procedure TFunctionTests.TestSemantic_Result_WrongType_RaisesError;
begin
  AnalyseExpectError(
    'program P;'                              + LineEnding +
    'type'                                    + LineEnding +
    '  TFoo = class'                          + LineEnding +
    '    function GetInt: Integer;'           + LineEnding +
    '    begin'                               + LineEnding +
    '      Result := ''not an int'''          + LineEnding +
    '    end;'                                + LineEnding +
    '  end;'                                  + LineEnding +
    'begin end.');
end;

{ ------------------------------------------------------------------ }
{ Code generation                                                     }
{ ------------------------------------------------------------------ }

procedure TFunctionTests.TestCodegen_Function_EmitsReturnType;
var
  IR: string;
begin
  IR := GenIR(SrcGetterClass);
  AssertTrue('function keyword with return type',
    Pos('function w $TBox_GetValue', IR) > 0);
end;

procedure TFunctionTests.TestCodegen_Function_ReturnTypeW;
var
  IR: string;
begin
  IR := GenIR(SrcAdderClass);
  AssertTrue('Add returns w (Integer)',
    Pos('function w $TCalc_Add', IR) > 0);
end;

procedure TFunctionTests.TestCodegen_Function_HasResultVar;
var
  IR: string;
begin
  IR := GenIR(SrcGetterClass);
  AssertTrue('_var_Result allocated',
    Pos('%_var_Result', IR) > 0);
end;

procedure TFunctionTests.TestCodegen_FunctionCall_EmitsCall;
var
  IR: string;
begin
  IR := GenIR(SrcGetterClass);
  AssertTrue('call to TBox_GetValue',
    Pos('call $TBox_GetValue', IR) > 0);
end;

procedure TFunctionTests.TestCodegen_FunctionCall_ResultLoaded;
var
  IR: string;
begin
  IR := GenIR(SrcGetterClass);
  { The call result is assigned into a temp and then stored into %_var_N }
  AssertTrue('result stored into N',
    Pos('%_var_N', IR) > 0);
end;

procedure TFunctionTests.TestCodegen_Function_ReturnsResult;
var
  IR: string;
begin
  IR := GenIR(SrcGetterClass);
  { Function must emit 'ret %_tN' (not just 'ret') }
  AssertTrue('function has ret with value',
    Pos('ret %_t', IR) > 0);
end;

initialization
  RegisterTest(TFunctionTests);

end.
