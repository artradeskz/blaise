{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.procs;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TProcFuncTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_StandaloneProc_InProcDecls;
    procedure TestParse_StandaloneProc_Name;
    procedure TestParse_StandaloneProc_Params;
    procedure TestParse_StandaloneProc_ParamName;
    procedure TestParse_StandaloneProc_ParamTypeName;
    procedure TestParse_StandaloneProc_Body;
    procedure TestParse_StandaloneFunc_InProcDecls;
    procedure TestParse_StandaloneFunc_Name;
    procedure TestParse_StandaloneFunc_ReturnTypeName;
    procedure TestParse_ProcCall_IsTProcCall;
    procedure TestParse_FuncCall_Expr_IsTFuncCallExpr;
    procedure TestParse_FuncCall_Expr_Name;
    procedure TestParse_FuncCall_Expr_ArgCount;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_StandaloneProc_Resolves;
    procedure TestSemantic_StandaloneFunc_Resolves;
    procedure TestSemantic_ProcCall_WrongArgCount_RaisesError;
    procedure TestSemantic_ProcCall_ArgTypeMismatch_RaisesError;
    procedure TestSemantic_FuncCall_ReturnsCorrectType;
    procedure TestSemantic_StandaloneFunc_ResultVar_Available;
    procedure TestSemantic_UnknownProc_RaisesError;
    procedure TestSemantic_Proc_CanCallOtherProc;

    { ------------------------------------------------------------------ }
    { Code generation                                                      }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_StandaloneProc_EmitsFunction;
    procedure TestCodegen_StandaloneFunc_EmitsFunctionWithRetType;
    procedure TestCodegen_StandaloneProc_NoSelfParam;
    procedure TestCodegen_StandaloneFunc_HasResultVar;
    procedure TestCodegen_ProcCall_EmitsCall;
    procedure TestCodegen_FuncCall_EmitsTypedCall;
    procedure TestCodegen_Proc_ParamAccessible;

    { Regression: float-typed parameter spill must use stored/stores
      (matching the QBE 'd'/'s' parameter type), not storel — QBE
      rejects 'storel %_par_D' for a 'd %_par_D' parameter. }
    procedure TestCodegen_DoubleParam_SpillsWithStored;
    procedure TestCodegen_SingleParam_SpillsWithStores;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TProcFuncTests.ParseSrc(const ASrc: string): TProgram;
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

function TProcFuncTests.AnalyseSrc(const ASrc: string): TProgram;
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

function TProcFuncTests.GenIR(const ASrc: string): string;
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

procedure TProcFuncTests.AnalyseExpectError(const ASrc: string);
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
{ Shared source snippets                                               }
{ ------------------------------------------------------------------ }

const
  SrcWithProc =
    'program P;'                          + LineEnding +
    'var N: Integer;'                     + LineEnding +
    'procedure PrintIt(X: Integer);'      + LineEnding +
    'begin'                               + LineEnding +
    '  WriteLn(X)'                        + LineEnding +
    'end;'                                + LineEnding +
    'begin'                               + LineEnding +
    '  N := 7;'                           + LineEnding +
    '  PrintIt(N)'                        + LineEnding +
    'end.';

  SrcWithFunc =
    'program P;'                          + LineEnding +
    'var N: Integer;'                     + LineEnding +
    'function Add(A, B: Integer): Integer;' + LineEnding +
    'begin'                               + LineEnding +
    '  Result := A + B'                   + LineEnding +
    'end;'                                + LineEnding +
    'begin'                               + LineEnding +
    '  N := Add(3, 4)'                    + LineEnding +
    'end.';

  SrcTwoProcs =
    'program P;'                          + LineEnding +
    'var N: Integer;'                     + LineEnding +
    'procedure Inner(X: Integer);'        + LineEnding +
    'begin'                               + LineEnding +
    '  WriteLn(X)'                        + LineEnding +
    'end;'                                + LineEnding +
    'procedure Outer(Y: Integer);'        + LineEnding +
    'begin'                               + LineEnding +
    '  Inner(Y)'                          + LineEnding +
    'end;'                                + LineEnding +
    'begin'                               + LineEnding +
    '  N := 1;'                           + LineEnding +
    '  Outer(N)'                          + LineEnding +
    'end.';

{ ------------------------------------------------------------------ }
{ Parser tests                                                        }
{ ------------------------------------------------------------------ }

procedure TProcFuncTests.TestParse_StandaloneProc_InProcDecls;
var
  Prog: TProgram;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    AssertEquals('one proc decl', 1, Prog.Block.ProcDecls.Count);
  finally
    Prog.Free;
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneProc_Name;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('proc name', 'PrintIt', MD.Name);
  finally
    Prog.Free;
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneProc_Params;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('one param', 1, MD.Params.Count);
  finally
    Prog.Free;
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneProc_ParamName;
var
  Prog: TProgram;
  MD:   TMethodDecl;
  Par:  TMethodParam;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    MD  := TMethodDecl(Prog.Block.ProcDecls[0]);
    Par := TMethodParam(MD.Params[0]);
    AssertEquals('param name', 'X', Par.ParamName);
  finally
    Prog.Free;
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneProc_ParamTypeName;
var
  Prog: TProgram;
  MD:   TMethodDecl;
  Par:  TMethodParam;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    MD  := TMethodDecl(Prog.Block.ProcDecls[0]);
    Par := TMethodParam(MD.Params[0]);
    AssertEquals('param type', 'Integer', Par.TypeName);
  finally
    Prog.Free;
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneProc_Body;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertNotNull('body exists', MD.Body);
    AssertEquals('body has 1 stmt', 1, MD.Body.Stmts.Count);
    AssertTrue('stmt is TProcCall', MD.Body.Stmts[0] is TProcCall);
  finally
    Prog.Free;
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneFunc_InProcDecls;
var
  Prog: TProgram;
begin
  Prog := ParseSrc(SrcWithFunc);
  try
    AssertEquals('one proc decl', 1, Prog.Block.ProcDecls.Count);
  finally
    Prog.Free;
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneFunc_Name;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcWithFunc);
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('func name', 'Add', MD.Name);
  finally
    Prog.Free;
  end;
end;

procedure TProcFuncTests.TestParse_StandaloneFunc_ReturnTypeName;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcWithFunc);
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('return type', 'Integer', MD.ReturnTypeName);
  finally
    Prog.Free;
  end;
end;

procedure TProcFuncTests.TestParse_ProcCall_IsTProcCall;
var
  Prog: TProgram;
  Stmt: TASTStmt;
begin
  Prog := ParseSrc(SrcWithProc);
  try
    { second stmt in main body: PrintIt(N) }
    Stmt := TASTStmt(Prog.Block.Stmts[1]);
    AssertTrue('stmt is TProcCall', Stmt is TProcCall);
    AssertEquals('proc name', 'PrintIt', TProcCall(Stmt).Name);
  finally
    Prog.Free;
  end;
end;

procedure TProcFuncTests.TestParse_FuncCall_Expr_IsTFuncCallExpr;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Prog := ParseSrc(SrcWithFunc);
  try
    { N := Add(3, 4) }
    AssertTrue('stmt is TAssignment', Prog.Block.Stmts[0] is TAssignment);
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertTrue('rhs is TFuncCallExpr', Assign.Expr is TFuncCallExpr);
  finally
    Prog.Free;
  end;
end;

procedure TProcFuncTests.TestParse_FuncCall_Expr_Name;
var
  Prog:   TProgram;
  Assign: TAssignment;
  FCall:  TFuncCallExpr;
begin
  Prog := ParseSrc(SrcWithFunc);
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    FCall  := TFuncCallExpr(Assign.Expr);
    AssertEquals('func name', 'Add', FCall.Name);
  finally
    Prog.Free;
  end;
end;

procedure TProcFuncTests.TestParse_FuncCall_Expr_ArgCount;
var
  Prog:   TProgram;
  Assign: TAssignment;
  FCall:  TFuncCallExpr;
begin
  Prog := ParseSrc(SrcWithFunc);
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    FCall  := TFuncCallExpr(Assign.Expr);
    AssertEquals('two args', 2, FCall.Args.Count);
  finally
    Prog.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                      }
{ ------------------------------------------------------------------ }

procedure TProcFuncTests.TestSemantic_StandaloneProc_Resolves;
begin
  AnalyseSrc(SrcWithProc).Free;
end;

procedure TProcFuncTests.TestSemantic_StandaloneFunc_Resolves;
begin
  AnalyseSrc(SrcWithFunc).Free;
end;

procedure TProcFuncTests.TestSemantic_ProcCall_WrongArgCount_RaisesError;
begin
  AnalyseExpectError(
    'program P;'                        + LineEnding +
    'var N: Integer;'                   + LineEnding +
    'procedure Foo(X: Integer);'        + LineEnding +
    'begin'                             + LineEnding +
    '  WriteLn(X)'                      + LineEnding +
    'end;'                              + LineEnding +
    'begin'                             + LineEnding +
    '  Foo(1, 2)'                       + LineEnding +
    'end.');
end;

procedure TProcFuncTests.TestSemantic_ProcCall_ArgTypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    'program P;'                        + LineEnding +
    'var N: Integer;'                   + LineEnding +
    'procedure Foo(X: Integer);'        + LineEnding +
    'begin'                             + LineEnding +
    '  WriteLn(X)'                      + LineEnding +
    'end;'                              + LineEnding +
    'begin'                             + LineEnding +
    '  Foo(''not an int'')'             + LineEnding +
    'end.');
end;

procedure TProcFuncTests.TestSemantic_FuncCall_ReturnsCorrectType;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Prog := AnalyseSrc(SrcWithFunc);
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertNotNull('expr has resolved type', Assign.Expr.ResolvedType);
    AssertEquals('return type is Integer',
      Ord(tyInteger), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TProcFuncTests.TestSemantic_StandaloneFunc_ResultVar_Available;
begin
  { Result := A + B inside the function body must not raise an error }
  AnalyseSrc(SrcWithFunc).Free;
end;

procedure TProcFuncTests.TestSemantic_UnknownProc_RaisesError;
begin
  AnalyseExpectError(
    'program P;'       + LineEnding +
    'begin'            + LineEnding +
    '  NoSuchProc(1)'  + LineEnding +
    'end.');
end;

procedure TProcFuncTests.TestSemantic_Proc_CanCallOtherProc;
begin
  AnalyseSrc(SrcTwoProcs).Free;
end;

{ ------------------------------------------------------------------ }
{ Code generation tests                                               }
{ ------------------------------------------------------------------ }

procedure TProcFuncTests.TestCodegen_StandaloneProc_EmitsFunction;
var
  IR: string;
begin
  IR := GenIR(SrcWithProc);
  AssertTrue('emits $PrintIt function', Pos('$PrintIt', IR) > 0);
  AssertTrue('function keyword present', Pos('function $PrintIt', IR) > 0);
end;

procedure TProcFuncTests.TestCodegen_StandaloneFunc_EmitsFunctionWithRetType;
var
  IR: string;
begin
  IR := GenIR(SrcWithFunc);
  AssertTrue('emits $Add function', Pos('$Add', IR) > 0);
  { function has return type: 'function w $Add(' }
  AssertTrue('function has return qtype', Pos('function w $Add', IR) > 0);
end;

procedure TProcFuncTests.TestCodegen_StandaloneProc_NoSelfParam;
var
  IR: string;
begin
  IR := GenIR(SrcWithProc);
  { Standalone proc should NOT have %_par_Self }
  AssertFalse('no Self param in standalone proc',
    Pos('%_par_Self', IR) > 0);
end;

procedure TProcFuncTests.TestCodegen_StandaloneFunc_HasResultVar;
var
  IR: string;
begin
  IR := GenIR(SrcWithFunc);
  AssertTrue('Result variable slot emitted', Pos('%_var_Result', IR) > 0);
end;

procedure TProcFuncTests.TestCodegen_ProcCall_EmitsCall;
var
  IR: string;
begin
  IR := GenIR(SrcWithProc);
  AssertTrue('call to PrintIt', Pos('call $PrintIt', IR) > 0);
end;

procedure TProcFuncTests.TestCodegen_FuncCall_EmitsTypedCall;
var
  IR: string;
begin
  IR := GenIR(SrcWithFunc);
  { Function call in expression must capture return value: '%t =w call $Add' }
  AssertTrue('typed call to Add', Pos('call $Add', IR) > 0);
  AssertTrue('call captures return value', Pos('=w call $Add', IR) > 0);
end;

procedure TProcFuncTests.TestCodegen_Proc_ParamAccessible;
var
  IR: string;
begin
  IR := GenIR(SrcWithProc);
  { Param X should have a local alloc slot inside PrintIt }
  AssertTrue('param X has local slot', Pos('%_var_X', IR) > 0);
end;

procedure TProcFuncTests.TestCodegen_DoubleParam_SpillsWithStored;
var
  IR: string;
begin
  IR := GenIR(
    'program P;'                                    + LineEnding +
    'procedure F(D: Double);'                       + LineEnding +
    'begin'                                         + LineEnding +
    '  WriteLn(DoubleToStr(D))'                     + LineEnding +
    'end;'                                          + LineEnding +
    'begin F(3.14) end.');
  AssertTrue('Double param spilt with ''stored''',
    Pos('stored %_par_D', IR) > 0);
  AssertFalse('Double param must NOT use ''storel''',
    Pos('storel %_par_D', IR) > 0);
end;

procedure TProcFuncTests.TestCodegen_SingleParam_SpillsWithStores;
var
  IR: string;
begin
  IR := GenIR(
    'program P;'                                    + LineEnding +
    'procedure F(S: Single);'                       + LineEnding +
    'begin'                                         + LineEnding +
    '  WriteLn(SingleToStr(S))'                     + LineEnding +
    'end;'                                          + LineEnding +
    'begin F(1.5) end.');
  AssertTrue('Single param spilt with ''stores''',
    Pos('stores %_par_S', IR) > 0);
  AssertFalse('Single param must NOT use ''storel''',
    Pos('storel %_par_S', IR) > 0);
end;

initialization
  RegisterTest(TProcFuncTests);

end.
