{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.varparams;

{$mode objfpc}{$H+}

{ Tests for var parameters: pass-by-reference semantics across
  lexer, parser, semantic analysis, and code generation. }

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TVarParamTests = class(TTestCase)
  private
    function  ParseSrc(const ASrc: string): TProgram;
    function  AnalyseSrc(const ASrc: string): TProgram;
    function  GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_VarParam_IsVarParam;
    procedure TestParse_VarParam_MultiInGroup;
    procedure TestParse_VarParam_Mixed_VarAndValue;
    procedure TestParse_VarParam_ValueParam_IsNotVar;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_VarParam_OK;
    procedure TestSemantic_VarParam_NonVariable_RaisesError;
    procedure TestSemantic_VarParam_TypeMismatch_RaisesError;

    { ------------------------------------------------------------------ }
    { Codegen                                                              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_VarParam_SignatureUsesPointerType;
    procedure TestCodegen_VarParam_CallPassesAddress;
    procedure TestCodegen_VarParam_WriteStoresThroughPointer;
    procedure TestCodegen_VarParam_ReadDereferencesPointer;
    procedure TestCodegen_VarParam_Swap;
    { Var-param forwarding: passing a var param directly to another var param }
    procedure TestCodegen_VarParam_ForwardToProc;
    procedure TestCodegen_VarParam_ForwardToMethod;

    { L-value var args beyond simple identifiers: a record-field access
      (R.F) and a pointer-deref-then-field (P^.F) must both be accepted
      where the parameter is var-typed. }
    procedure TestSemantic_VarParam_FieldAccess_OK;
    procedure TestSemantic_VarParam_DerefField_OK;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TVarParamTests.ParseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse;
  finally
    P.Free; L.Free;
  end;
end;

function TVarParamTests.AnalyseSrc(const ASrc: string): TProgram;
var A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create;
  try
    A.Analyse(Result);
  finally
    A.Free;
  end;
end;

function TVarParamTests.GenIR(const ASrc: string): string;
var P: TProgram; CG: TCodeGenQBE;
begin
  P := AnalyseSrc(ASrc);
  try
    CG := TCodeGenQBE.Create;
    try
      CG.Generate(P);
      Result := CG.GetOutput;
    finally
      CG.Free;
    end;
  finally
    P.Free;
  end;
end;

procedure TVarParamTests.AnalyseExpectError(const ASrc: string);
var P: TProgram;
begin
  try
    P := AnalyseSrc(ASrc);
    P.Free;
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ;
  end;
end;

{ ------------------------------------------------------------------ }
{ Shared source snippets                                               }
{ ------------------------------------------------------------------ }

const
  SrcVarSet =
    'program VarTest;'                              + LineEnding +
    'procedure SetVal(var X: Integer);'             + LineEnding +
    'begin'                                         + LineEnding +
    '  X := 42'                                     + LineEnding +
    'end;'                                          + LineEnding +
    'var V: Integer;'                               + LineEnding +
    'begin'                                         + LineEnding +
    '  V := 0;'                                     + LineEnding +
    '  SetVal(V)'                                   + LineEnding +
    'end.';

  SrcVarSwap =
    'program SwapTest;'                             + LineEnding +
    'procedure Swap(var A, B: Integer);'            + LineEnding +
    'var T: Integer;'                               + LineEnding +
    'begin'                                         + LineEnding +
    '  T := A;'                                     + LineEnding +
    '  A := B;'                                     + LineEnding +
    '  B := T'                                      + LineEnding +
    'end;'                                          + LineEnding +
    'var X, Y: Integer;'                            + LineEnding +
    'begin'                                         + LineEnding +
    '  X := 1;'                                     + LineEnding +
    '  Y := 2;'                                     + LineEnding +
    '  Swap(X, Y)'                                  + LineEnding +
    'end.';

  SrcMixed =
    'program MixedTest;'                            + LineEnding +
    'procedure P(var A: Integer; B: Integer);'      + LineEnding +
    'begin'                                         + LineEnding +
    '  A := B'                                      + LineEnding +
    'end;'                                          + LineEnding +
    'var X: Integer;'                               + LineEnding +
    'begin'                                         + LineEnding +
    '  P(X, 5)'                                     + LineEnding +
    'end.';

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TVarParamTests.TestParse_VarParam_IsVarParam;
var P: TProgram; MD: TMethodDecl; Par: TMethodParam;
begin
  P := ParseSrc(SrcVarSet);
  try
    MD  := TMethodDecl(P.Block.ProcDecls[0]);  { SetVal }
    Par := TMethodParam(MD.Params[0]);         { var X }
    AssertTrue('X is var param', Par.IsVarParam);
  finally P.Free; end;
end;

procedure TVarParamTests.TestParse_VarParam_MultiInGroup;
var P: TProgram; MD: TMethodDecl;
begin
  P := ParseSrc(SrcVarSwap);
  try
    MD := TMethodDecl(P.Block.ProcDecls[0]);  { Swap }
    AssertTrue('A is var param', TMethodParam(MD.Params[0]).IsVarParam);
    AssertTrue('B is var param', TMethodParam(MD.Params[1]).IsVarParam);
  finally P.Free; end;
end;

procedure TVarParamTests.TestParse_VarParam_Mixed_VarAndValue;
var P: TProgram; MD: TMethodDecl;
begin
  P := ParseSrc(SrcMixed);
  try
    MD := TMethodDecl(P.Block.ProcDecls[0]);  { P(var A; B) }
    AssertTrue('A is var param',    TMethodParam(MD.Params[0]).IsVarParam);
    AssertFalse('B is value param', TMethodParam(MD.Params[1]).IsVarParam);
  finally P.Free; end;
end;

procedure TVarParamTests.TestParse_VarParam_ValueParam_IsNotVar;
var P: TProgram; MD: TMethodDecl;
begin
  P := ParseSrc(
    'program T;'                                    + LineEnding +
    'procedure Q(X: Integer);'                      + LineEnding +
    'begin end;'                                    + LineEnding +
    'begin end.');
  try
    MD := TMethodDecl(P.Block.ProcDecls[0]);
    AssertFalse('X is not var param', TMethodParam(MD.Params[0]).IsVarParam);
  finally P.Free; end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TVarParamTests.TestSemantic_VarParam_OK;
begin
  AnalyseSrc(SrcVarSet).Free;
end;

procedure TVarParamTests.TestSemantic_VarParam_NonVariable_RaisesError;
begin
  AnalyseExpectError(
    'program Bad;'                                  + LineEnding +
    'procedure Inc(var X: Integer);'                + LineEnding +
    'begin X := X + 1 end;'                        + LineEnding +
    'begin'                                         + LineEnding +
    '  Inc(42)'                                     + LineEnding +  { literal, not a variable }
    'end.');
end;

procedure TVarParamTests.TestSemantic_VarParam_TypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    'program Bad;'                                  + LineEnding +
    'procedure SetI(var X: Integer);'               + LineEnding +
    'begin X := 1 end;'                             + LineEnding +
    'var B: Boolean;'                               + LineEnding +
    'begin'                                         + LineEnding +
    '  SetI(B)'                                     + LineEnding +  { wrong type }
    'end.');
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                        }
{ ------------------------------------------------------------------ }

procedure TVarParamTests.TestCodegen_VarParam_SignatureUsesPointerType;
var IR: string;
begin
  IR := GenIR(SrcVarSet);
  { var X: Integer → pointer param, QBE type l }
  AssertTrue('var param uses l type', Pos('l %_par_X', IR) > 0);
end;

procedure TVarParamTests.TestCodegen_VarParam_CallPassesAddress;
var IR: string;
begin
  IR := GenIR(SrcVarSet);
  { SetVal(V) must pass the address of V — V is a global so address is $V }
  AssertTrue('call passes address of V', Pos('call $SetVal(l $V)', IR) > 0);
end;

procedure TVarParamTests.TestCodegen_VarParam_WriteStoresThroughPointer;
var IR: string;
begin
  IR := GenIR(SrcVarSet);
  { X := 42 inside SetVal must load the pointer then store through it }
  AssertTrue('loads pointer for write', Pos('loadl %_var_X', IR) > 0);
  AssertTrue('storew used for Integer write', Pos('storew', IR) > 0);
end;

procedure TVarParamTests.TestCodegen_VarParam_ReadDereferencesPointer;
var IR: string;
begin
  IR := GenIR(SrcVarSwap);
  { T := A inside Swap must load the pointer then load through it }
  AssertTrue('loads pointer for read', Pos('loadl %_var_A', IR) > 0);
end;

procedure TVarParamTests.TestCodegen_VarParam_Swap;
var IR: string;
begin
  IR := GenIR(SrcVarSwap);
  { Both X and Y addresses passed to Swap — X and Y are globals so addresses are $X, $Y }
  AssertTrue('passes address of X', Pos('l $X', IR) > 0);
  AssertTrue('passes address of Y', Pos('l $Y', IR) > 0);
end;

procedure TVarParamTests.TestCodegen_VarParam_ForwardToProc;
var IR: string;
begin
  { A var param forwarded directly to another procedure's var param.
    SetViaCaller(var N) calls SetToFive(N) — N is a var param, so the codegen
    must emit  loadl %_var_N  to get the original caller's address, then pass
    that value.  Passing %_var_N directly (the slot address) is wrong. }
  IR := GenIR(
    'program FwdTest;'                                + LineEnding +
    'procedure SetToFive(var N: Integer);'            + LineEnding +
    'begin N := 5 end;'                               + LineEnding +
    'procedure SetViaCaller(var N: Integer);'         + LineEnding +
    'begin SetToFive(N) end;'                         + LineEnding +
    'var V: Integer;'                                 + LineEnding +
    'begin V := 0; SetViaCaller(V) end.');
  AssertTrue('SetViaCaller must loadl %_var_N to obtain original pointer',
    Pos('loadl %_var_N', IR) > 0);
  AssertFalse('must NOT pass slot address directly',
    Pos('call $SetToFive(l %_var_N)', IR) > 0);
end;

procedure TVarParamTests.TestCodegen_VarParam_ForwardToMethod;
const
  SrcMethodFwd =
    'program MethodFwd;'                              + LineEnding +
    'type'                                            + LineEnding +
    '  THelper = class'                               + LineEnding +
    '    procedure SetVal(var N: Integer);'           + LineEnding +
    '  end;'                                          + LineEnding +
    'procedure THelper.SetVal(var N: Integer);'       + LineEnding +
    'begin N := 7 end;'                               + LineEnding +
    'procedure Wrapper(H: THelper; var N: Integer);'  + LineEnding +
    'begin H.SetVal(N) end;'                          + LineEnding +
    'var H: THelper; V: Integer;'                     + LineEnding +
    'begin'                                           + LineEnding +
    '  H := THelper.Create;'                          + LineEnding +
    '  V := 0;'                                       + LineEnding +
    '  Wrapper(H, V);'                                + LineEnding +
    '  H.Free'                                        + LineEnding +
    'end.';
var IR: string;
begin
  { Wrapper(H: THelper; var N: Integer) calls H.SetVal(N).
    N is a var param so the codegen must emit loadl %_var_N and pass the
    result, not %_var_N itself (which is only the pointer's storage slot). }
  IR := GenIR(SrcMethodFwd);
  AssertTrue('Wrapper must loadl %_var_N for method forwarding',
    Pos('loadl %_var_N', IR) > 0);
  AssertFalse('must NOT pass slot address directly to SetVal',
    Pos('call $THelper_SetVal(l %_var_N)', IR) > 0);
end;

procedure TVarParamTests.TestSemantic_VarParam_FieldAccess_OK;
var
  Prog: TProgram;
begin
  { Pass R.Count (a field access expression) as a var argument.
    Must analyse without error — field accesses are L-values. }
  Prog := AnalyseSrc(
    'program P;'                                            + LineEnding +
    'type'                                                  + LineEnding +
    '  TRec = record Count: Integer; end;'                  + LineEnding +
    'procedure Bump(var N: Integer);'                       + LineEnding +
    'begin Inc(N) end;'                                     + LineEnding +
    'var R: TRec;'                                          + LineEnding +
    'begin'                                                 + LineEnding +
    '  R.Count := 0;'                                       + LineEnding +
    '  Bump(R.Count)'                                       + LineEnding +
    'end.');
  Prog.Free;
end;

procedure TVarParamTests.TestSemantic_VarParam_DerefField_OK;
var
  Prog: TProgram;
begin
  { Pass P^.Count (pointer deref + field) as a var argument. }
  Prog := AnalyseSrc(
    'program P;'                                            + LineEnding +
    'type'                                                  + LineEnding +
    '  TRec = record Count: Integer; end;'                  + LineEnding +
    '  PRec = ^TRec;'                                       + LineEnding +
    'procedure Bump(var N: Integer);'                       + LineEnding +
    'begin Inc(N) end;'                                     + LineEnding +
    'var P: PRec; R: TRec;'                                 + LineEnding +
    'begin'                                                 + LineEnding +
    '  P := @R;'                                            + LineEnding +
    '  P^.Count := 0;'                                      + LineEnding +
    '  Bump(P^.Count)'                                      + LineEnding +
    'end.');
  Prog.Free;
end;

initialization
  RegisterTest(TVarParamTests);

end.
