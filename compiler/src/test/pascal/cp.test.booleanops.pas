{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

unit cp.test.booleanops;

{$mode objfpc}{$H+}

{ Tests for the AND / OR / NOT logical operators on Boolean operands. }

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TBooleanOpsTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    procedure TestLexer_And_Keyword;
    procedure TestLexer_Or_Keyword;
    procedure TestLexer_Not_Keyword;
    procedure TestParse_And_IsBinaryExpr;
    procedure TestParse_Or_IsBinaryExpr;
    procedure TestParse_Not_IsNotExpr;
    procedure TestSemantic_And_TypeIsBoolean;
    procedure TestSemantic_Or_TypeIsBoolean;
    procedure TestSemantic_Not_TypeIsBoolean;
    procedure TestSemantic_And_IntOperand_RaisesError;
    procedure TestSemantic_Not_IntOperand_RaisesError;
    procedure TestCodegen_And_EmitsAnd;
    procedure TestCodegen_Or_EmitsOr;
    procedure TestCodegen_Not_EmitsXor;
  end;

implementation

function TBooleanOpsTests.ParseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try Result := P.Parse; finally P.Free; L.Free; end;
end;

function TBooleanOpsTests.AnalyseSrc(const ASrc: string): TProgram;
var A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create;
  try A.Analyse(Result); finally A.Free; end;
end;

function TBooleanOpsTests.GenIR(const ASrc: string): string;
var Prog: TProgram; CG: TCodeGenQBE;
begin
  Prog := AnalyseSrc(ASrc);
  try
    CG := TCodeGenQBE.Create;
    try CG.Generate(Prog); Result := CG.GetOutput; finally CG.Free; end;
  finally Prog.Free; end;
end;

procedure TBooleanOpsTests.AnalyseExpectError(const ASrc: string);
var Prog: TProgram;
begin
  try
    Prog := AnalyseSrc(ASrc);
    Prog.Free;
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ;
  end;
end;

const
  SrcAnd =
    'program P;'                         + LineEnding +
    'var A, B: Boolean; C: Boolean;'     + LineEnding +
    'begin'                              + LineEnding +
    '  A := True;'                       + LineEnding +
    '  B := False;'                      + LineEnding +
    '  C := A and B'                     + LineEnding +
    'end.';

  SrcOr =
    'program P;'                         + LineEnding +
    'var A, B: Boolean; C: Boolean;'     + LineEnding +
    'begin'                              + LineEnding +
    '  A := True;'                       + LineEnding +
    '  B := False;'                      + LineEnding +
    '  C := A or B'                      + LineEnding +
    'end.';

  SrcNot =
    'program P;'                         + LineEnding +
    'var A: Boolean; C: Boolean;'        + LineEnding +
    'begin'                              + LineEnding +
    '  A := True;'                       + LineEnding +
    '  C := not A'                       + LineEnding +
    'end.';

procedure TBooleanOpsTests.TestLexer_And_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('and');
  try T := L.Next; AssertEquals(Ord(tkAnd), Ord(T.Kind)); finally L.Free; end;
end;

procedure TBooleanOpsTests.TestLexer_Or_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('or');
  try T := L.Next; AssertEquals(Ord(tkOr), Ord(T.Kind)); finally L.Free; end;
end;

procedure TBooleanOpsTests.TestLexer_Not_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('not');
  try T := L.Next; AssertEquals(Ord(tkNot), Ord(T.Kind)); finally L.Free; end;
end;

procedure TBooleanOpsTests.TestParse_And_IsBinaryExpr;
var Prog: TProgram; Assn: TAssignment;
begin
  Prog := ParseSrc(SrcAnd);
  try
    Assn := TAssignment(Prog.Block.Stmts[2]);
    AssertTrue('and is binary expr', Assn.Expr is TBinaryExpr);
    AssertEquals('and op', Ord(boAnd), Ord(TBinaryExpr(Assn.Expr).Op));
  finally Prog.Free; end;
end;

procedure TBooleanOpsTests.TestParse_Or_IsBinaryExpr;
var Prog: TProgram; Assn: TAssignment;
begin
  Prog := ParseSrc(SrcOr);
  try
    Assn := TAssignment(Prog.Block.Stmts[2]);
    AssertTrue(Assn.Expr is TBinaryExpr);
    AssertEquals(Ord(boOr), Ord(TBinaryExpr(Assn.Expr).Op));
  finally Prog.Free; end;
end;

procedure TBooleanOpsTests.TestParse_Not_IsNotExpr;
var Prog: TProgram; Assn: TAssignment;
begin
  Prog := ParseSrc(SrcNot);
  try
    Assn := TAssignment(Prog.Block.Stmts[1]);
    AssertTrue('not is TNotExpr', Assn.Expr is TNotExpr);
  finally Prog.Free; end;
end;

procedure TBooleanOpsTests.TestSemantic_And_TypeIsBoolean;
var Prog: TProgram; Assn: TAssignment;
begin
  Prog := AnalyseSrc(SrcAnd);
  try
    Assn := TAssignment(Prog.Block.Stmts[2]);
    AssertEquals(Ord(tyBoolean), Ord(Assn.Expr.ResolvedType.Kind));
  finally Prog.Free; end;
end;

procedure TBooleanOpsTests.TestSemantic_Or_TypeIsBoolean;
var Prog: TProgram; Assn: TAssignment;
begin
  Prog := AnalyseSrc(SrcOr);
  try
    Assn := TAssignment(Prog.Block.Stmts[2]);
    AssertEquals(Ord(tyBoolean), Ord(Assn.Expr.ResolvedType.Kind));
  finally Prog.Free; end;
end;

procedure TBooleanOpsTests.TestSemantic_Not_TypeIsBoolean;
var Prog: TProgram; Assn: TAssignment;
begin
  Prog := AnalyseSrc(SrcNot);
  try
    Assn := TAssignment(Prog.Block.Stmts[1]);
    AssertEquals(Ord(tyBoolean), Ord(Assn.Expr.ResolvedType.Kind));
  finally Prog.Free; end;
end;

procedure TBooleanOpsTests.TestSemantic_And_IntOperand_RaisesError;
begin
  AnalyseExpectError(
    'program P;'                     + LineEnding +
    'var I, J: Integer; C: Boolean;' + LineEnding +
    'begin'                          + LineEnding +
    '  I := 1; J := 2;'              + LineEnding +
    '  C := I and J'                 + LineEnding +
    'end.');
end;

procedure TBooleanOpsTests.TestSemantic_Not_IntOperand_RaisesError;
begin
  AnalyseExpectError(
    'program P;'                    + LineEnding +
    'var I: Integer; C: Boolean;'   + LineEnding +
    'begin'                         + LineEnding +
    '  I := 1;'                     + LineEnding +
    '  C := not I'                  + LineEnding +
    'end.');
end;

procedure TBooleanOpsTests.TestCodegen_And_EmitsAnd;
var IR: string;
begin
  IR := GenIR(SrcAnd);
  { Short-circuit and: LHS jumps to RHS on non-zero, to end on zero }
  AssertTrue('emits sc_rhs label', Pos('@sc_rhs', IR) > 0);
  AssertTrue('emits sc_end label', Pos('@sc_end', IR) > 0);
end;

procedure TBooleanOpsTests.TestCodegen_Or_EmitsOr;
var IR: string;
begin
  IR := GenIR(SrcOr);
  AssertTrue('emits sc_rhs label', Pos('@sc_rhs', IR) > 0);
  AssertTrue('emits sc_end label', Pos('@sc_end', IR) > 0);
end;

procedure TBooleanOpsTests.TestCodegen_Not_EmitsXor;
var IR: string;
begin
  IR := GenIR(SrcNot);
  AssertTrue('emits xor', Pos('xor ', IR) > 0);
end;

initialization
  RegisterTest(TBooleanOpsTests);

end.
