{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.codegen;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSemantic, uCodeGenQBE;

type
  TCodeGenTests = class(TTestCase)
  private
    function GenerateIR(const ASrc: string): string;
    function IRContains(const AIR, AFragment: string): Boolean;
  published
    { Data sections }
    procedure TestHelloWorld_HasStrLitData;
    procedure TestHelloWorld_UsesSysWriteStr;

    { Main function structure }
    procedure TestOutput_HasMainFunction;
    procedure TestOutput_HasRetZero;

    { WriteLn }
    procedure TestWriteLn_NoArgs_CallsSysWriteNewline;
    procedure TestWriteLn_StringLit_CallsSysWriteStr;
    procedure TestWriteLn_IntExpr_CallsSysWriteInt;

    { Variables and assignment }
    procedure TestIntVar_HasAlloc;
    procedure TestAssignment_HasStorew;
    procedure TestAssignment_LoadAndStore;

    { Arithmetic }
    procedure TestAdd_EmitsAddInstruction;
    procedure TestMul_EmitsMulInstruction;

    { Header comment }
    procedure TestOutput_HasSourceComment;

    { String equality }
    procedure TestStringEq_EmitsStringEquals;
    procedure TestStringNe_EmitsStringEqualsNegated;
    procedure TestStringEq_SemanticCompiles;

    { True / False built-in constants }
    procedure TestTrue_EmitsCopyOne;
    procedure TestFalse_EmitsCopyZero;
    procedure TestTrue_AssignToBoolVar;
    procedure TestFalse_AssignToBoolVar;
    procedure TestTrue_InIfCondition;
    procedure TestBoolFunc_ReturnTrue;

    { Case-insensitive identifier normalisation }
    procedure TestResult_LowercaseAssign_CompilesOK;
    procedure TestIdent_WrongCase_NormalisedInIR;
  end;

implementation

function TCodeGenTests.GenerateIR(const ASrc: string): string;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  CG: TCodeGenQBE;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse;
  A  := TSemanticAnalyser.Create;
  try
    A.Analyse(Pr);
  finally
    A.Free;
  end;
  CG := TCodeGenQBE.Create;
  try
    CG.Generate(Pr);
    Result := CG.GetOutput;
  finally
    CG.Free;
    Pr.Free;
    P.Free;
    L.Free;
  end;
end;

function TCodeGenTests.IRContains(const AIR, AFragment: string): Boolean;
begin
  Result := Pos(AFragment, AIR) > 0;
end;

{ Data sections }

procedure TCodeGenTests.TestHelloWorld_HasStrLitData;
var
  IR: string;
begin
  IR := GenerateIR('program P; begin WriteLn(''Hello'') end.');
  AssertTrue('Has str data',
    IRContains(IR, 'data $__s0'));
  AssertTrue('Contains Hello',
    IRContains(IR, '"Hello"'));
end;

procedure TCodeGenTests.TestHelloWorld_UsesSysWriteStr;
var
  IR: string;
begin
  IR := GenerateIR('program P; begin WriteLn(''Hello'') end.');
  AssertTrue('Calls _SysWriteStr',
    IRContains(IR, 'call $_SysWriteStr('));
end;

{ Main function structure }

procedure TCodeGenTests.TestOutput_HasMainFunction;
var
  IR: string;
begin
  IR := GenerateIR('program P; begin end.');
  AssertTrue('Has export function $main',
    IRContains(IR, 'export function w $main('));
end;

procedure TCodeGenTests.TestOutput_HasRetZero;
var
  IR: string;
begin
  IR := GenerateIR('program P; begin end.');
  AssertTrue('Has ret 0', IRContains(IR, 'ret 0'));
end;

{ WriteLn }

procedure TCodeGenTests.TestWriteLn_NoArgs_CallsSysWriteNewline;
var
  IR: string;
begin
  IR := GenerateIR('program P; begin WriteLn() end.');
  AssertTrue('Calls _SysWriteNewline',
    IRContains(IR, 'call $_SysWriteNewline(w 1)'));
end;

procedure TCodeGenTests.TestWriteLn_StringLit_CallsSysWriteStr;
var
  IR: string;
begin
  IR := GenerateIR('program P; begin WriteLn(''Hi'') end.');
  AssertTrue('Calls _SysWriteStr with string pointer',
    IRContains(IR, 'call $_SysWriteStr(w 1,'));
  AssertTrue('Calls _SysWriteNewline for line ending',
    IRContains(IR, 'call $_SysWriteNewline(w 1)'));
end;

procedure TCodeGenTests.TestWriteLn_IntExpr_CallsSysWriteInt;
var
  IR: string;
begin
  IR := GenerateIR('program P; begin WriteLn(42) end.');
  AssertTrue('Calls _SysWriteInt',
    IRContains(IR, 'call $_SysWriteInt(w 1,'));
  AssertTrue('Calls _SysWriteNewline for line ending',
    IRContains(IR, 'call $_SysWriteNewline(w 1)'));
end;

{ Variables and assignment }

procedure TCodeGenTests.TestIntVar_HasAlloc;
var
  IR: string;
begin
  IR := GenerateIR('program P; var x: Integer; begin end.');
  { Program-level var is a data-section global, not a stack alloc }
  AssertTrue('Has data decl for x',
    IRContains(IR, 'data $x'));
end;

procedure TCodeGenTests.TestAssignment_HasStorew;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P; var n: Integer; begin n := 7 end.');
  AssertTrue('Has storew', IRContains(IR, 'storew'));
  { Program-level var n is a global: store goes to $n }
  AssertTrue('Stores to n', IRContains(IR, 'storew %_t0, $n'));
end;

procedure TCodeGenTests.TestAssignment_LoadAndStore;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P; var x, y: Integer; begin x := 1; y := x end.');
  { Program-level vars x, y are globals: load/store use $name }
  AssertTrue('Loads x', IRContains(IR, 'loadw $x'));
  AssertTrue('Stores y', IRContains(IR, '$y'));
end;

{ Arithmetic }

procedure TCodeGenTests.TestAdd_EmitsAddInstruction;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P; var n: Integer; begin n := 3 + 4 end.');
  AssertTrue('Has add', IRContains(IR, '=w add'));
end;

procedure TCodeGenTests.TestMul_EmitsMulInstruction;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P; var n: Integer; begin n := 2 * 5 end.');
  AssertTrue('Has mul', IRContains(IR, '=w mul'));
end;

{ Header comment }

procedure TCodeGenTests.TestOutput_HasSourceComment;
var
  IR: string;
begin
  IR := GenerateIR('program MyProg; begin end.');
  AssertTrue('Has source comment',
    IRContains(IR, '# Generated by Blaise Compiler'));
end;

{ String equality }

procedure TCodeGenTests.TestStringEq_EmitsStringEquals;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P;'                                   + LineEnding +
    'var S1, S2: string; B: Boolean;'              + LineEnding +
    'begin'                                        + LineEnding +
    '  B := S1 = S2'                               + LineEnding +
    'end.');
  AssertTrue('Uses _StringEquals', IRContains(IR, '$_StringEquals'));
end;

procedure TCodeGenTests.TestStringNe_EmitsStringEqualsNegated;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P;'                                   + LineEnding +
    'var S1, S2: string; B: Boolean;'              + LineEnding +
    'begin'                                        + LineEnding +
    '  B := S1 <> S2'                              + LineEnding +
    'end.');
  AssertTrue('Uses _StringEquals for <>', IRContains(IR, '$_StringEquals'));
end;

procedure TCodeGenTests.TestStringEq_SemanticCompiles;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P;'                                   + LineEnding +
    'function Same(A, B: string): Boolean;'        + LineEnding +
    'begin'                                        + LineEnding +
    '  Result := A = B'                            + LineEnding +
    'end;'                                         + LineEnding +
    'var B: Boolean;'                              + LineEnding +
    'begin'                                        + LineEnding +
    '  B := Same(''hello'', ''world'')'            + LineEnding +
    'end.');
  AssertTrue('Compiles', Length(IR) > 0);
  AssertTrue('Uses _StringEquals', IRContains(IR, '$_StringEquals'));
end;

{ True / False built-in constants }

procedure TCodeGenTests.TestTrue_EmitsCopyOne;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P; var B: Boolean; begin B := True end.');
  AssertTrue('True emits copy 1', IRContains(IR, 'copy 1'));
end;

procedure TCodeGenTests.TestFalse_EmitsCopyZero;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P; var B: Boolean; begin B := False end.');
  AssertTrue('False emits copy 0', IRContains(IR, 'copy 0'));
end;

procedure TCodeGenTests.TestTrue_AssignToBoolVar;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P; var B: Boolean; begin B := True end.');
  AssertTrue('Compiles to IR', Length(IR) > 0);
end;

procedure TCodeGenTests.TestFalse_AssignToBoolVar;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P; var B: Boolean; begin B := False end.');
  AssertTrue('Compiles to IR', Length(IR) > 0);
end;

procedure TCodeGenTests.TestTrue_InIfCondition;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P; var N: Integer; begin if True then N := 1 end.');
  AssertTrue('Compiles to IR', Length(IR) > 0);
  AssertTrue('Has conditional branch', IRContains(IR, 'jnz'));
end;

procedure TCodeGenTests.TestBoolFunc_ReturnTrue;
var
  IR: string;
begin
  IR := GenerateIR(
    'program P;'                                   + LineEnding +
    'function IsOK: Boolean;'                      + LineEnding +
    'begin'                                        + LineEnding +
    '  Result := True'                             + LineEnding +
    'end;'                                         + LineEnding +
    'var B: Boolean;'                              + LineEnding +
    'begin'                                        + LineEnding +
    '  B := IsOK'                                  + LineEnding +
    'end.');
  AssertTrue('IsOK function emitted', IRContains(IR, '$IsOK'));
  AssertTrue('True emits copy 1', IRContains(IR, 'copy 1'));
end;

procedure TCodeGenTests.TestResult_LowercaseAssign_CompilesOK;
var
  IR: string;
begin
  { 'result' (lowercase) must resolve to the same slot as 'Result' and
    produce valid QBE — regression test for the case-normalisation bug
    reported in https://github.com/graemeg/blaise/discussions/15 }
  IR := GenerateIR(
    'program P;'                                   + LineEnding +
    'function MyAdd(X, Y: Integer): Integer;'      + LineEnding +
    'begin'                                        + LineEnding +
    '  result := X + Y'                            + LineEnding +
    'end;'                                         + LineEnding +
    'var Z: Integer;'                              + LineEnding +
    'begin'                                        + LineEnding +
    '  Z := MyAdd(2, 3)'                           + LineEnding +
    'end.');
  AssertTrue('storew to Result slot (canonical casing)',
    IRContains(IR, 'storew %_t'));
  AssertFalse('no mis-cased %_var_result slot',
    IRContains(IR, '%_var_result ='));
end;

procedure TCodeGenTests.TestIdent_WrongCase_NormalisedInIR;
var
  IR: string;
begin
  { Reading a variable with wrong casing must use the declared slot name }
  IR := GenerateIR(
    'program P;'                                   + LineEnding +
    'var N: Integer;'                              + LineEnding +
    'begin'                                        + LineEnding +
    '  n := 42'                                    + LineEnding +
    'end.');
  AssertTrue('canonical $N global used', IRContains(IR, '$N'));
  AssertFalse('no mis-cased $n global', IRContains(IR, '$n ='));
end;

initialization
  RegisterTest(TCodeGenTests);

end.
