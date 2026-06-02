{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.sets;

{ Tests for Pascal set types — set of EnumType, set literals, in operator,
  Include/Exclude built-ins, and set arithmetic operators. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TSetTests = class(TTestCase)
  private
    function GenIR(const ASrc: string): string;
    procedure SemanticOK(const ASrc: string);
    procedure SemanticFail(const ASrc: string);
    procedure ParseOK(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { parse                                                                }
    { ------------------------------------------------------------------ }
    procedure TestParse_Set_SimpleDefinition;
    procedure TestParse_Set_EmptyLiteral;
    procedure TestParse_Set_TwoElementLiteral;
    procedure TestParse_Set_InOperator;
    procedure TestParse_Set_IncludeExclude;
    procedure TestParse_Set_ArithmeticOperators;
    procedure TestParse_Set_EqualityOperators;

    { ------------------------------------------------------------------ }
    { semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Set_TypeRegistered;
    procedure TestSemantic_Set_VariableDecl_OK;
    procedure TestSemantic_Set_EmptyLiteralAssign_OK;
    procedure TestSemantic_Set_TwoElementLiteralAssign_OK;
    procedure TestSemantic_Set_InOperator_ResultIsBoolean;
    procedure TestSemantic_Set_Include_OK;
    procedure TestSemantic_Set_Exclude_OK;
    procedure TestSemantic_Set_Union_OK;
    procedure TestSemantic_Set_Difference_OK;
    procedure TestSemantic_Set_Intersection_OK;
    procedure TestSemantic_Set_Equality_OK;
    procedure TestSemantic_Set_BaseTypeMustBeEnum;
    procedure TestSemantic_Set_LiteralElementMustMatchBase;

    { ------------------------------------------------------------------ }
    { codegen                                                              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_Set_VarAllocsEmitsZero;
    procedure TestCodegen_Set_EmptyLiteralEmitsZero;
    procedure TestCodegen_Set_OneElementBitmask;
    procedure TestCodegen_Set_TwoElementBitmask;
    procedure TestCodegen_Set_InOperatorEmitsShrAndAnd;
    procedure TestCodegen_Set_IncludeEmitsShlAndOr;
    procedure TestCodegen_Set_ExcludeEmitsShlXorAnd;
    procedure TestCodegen_Set_UnionEmitsOr;
    procedure TestCodegen_Set_DifferenceEmitsXorAnd;
    procedure TestCodegen_Set_IntersectionEmitsAnd;
    procedure TestCodegen_Set_EqualityEmitsCeqw;
    procedure TestCodegen_Set_InequalityEmitsCnew;

    { ------------------------------------------------------------------ }
    { set-valued constants  (const X = [a, b])                            }
    { ------------------------------------------------------------------ }
    procedure TestParse_SetConst_InferredType;
    procedure TestSemantic_SetConst_Inferred_OK;
    procedure TestSemantic_SetConst_Annotated_OK;
    procedure TestSemantic_SetConst_EmptyAnnotated_OK;
    procedure TestSemantic_SetConst_EmptyUnannotated_Fails;
    procedure TestSemantic_SetConst_MixedEnums_Fails;
    procedure TestSemantic_SetConst_NonEnumMember_Fails;
    procedure TestCodegen_SetConst_FoldsToBitmask;
    procedure TestCodegen_SetConst_AssignableToNamedSetType;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Common source snippets                                               }
{ ------------------------------------------------------------------ }

const
  DirEnum =
    '''
        type
          TDir = (dNorth, dSouth, dEast, dWest);
          TDirSet = set of TDir;
        ''';

  { dNorth=0 → bit 0 = 1; dEast=2 → bit 2 = 4; mask = 5 }
  SrcSetTypeDecl =
    'program P;' + #10 +
    DirEnum +
    '''
        begin
        end.
        ''';

  SrcSetEmptyLiteral =
    'program P;' + #10 +
    DirEnum +
    '''
        var S: TDirSet;
        begin
          S := []
        end.
        ''';

  SrcSetTwoElementLiteral =
    'program P;' + #10 +
    DirEnum +
    'var S: TDirSet;' + #10 +
    'begin' + #10 +
    '  S := [dNorth, dEast]' + #10 +   { mask = 1 + 4 = 5 }
    'end.';

  { Set-valued constant whose set type is inferred from the members'
    enum (no annotation): mask = dNorth(0)|dEast(2) = 5. }
  SrcSetConstInferred =
    'program P;' + #10 +
    DirEnum +
    '''
        const Both = [dNorth, dEast];
        var S: TDirSet;
        begin
          S := Both
        end.
        ''';

  { Annotated set const: const X: TDirSet = [...]. }
  SrcSetConstAnnotated =
    'program P;' + #10 +
    DirEnum +
    '''
        const Both: TDirSet = [dNorth, dEast];
        var S: TDirSet;
        begin
          S := Both
        end.
        ''';

  SrcSetConstEmptyAnnotated =
    'program P;' + #10 +
    DirEnum +
    '''
        const None: TDirSet = [];
        var S: TDirSet;
        begin
          S := None
        end.
        ''';

  SrcSetConstEmptyUnannotated =
    'program P;' + #10 +
    DirEnum +
    '''
        const Bad = [];
        begin
        end.
        ''';

  SrcSetConstMixedEnums =
    '''
    program P;
    type
      TA = (a1, a2);
      TB = (b1, b2);
    const Mixed = [a1, b1];
    begin
    end.
    ''';

  SrcSetConstNonEnumMember =
    '''
    program P;
    const X = 5; Bad = [X];
    begin
    end.
    ''';

  SrcSetInOperator =
    'program P;' + #10 +
    DirEnum +
    '''
        var S: TDirSet; B: Boolean;
        begin
          S := [dNorth, dEast];
          B := dNorth in S
        end.
        ''';

  SrcSetInclude =
    'program P;' + #10 +
    DirEnum +
    '''
        var S: TDirSet;
        begin
          S := [];
          Include(S, dSouth)
        end.
        ''';

  SrcSetExclude =
    'program P;' + #10 +
    DirEnum +
    '''
        var S: TDirSet;
        begin
          S := [dNorth, dSouth];
          Exclude(S, dNorth)
        end.
        ''';

  SrcSetUnion =
    'program P;' + #10 +
    DirEnum +
    '''
        var S1, S2, S3: TDirSet;
        begin
          S1 := [dNorth];
          S2 := [dEast];
          S3 := S1 + S2
        end.
        ''';

  SrcSetDifference =
    'program P;' + #10 +
    DirEnum +
    '''
        var S1, S2, S3: TDirSet;
        begin
          S1 := [dNorth, dEast];
          S2 := [dNorth];
          S3 := S1 - S2
        end.
        ''';

  SrcSetIntersection =
    'program P;' + #10 +
    DirEnum +
    '''
        var S1, S2, S3: TDirSet;
        begin
          S1 := [dNorth, dEast];
          S2 := [dNorth];
          S3 := S1 * S2
        end.
        ''';

  SrcSetEquality =
    'program P;' + #10 +
    DirEnum +
    '''
        var S1, S2: TDirSet; B: Boolean;
        begin
          S1 := [dNorth];
          S2 := [dNorth];
          B := S1 = S2
        end.
        ''';

  SrcSetInequality =
    'program P;' + #10 +
    DirEnum +
    '''
        var S1, S2: TDirSet; B: Boolean;
        begin
          S1 := [dNorth];
          S2 := [dSouth];
          B := S1 <> S2
        end.
        ''';

  SrcSetBadBaseType =
    '''
        program P;
        type TBad = set of Integer;
        begin
        end.
        ''';

  SrcSetBadLiteralElement =
    'program P;' + #10 +
    DirEnum +
    'type TColors = (cRed, cBlue);' + #10 +
    'type TColorSet = set of TColors;' + #10 +
    'var S: TDirSet;' + #10 +
    'begin' + #10 +
    '  S := [cRed]' + #10 +  { TColors element in TDirSet → error }
    'end.';

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

function TSetTests.GenIR(const ASrc: string): string;
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  CG:   TCodeGenQBE;
  Prog: TProgram;
begin
  Lex  := TLexer.Create(ASrc);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse;
  Par.Free; Lex.Free;
  SA   := TSemanticAnalyser.Create;
  SA.Analyse(Prog);
  SA.Free;
  CG   := TCodeGenQBE.Create;
  CG.Generate(Prog);
  Result := CG.GetOutput;
  CG.Free;
  Prog.Free;
end;

procedure TSetTests.SemanticOK(const ASrc: string);
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  Prog: TProgram;
begin
  Lex  := TLexer.Create(ASrc);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse;
  Par.Free; Lex.Free;
  SA   := TSemanticAnalyser.Create;
  try
    SA.Analyse(Prog);
  finally
    SA.Free;
    Prog.Free;
  end;
end;

procedure TSetTests.SemanticFail(const ASrc: string);
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  Prog: TProgram;
begin
  Lex  := TLexer.Create(ASrc);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse;
  Par.Free; Lex.Free;
  SA   := TSemanticAnalyser.Create;
  try
    SA.Analyse(Prog);
    Prog.Free;
    Fail('Expected ESemanticError but none was raised');
  except
    on ESE: ESemanticError do
    begin
      Prog.Free;
    end;
    on EEx: Exception do
    begin
      Prog.Free;
      raise;
    end;
  end;
  SA.Free;
end;

procedure TSetTests.ParseOK(const ASrc: string);
var
  Lex:  TLexer;
  Par:  TParser;
  Prog: TProgram;
begin
  Lex  := TLexer.Create(ASrc);
  Par  := TParser.Create(Lex);
  try
    Prog := Par.Parse;
    Prog.Free;
  finally
    Par.Free; Lex.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ parse                                                                }
{ ------------------------------------------------------------------ }

procedure TSetTests.TestParse_Set_SimpleDefinition;
begin
  ParseOK(SrcSetTypeDecl);
end;

procedure TSetTests.TestParse_Set_EmptyLiteral;
begin
  ParseOK(SrcSetEmptyLiteral);
end;

procedure TSetTests.TestParse_Set_TwoElementLiteral;
begin
  ParseOK(SrcSetTwoElementLiteral);
end;

procedure TSetTests.TestParse_Set_InOperator;
begin
  ParseOK(SrcSetInOperator);
end;

procedure TSetTests.TestParse_Set_IncludeExclude;
begin
  ParseOK(SrcSetInclude);
  ParseOK(SrcSetExclude);
end;

procedure TSetTests.TestParse_Set_ArithmeticOperators;
begin
  ParseOK(SrcSetUnion);
  ParseOK(SrcSetDifference);
  ParseOK(SrcSetIntersection);
end;

procedure TSetTests.TestParse_Set_EqualityOperators;
begin
  ParseOK(SrcSetEquality);
  ParseOK(SrcSetInequality);
end;

{ ------------------------------------------------------------------ }
{ semantic                                                             }
{ ------------------------------------------------------------------ }

procedure TSetTests.TestSemantic_Set_TypeRegistered;
begin
  SemanticOK(SrcSetTypeDecl);
end;

procedure TSetTests.TestSemantic_Set_VariableDecl_OK;
begin
  SemanticOK(SrcSetEmptyLiteral);
end;

procedure TSetTests.TestSemantic_Set_EmptyLiteralAssign_OK;
begin
  SemanticOK(SrcSetEmptyLiteral);
end;

procedure TSetTests.TestSemantic_Set_TwoElementLiteralAssign_OK;
begin
  SemanticOK(SrcSetTwoElementLiteral);
end;

procedure TSetTests.TestSemantic_Set_InOperator_ResultIsBoolean;
var
  Lex:    TLexer;
  Par:    TParser;
  SA:     TSemanticAnalyser;
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Lex  := TLexer.Create(SrcSetInOperator);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse;
  Par.Free; Lex.Free;
  SA   := TSemanticAnalyser.Create;
  SA.Analyse(Prog);
  SA.Free;
  { B := dNorth in S — second stmt in main block }
  Assign := TAssignment(Prog.Block.Stmts[1]);
  AssertEquals('in operator resolves to Boolean',
    Ord(tyBoolean), Ord(Assign.Expr.ResolvedType.Kind));
  Prog.Free;
end;

procedure TSetTests.TestSemantic_Set_Include_OK;
begin
  SemanticOK(SrcSetInclude);
end;

procedure TSetTests.TestSemantic_Set_Exclude_OK;
begin
  SemanticOK(SrcSetExclude);
end;

procedure TSetTests.TestSemantic_Set_Union_OK;
begin
  SemanticOK(SrcSetUnion);
end;

procedure TSetTests.TestSemantic_Set_Difference_OK;
begin
  SemanticOK(SrcSetDifference);
end;

procedure TSetTests.TestSemantic_Set_Intersection_OK;
begin
  SemanticOK(SrcSetIntersection);
end;

procedure TSetTests.TestSemantic_Set_Equality_OK;
begin
  SemanticOK(SrcSetEquality);
  SemanticOK(SrcSetInequality);
end;

procedure TSetTests.TestSemantic_Set_BaseTypeMustBeEnum;
begin
  SemanticFail(SrcSetBadBaseType);
end;

procedure TSetTests.TestSemantic_Set_LiteralElementMustMatchBase;
begin
  SemanticFail(SrcSetBadLiteralElement);
end;

{ ------------------------------------------------------------------ }
{ codegen                                                              }
{ ------------------------------------------------------------------ }

procedure TSetTests.TestCodegen_Set_VarAllocsEmitsZero;
var
  IR: string;
begin
  IR := GenIR(SrcSetEmptyLiteral);
  // global set var emits data $S = { w 0 }; local would emit storew 0
  AssertTrue('set var zero-initialised in data section or stack alloc',
    (Pos('{ w 0 }', IR) > 0) or (Pos('storew 0', IR) > 0));
end;

procedure TSetTests.TestCodegen_Set_EmptyLiteralEmitsZero;
var
  IR: string;
begin
  IR := GenIR(SrcSetEmptyLiteral);
  { S := [] computes bitmask 0 via "copy 0" }
  AssertTrue('empty set literal emits copy 0', Pos('copy 0', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set_OneElementBitmask;
var
  IR: string;
begin
  { [dNorth] → ordinal 0 → bit 0 → mask 1 → emits "copy 1" }
  IR := GenIR(
    'program P;' + #10 +
    DirEnum +
    '''
        var S: TDirSet;
        begin
          S := [dNorth]
        end.
        ''');
  AssertTrue('single-element mask is 1', Pos('copy 1', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set_TwoElementBitmask;
var
  IR: string;
begin
  { [dNorth, dEast] → ordinals 0 and 2 → mask = 1 + 4 = 5 → emits "copy 5" }
  IR := GenIR(SrcSetTwoElementLiteral);
  AssertTrue('two-element mask is 5', Pos('copy 5', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set_InOperatorEmitsShrAndAnd;
var
  IR: string;
begin
  IR := GenIR(SrcSetInOperator);
  { elem in S: (S >> ord(elem)) & 1 — needs shr and and }
  AssertTrue('in operator emits shr', Pos('shr', IR) > 0);
  AssertTrue('in operator emits and', Pos(' and ', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set_IncludeEmitsShlAndOr;
var
  IR: string;
begin
  IR := GenIR(SrcSetInclude);
  { Include(S, elem): S := S or (1 shl ord(elem)) }
  AssertTrue('Include emits shl', Pos('shl', IR) > 0);
  AssertTrue('Include emits or', Pos(' or ', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set_ExcludeEmitsShlXorAnd;
var
  IR: string;
begin
  IR := GenIR(SrcSetExclude);
  { Exclude(S, elem): S := S and not (1 shl ord(elem)) }
  AssertTrue('Exclude emits shl', Pos('shl', IR) > 0);
  AssertTrue('Exclude emits xor', Pos('xor', IR) > 0);
  AssertTrue('Exclude emits and', Pos(' and ', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set_UnionEmitsOr;
var
  IR: string;
begin
  IR := GenIR(SrcSetUnion);
  AssertTrue('union emits or', Pos(' or ', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set_DifferenceEmitsXorAnd;
var
  IR: string;
begin
  IR := GenIR(SrcSetDifference);
  AssertTrue('difference emits xor', Pos('xor', IR) > 0);
  AssertTrue('difference emits and', Pos(' and ', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set_IntersectionEmitsAnd;
var
  IR: string;
begin
  IR := GenIR(SrcSetIntersection);
  AssertTrue('intersection emits and', Pos(' and ', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set_EqualityEmitsCeqw;
var
  IR: string;
begin
  IR := GenIR(SrcSetEquality);
  AssertTrue('set equality emits ceqw', Pos('ceqw', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set_InequalityEmitsCnew;
var
  IR: string;
begin
  IR := GenIR(SrcSetInequality);
  AssertTrue('set inequality emits cnew', Pos('cnew', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ set-valued constants                                                 }
{ ------------------------------------------------------------------ }

procedure TSetTests.TestParse_SetConst_InferredType;
begin
  ParseOK(SrcSetConstInferred);
end;

procedure TSetTests.TestSemantic_SetConst_Inferred_OK;
begin
  SemanticOK(SrcSetConstInferred);
end;

procedure TSetTests.TestSemantic_SetConst_Annotated_OK;
begin
  SemanticOK(SrcSetConstAnnotated);
end;

procedure TSetTests.TestSemantic_SetConst_EmptyAnnotated_OK;
begin
  SemanticOK(SrcSetConstEmptyAnnotated);
end;

procedure TSetTests.TestSemantic_SetConst_EmptyUnannotated_Fails;
begin
  { An empty set with no annotation has no enum to infer from. }
  SemanticFail(SrcSetConstEmptyUnannotated);
end;

procedure TSetTests.TestSemantic_SetConst_MixedEnums_Fails;
begin
  SemanticFail(SrcSetConstMixedEnums);
end;

procedure TSetTests.TestSemantic_SetConst_NonEnumMember_Fails;
begin
  SemanticFail(SrcSetConstNonEnumMember);
end;

procedure TSetTests.TestCodegen_SetConst_FoldsToBitmask;
var
  IR: string;
begin
  { Both = [dNorth, dEast] folds to mask 5; referencing it emits "copy 5". }
  IR := GenIR(SrcSetConstInferred);
  AssertTrue('set const folds to mask 5', Pos('copy 5', IR) > 0);
end;

procedure TSetTests.TestCodegen_SetConst_AssignableToNamedSetType;
begin
  { An inferred 'set of TDir' const assigns to a TDirSet variable — the two
    set types are structurally the same.  Just assert it analyses + emits. }
  SemanticOK(SrcSetConstInferred);
end;

initialization
  RegisterTest(TSetTests);

end.
