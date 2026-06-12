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
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

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
    procedure TestSemantic_Set_EqualityEmptyLiteral_OK;
    procedure TestSemantic_Set_EqualityLiteral_OK;
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
    procedure TestCodegen_Set_EqualityEmptyLiteralEmitsCeqw;
    procedure TestCodegen_Set_EqualityLiteralEmitsCeqw;

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

    { ------------------------------------------------------------------ }
    { set literal as a call argument                                       }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_SetLiteralArg_OK;
    procedure TestSemantic_SetLiteralArg_Empty_OK;
    procedure TestSemantic_SetLiteralArg_WrongEnum_Fails;
    procedure TestSemantic_EmptyLiteral_NonSetAssign_Fails;
    procedure TestCodegen_SetLiteralArg_FoldsToBitmask;
    procedure TestCodegen_SetParam_SpillsAtWordWidth;

    { ------------------------------------------------------------------ }
    { 64-bit sets (>32 members)                                            }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Set64_TypeRegistered;
    procedure TestSemantic_Set64_TooManyMembers_Fails;
    procedure TestCodegen_Set64_VarAllocsEmitsLongZero;
    procedure TestCodegen_Set64_LiteralEmitsLongMask;
    procedure TestCodegen_Set64_InOperatorUsesLong;
    procedure TestCodegen_Set64_IncludeUsesLong;
    procedure TestCodegen_Set64_ExcludeUsesLong;
    procedure TestCodegen_Set64_UnionUsesLong;
    procedure TestCodegen_Set64_DifferenceUsesLong;
    procedure TestCodegen_Set64_IntersectionUsesLong;
    procedure TestCodegen_Set64_EqualityUsesLong;
    procedure TestCodegen_Set64_InequalityUsesLong;
    procedure TestCodegen_Set64_SizeOfReturns8;
    procedure TestCodegen_Set64_ParamSpillsAtLongWidth;
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

  { A set literal passed directly as a `set of` argument: mask dNorth(0)|
    dEast(2) = 5. }
  SrcSetLiteralArg =
    'program P;' + #10 +
    DirEnum +
    '''
        procedure Take(S: TDirSet);
        begin
          if dNorth in S then Halt(0)
        end;
        begin
          Take([dNorth, dEast])
        end.
        ''';

  SrcSetLiteralArgEmpty =
    'program P;' + #10 +
    DirEnum +
    '''
        procedure Take(S: TDirSet);
        begin
          if dNorth in S then Halt(0)
        end;
        begin
          Take([])
        end.
        ''';

  SrcSetLiteralArgWrongEnum =
    '''
    program P;
    type
      TDir = (dNorth, dEast);
      TDirSet = set of TDir;
      TColor = (cRed, cBlue);
    procedure Take(S: TDirSet);
    begin
    end;
    begin
      Take([cRed])
    end.
    ''';

  SrcEmptyLiteralNonSetAssign =
    '''
    program P;
    var x: Integer;
    begin
      x := []
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

  SrcSetEqualityEmptyLiteral =
    'program P;' + #10 +
    DirEnum +
    '''
        var S: TDirSet; B: Boolean;
        begin
          S := [];
          B := S = []
        end.
        ''';

  SrcSetEqualityLiteral =
    'program P;' + #10 +
    DirEnum +
    '''
        var S: TDirSet; B: Boolean;
        begin
          S := [dNorth, dEast];
          B := S = [dNorth, dEast]
        end.
        ''';

  BigEnum =
    '''
        type
          TBig = (
            X00, X01, X02, X03, X04, X05, X06, X07,
            X08, X09, X10, X11, X12, X13, X14, X15,
            X16, X17, X18, X19, X20, X21, X22, X23,
            X24, X25, X26, X27, X28, X29, X30, X31,
            X32, X33, X34, X35, X36, X37, X38, X39,
            X40, X41, X42, X43, X44, X45, X46, X47);
          TBigSet = set of TBig;
        ''';

  SrcSet64TypeDecl =
    'program P;' + #10 +
    BigEnum +
    '''
        begin
        end.
        ''';

  SrcSet64VarEmpty =
    'program P;' + #10 +
    BigEnum +
    '''
        var S: TBigSet;
        begin
          S := []
        end.
        ''';

  SrcSet64Literal =
    'program P;' + #10 +
    BigEnum +
    '''
        var S: TBigSet;
        begin
          S := [X40]
        end.
        ''';

  SrcSet64InOperator =
    'program P;' + #10 +
    BigEnum +
    '''
        var S: TBigSet; B: Boolean;
        begin
          S := [X40];
          B := X40 in S
        end.
        ''';

  SrcSet64Include =
    'program P;' + #10 +
    BigEnum +
    '''
        var S: TBigSet;
        begin
          S := [];
          Include(S, X40)
        end.
        ''';

  SrcSet64Exclude =
    'program P;' + #10 +
    BigEnum +
    '''
        var S: TBigSet;
        begin
          S := [X40];
          Exclude(S, X40)
        end.
        ''';

  SrcSet64Union =
    'program P;' + #10 +
    BigEnum +
    '''
        var S1, S2, S3: TBigSet;
        begin
          S1 := [X00];
          S2 := [X40];
          S3 := S1 + S2
        end.
        ''';

  SrcSet64Difference =
    'program P;' + #10 +
    BigEnum +
    '''
        var S1, S2, S3: TBigSet;
        begin
          S1 := [X00, X40];
          S2 := [X00];
          S3 := S1 - S2
        end.
        ''';

  SrcSet64Intersection =
    'program P;' + #10 +
    BigEnum +
    '''
        var S1, S2, S3: TBigSet;
        begin
          S1 := [X00, X40];
          S2 := [X40];
          S3 := S1 * S2
        end.
        ''';

  SrcSet64Equality =
    'program P;' + #10 +
    BigEnum +
    '''
        var S1, S2: TBigSet; B: Boolean;
        begin
          S1 := [X40];
          S2 := [X40];
          B := S1 = S2
        end.
        ''';

  SrcSet64Inequality =
    'program P;' + #10 +
    BigEnum +
    '''
        var S1, S2: TBigSet; B: Boolean;
        begin
          S1 := [X40];
          S2 := [X00];
          B := S1 <> S2
        end.
        ''';

  SrcSet64LiteralArg =
    'program P;' + #10 +
    BigEnum +
    '''
        procedure Take(S: TBigSet);
        begin
          if X40 in S then Halt(0)
        end;
        begin
          Take([X40])
        end.
        ''';

  SrcSet64SizeOf =
    'program P;' + #10 +
    BigEnum +
    '''
        var N: Integer;
        begin
          N := SizeOf(TBigSet)
        end.
        ''';

  SrcSetTooManyMembers =
    '''
    program P;
    type
      THuge = (
        A00, A01, A02, A03, A04, A05, A06, A07,
        A08, A09, A10, A11, A12, A13, A14, A15,
        A16, A17, A18, A19, A20, A21, A22, A23,
        A24, A25, A26, A27, A28, A29, A30, A31,
        A32, A33, A34, A35, A36, A37, A38, A39,
        A40, A41, A42, A43, A44, A45, A46, A47,
        A48, A49, A50, A51, A52, A53, A54, A55,
        A56, A57, A58, A59, A60, A61, A62, A63,
        A64);
      THugeSet = set of THuge;
    begin
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
  Prog := Par.Parse();
  Par.Free(); Lex.Free();
  SA   := TSemanticAnalyser.Create();
  SA.Analyse(Prog);
  SA.Free();
  CG   := TCodeGenQBE.Create();
  CG.Generate(Prog);
  Result := CG.GetOutput();
  CG.Free();
  Prog.Free();
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
  Prog := Par.Parse();
  Par.Free(); Lex.Free();
  SA   := TSemanticAnalyser.Create();
  try
    SA.Analyse(Prog);
  finally
    SA.Free();
    Prog.Free();
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
  Prog := Par.Parse();
  Par.Free(); Lex.Free();
  SA   := TSemanticAnalyser.Create();
  try
    SA.Analyse(Prog);
    Prog.Free();
    Fail('Expected ESemanticError but none was raised');
  except
    on ESE: ESemanticError do
    begin
      Prog.Free();
    end;
    on EEx: Exception do
    begin
      Prog.Free();
      raise;
    end;
  end;
  SA.Free();
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
    Prog := Par.Parse();
    Prog.Free();
  finally
    Par.Free(); Lex.Free();
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
  Prog := Par.Parse();
  Par.Free(); Lex.Free();
  SA   := TSemanticAnalyser.Create();
  SA.Analyse(Prog);
  SA.Free();
  { B := dNorth in S — second stmt in main block }
  Assign := TAssignment(Prog.Block.Stmts[1]);
  AssertEquals('in operator resolves to Boolean',
    Ord(tyBoolean), Ord(Assign.Expr.ResolvedType.Kind));
  Prog.Free();
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

procedure TSetTests.TestSemantic_Set_EqualityEmptyLiteral_OK;
begin
  { S = [] must not crash the semantic pass (was nil-deref before fix). }
  SemanticOK(SrcSetEqualityEmptyLiteral);
end;

procedure TSetTests.TestSemantic_Set_EqualityLiteral_OK;
begin
  { S = [dNorth, dEast] — literal RHS coerced to the set type of LHS. }
  SemanticOK(SrcSetEqualityLiteral);
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

procedure TSetTests.TestCodegen_Set_EqualityEmptyLiteralEmitsCeqw;
var
  IR: string;
begin
  { S = [] coerces [] to the set type of S; bitmask 0 vs S — still ceqw. }
  IR := GenIR(SrcSetEqualityEmptyLiteral);
  AssertTrue('S = [] emits ceqw', Pos('ceqw', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set_EqualityLiteralEmitsCeqw;
var
  IR: string;
begin
  { S = [dNorth, dEast] coerces the literal to mask 5; comparison is ceqw. }
  IR := GenIR(SrcSetEqualityLiteral);
  AssertTrue('S = [dNorth, dEast] emits ceqw', Pos('ceqw', IR) > 0);
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

{ ------------------------------------------------------------------ }
{ set literal as a call argument                                       }
{ ------------------------------------------------------------------ }

procedure TSetTests.TestSemantic_SetLiteralArg_OK;
begin
  { Take([dNorth, dEast]) resolves the set-literal argument against the
    `set of TDir` parameter. }
  SemanticOK(SrcSetLiteralArg);
end;

procedure TSetTests.TestSemantic_SetLiteralArg_Empty_OK;
begin
  { An empty literal [] matches any set parameter. }
  SemanticOK(SrcSetLiteralArgEmpty);
end;

procedure TSetTests.TestSemantic_SetLiteralArg_WrongEnum_Fails;
begin
  { [cRed] (a TColor set constructor) does not match a `set of TDir`. }
  SemanticFail(SrcSetLiteralArgWrongEnum);
end;

procedure TSetTests.TestSemantic_EmptyLiteral_NonSetAssign_Fails;
begin
  { x := [] where x is Integer: empty literal has no set context — a clean
    error, not a crash. }
  SemanticFail(SrcEmptyLiteralNonSetAssign);
end;

procedure TSetTests.TestCodegen_SetLiteralArg_FoldsToBitmask;
var
  IR: string;
begin
  { [dNorth, dEast] at the call site folds to mask 5. }
  IR := GenIR(SrcSetLiteralArg);
  AssertTrue('set literal arg folds to mask 5', Pos('copy 5', IR) > 0);
end;

procedure TSetTests.TestCodegen_SetParam_SpillsAtWordWidth;
var
  IR: string;
begin
  { A ≤32-member set parameter is a w; its prologue spill must use storew, not
    storel (which QBE rejects for a w operand). }
  IR := GenIR(SrcSetLiteralArg);
  AssertTrue('set param spilled with storew', Pos('storew %_par_S', IR) > 0);
  AssertFalse('set param not spilled with storel', Pos('storel %_par_S', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ 64-bit sets (>32 members)                                            }
{ ------------------------------------------------------------------ }

procedure TSetTests.TestSemantic_Set64_TypeRegistered;
begin
  SemanticOK(SrcSet64TypeDecl);
end;

procedure TSetTests.TestSemantic_Set64_TooManyMembers_Fails;
begin
  SemanticFail(SrcSetTooManyMembers);
end;

procedure TSetTests.TestCodegen_Set64_VarAllocsEmitsLongZero;
var
  IR: string;
begin
  IR := GenIR(SrcSet64VarEmpty);
  AssertTrue('64-bit set var zero-initialised with l 0',
    (Pos('{ l 0 }', IR) > 0) or (Pos('storel 0', IR) > 0));
end;

procedure TSetTests.TestCodegen_Set64_LiteralEmitsLongMask;
var
  IR: string;
begin
  { [X40] -> bit 40 -> mask = 1099511627776 = Int64(1) shl 40 }
  IR := GenIR(SrcSet64Literal);
  AssertTrue('64-bit set literal emits =l copy',
    Pos('=l copy 1099511627776', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set64_InOperatorUsesLong;
var
  IR: string;
begin
  IR := GenIR(SrcSet64InOperator);
  AssertTrue('in operator on 64-bit set uses =l shr',
    Pos('=l shr', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set64_IncludeUsesLong;
var
  IR: string;
begin
  IR := GenIR(SrcSet64Include);
  AssertTrue('Include on 64-bit set uses loadl', Pos('loadl', IR) > 0);
  AssertTrue('Include on 64-bit set uses =l shl', Pos('=l shl', IR) > 0);
  AssertTrue('Include on 64-bit set uses =l or', Pos('=l or', IR) > 0);
  AssertTrue('Include on 64-bit set uses storel', Pos('storel', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set64_ExcludeUsesLong;
var
  IR: string;
begin
  IR := GenIR(SrcSet64Exclude);
  AssertTrue('Exclude on 64-bit set uses loadl', Pos('loadl', IR) > 0);
  AssertTrue('Exclude on 64-bit set uses =l shl', Pos('=l shl', IR) > 0);
  AssertTrue('Exclude on 64-bit set uses =l xor', Pos('=l xor', IR) > 0);
  AssertTrue('Exclude on 64-bit set uses =l and', Pos('=l and', IR) > 0);
  AssertTrue('Exclude on 64-bit set uses storel', Pos('storel', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set64_UnionUsesLong;
var
  IR: string;
begin
  IR := GenIR(SrcSet64Union);
  AssertTrue('union on 64-bit set uses =l or', Pos('=l or', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set64_DifferenceUsesLong;
var
  IR: string;
begin
  IR := GenIR(SrcSet64Difference);
  AssertTrue('difference on 64-bit set uses =l xor', Pos('=l xor', IR) > 0);
  AssertTrue('difference on 64-bit set uses =l and', Pos('=l and', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set64_IntersectionUsesLong;
var
  IR: string;
begin
  IR := GenIR(SrcSet64Intersection);
  AssertTrue('intersection on 64-bit set uses =l and', Pos('=l and', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set64_EqualityUsesLong;
var
  IR: string;
begin
  IR := GenIR(SrcSet64Equality);
  AssertTrue('64-bit set equality uses ceql', Pos('ceql', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set64_InequalityUsesLong;
var
  IR: string;
begin
  IR := GenIR(SrcSet64Inequality);
  AssertTrue('64-bit set inequality uses cnel', Pos('cnel', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set64_SizeOfReturns8;
var
  IR: string;
begin
  IR := GenIR(SrcSet64SizeOf);
  AssertTrue('SizeOf(TBigSet) emits copy 8', Pos('copy 8', IR) > 0);
end;

procedure TSetTests.TestCodegen_Set64_ParamSpillsAtLongWidth;
var
  IR: string;
begin
  IR := GenIR(SrcSet64LiteralArg);
  AssertTrue('64-bit set param spilled with storel', Pos('storel %_par_S', IR) > 0);
  AssertFalse('64-bit set param not spilled with storew', Pos('storew %_par_S', IR) > 0);
end;

initialization
  RegisterTest(TSetTests);

end.
