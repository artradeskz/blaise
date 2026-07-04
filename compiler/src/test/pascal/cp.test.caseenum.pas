{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.caseenum;

{ Tests for case statements and enum types — required for self-hosting.
  The compiler source uses both throughout (TTokenKind, TTypeKind, etc.). }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

type
  TCaseEnumTests = class(TTestCase)
  private
    function GenIR(const ASrc: string): string;
    procedure SemanticOK(const ASrc: string);
    procedure ParseOK(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { case — parse                                                         }
    { ------------------------------------------------------------------ }
    procedure TestParse_Case_SimpleInteger;
    procedure TestParse_Case_WithElse;
    procedure TestParse_Case_MultipleValuesPerBranch;

    { ------------------------------------------------------------------ }
    { case — semantic                                                      }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Case_IntegerSelector_OK;
    procedure TestSemantic_Case_MultipleValues_OK;

    { ------------------------------------------------------------------ }
    { case — codegen                                                       }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_Case_EmitsComparisons;
    procedure TestCodegen_Case_ElseBranch;

    { ------------------------------------------------------------------ }
    { enum — parse                                                         }
    { ------------------------------------------------------------------ }
    procedure TestParse_Enum_SimpleDefinition;
    procedure TestParse_Enum_ThreeMembers;

    { ------------------------------------------------------------------ }
    { enum — semantic                                                      }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Enum_MembersResolveAsConstants;
    procedure TestSemantic_Enum_VariableAssignment_OK;
    procedure TestSemantic_Enum_CompareMembers_OK;

    { ------------------------------------------------------------------ }
    { enum — codegen                                                       }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_Enum_MemberEmitsIntegerCopy;
    procedure TestCodegen_Enum_AssignEmitsStore;

    { ------------------------------------------------------------------ }
    { enum + case integration                                              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_Enum_In_Case_Compiles;

    { ------------------------------------------------------------------ }
    { enum — explicit ordinal values                                       }
    { ------------------------------------------------------------------ }
    procedure TestParse_Enum_ExplicitOrdinals;
    procedure TestParse_Enum_PartialExplicitOrdinals;
    procedure TestParse_Enum_ExplicitNegativeOrdinal;
    procedure TestSemantic_Enum_ExplicitOrdinals_CorrectValues;
    procedure TestCodegen_Enum_ExplicitOrdinal_EmitsCorrectCopy;
    procedure TestCodegen_Enum_AutoContinueAfterExplicit;

    { ------------------------------------------------------------------ }
    { case — string selector (Step 11f prerequisite)                       }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_CaseString_AcceptsStringSelector;
    procedure TestSemantic_CaseString_RejectsIntLabelOnStringSelector;
    procedure TestCodegen_CaseString_EmitsStringEqualsCalls;
    procedure TestCodegen_CaseString_OrdinalCaseStillUsesCEQW;
  end;

implementation

const
  SrcCaseSimple =
    '''
        program P;
        var N: Integer;
        begin
          N := 2;
          case N of
            1: WriteLn(1);
            2: WriteLn(2);
            3: WriteLn(3)
          end
        end.
        ''';

  SrcCaseWithElse =
    '''
        program P;
        var N: Integer;
        begin
          N := 5;
          case N of
            1: WriteLn(1);
            2: WriteLn(2)
          else
            WriteLn(99)
          end
        end.
        ''';

  SrcCaseMultiValue =
    '''
        program P;
        var N: Integer;
        begin
          N := 3;
          case N of
            1, 2: WriteLn(12);
            3, 4: WriteLn(34)
          end
        end.
        ''';

  SrcEnumSimple =
    '''
        program P;
        type
          TDir = (dNorth, dSouth, dEast, dWest);
        begin
        end.
        ''';

  SrcEnumAssign =
    '''
        program P;
        type
          TDir = (dNorth, dSouth, dEast, dWest);
        var D: TDir;
        begin
          D := dSouth
        end.
        ''';

  SrcEnumCompare =
    '''
        program P;
        type
          TDir = (dNorth, dSouth);
        var
          D: TDir;
          B: Boolean;
        begin
          D := dNorth;
          B := (D = dNorth)
        end.
        ''';

  SrcEnumInCase =
    '''
        program P;
        type
          TState = (sIdle, sRunning, sDone);
        var
          S: TState;
          N: Integer;
        begin
          S := sRunning;
          case S of
            sIdle:    N := 0;
            sRunning: N := 1;
            sDone:    N := 2
          end
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

function TCaseEnumTests.GenIR(const ASrc: string): string;
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

procedure TCaseEnumTests.SemanticOK(const ASrc: string);
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

procedure TCaseEnumTests.ParseOK(const ASrc: string);
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
{ case — parse                                                         }
{ ------------------------------------------------------------------ }

procedure TCaseEnumTests.TestParse_Case_SimpleInteger;
begin
  ParseOK(SrcCaseSimple);
end;

procedure TCaseEnumTests.TestParse_Case_WithElse;
begin
  ParseOK(SrcCaseWithElse);
end;

procedure TCaseEnumTests.TestParse_Case_MultipleValuesPerBranch;
begin
  ParseOK(SrcCaseMultiValue);
end;

{ ------------------------------------------------------------------ }
{ case — semantic                                                      }
{ ------------------------------------------------------------------ }

procedure TCaseEnumTests.TestSemantic_Case_IntegerSelector_OK;
begin
  SemanticOK(SrcCaseSimple);
end;

procedure TCaseEnumTests.TestSemantic_Case_MultipleValues_OK;
begin
  SemanticOK(SrcCaseMultiValue);
end;

{ ------------------------------------------------------------------ }
{ case — codegen                                                       }
{ ------------------------------------------------------------------ }

procedure TCaseEnumTests.TestCodegen_Case_EmitsComparisons;
var
  IR: string;
begin
  IR := GenIR(SrcCaseSimple);
  { Each branch needs a comparison: ceqw selector, value }
  AssertTrue('case emits ceqw comparisons', Pos('ceqw', IR) > 0);
end;

procedure TCaseEnumTests.TestCodegen_Case_ElseBranch;
var
  IR: string;
begin
  IR := GenIR(SrcCaseWithElse);
  { else branch: jmp to default label }
  AssertTrue('case+else produces IR', Length(IR) > 0);
  AssertTrue('case+else emits ceqw', Pos('ceqw', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ enum — parse                                                         }
{ ------------------------------------------------------------------ }

procedure TCaseEnumTests.TestParse_Enum_SimpleDefinition;
begin
  ParseOK(SrcEnumSimple);
end;

procedure TCaseEnumTests.TestParse_Enum_ThreeMembers;
begin
  ParseOK(SrcEnumAssign);
end;

{ ------------------------------------------------------------------ }
{ enum — semantic                                                      }
{ ------------------------------------------------------------------ }

procedure TCaseEnumTests.TestSemantic_Enum_MembersResolveAsConstants;
var
  Lex:    TLexer;
  Par:    TParser;
  SA:     TSemanticAnalyser;
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Lex  := TLexer.Create(SrcEnumAssign);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse();
  Par.Free(); Lex.Free();
  SA := TSemanticAnalyser.Create();
  SA.Analyse(Prog);
  SA.Free();
  { D := dSouth — the RHS should have tyEnum resolved type }
  Assign := TAssignment(Prog.Block.Stmts[0]);
  AssertEquals('dSouth resolves to enum type',
    Ord(tyEnum), Ord(Assign.Expr.ResolvedType.Kind));
  Prog.Free();
end;

procedure TCaseEnumTests.TestSemantic_Enum_VariableAssignment_OK;
begin
  SemanticOK(SrcEnumAssign);
end;

procedure TCaseEnumTests.TestSemantic_Enum_CompareMembers_OK;
begin
  SemanticOK(SrcEnumCompare);
end;

{ ------------------------------------------------------------------ }
{ enum — codegen                                                       }
{ ------------------------------------------------------------------ }

procedure TCaseEnumTests.TestCodegen_Enum_MemberEmitsIntegerCopy;
var
  IR: string;
begin
  IR := GenIR(SrcEnumAssign);
  { dSouth = ordinal 1 → should emit copy 1 }
  AssertTrue('dSouth emits copy 1', Pos('copy 1', IR) > 0);
end;

procedure TCaseEnumTests.TestCodegen_Enum_AssignEmitsStore;
var
  IR: string;
begin
  IR := GenIR(SrcEnumAssign);
  AssertTrue('enum assign emits storew', Pos('storew', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ enum + case integration                                              }
{ ------------------------------------------------------------------ }

procedure TCaseEnumTests.TestCodegen_Enum_In_Case_Compiles;
var
  IR: string;
begin
  IR := GenIR(SrcEnumInCase);
  AssertTrue('enum-in-case produces IR', Length(IR) > 0);
  AssertTrue('enum-in-case emits ceqw', Pos('ceqw', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ enum — explicit ordinal values                                       }
{ ------------------------------------------------------------------ }

procedure TCaseEnumTests.TestParse_Enum_ExplicitOrdinals;
begin
  ParseOK(
    '''
        program P;
        type
          TStatus = (Idle=10, Running=20, Done=30);
        begin
        end.
        ''');
end;

procedure TCaseEnumTests.TestParse_Enum_PartialExplicitOrdinals;
begin
  ParseOK(
    '''
        program P;
        type
          TCode = (A=100, B, C);
        begin
        end.
        ''');
end;

procedure TCaseEnumTests.TestParse_Enum_ExplicitNegativeOrdinal;
begin
  ParseOK(
    '''
        program P;
        type
          TOffset = (Before=-1, At=0, After=1);
        begin
        end.
        ''');
end;

procedure TCaseEnumTests.TestSemantic_Enum_ExplicitOrdinals_CorrectValues;
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  Prog: TProgram;
  Assign: TAssignment;
begin
  { Running=20 — the RHS ConstValue should be 20, not 1 }
  Lex  := TLexer.Create(
    '''
        program P;
        type
          TStatus = (Idle=10, Running=20, Done=30);
        var S: TStatus;
        begin
          S := Running
        end.
        ''');
  Par  := TParser.Create(Lex);
  Prog := Par.Parse();
  Par.Free(); Lex.Free();
  SA := TSemanticAnalyser.Create();
  SA.Analyse(Prog);
  SA.Free();
  Assign := TAssignment(Prog.Block.Stmts[0]);
  AssertEquals('Running ordinal is 20', 20, TIdentExpr(Assign.Expr).ConstValue);
  Prog.Free();
end;

procedure TCaseEnumTests.TestCodegen_Enum_ExplicitOrdinal_EmitsCorrectCopy;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TStatus = (Idle=10, Running=20, Done=30);
        var S: TStatus;
        begin
          S := Running
        end.
        ''');
  AssertTrue('Running=20 emits copy 20', Pos('copy 20', IR) > 0);
  AssertTrue('Running does not emit positional copy 1', Pos('copy 1', IR) < 0);
end;

procedure TCaseEnumTests.TestCodegen_Enum_AutoContinueAfterExplicit;
var
  IR: string;
begin
  { A=100 → B auto-continues to 101, C to 102 }
  IR := GenIR(
    '''
        program P;
        type
          TCode = (A=100, B, C);
        var X: TCode;
        begin
          X := B
        end.
        ''');
  AssertTrue('B auto-continues to 101', Pos('copy 101', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ case — string selector                                               }
{ ------------------------------------------------------------------ }

procedure TCaseEnumTests.TestSemantic_CaseString_AcceptsStringSelector;
const
  Src =
    '''
        program P;
        var S: string; R: Integer;
        begin
          S := 'foo';
          case S of
            'bar': R := 1;
            'foo': R := 2
          else
            R := 99
          end
        end.
        ''';
begin
  SemanticOK(Src);
end;

procedure TCaseEnumTests.TestSemantic_CaseString_RejectsIntLabelOnStringSelector;
const
  Src =
    '''
        program P;
        var S: string;
        begin
          S := 'foo';
          case S of
            1: S := 'one'
          end
        end.
        ''';
var
  Raised: Boolean;
begin
  Raised := False;
  try
    SemanticOK(Src);
  except
    on E: Exception do Raised := True;
  end;
  AssertTrue('integer literal label on string-typed selector rejected', Raised);
end;

procedure TCaseEnumTests.TestCodegen_CaseString_EmitsStringEqualsCalls;
const
  Src =
    '''
        program P;
        var S: string; R: Integer;
        begin
          S := 'foo';
          case S of
            'bar': R := 1;
            'foo': R := 2
          else
            R := 99
          end
        end.
        ''';
var
  IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('string case emits _StringEquals call',
    Pos('call $_StringEquals(', IR) > 0);
end;

procedure TCaseEnumTests.TestCodegen_CaseString_OrdinalCaseStillUsesCEQW;
{ Regression: the new string-case codegen must not affect the ordinal
  case path.  Use the existing SrcCaseSimple fixture. }
var
  IR: string;
begin
  IR := GenIR(SrcCaseSimple);
  AssertTrue('integer case still emits ceqw', Pos('ceqw', IR) > 0);
  AssertTrue('integer case does NOT emit _StringEquals',
    Pos('_StringEquals', IR) < 0);
end;

initialization
  RegisterTest(TCaseEnumTests);

end.
