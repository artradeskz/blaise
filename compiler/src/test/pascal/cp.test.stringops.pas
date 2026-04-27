{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

unit cp.test.stringops;

{$mode objfpc}{$H+}

{ Tests for built-in string operation functions:
  Length, Pos, Copy, UpperCase, LowerCase, SameText, IntToStr, StrToInt. }

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TStringOpsTests = class(TTestCase)
  private
    function GenIR(const ASrc: string): string;
    function IRContains(const AIR, AFragment: string): Boolean;
    procedure SemanticOK(const ASrc: string);
    procedure SemanticError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Length                                                               }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Length_StringArg_OK;
    procedure TestSemantic_Length_IntArg_Error;
    procedure TestSemantic_Length_ReturnsInteger;
    procedure TestCodegen_Length_CallsRTL;

    { ------------------------------------------------------------------ }
    { Pos                                                                  }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Pos_TwoStringArgs_OK;
    procedure TestSemantic_Pos_ReturnsInteger;
    procedure TestCodegen_Pos_CallsRTL;

    { ------------------------------------------------------------------ }
    { Copy                                                                 }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Copy_OK;
    procedure TestSemantic_Copy_ReturnsString;
    procedure TestCodegen_Copy_CallsRTL;

    { ------------------------------------------------------------------ }
    { UpperCase / LowerCase                                                }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_UpperCase_OK;
    procedure TestSemantic_UpperCase_ReturnsString;
    procedure TestCodegen_UpperCase_CallsRTL;
    procedure TestSemantic_LowerCase_OK;
    procedure TestCodegen_LowerCase_CallsRTL;

    { ------------------------------------------------------------------ }
    { SameText                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_SameText_OK;
    procedure TestSemantic_SameText_ReturnsBoolean;
    procedure TestCodegen_SameText_CallsRTL;

    { ------------------------------------------------------------------ }
    { IntToStr / StrToInt                                                  }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_IntToStr_OK;
    procedure TestSemantic_IntToStr_ReturnsString;
    procedure TestCodegen_IntToStr_CallsRTL;
    procedure TestSemantic_StrToInt_OK;
    procedure TestSemantic_StrToInt_ReturnsInteger;
    procedure TestCodegen_StrToInt_CallsRTL;

    { ------------------------------------------------------------------ }
    { Format                                                               }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Format_OneIntArg_OK;
    procedure TestSemantic_Format_OneStringArg_OK;
    procedure TestSemantic_Format_MixedArgs_OK;
    procedure TestSemantic_Format_ReturnsString;
    procedure TestCodegen_Format_CallsRTL;
    procedure TestCodegen_Format_IntArgUsesTagZero;
    procedure TestCodegen_Format_StringArgUsesTagOne;
    { ------------------------------------------------------------------ }
    { String subscript S[N]                                               }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_StringSubscript_EmitsLoadub;
    procedure TestCodegen_StringSubscript_CharLiteralCoerce;
    procedure TestSemantic_StringSubscript_NonStringError;
    procedure TestSemantic_StringSubscript_MultiByteCharError;
    procedure TestCodegen_StringSubscript_HashLiteralCoerce;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

function TStringOpsTests.GenIR(const ASrc: string): string;
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

function TStringOpsTests.IRContains(const AIR, AFragment: string): Boolean;
begin
  Result := Pos(AFragment, AIR) > 0;
end;

procedure TStringOpsTests.SemanticOK(const ASrc: string);
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse;
  A  := TSemanticAnalyser.Create;
  try
    A.Analyse(Pr);
  finally
    A.Free;
    Pr.Free;
    P.Free;
    L.Free;
  end;
end;

procedure TStringOpsTests.SemanticError(const ASrc: string);
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse;
  A  := TSemanticAnalyser.Create;
  try
    try
      A.Analyse(Pr);
      Fail('Expected ESemanticError');
    except
      on E: ESemanticError do ;
    end;
  finally
    A.Free;
    Pr.Free;
    P.Free;
    L.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Source snippets                                                       }
{ ------------------------------------------------------------------ }

const
  SrcLength =
    'program P;'            + LineEnding +
    'var s: string;'        + LineEnding +
    'var n: Integer;'       + LineEnding +
    'begin'                 + LineEnding +
    '  n := Length(s)'      + LineEnding +
    'end.';

  SrcPos =
    'program P;'                + LineEnding +
    'var s, sub: string;'       + LineEnding +
    'var n: Integer;'           + LineEnding +
    'begin'                     + LineEnding +
    '  n := Pos(sub, s)'        + LineEnding +
    'end.';

  SrcCopy =
    'program P;'                          + LineEnding +
    'var s, t: string;'                   + LineEnding +
    'var i, n: Integer;'                  + LineEnding +
    'begin'                               + LineEnding +
    '  t := Copy(s, i, n)'               + LineEnding +
    'end.';

  SrcUpperCase =
    'program P;'                + LineEnding +
    'var s, t: string;'         + LineEnding +
    'begin'                     + LineEnding +
    '  t := UpperCase(s)'       + LineEnding +
    'end.';

  SrcLowerCase =
    'program P;'                + LineEnding +
    'var s, t: string;'         + LineEnding +
    'begin'                     + LineEnding +
    '  t := LowerCase(s)'       + LineEnding +
    'end.';

  SrcSameText =
    'program P;'                    + LineEnding +
    'var s, t: string;'             + LineEnding +
    'var b: Boolean;'               + LineEnding +
    'begin'                         + LineEnding +
    '  b := SameText(s, t)'         + LineEnding +
    'end.';

  SrcIntToStr =
    'program P;'               + LineEnding +
    'var n: Integer;'          + LineEnding +
    'var s: string;'           + LineEnding +
    'begin'                    + LineEnding +
    '  s := IntToStr(n)'       + LineEnding +
    'end.';

  SrcStrToInt =
    'program P;'               + LineEnding +
    'var s: string;'           + LineEnding +
    'var n: Integer;'          + LineEnding +
    'begin'                    + LineEnding +
    '  n := StrToInt(s)'       + LineEnding +
    'end.';

{ ------------------------------------------------------------------ }
{ Length tests                                                          }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestSemantic_Length_StringArg_OK;
begin
  SemanticOK(SrcLength);
end;

procedure TStringOpsTests.TestSemantic_Length_IntArg_Error;
begin
  SemanticError(
    'program P;'          + LineEnding +
    'var n: Integer;'     + LineEnding +
    'var r: Integer;'     + LineEnding +
    'begin'               + LineEnding +
    '  r := Length(n)'    + LineEnding +
    'end.');
end;

procedure TStringOpsTests.TestSemantic_Length_ReturnsInteger;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  Assign: TAssignment;
begin
  L  := TLexer.Create(SrcLength);
  P  := TParser.Create(L);
  Pr := P.Parse;
  A  := TSemanticAnalyser.Create;
  try
    A.Analyse(Pr);
    Assign := TAssignment(Pr.Block.Stmts[0]);
    AssertNotNull('expr resolved', Assign.Expr.ResolvedType);
    AssertEquals('Length returns Integer',
      Ord(tyInteger), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    A.Free;
    Pr.Free;
    P.Free;
    L.Free;
  end;
end;

procedure TStringOpsTests.TestCodegen_Length_CallsRTL;
var IR: string;
begin
  IR := GenIR(SrcLength);
  AssertTrue('call $_StringLength in IR', IRContains(IR, 'call $_StringLength'));
end;

{ ------------------------------------------------------------------ }
{ Pos tests                                                            }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestSemantic_Pos_TwoStringArgs_OK;
begin
  SemanticOK(SrcPos);
end;

procedure TStringOpsTests.TestSemantic_Pos_ReturnsInteger;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  Assign: TAssignment;
begin
  L  := TLexer.Create(SrcPos);
  P  := TParser.Create(L);
  Pr := P.Parse;
  A  := TSemanticAnalyser.Create;
  try
    A.Analyse(Pr);
    Assign := TAssignment(Pr.Block.Stmts[0]);
    AssertEquals('Pos returns Integer',
      Ord(tyInteger), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    A.Free;
    Pr.Free;
    P.Free;
    L.Free;
  end;
end;

procedure TStringOpsTests.TestCodegen_Pos_CallsRTL;
var IR: string;
begin
  IR := GenIR(SrcPos);
  AssertTrue('call $_StringPos in IR', IRContains(IR, 'call $_StringPos'));
end;

{ ------------------------------------------------------------------ }
{ Copy tests                                                           }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestSemantic_Copy_OK;
begin
  SemanticOK(SrcCopy);
end;

procedure TStringOpsTests.TestSemantic_Copy_ReturnsString;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  Assign: TAssignment;
begin
  L  := TLexer.Create(SrcCopy);
  P  := TParser.Create(L);
  Pr := P.Parse;
  A  := TSemanticAnalyser.Create;
  try
    A.Analyse(Pr);
    Assign := TAssignment(Pr.Block.Stmts[0]);
    AssertEquals('Copy returns string',
      Ord(tyString), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    A.Free;
    Pr.Free;
    P.Free;
    L.Free;
  end;
end;

procedure TStringOpsTests.TestCodegen_Copy_CallsRTL;
var IR: string;
begin
  IR := GenIR(SrcCopy);
  AssertTrue('call $_StringCopy in IR', IRContains(IR, 'call $_StringCopy'));
end;

{ ------------------------------------------------------------------ }
{ UpperCase tests                                                       }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestSemantic_UpperCase_OK;
begin
  SemanticOK(SrcUpperCase);
end;

procedure TStringOpsTests.TestSemantic_UpperCase_ReturnsString;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  Assign: TAssignment;
begin
  L  := TLexer.Create(SrcUpperCase);
  P  := TParser.Create(L);
  Pr := P.Parse;
  A  := TSemanticAnalyser.Create;
  try
    A.Analyse(Pr);
    Assign := TAssignment(Pr.Block.Stmts[0]);
    AssertEquals('UpperCase returns string',
      Ord(tyString), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    A.Free;
    Pr.Free;
    P.Free;
    L.Free;
  end;
end;

procedure TStringOpsTests.TestCodegen_UpperCase_CallsRTL;
var IR: string;
begin
  IR := GenIR(SrcUpperCase);
  AssertTrue('call $_StringUpperCase in IR', IRContains(IR, 'call $_StringUpperCase'));
end;

procedure TStringOpsTests.TestSemantic_LowerCase_OK;
begin
  SemanticOK(SrcLowerCase);
end;

procedure TStringOpsTests.TestCodegen_LowerCase_CallsRTL;
var IR: string;
begin
  IR := GenIR(SrcLowerCase);
  AssertTrue('call $_StringLowerCase in IR', IRContains(IR, 'call $_StringLowerCase'));
end;

{ ------------------------------------------------------------------ }
{ SameText tests                                                        }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestSemantic_SameText_OK;
begin
  SemanticOK(SrcSameText);
end;

procedure TStringOpsTests.TestSemantic_SameText_ReturnsBoolean;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  Assign: TAssignment;
begin
  L  := TLexer.Create(SrcSameText);
  P  := TParser.Create(L);
  Pr := P.Parse;
  A  := TSemanticAnalyser.Create;
  try
    A.Analyse(Pr);
    Assign := TAssignment(Pr.Block.Stmts[0]);
    AssertEquals('SameText returns Boolean',
      Ord(tyBoolean), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    A.Free;
    Pr.Free;
    P.Free;
    L.Free;
  end;
end;

procedure TStringOpsTests.TestCodegen_SameText_CallsRTL;
var IR: string;
begin
  IR := GenIR(SrcSameText);
  AssertTrue('call $_StringSameText in IR', IRContains(IR, 'call $_StringSameText'));
end;

{ ------------------------------------------------------------------ }
{ IntToStr / StrToInt tests                                            }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestSemantic_IntToStr_OK;
begin
  SemanticOK(SrcIntToStr);
end;

procedure TStringOpsTests.TestSemantic_IntToStr_ReturnsString;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  Assign: TAssignment;
begin
  L  := TLexer.Create(SrcIntToStr);
  P  := TParser.Create(L);
  Pr := P.Parse;
  A  := TSemanticAnalyser.Create;
  try
    A.Analyse(Pr);
    Assign := TAssignment(Pr.Block.Stmts[0]);
    AssertEquals('IntToStr returns string',
      Ord(tyString), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    A.Free;
    Pr.Free;
    P.Free;
    L.Free;
  end;
end;

procedure TStringOpsTests.TestCodegen_IntToStr_CallsRTL;
var IR: string;
begin
  IR := GenIR(SrcIntToStr);
  AssertTrue('call $_IntToStr in IR', IRContains(IR, 'call $_IntToStr'));
end;

procedure TStringOpsTests.TestSemantic_StrToInt_OK;
begin
  SemanticOK(SrcStrToInt);
end;

procedure TStringOpsTests.TestSemantic_StrToInt_ReturnsInteger;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  Assign: TAssignment;
begin
  L  := TLexer.Create(SrcStrToInt);
  P  := TParser.Create(L);
  Pr := P.Parse;
  A  := TSemanticAnalyser.Create;
  try
    A.Analyse(Pr);
    Assign := TAssignment(Pr.Block.Stmts[0]);
    AssertEquals('StrToInt returns Integer',
      Ord(tyInteger), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    A.Free;
    Pr.Free;
    P.Free;
    L.Free;
  end;
end;

procedure TStringOpsTests.TestCodegen_StrToInt_CallsRTL;
var IR: string;
begin
  IR := GenIR(SrcStrToInt);
  AssertTrue('call $_StrToInt in IR', IRContains(IR, 'call $_StrToInt'));
end;

{ ------------------------------------------------------------------ }
{ Format tests                                                         }
{ ------------------------------------------------------------------ }

const
  SrcFormatOneInt =
    'program P;'                          + LineEnding +
    'var n: Integer;'                     + LineEnding +
    'var s: string;'                      + LineEnding +
    'begin'                               + LineEnding +
    '  n := 42;'                          + LineEnding +
    '  s := Format(''value=%d'', n)'      + LineEnding +
    'end.';

  SrcFormatOneStr =
    'program P;'                          + LineEnding +
    'var t: string;'                      + LineEnding +
    'var s: string;'                      + LineEnding +
    'begin'                               + LineEnding +
    '  t := ''hello'';'                   + LineEnding +
    '  s := Format(''say %s'', t)'        + LineEnding +
    'end.';

  SrcFormatMixed =
    'program P;'                              + LineEnding +
    'var name: string;'                       + LineEnding +
    'var age: Integer;'                       + LineEnding +
    'var s: string;'                          + LineEnding +
    'begin'                                   + LineEnding +
    '  name := ''Bob'';'                      + LineEnding +
    '  age  := 30;'                           + LineEnding +
    '  s := Format(''%s is %d'', name, age)'  + LineEnding +
    'end.';

procedure TStringOpsTests.TestSemantic_Format_OneIntArg_OK;
begin
  SemanticOK(SrcFormatOneInt);
end;

procedure TStringOpsTests.TestSemantic_Format_OneStringArg_OK;
begin
  SemanticOK(SrcFormatOneStr);
end;

procedure TStringOpsTests.TestSemantic_Format_MixedArgs_OK;
begin
  SemanticOK(SrcFormatMixed);
end;

procedure TStringOpsTests.TestSemantic_Format_ReturnsString;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  Assign: TAssignment;
begin
  L  := TLexer.Create(SrcFormatOneInt);
  P  := TParser.Create(L);
  Pr := P.Parse;
  A  := TSemanticAnalyser.Create;
  try
    A.Analyse(Pr);
    Assign := TAssignment(Pr.Block.Stmts[1]);
    AssertEquals('Format returns string',
      Ord(tyString), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    A.Free;
    Pr.Free;
    P.Free;
    L.Free;
  end;
end;

procedure TStringOpsTests.TestCodegen_Format_CallsRTL;
var IR: string;
begin
  IR := GenIR(SrcFormatOneInt);
  AssertTrue('call $_StringFormat in IR', IRContains(IR, 'call $_StringFormat'));
end;

procedure TStringOpsTests.TestCodegen_Format_IntArgUsesTagZero;
var IR: string;
begin
  IR := GenIR(SrcFormatOneInt);
  { Integer args are preceded by tag 0 }
  AssertTrue('tag 0 for int arg', IRContains(IR, 'w 0,'));
end;

procedure TStringOpsTests.TestCodegen_Format_StringArgUsesTagOne;
var IR: string;
begin
  IR := GenIR(SrcFormatOneStr);
  { String args are preceded by tag 1 }
  AssertTrue('tag 1 for str arg', IRContains(IR, 'w 1,'));
end;

{ ------------------------------------------------------------------ }
{ String subscript S[N]                                               }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestCodegen_StringSubscript_EmitsLoadub;
const
  Src =
    'program T;'                   + LineEnding +
    'var S: string;'               + LineEnding +
    'var B: Integer;'              + LineEnding +
    'begin'                        + LineEnding +
    '  S := ''hello'';'            + LineEnding +
    '  B := S[1]'                  + LineEnding +
    'end.';
var
  IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('loadub instruction present', IRContains(IR, 'loadub'));
end;

procedure TStringOpsTests.TestCodegen_StringSubscript_CharLiteralCoerce;
const
  Src =
    'program T;'                   + LineEnding +
    'var S: string;'               + LineEnding +
    'begin'                        + LineEnding +
    '  S := ''hello'';'            + LineEnding +
    '  if S[1] = ''h'' then WriteLn(''yes'')' + LineEnding +
    'end.';
var
  IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('loadub for subscript', IRContains(IR, 'loadub'));
  AssertTrue('copy 104 for h', IRContains(IR, 'copy 104'));  { Ord('h') = 104 }
end;

procedure TStringOpsTests.TestSemantic_StringSubscript_NonStringError;
const
  Src =
    'program T;'                   + LineEnding +
    'var N: Integer;'              + LineEnding +
    'var B: Integer;'              + LineEnding +
    'begin'                        + LineEnding +
    '  B := N[1]'                  + LineEnding +
    'end.';
begin
  SemanticError(Src);
end;

procedure TStringOpsTests.TestSemantic_StringSubscript_MultiByteCharError;
const
  Src =
    'program T;'                   + LineEnding +
    'var S: string;'               + LineEnding +
    'begin'                        + LineEnding +
    '  if S[1] = ''😀'' then WriteLn(''yes'')' + LineEnding +
    'end.';
begin
  SemanticError(Src);
end;

procedure TStringOpsTests.TestCodegen_StringSubscript_HashLiteralCoerce;
const
  Src =
    'program T;'                   + LineEnding +
    'var S: string;'               + LineEnding +
    'begin'                        + LineEnding +
    '  if S[1] = #45 then WriteLn(''yes'')' + LineEnding +  { #45 = Ord('-') }
    'end.';
var
  IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('loadub for subscript', IRContains(IR, 'loadub'));
  AssertTrue('copy 45 for #45',      IRContains(IR, 'copy 45'));
end;

initialization
  RegisterTest(TStringOpsTests);

end.
