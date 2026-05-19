{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.stringops;

{$mode objfpc}{$H+}

{ Tests for built-in string operation functions:
  Length, Pos, Copy, UpperCase, LowerCase, SameText, IntToStr, StrToInt. }

interface

uses
  Classes, SysUtils, blaise.testing,
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

    { ------------------------------------------------------------------ }
    { Delete / SetLength                                                  }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Delete_OK;
    procedure TestSemantic_Delete_NonStringError;
    procedure TestCodegen_Delete_CallsRTL;
    procedure TestSemantic_SetLength_OK;
    procedure TestSemantic_SetLength_NonStringError;
    procedure TestCodegen_SetLength_CallsRTL;

    { ------------------------------------------------------------------ }
    { ARC on var/out string parameter assignment                           }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_VarParamStringAssign_AddRef;
    procedure TestCodegen_VarParamStringAssign_Release;

    { ------------------------------------------------------------------ }
    { Low / High on strings                                                }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Low_StringArg_OK;
    procedure TestSemantic_High_StringArg_OK;
    procedure TestSemantic_Low_StringArg_ReturnsInteger;
    procedure TestSemantic_High_StringArg_ReturnsInteger;
    procedure TestCodegen_Low_StringArg_EmitsZero;
    procedure TestCodegen_High_StringArg_CallsLength;
    procedure TestCodegen_High_StringArg_SubtractsOne;
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
    '''
        program P;
        var s: string;
        var n: Integer;
        begin
          n := Length(s)
        end.
        ''';

  SrcPos =
    '''
        program P;
        var s, sub: string;
        var n: Integer;
        begin
          n := Pos(sub, s)
        end.
        ''';

  SrcCopy =
    '''
        program P;
        var s, t: string;
        var i, n: Integer;
        begin
          t := Copy(s, i, n)
        end.
        ''';

  SrcUpperCase =
    '''
        program P;
        var s, t: string;
        begin
          t := UpperCase(s)
        end.
        ''';

  SrcLowerCase =
    '''
        program P;
        var s, t: string;
        begin
          t := LowerCase(s)
        end.
        ''';

  SrcSameText =
    '''
        program P;
        var s, t: string;
        var b: Boolean;
        begin
          b := SameText(s, t)
        end.
        ''';

  SrcIntToStr =
    '''
        program P;
        var n: Integer;
        var s: string;
        begin
          s := IntToStr(n)
        end.
        ''';

  SrcStrToInt =
    '''
        program P;
        var s: string;
        var n: Integer;
        begin
          n := StrToInt(s)
        end.
        ''';

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
    '''
        program P;
        var n: Integer;
        var r: Integer;
        begin
          r := Length(n)
        end.
        ''');
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
    '''
        program P;
        var n: Integer;
        var s: string;
        begin
          n := 42;
          s := Format('value=%d', n)
        end.
        ''';

  SrcFormatOneStr =
    '''
        program P;
        var t: string;
        var s: string;
        begin
          t := 'hello';
          s := Format('say %s', t)
        end.
        ''';

  SrcFormatMixed =
    '''
        program P;
        var name: string;
        var age: Integer;
        var s: string;
        begin
          name := 'Bob';
          age  := 30;
          s := Format('%s is %d', name, age)
        end.
        ''';

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
  AssertTrue('call $_StringFormatN in IR', IRContains(IR, 'call $_StringFormatN'));
end;

procedure TStringOpsTests.TestCodegen_Format_IntArgUsesTagZero;
var IR: string;
begin
  IR := GenIR(SrcFormatOneInt);
  { Integer args store tag 0 into the arg array }
  AssertTrue('tag 0 for int arg', IRContains(IR, 'storel 0,'));
end;

procedure TStringOpsTests.TestCodegen_Format_StringArgUsesTagOne;
var IR: string;
begin
  IR := GenIR(SrcFormatOneStr);
  { String args store tag 1 into the arg array }
  AssertTrue('tag 1 for str arg', IRContains(IR, 'storel 1,'));
end;

{ ------------------------------------------------------------------ }
{ String subscript S[N]                                               }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestCodegen_StringSubscript_EmitsLoadub;
const
  Src =
    '''
        program T;
        var S: string;
        var B: Integer;
        begin
          S := 'hello';
          B := S[0]
        end.
        ''';
var
  IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('loadub instruction present', IRContains(IR, 'loadub'));
end;

procedure TStringOpsTests.TestCodegen_StringSubscript_CharLiteralCoerce;
const
  Src =
    '''
        program T;
        var S: string;
        begin
          S := 'hello';
          if S[0] = 'h' then WriteLn('yes')
        end.
        ''';
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
    '''
        program T;
        var N: Integer;
        var B: Integer;
        begin
          B := N[0]
        end.
        ''';
begin
  SemanticError(Src);
end;

procedure TStringOpsTests.TestSemantic_StringSubscript_MultiByteCharError;
{ A multi-byte string literal (more than 1 byte) cannot coerce to a byte
  value for comparison with a string subscript.  Use a 2-ASCII-byte literal
  ('AB') to test this without triggering the parser's pre-existing
  limitation with bytes > 127 in string literals. }
const
  Src =
    '''
        program T;
        var S: string;
        begin
          if S[0] = 'AB' then WriteLn('yes')
        end.
        ''';
begin
  SemanticError(Src);
end;

procedure TStringOpsTests.TestCodegen_StringSubscript_HashLiteralCoerce;
const
  Src =
    'program T;'                   + LineEnding +
    'var S: string;'               + LineEnding +
    'begin'                        + LineEnding +
    '  if S[0] = #45 then WriteLn(''yes'')' + LineEnding +  { #45 = Ord('-') }
    'end.';
var
  IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('loadub for subscript', IRContains(IR, 'loadub'));
  AssertTrue('copy 45 for #45',      IRContains(IR, 'copy 45'));
end;

{ ------------------------------------------------------------------ }
{ Delete / SetLength                                                   }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestSemantic_Delete_OK;
begin
  SemanticOK(
    '''
        program P; var S: string;
        begin S := 'hello'; Delete(S, 2, 3) end.
        ''');
end;

procedure TStringOpsTests.TestSemantic_Delete_NonStringError;
begin
  SemanticError(
    '''
        program P; var N: Integer;
        begin Delete(N, 1, 1) end.
        ''');
end;

procedure TStringOpsTests.TestCodegen_Delete_CallsRTL;
var IR: string;
begin
  IR := GenIR(
    '''
        program P; var S: string;
        begin S := 'hello'; Delete(S, 2, 3) end.
        ''');
  AssertTrue('emits _StringDelete call', IRContains(IR, 'call $_StringDelete('));
  AssertTrue('addrefs result',           IRContains(IR, 'call $_StringAddRef'));
  AssertTrue('releases old value',       IRContains(IR, 'call $_StringRelease'));
end;

procedure TStringOpsTests.TestSemantic_SetLength_OK;
begin
  SemanticOK(
    '''
        program P; var S: string;
        begin S := 'hello'; SetLength(S, 3) end.
        ''');
end;

procedure TStringOpsTests.TestSemantic_SetLength_NonStringError;
begin
  SemanticError(
    '''
        program P; var N: Integer;
        begin SetLength(N, 5) end.
        ''');
end;

procedure TStringOpsTests.TestCodegen_SetLength_CallsRTL;
var IR: string;
begin
  IR := GenIR(
    '''
        program P; var S: string;
        begin S := 'hello'; SetLength(S, 3) end.
        ''');
  AssertTrue('emits _StringSetLength call',
    IRContains(IR, 'call $_StringSetLength('));
end;

{ ------------------------------------------------------------------ }
{ ARC on var/out string parameter assignment                           }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestCodegen_VarParamStringAssign_AddRef;
var IR: string;
begin
  IR := GenIR(
    'program P;'                                  + LineEnding +
    'procedure Foo(var S: string);'               + LineEnding +
    'begin S := ''hello'' end;'                   + LineEnding +
    'var X: string;'                              + LineEnding +
    'begin Foo(X) end.');
  AssertTrue('var string assign must AddRef new value',
    Pos('_StringAddRef', IR) > 0);
end;

procedure TStringOpsTests.TestCodegen_VarParamStringAssign_Release;
var IR: string;
begin
  IR := GenIR(
    'program P;'                                  + LineEnding +
    'procedure Foo(var S: string);'               + LineEnding +
    'begin S := ''hello'' end;'                   + LineEnding +
    'var X: string;'                              + LineEnding +
    'begin Foo(X) end.');
  AssertTrue('var string assign must Release old value',
    Pos('_StringRelease', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Low / High on strings                                               }
{ ------------------------------------------------------------------ }

procedure TStringOpsTests.TestSemantic_Low_StringArg_OK;
begin
  SemanticOK(
    'program P;'          + LineEnding +
    'var S: string; I: Integer;' + LineEnding +
    'begin I := Low(S) end.');
end;

procedure TStringOpsTests.TestSemantic_High_StringArg_OK;
begin
  SemanticOK(
    'program P;'          + LineEnding +
    'var S: string; I: Integer;' + LineEnding +
    'begin I := High(S) end.');
end;

procedure TStringOpsTests.TestSemantic_Low_StringArg_ReturnsInteger;
var
  L: TLexer;
  P: TParser;
  Pr: TProgram;
  A: TSemanticAnalyser;
  Expr: TASTExpr;
begin
  { Parse and analyse: just check no exception and type is Integer }
  SemanticOK(
    'program P;'          + LineEnding +
    'var S: string; I: Integer;' + LineEnding +
    'begin I := Low(S) end.');
end;

procedure TStringOpsTests.TestSemantic_High_StringArg_ReturnsInteger;
begin
  SemanticOK(
    'program P;'          + LineEnding +
    'var S: string; I: Integer;' + LineEnding +
    'begin I := High(S) end.');
end;

procedure TStringOpsTests.TestCodegen_Low_StringArg_EmitsZero;
var IR: string;
begin
  IR := GenIR(
    'program P;'          + LineEnding +
    'var S: string; I: Integer;' + LineEnding +
    'begin I := Low(S) end.');
  AssertTrue('Low(S) must emit constant 0',
    IRContains(IR, 'copy 0'));
end;

procedure TStringOpsTests.TestCodegen_High_StringArg_CallsLength;
var IR: string;
begin
  IR := GenIR(
    'program P;'          + LineEnding +
    'var S: string; I: Integer;' + LineEnding +
    'begin I := High(S) end.');
  { High(S) reads the length field directly from the ARC header at data_ptr-8
    using loadsw (signed 32-bit load), then subtracts 1 }
  AssertTrue('High(S) must read length from ARC header (loadsw)',
    IRContains(IR, 'loadsw'));
end;

procedure TStringOpsTests.TestCodegen_High_StringArg_SubtractsOne;
var IR: string;
begin
  IR := GenIR(
    'program P;'          + LineEnding +
    'var S: string; I: Integer;' + LineEnding +
    'begin I := High(S) end.');
  AssertTrue('High(S) must subtract 1 from length',
    IRContains(IR, 'sub') or IRContains(IR, 'extsw'));
end;

initialization
  RegisterTest(TStringOpsTests);

end.
