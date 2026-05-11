{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.tokenkindname;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, bcl.testing,
  uLexer;

type
  TTokenKindNameTests = class(TTestCase)
  published
    { Guard: if a new TTokenKind value is added without updating TokenKindName,
      the max-ordinal test fails, giving immediate feedback. }
    procedure TestMaxOrdinal_IstkAt;

    { Completeness: every defined TTokenKind must map to a non-empty name
      that does not fall through to the <unknown(...)> fallback. }
    procedure TestAllKindsHaveNonEmptyName;
    procedure TestNoKindReturnsUnknown;

    { Spot-checks for a representative sample of tokens. }
    procedure TestName_EOF;
    procedure TestName_IntLit;
    procedure TestName_FloatLit;
    procedure TestName_StringLit;
    procedure TestName_Initialization;
    procedure TestName_Finalization;
    procedure TestName_Program;
    procedure TestName_Uses;
    procedure TestName_Type;
    procedure TestName_Record;
    procedure TestName_Class;
    procedure TestName_Procedure;
    procedure TestName_Function;
    procedure TestName_Var;
    procedure TestName_Begin;
    procedure TestName_End;
    procedure TestName_If;
    procedure TestName_Then;
    procedure TestName_Else;
    procedure TestName_While;
    procedure TestName_Do;
    procedure TestName_For;
    procedure TestName_To;
    procedure TestName_Downto;
    procedure TestName_Repeat;
    procedure TestName_Until;
    procedure TestName_Try;
    procedure TestName_Finally;
    procedure TestName_Except;
    procedure TestName_Raise;
    procedure TestName_Nil;
    procedure TestName_Unit;
    procedure TestName_Interface;
    procedure TestName_Implementation;
    procedure TestName_Virtual;
    procedure TestName_Override;
    procedure TestName_External;
    procedure TestName_Is;
    procedure TestName_As;
    procedure TestName_And;
    procedure TestName_Or;
    procedure TestName_Not;
    procedure TestName_Exit;
    procedure TestName_Break;
    procedure TestName_Continue;
    procedure TestName_Inherited;
    procedure TestName_Case;
    procedure TestName_Of;
    procedure TestName_Array;
    procedure TestName_Set;
    procedure TestName_In;
    procedure TestName_Shl;
    procedure TestName_Shr;
    procedure TestName_Xor;
    procedure TestName_Const;
    procedure TestName_Out;
    procedure TestName_Constructor;
    procedure TestName_Destructor;
    procedure TestName_Ident;
    procedure TestName_Plus;
    procedure TestName_Minus;
    procedure TestName_Star;
    procedure TestName_Slash;
    procedure TestName_Div;
    procedure TestName_Mod;
    procedure TestName_Assign;
    procedure TestName_Equals;
    procedure TestName_NotEquals;
    procedure TestName_LessThan;
    procedure TestName_GreaterThan;
    procedure TestName_LessEqual;
    procedure TestName_GreaterEqual;
    procedure TestName_Colon;
    procedure TestName_LParen;
    procedure TestName_RParen;
    procedure TestName_LBracket;
    procedure TestName_RBracket;
    procedure TestName_Comma;
    procedure TestName_Semicolon;
    procedure TestName_Dot;
    procedure TestName_DotDot;
    procedure TestName_Caret;
    procedure TestName_At;
  end;

implementation

{ The highest ordinal of TTokenKind.  Update this constant whenever a new
  token kind is appended to the enum — the test below will fail and remind
  you to also update TokenKindName. }
const
  ExpectedMaxTokenKindOrd = 82; { tkAt }

procedure TTokenKindNameTests.TestMaxOrdinal_IstkAt;
begin
  AssertEquals('tkAt must be the last TTokenKind (ord 82); update this test and TokenKindName when adding new kinds',
    ExpectedMaxTokenKindOrd, Ord(tkAt));
end;

procedure TTokenKindNameTests.TestAllKindsHaveNonEmptyName;
var
  k: TTokenKind;
  name: string;
begin
  for k := TTokenKind(0) to TTokenKind(ExpectedMaxTokenKindOrd) do
  begin
    name := TokenKindName(k);
    AssertTrue('TokenKindName returned empty string for ordinal ' + IntToStr(Ord(k)),
      name <> '');
  end;
end;

procedure TTokenKindNameTests.TestNoKindReturnsUnknown;
var
  k: TTokenKind;
  name: string;
begin
  for k := TTokenKind(0) to TTokenKind(ExpectedMaxTokenKindOrd) do
  begin
    name := TokenKindName(k);
    AssertTrue('TokenKindName returned <unknown(...)> for ordinal ' + IntToStr(Ord(k)),
      Pos('<unknown(', name) = 0);
  end;
end;

{ Spot-checks }

procedure TTokenKindNameTests.TestName_EOF;
begin
  AssertEquals('<eof>', TokenKindName(tkEOF));
end;

procedure TTokenKindNameTests.TestName_IntLit;
begin
  AssertEquals('integer literal', TokenKindName(tkIntLit));
end;

procedure TTokenKindNameTests.TestName_FloatLit;
begin
  AssertEquals('float literal', TokenKindName(tkFloatLit));
end;

procedure TTokenKindNameTests.TestName_StringLit;
begin
  AssertEquals('string literal', TokenKindName(tkStringLit));
end;

procedure TTokenKindNameTests.TestName_Initialization;
begin
  AssertEquals('initialization', TokenKindName(tkInitialization));
end;

procedure TTokenKindNameTests.TestName_Finalization;
begin
  AssertEquals('finalization', TokenKindName(tkFinalization));
end;

procedure TTokenKindNameTests.TestName_Program;
begin
  AssertEquals('program', TokenKindName(tkProgram));
end;

procedure TTokenKindNameTests.TestName_Uses;
begin
  AssertEquals('uses', TokenKindName(tkUses));
end;

procedure TTokenKindNameTests.TestName_Type;
begin
  AssertEquals('type', TokenKindName(tkType));
end;

procedure TTokenKindNameTests.TestName_Record;
begin
  AssertEquals('record', TokenKindName(tkRecord));
end;

procedure TTokenKindNameTests.TestName_Class;
begin
  AssertEquals('class', TokenKindName(tkClass));
end;

procedure TTokenKindNameTests.TestName_Procedure;
begin
  AssertEquals('procedure', TokenKindName(tkProcedure));
end;

procedure TTokenKindNameTests.TestName_Function;
begin
  AssertEquals('function', TokenKindName(tkFunction));
end;

procedure TTokenKindNameTests.TestName_Var;
begin
  AssertEquals('var', TokenKindName(tkVar));
end;

procedure TTokenKindNameTests.TestName_Begin;
begin
  AssertEquals('begin', TokenKindName(tkBegin));
end;

procedure TTokenKindNameTests.TestName_End;
begin
  AssertEquals('end', TokenKindName(tkEnd));
end;

procedure TTokenKindNameTests.TestName_If;
begin
  AssertEquals('if', TokenKindName(tkIf));
end;

procedure TTokenKindNameTests.TestName_Then;
begin
  AssertEquals('then', TokenKindName(tkThen));
end;

procedure TTokenKindNameTests.TestName_Else;
begin
  AssertEquals('else', TokenKindName(tkElse));
end;

procedure TTokenKindNameTests.TestName_While;
begin
  AssertEquals('while', TokenKindName(tkWhile));
end;

procedure TTokenKindNameTests.TestName_Do;
begin
  AssertEquals('do', TokenKindName(tkDo));
end;

procedure TTokenKindNameTests.TestName_For;
begin
  AssertEquals('for', TokenKindName(tkFor));
end;

procedure TTokenKindNameTests.TestName_To;
begin
  AssertEquals('to', TokenKindName(tkTo));
end;

procedure TTokenKindNameTests.TestName_Downto;
begin
  AssertEquals('downto', TokenKindName(tkDownto));
end;

procedure TTokenKindNameTests.TestName_Repeat;
begin
  AssertEquals('repeat', TokenKindName(tkRepeat));
end;

procedure TTokenKindNameTests.TestName_Until;
begin
  AssertEquals('until', TokenKindName(tkUntil));
end;

procedure TTokenKindNameTests.TestName_Try;
begin
  AssertEquals('try', TokenKindName(tkTry));
end;

procedure TTokenKindNameTests.TestName_Finally;
begin
  AssertEquals('finally', TokenKindName(tkFinally));
end;

procedure TTokenKindNameTests.TestName_Except;
begin
  AssertEquals('except', TokenKindName(tkExcept));
end;

procedure TTokenKindNameTests.TestName_Raise;
begin
  AssertEquals('raise', TokenKindName(tkRaise));
end;

procedure TTokenKindNameTests.TestName_Nil;
begin
  AssertEquals('nil', TokenKindName(tkNil));
end;

procedure TTokenKindNameTests.TestName_Unit;
begin
  AssertEquals('unit', TokenKindName(tkUnit));
end;

procedure TTokenKindNameTests.TestName_Interface;
begin
  AssertEquals('interface', TokenKindName(tkIntf));
end;

procedure TTokenKindNameTests.TestName_Implementation;
begin
  AssertEquals('implementation', TokenKindName(tkImplementation));
end;

procedure TTokenKindNameTests.TestName_Virtual;
begin
  AssertEquals('virtual', TokenKindName(tkVirtual));
end;

procedure TTokenKindNameTests.TestName_Override;
begin
  AssertEquals('override', TokenKindName(tkOverride));
end;

procedure TTokenKindNameTests.TestName_External;
begin
  AssertEquals('external', TokenKindName(tkExternal));
end;

procedure TTokenKindNameTests.TestName_Is;
begin
  AssertEquals('is', TokenKindName(tkIs));
end;

procedure TTokenKindNameTests.TestName_As;
begin
  AssertEquals('as', TokenKindName(tkAs));
end;

procedure TTokenKindNameTests.TestName_And;
begin
  AssertEquals('and', TokenKindName(tkAnd));
end;

procedure TTokenKindNameTests.TestName_Or;
begin
  AssertEquals('or', TokenKindName(tkOr));
end;

procedure TTokenKindNameTests.TestName_Not;
begin
  AssertEquals('not', TokenKindName(tkNot));
end;

procedure TTokenKindNameTests.TestName_Exit;
begin
  AssertEquals('exit', TokenKindName(tkExit));
end;

procedure TTokenKindNameTests.TestName_Break;
begin
  AssertEquals('break', TokenKindName(tkBreak));
end;

procedure TTokenKindNameTests.TestName_Continue;
begin
  AssertEquals('continue', TokenKindName(tkContinue));
end;

procedure TTokenKindNameTests.TestName_Inherited;
begin
  AssertEquals('inherited', TokenKindName(tkInherited));
end;

procedure TTokenKindNameTests.TestName_Case;
begin
  AssertEquals('case', TokenKindName(tkCase));
end;

procedure TTokenKindNameTests.TestName_Of;
begin
  AssertEquals('of', TokenKindName(tkOf));
end;

procedure TTokenKindNameTests.TestName_Array;
begin
  AssertEquals('array', TokenKindName(tkArray));
end;

procedure TTokenKindNameTests.TestName_Set;
begin
  AssertEquals('set', TokenKindName(tkSet));
end;

procedure TTokenKindNameTests.TestName_In;
begin
  AssertEquals('in', TokenKindName(tkIn));
end;

procedure TTokenKindNameTests.TestName_Shl;
begin
  AssertEquals('shl', TokenKindName(tkShl));
end;

procedure TTokenKindNameTests.TestName_Shr;
begin
  AssertEquals('shr', TokenKindName(tkShr));
end;

procedure TTokenKindNameTests.TestName_Xor;
begin
  AssertEquals('xor', TokenKindName(tkXor));
end;

procedure TTokenKindNameTests.TestName_Const;
begin
  AssertEquals('const', TokenKindName(tkConst));
end;

procedure TTokenKindNameTests.TestName_Out;
begin
  AssertEquals('out', TokenKindName(tkOut));
end;

procedure TTokenKindNameTests.TestName_Constructor;
begin
  AssertEquals('constructor', TokenKindName(tkConstructor));
end;

procedure TTokenKindNameTests.TestName_Destructor;
begin
  AssertEquals('destructor', TokenKindName(tkDestructor));
end;

procedure TTokenKindNameTests.TestName_Ident;
begin
  AssertEquals('identifier', TokenKindName(tkIdent));
end;

procedure TTokenKindNameTests.TestName_Plus;
begin
  AssertEquals('+', TokenKindName(tkPlus));
end;

procedure TTokenKindNameTests.TestName_Minus;
begin
  AssertEquals('-', TokenKindName(tkMinus));
end;

procedure TTokenKindNameTests.TestName_Star;
begin
  AssertEquals('*', TokenKindName(tkStar));
end;

procedure TTokenKindNameTests.TestName_Slash;
begin
  AssertEquals('/', TokenKindName(tkSlash));
end;

procedure TTokenKindNameTests.TestName_Div;
begin
  AssertEquals('div', TokenKindName(tkDiv));
end;

procedure TTokenKindNameTests.TestName_Mod;
begin
  AssertEquals('mod', TokenKindName(tkMod));
end;

procedure TTokenKindNameTests.TestName_Assign;
begin
  AssertEquals(':=', TokenKindName(tkAssign));
end;

procedure TTokenKindNameTests.TestName_Equals;
begin
  AssertEquals('=', TokenKindName(tkEquals));
end;

procedure TTokenKindNameTests.TestName_NotEquals;
begin
  AssertEquals('<>', TokenKindName(tkNotEquals));
end;

procedure TTokenKindNameTests.TestName_LessThan;
begin
  AssertEquals('<', TokenKindName(tkLessThan));
end;

procedure TTokenKindNameTests.TestName_GreaterThan;
begin
  AssertEquals('>', TokenKindName(tkGreaterThan));
end;

procedure TTokenKindNameTests.TestName_LessEqual;
begin
  AssertEquals('<=', TokenKindName(tkLessEqual));
end;

procedure TTokenKindNameTests.TestName_GreaterEqual;
begin
  AssertEquals('>=', TokenKindName(tkGreaterEqual));
end;

procedure TTokenKindNameTests.TestName_Colon;
begin
  AssertEquals(':', TokenKindName(tkColon));
end;

procedure TTokenKindNameTests.TestName_LParen;
begin
  AssertEquals('(', TokenKindName(tkLParen));
end;

procedure TTokenKindNameTests.TestName_RParen;
begin
  AssertEquals(')', TokenKindName(tkRParen));
end;

procedure TTokenKindNameTests.TestName_LBracket;
begin
  AssertEquals('[', TokenKindName(tkLBracket));
end;

procedure TTokenKindNameTests.TestName_RBracket;
begin
  AssertEquals(']', TokenKindName(tkRBracket));
end;

procedure TTokenKindNameTests.TestName_Comma;
begin
  AssertEquals(',', TokenKindName(tkComma));
end;

procedure TTokenKindNameTests.TestName_Semicolon;
begin
  AssertEquals(';', TokenKindName(tkSemicolon));
end;

procedure TTokenKindNameTests.TestName_Dot;
begin
  AssertEquals('.', TokenKindName(tkDot));
end;

procedure TTokenKindNameTests.TestName_DotDot;
begin
  AssertEquals('..', TokenKindName(tkDotDot));
end;

procedure TTokenKindNameTests.TestName_Caret;
begin
  AssertEquals('^', TokenKindName(tkCaret));
end;

procedure TTokenKindNameTests.TestName_At;
begin
  AssertEquals('@', TokenKindName(tkAt));
end;

initialization
  RegisterTest(TTokenKindNameTests);

end.
