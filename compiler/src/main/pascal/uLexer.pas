{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

unit uLexer;

{$mode objfpc}{$H+}

{ Compiler lexer — wraps uPasTokeniser and converts its flat token stream
  into the compiler's specific token kinds. Skips whitespace, line endings,
  comments, and compiler directives. Unescapes string literal values. }

interface

uses
  SysUtils, uPasTokeniser;

type
  TTokenKind = (
    tkEOF,
    { Literals }
    tkIntLit,
    tkStringLit,
    { Keywords }
    tkProgram,
    tkUses,
    tkType,
    tkRecord,
    tkClass,
    tkProcedure,
    tkFunction,
    tkVar,
    tkBegin,
    tkEnd,
    tkIf,
    tkThen,
    tkElse,
    tkWhile,
    tkDo,
    tkFor,
    tkTo,
    tkDownto,
    tkTry,
    tkFinally,
    tkExcept,
    tkRaise,
    tkNil,
    tkUnit,
    tkIntf,
    tkImplementation,
    tkVirtual,
    tkOverride,
    tkIs,
    tkAs,
    tkAnd,
    tkOr,
    tkNot,
    tkExit,
    tkBreak,
    tkContinue,
    tkInherited,
    tkCase,
    tkOf,
    tkConst,
    tkOut,
    { Identifier }
    tkIdent,
    { Arithmetic operators }
    tkPlus,
    tkMinus,
    tkStar,
    tkSlash,    { '/' — future: float division }
    tkDiv,      { 'div' keyword — integer division }
    { Assignment and equality }
    tkAssign,        { := }
    tkEquals,        { =  — type declarations and equality comparison }
    tkNotEquals,     { <> }
    tkLessThan,      { <  }
    tkGreaterThan,   { >  }
    tkLessEqual,     { <= }
    tkGreaterEqual,  { >= }
    tkColon,         { :  }
    { Grouping and punctuation }
    tkLParen,
    tkRParen,
    tkLBracket,      { [  — attribute list / future array indexing }
    tkRBracket,      { ]  — attribute list / future array indexing }
    tkComma,
    tkSemicolon,
    tkDot,
    tkCaret          { ^ — pointer dereference / pointer type prefix }
  );

  TToken = record
    Kind:  TTokenKind;
    Value: string;   { parsed value: ident text, int digits, unescaped string }
    Line:  Integer;
    Col:   Integer;
  end;

  TLexer = class
  private
    FTok:  TFpgPascalTokeniser;
    function MapKeyword(const AUpper: string): TTokenKind;
    function UnescapeString(const ARaw: string): string;
  public
    constructor Create(const ASource: string);
    destructor Destroy; override;
    function Next: TToken;
  end;

implementation

{ Local helper matching the Blaise builtin — lets UnescapeString share one
  body under FPC and the self-hosted compiler. The migration tool strips
  this declaration; self-hosted builds resolve OrdAt to the builtin. }
function OrdAt(const S: string; I: Integer): Integer;
begin
  Result := Ord(S[I]);
end;

constructor TLexer.Create(const ASource: string);
begin
  inherited Create;
  FTok := TFpgPascalTokeniser.Create;
  FTok.SetSource(ASource);
end;

destructor TLexer.Destroy;
begin
  FTok.Free;
  inherited Destroy;
end;

function TLexer.MapKeyword(const AUpper: string): TTokenKind;
begin
  if AUpper = 'PROGRAM' then Result := tkProgram
  else if AUpper = 'USES'    then Result := tkUses
  else if AUpper = 'VAR'     then Result := tkVar
  else if AUpper = 'BEGIN'   then Result := tkBegin
  else if AUpper = 'END'     then Result := tkEnd
  else if AUpper = 'TYPE'    then Result := tkType
  else if AUpper = 'RECORD'  then Result := tkRecord
  else if AUpper = 'CLASS'     then Result := tkClass
  else if AUpper = 'PROCEDURE' then Result := tkProcedure
  else if AUpper = 'FUNCTION'  then Result := tkFunction
  else if AUpper = 'DIV'       then Result := tkDiv
  else if AUpper = 'IF'        then Result := tkIf
  else if AUpper = 'THEN'      then Result := tkThen
  else if AUpper = 'ELSE'      then Result := tkElse
  else if AUpper = 'WHILE'     then Result := tkWhile
  else if AUpper = 'DO'        then Result := tkDo
  else if AUpper = 'FOR'       then Result := tkFor
  else if AUpper = 'TO'        then Result := tkTo
  else if AUpper = 'DOWNTO'   then Result := tkDownto
  else if AUpper = 'TRY'       then Result := tkTry
  else if AUpper = 'FINALLY'   then Result := tkFinally
  else if AUpper = 'EXCEPT'    then Result := tkExcept
  else if AUpper = 'RAISE'     then Result := tkRaise
  else if AUpper = 'NIL'            then Result := tkNil
  else if AUpper = 'UNIT'           then Result := tkUnit
  else if AUpper = 'INTERFACE'      then Result := tkIntf
  else if AUpper = 'IMPLEMENTATION' then Result := tkImplementation
  else if AUpper = 'VIRTUAL'        then Result := tkVirtual
  else if AUpper = 'OVERRIDE'       then Result := tkOverride
  else if AUpper = 'IS'             then Result := tkIs
  else if AUpper = 'AS'             then Result := tkAs
  else if AUpper = 'AND'            then Result := tkAnd
  else if AUpper = 'OR'             then Result := tkOr
  else if AUpper = 'NOT'            then Result := tkNot
  else if AUpper = 'EXIT'           then Result := tkExit
  else if AUpper = 'BREAK'          then Result := tkBreak
  else if AUpper = 'CONTINUE'       then Result := tkContinue
  else if AUpper = 'CASE'           then Result := tkCase
  else if AUpper = 'OF'             then Result := tkOf
  else if AUpper = 'CONST'          then Result := tkConst
  else if AUpper = 'OUT'            then Result := tkOut
  else if AUpper = 'INHERITED'      then Result := tkInherited
  else
    Result := tkIdent;  { keyword outside Phase 1 grammar treated as ident }
end;

function TLexer.UnescapeString(const ARaw: string): string;
{ ARaw is the full source span. Handles: 'text' with '' → ' escaping,
  #nn numeric char literals (decimal), and concatenated runs like
  'abc'#13#10'def'. Uses OrdAt so the body parses under both FPC and
  the self-hosted Blaise compiler. }
var
  I, Len, N, C: Integer;
begin
  Result := '';
  Len := Length(ARaw);
  I := 1;
  while I <= Len do
  begin
    C := OrdAt(ARaw, I);
    if C = 39 then  { single quote }
    begin
      I := I + 1;
      while I <= Len do
      begin
        C := OrdAt(ARaw, I);
        if C = 39 then
        begin
          if (I < Len) and (OrdAt(ARaw, I + 1) = 39) then
          begin
            Result := Result + '''';
            I := I + 2;
          end
          else
          begin
            I := I + 1;
            Break;
          end;
        end
        else
        begin
          Result := Result + Chr(C);
          I := I + 1;
        end;
      end;
    end
    else if C = 35 then  { '#' }
    begin
      I := I + 1;
      N := 0;
      while I <= Len do
      begin
        C := OrdAt(ARaw, I);
        if (C < 48) or (C > 57) then Break;
        N := N * 10 + (C - 48);
        I := I + 1;
      end;
      Result := Result + Chr(N);
    end
    else
      I := I + 1;
  end;
end;

function TLexer.Next: TToken;
var
  raw:  TFpgPasToken;
  text: string;
begin
  repeat
    raw := FTok.NextToken;
  until not (raw.Kind in [fptkWhitespace, fptkLineEnding,
                           fptkComment, fptkDirective]);

  Result.Line := raw.Line;
  Result.Col  := raw.Column;

  case raw.Kind of
    fptkEOF:
      begin
        Result.Kind  := tkEOF;
        Result.Value := '';
      end;

    fptkKeyword:
      begin
        text := FTok.TokenTextUpper;
        Result.Kind  := MapKeyword(text);
        Result.Value := FTok.TokenText;
      end;

    fptkIdentifier:
      begin
        text := FTok.TokenTextUpper;
        if      text = 'VIRTUAL'  then Result.Kind := tkVirtual
        else if text = 'OVERRIDE' then Result.Kind := tkOverride
        else if text = 'EXIT'     then Result.Kind := tkExit
        else if text = 'BREAK'    then Result.Kind := tkBreak
        else if text = 'CONTINUE' then Result.Kind := tkContinue
        else if text = 'CASE'     then Result.Kind := tkCase
        else if text = 'OF'       then Result.Kind := tkOf
        else if text = 'CONST'    then Result.Kind := tkConst
        else if text = 'OUT'      then Result.Kind := tkOut
        else                           Result.Kind := tkIdent;
        Result.Value := FTok.TokenText;
      end;

    fptkNumber:
      begin
        Result.Kind  := tkIntLit;
        Result.Value := FTok.TokenText;
      end;

    fptkString:
      begin
        Result.Kind  := tkStringLit;
        Result.Value := UnescapeString(FTok.TokenText);
      end;

    fptkSymbol:
      begin
        text := FTok.TokenText;
        if      text = ':=' then Result.Kind := tkAssign
        else if text = '='  then Result.Kind := tkEquals
        else if text = '<>' then Result.Kind := tkNotEquals
        else if text = '<=' then Result.Kind := tkLessEqual
        else if text = '>=' then Result.Kind := tkGreaterEqual
        else if text = '<'  then Result.Kind := tkLessThan
        else if text = '>'  then Result.Kind := tkGreaterThan
        else if text = ':'  then Result.Kind := tkColon
        else if text = '('  then Result.Kind := tkLParen
        else if text = ')'  then Result.Kind := tkRParen
        else if text = '['  then Result.Kind := tkLBracket
        else if text = ']'  then Result.Kind := tkRBracket
        else if text = ','  then Result.Kind := tkComma
        else if text = ';'  then Result.Kind := tkSemicolon
        else if text = '.'  then Result.Kind := tkDot
        else if text = '+'  then Result.Kind := tkPlus
        else if text = '-'  then Result.Kind := tkMinus
        else if text = '*'  then Result.Kind := tkStar
        else if text = '/'  then Result.Kind := tkSlash
        else if text = '^'  then Result.Kind := tkCaret
        else
          raise Exception.CreateFmt(
            'Unexpected symbol ''%s'' at line %d col %d',
            [text, raw.Line, raw.Column]);
        Result.Value := text;
      end;

  else
    raise Exception.CreateFmt(
      'Unexpected token kind %d at line %d col %d',
      [Ord(raw.Kind), raw.Line, raw.Column]);
  end;
end;

end.
