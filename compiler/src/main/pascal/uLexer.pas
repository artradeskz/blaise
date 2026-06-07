{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uLexer;

{ Compiler lexer — wraps uPasTokeniser and converts its flat token stream
  into the compiler's specific token kinds. Skips whitespace, line endings,
  comments, and compiler directives. Unescapes string literal values. }

interface

uses
  SysUtils, uPasTokeniser, uStrCompat;

type
  TTokenKind = (
    tkEOF,
    { Literals }
    tkIntLit,
    tkFloatLit,
    tkStringLit,
    tkInitialization,
    tkFinalization,
    { Keywords }
    tkProgram,
    tkUses,
    tkType,
    tkRecord,
    tkPacked,        { 'packed' — record-layout qualifier (only legal before
                       'record'; affects field offsets + tail padding) }
    tkClass,
    tkProcedure,
    tkFunction,
    tkVar,
    tkThreadVar,
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
    tkRepeat,
    tkUntil,
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
    tkExternal,
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
    tkArray,
    tkSet,    { 'set' keyword — set type declaration }
    tkIn,     { 'in'  keyword — set membership test operator }
    tkShl,    { 'shl' keyword — shift left }
    tkShr,    { 'shr' keyword — logical shift right (zero-fill) }
    tkSar,    { 'sar' keyword — arithmetic shift right (sign-preserving) }
    tkXor,    { 'xor' keyword — bitwise exclusive-or }
    tkConst,
    tkOut,
    tkConstructor,
    tkDestructor,
    { Identifier }
    tkIdent,
    { Arithmetic operators }
    tkPlus,
    tkMinus,
    tkStar,
    tkSlash,    { '/' — future: float division }
    tkDiv,      { 'div' keyword — integer division }
    tkMod,      { 'mod' keyword — integer modulo }
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
    tkDotDot,        { .. — array bounds separator and case range }
    tkCaret,         { ^ — pointer dereference / pointer type prefix }
    tkAt             { @ — address-of operator }
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
    FFilename: string;
    function MapKeyword(const AUpper: string): TTokenKind;
    function UnescapeString(const ARaw: string): string;
    function ProcessTextBlock(const ARaw: string): string;
    function DirectiveName(const AText: string): string;
    procedure SkipToElseOrEndif;
    procedure SkipToEndif;
  public
    constructor Create(const ASource: string; const AFilename: string = '');
    destructor Destroy; override;
    property Filename: string read FFilename;
    function Next: TToken;
  end;

function TokenKindName(AKind: TTokenKind): string;

implementation

{ Local helper matching the Blaise builtin — lets UnescapeString share one
  body under FPC and the self-hosted compiler. The migration tool strips
  this declaration; self-hosted builds resolve OrdAt to the builtin.
  I is 0-based; under FPC we convert to FPC's 1-based string indexing. }
function OrdAt(const S: string; I: Integer): Integer;
begin
  Result := Ord(S[I + 1]);
end;

constructor TLexer.Create(const ASource: string; const AFilename: string = '');
begin
  inherited Create();
  FTok := TFpgPascalTokeniser.Create();
  FTok.SetSource(ASource);
  FFilename := AFilename;
end;

destructor TLexer.Destroy;
begin
  FTok.Free();
  inherited Destroy();
end;

function TLexer.MapKeyword(const AUpper: string): TTokenKind;
begin
  if AUpper = 'PROGRAM' then Result := tkProgram
  else if AUpper = 'USES'    then Result := tkUses
  else if AUpper = 'VAR'     then Result := tkVar
  else if AUpper = 'THREADVAR' then Result := tkThreadVar
  else if AUpper = 'BEGIN'   then Result := tkBegin
  else if AUpper = 'END'     then Result := tkEnd
  else if AUpper = 'TYPE'    then Result := tkType
  else if AUpper = 'RECORD'  then Result := tkRecord
  else if AUpper = 'PACKED'  then Result := tkPacked
  else if AUpper = 'CLASS'     then Result := tkClass
  else if AUpper = 'PROCEDURE' then Result := tkProcedure
  else if AUpper = 'FUNCTION'  then Result := tkFunction
  else if AUpper = 'DIV'       then Result := tkDiv
  else if AUpper = 'MOD'       then Result := tkMod
  else if AUpper = 'IF'        then Result := tkIf
  else if AUpper = 'THEN'      then Result := tkThen
  else if AUpper = 'ELSE'      then Result := tkElse
  else if AUpper = 'WHILE'     then Result := tkWhile
  else if AUpper = 'DO'        then Result := tkDo
  else if AUpper = 'FOR'       then Result := tkFor
  else if AUpper = 'TO'        then Result := tkTo
  else if AUpper = 'DOWNTO'   then Result := tkDownto
  else if AUpper = 'REPEAT'   then Result := tkRepeat
  else if AUpper = 'UNTIL'    then Result := tkUntil
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
  else if AUpper = 'ARRAY'          then Result := tkArray
  else if AUpper = 'SET'            then Result := tkSet
  else if AUpper = 'IN'             then Result := tkIn
  else if AUpper = 'SHL'            then Result := tkShl
  else if AUpper = 'SHR'            then Result := tkShr
  else if AUpper = 'SAR'            then Result := tkSar
  else if AUpper = 'XOR'            then Result := tkXor
  else if AUpper = 'CONST'          then Result := tkConst
  else if AUpper = 'OUT'         then Result := tkOut
  else if AUpper = 'CONSTRUCTOR' then Result := tkConstructor
  else if AUpper = 'DESTRUCTOR'  then Result := tkDestructor
  else if AUpper = 'INHERITED'     then Result := tkInherited
  else if AUpper = 'INITIALIZATION' then Result := tkInitialization
  else if AUpper = 'FINALIZATION'   then Result := tkFinalization
  else
    Result := tkIdent;  { keyword outside Phase 1 grammar treated as ident }
end;

function TLexer.UnescapeString(const ARaw: string): string;
{ ARaw is the full source span. Handles: 'text' with '' → ' escaping,
  #nn numeric char literals (decimal), and concatenated runs like
  'abc'#13#10'def'. Uses OrdAt (0-based) so the body parses under both
  FPC and the self-hosted Blaise compiler. }
var
  I, Len, N, C: Integer;
begin
  Result := '';
  Len := Length(ARaw);
  I := 0;
  while I < Len do
  begin
    C := OrdAt(ARaw, I);
    if C = 39 then  { single quote }
    begin
      I := I + 1;
      while I < Len do
      begin
        C := OrdAt(ARaw, I);
        if C = 39 then
        begin
          if (I + 1 < Len) and (OrdAt(ARaw, I + 1) = 39) then
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
      while I < Len do
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

function TLexer.ProcessTextBlock(const ARaw: string): string;
var
  Len, I, C, Margin, LineStart, LineLen, Skip: Integer;
  Body: string;
begin
  Len := Length(ARaw);
  I := 3;  { 0-based: skip opening 3-char delimiter }
  if (I < Len) and (OrdAt(ARaw, I) = 13) then
    I := I + 1;
  if (I < Len) and (OrdAt(ARaw, I) = 10) then
    I := I + 1;
  Body := StrCopyFrom(ARaw, I, Len - 3 - I);

  Margin := 0;
  I := Len - 4;  { 0-based: last char before 3-char closing delimiter }
  while (I >= 0) and (OrdAt(ARaw, I) = 32) do
  begin
    Margin := Margin + 1;
    I := I - 1;
  end;

  if Margin = 0 then
  begin
    Result := '';
    Len := Length(Body);
    I := 0;
    while I < Len do
    begin
      C := OrdAt(Body, I);
      if C = 13 then
      begin
        Result := Result + #10;
        I := I + 1;
        if (I < Len) and (OrdAt(Body, I) = 10) then
          I := I + 1;
      end
      else if C = 10 then
      begin
        Result := Result + #10;
        I := I + 1;
      end
      else
      begin
        Result := Result + Chr(C);
        I := I + 1;
      end;
    end;
    Exit;
  end;

  Result := '';
  Len := Length(Body);
  I := 0;
  while I < Len do
  begin
    Skip := Margin;
    while (Skip > 0) and (I < Len) and (OrdAt(Body, I) = 32) do
    begin
      I := I + 1;
      Skip := Skip - 1;
    end;
    while I < Len do
    begin
      C := OrdAt(Body, I);
      if C = 13 then
      begin
        Result := Result + #10;
        I := I + 1;
        if (I < Len) and (OrdAt(Body, I) = 10) then
          I := I + 1;
        Break;
      end
      else if C = 10 then
      begin
        Result := Result + #10;
        I := I + 1;
        Break;
      end
      else
      begin
        Result := Result + Chr(C);
        I := I + 1;
      end;
    end;
  end;
end;

// Returns the directive keyword (uppercase) from a raw directive token text.
// e.g. '($IFDEF FPC)' -> 'IFDEF', '($ENDIF)' -> 'ENDIF'
// (angle brackets used in comment to avoid premature brace-comment closure)
function TLexer.DirectiveName(const AText: string): string;
var
  I, C: Integer;
begin
  Result := '';
  I := 2;  // 0-based: skip opening '{$' at indices 0 and 1
  while I < Length(AText) do
  begin
    C := OrdAt(AText, I);
    if (C = Ord('}')) or (C = Ord(' ')) then Break;
    Result := Result + UpCase(Chr(C));
    I := I + 1;
  end;
end;

// Skip tokens from inside a FALSE conditional block until the matching
// ELSE or ENDIF at depth 1 (handles nesting). Stops after consuming the token.
procedure TLexer.SkipToElseOrEndif;
var
  raw:   TFpgPasToken;
  depth: Integer;
  dname: string;
begin
  depth := 1;
  while depth > 0 do
  begin
    raw := FTok.NextToken();
    if raw.Kind = fptkEOF then Break;
    if raw.Kind = fptkDirective then
    begin
      dname := DirectiveName(FTok.TokenText());
      if (dname = 'IFDEF') or (dname = 'IFNDEF') then
        Inc(depth)
      else if dname = 'ENDIF' then
      begin
        Dec(depth);
      end
      else if (dname = 'ELSE') and (depth = 1) then
        Break;  // consumed the ELSE — caller continues in the true branch
    end;
  end;
end;

// Skip tokens from inside a TRUE conditional block (at ELSE) until
// the matching ENDIF at depth 1. Consumes the ENDIF.
procedure TLexer.SkipToEndif;
var
  raw:   TFpgPasToken;
  depth: Integer;
  dname: string;
begin
  depth := 1;
  while depth > 0 do
  begin
    raw := FTok.NextToken();
    if raw.Kind = fptkEOF then Break;
    if raw.Kind = fptkDirective then
    begin
      dname := DirectiveName(FTok.TokenText());
      if (dname = 'IFDEF') or (dname = 'IFNDEF') then
        Inc(depth)
      else if dname = 'ENDIF' then
        Dec(depth);
    end;
  end;
end;

function TLexer.Next: TToken;
var
  raw:  TFpgPasToken;
  text: string;
  dname: string;
begin
  while True do
  begin
    raw := FTok.NextToken();
    if raw.Kind in [fptkWhitespace, fptkLineEnding, fptkComment] then
      Continue;
    if raw.Kind = fptkDirective then
    begin
      text  := FTok.TokenText();
      dname := DirectiveName(text);
      if dname = 'IFDEF' then
      begin
        { Blaise defines no FPC-specific symbols — always skip the body }
        SkipToElseOrEndif();
      end
      else if dname = 'IFNDEF' then
      begin
        { Symbol is never defined in Blaise — always execute the body }
      end
      else if dname = 'ELSE' then
        SkipToEndif()   { we were in the true branch; skip the else }
      ;
      { ENDIF and all other directives: silently consumed }
      Continue;
    end;
    Break;
  end;

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
        text := FTok.TokenTextUpper();
        Result.Kind  := MapKeyword(text);
        Result.Value := FTok.TokenText();
      end;

    fptkIdentifier:
      begin
        text := FTok.TokenTextUpper();
        if      text = 'VIRTUAL'  then Result.Kind := tkVirtual
        else if text = 'OVERRIDE' then Result.Kind := tkOverride
        else if text = 'EXTERNAL' then Result.Kind := tkExternal
        else if text = 'EXIT'           then Result.Kind := tkExit
        else if text = 'BREAK'          then Result.Kind := tkBreak
        else if text = 'CONTINUE'       then Result.Kind := tkContinue
        else if text = 'INITIALIZATION' then Result.Kind := tkInitialization
        else if text = 'FINALIZATION'   then Result.Kind := tkFinalization
        else if text = 'CASE'     then Result.Kind := tkCase
        else if text = 'OF'       then Result.Kind := tkOf
        else if text = 'CONST'    then Result.Kind := tkConst
        else if text = 'OUT'      then Result.Kind := tkOut
        else                           Result.Kind := tkIdent;
        Result.Value := FTok.TokenText();
      end;

    fptkNumber:
      begin
        { Float only if it is a plain decimal literal (no $ % & prefix) and
          contains a decimal point or exponent marker.  Hex digits A-F and
          underscore groups like $FF_EC must not be misclassified as floats. }
        if (StrAt(FTok.TokenText(), 0) <> Ord('$')) and
           (StrAt(FTok.TokenText(), 0) <> Ord('%')) and
           (StrAt(FTok.TokenText(), 0) <> Ord('&')) and
           ((StrPos('.', FTok.TokenText()) >= 0) or
            (StrPos('e', FTok.TokenText()) >= 0) or
            (StrPos('E', FTok.TokenText()) >= 0)) then
          Result.Kind := tkFloatLit
        else
          Result.Kind := tkIntLit;
        Result.Value := FTok.TokenText();
      end;

    fptkString:
      begin
        Result.Kind  := tkStringLit;
        Result.Value := UnescapeString(FTok.TokenText());
      end;

    fptkTextBlock:
      begin
        Result.Kind  := tkStringLit;
        Result.Value := ProcessTextBlock(FTok.TokenText());
      end;

    fptkSymbol:
      begin
        text := FTok.TokenText();
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
        else if text = '..' then Result.Kind := tkDotDot
        else if text = '.'  then Result.Kind := tkDot
        else if text = '+'  then Result.Kind := tkPlus
        else if text = '-'  then Result.Kind := tkMinus
        else if text = '*'  then Result.Kind := tkStar
        else if text = '/'  then Result.Kind := tkSlash
        else if text = '^'  then Result.Kind := tkCaret
        else if text = '@'  then Result.Kind := tkAt
        else
          raise Exception.Create(Format(
            'Unexpected symbol ''%s'' at line %d col %d',
            [text, raw.Line, raw.Column]));
        Result.Value := text;
      end;

  else
    raise Exception.Create(Format(
      'Unexpected token kind %d at line %d col %d',
      [Ord(raw.Kind), raw.Line, raw.Column]));
  end;
end;

function TokenKindName(AKind: TTokenKind): string;
begin
  case AKind of
    tkEOF:            Result := '<eof>';
    tkIntLit:         Result := 'integer literal';
    tkFloatLit:       Result := 'float literal';
    tkStringLit:      Result := 'string literal';
    tkInitialization: Result := 'initialization';
    tkFinalization:   Result := 'finalization';
    tkProgram:        Result := 'program';
    tkUses:           Result := 'uses';
    tkType:           Result := 'type';
    tkRecord:         Result := 'record';
    tkPacked:         Result := 'packed';
    tkClass:          Result := 'class';
    tkProcedure:      Result := 'procedure';
    tkFunction:       Result := 'function';
    tkVar:            Result := 'var';
    tkThreadVar:      Result := 'threadvar';
    tkBegin:          Result := 'begin';
    tkEnd:            Result := 'end';
    tkIf:             Result := 'if';
    tkThen:           Result := 'then';
    tkElse:           Result := 'else';
    tkWhile:          Result := 'while';
    tkDo:             Result := 'do';
    tkFor:            Result := 'for';
    tkTo:             Result := 'to';
    tkDownto:         Result := 'downto';
    tkRepeat:         Result := 'repeat';
    tkUntil:          Result := 'until';
    tkTry:            Result := 'try';
    tkFinally:        Result := 'finally';
    tkExcept:         Result := 'except';
    tkRaise:          Result := 'raise';
    tkNil:            Result := 'nil';
    tkUnit:           Result := 'unit';
    tkIntf:           Result := 'interface';
    tkImplementation: Result := 'implementation';
    tkVirtual:        Result := 'virtual';
    tkOverride:       Result := 'override';
    tkExternal:       Result := 'external';
    tkIs:             Result := 'is';
    tkAs:             Result := 'as';
    tkAnd:            Result := 'and';
    tkOr:             Result := 'or';
    tkNot:            Result := 'not';
    tkExit:           Result := 'exit';
    tkBreak:          Result := 'break';
    tkContinue:       Result := 'continue';
    tkInherited:      Result := 'inherited';
    tkCase:           Result := 'case';
    tkOf:             Result := 'of';
    tkArray:          Result := 'array';
    tkSet:            Result := 'set';
    tkIn:             Result := 'in';
    tkShl:            Result := 'shl';
    tkShr:            Result := 'shr';
    tkSar:            Result := 'sar';
    tkXor:            Result := 'xor';
    tkConst:          Result := 'const';
    tkOut:            Result := 'out';
    tkConstructor:    Result := 'constructor';
    tkDestructor:     Result := 'destructor';
    tkIdent:          Result := 'identifier';
    tkPlus:           Result := '+';
    tkMinus:          Result := '-';
    tkStar:           Result := '*';
    tkSlash:          Result := '/';
    tkDiv:            Result := 'div';
    tkMod:            Result := 'mod';
    tkAssign:         Result := ':=';
    tkEquals:         Result := '=';
    tkNotEquals:      Result := '<>';
    tkLessThan:       Result := '<';
    tkGreaterThan:    Result := '>';
    tkLessEqual:      Result := '<=';
    tkGreaterEqual:   Result := '>=';
    tkColon:          Result := ':';
    tkLParen:         Result := '(';
    tkRParen:         Result := ')';
    tkLBracket:       Result := '[';
    tkRBracket:       Result := ']';
    tkComma:          Result := ',';
    tkSemicolon:      Result := ';';
    tkDot:            Result := '.';
    tkDotDot:         Result := '..';
    tkCaret:          Result := '^';
    tkAt:             Result := '@';
  else
    Result := '<unknown(' + IntToStr(Ord(AKind)) + ')>';
  end;
end;

end.
