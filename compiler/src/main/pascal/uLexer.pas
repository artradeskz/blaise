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
    tkVar,
    tkBegin,
    tkEnd,
    { Identifier }
    tkIdent,
    { Arithmetic operators }
    tkPlus,
    tkMinus,
    tkStar,
    tkSlash,    { '/' — future: float division }
    tkDiv,      { 'div' keyword — integer division }
    { Assignment and colon }
    tkAssign,     { := }
    tkColon,      { :  }
    { Grouping and punctuation }
    tkLParen,
    tkRParen,
    tkComma,
    tkSemicolon,
    tkDot
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
  else if AUpper = 'DIV'     then Result := tkDiv
  else
    Result := tkIdent;  { keyword outside Phase 1 grammar treated as ident }
end;

function TLexer.UnescapeString(const ARaw: string): string;
{ ARaw is the full source span including surrounding quotes.
  Handles: 'text' with '' → ' escaping.
  Phase 1 supports only single-quoted string literals; #nn and ^X forms
  are not yet part of the Clean Pascal spec. }
var
  I, Len: Integer;
begin
  Result := '';
  Len := Length(ARaw);
  if (Len >= 2) and (ARaw[1] = '''') then
  begin
    I := 2;
    while I <= Len do
    begin
      if ARaw[I] = '''' then
      begin
        if (I < Len) and (ARaw[I + 1] = '''') then
        begin
          Result := Result + '''';
          Inc(I, 2);
        end
        else
          Inc(I);  { closing quote }
      end
      else
      begin
        Result := Result + ARaw[I];
        Inc(I);
      end;
    end;
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
        Result.Kind  := tkIdent;
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
        else if text = ':'  then Result.Kind := tkColon
        else if text = '('  then Result.Kind := tkLParen
        else if text = ')'  then Result.Kind := tkRParen
        else if text = ','  then Result.Kind := tkComma
        else if text = ';'  then Result.Kind := tkSemicolon
        else if text = '.'  then Result.Kind := tkDot
        else if text = '+'  then Result.Kind := tkPlus
        else if text = '-'  then Result.Kind := tkMinus
        else if text = '*'  then Result.Kind := tkStar
        else if text = '/'  then Result.Kind := tkSlash
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
