{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  String helpers — 0-based string conventions.

  Blaise strings are 0-based: S[0] is the first character, Pos returns
  a 0-based index (-1 = not found), Copy takes a 0-based From argument.

  UTF-8 aware functions added for lexer/parser support:
    - UTF8CharLen: returns byte length of UTF-8 sequence starting at given byte
    - UTF8CodePoint: decodes Unicode codepoint from UTF-8 bytes at position
    - IsUTF8Letter: checks if codepoint is a letter (Latin, Cyrillic) or underscore
    - IsUTF8Digit: checks if codepoint is an ASCII digit 0-9
}

unit uStrCompat;

interface

{ StrAt: return ordinal of character at 0-based index I }
function StrAt(const S: string; I: Integer): Integer;

{ StrCopyFrom: copy from 0-based position From, Count chars }
function StrCopyFrom(const S: string; From, Count: Integer): string;

{ StrCopyTail: copy from 0-based position From to end of string }
function StrCopyTail(const S: string; From: Integer): string;

{ StrHead: copy the first N characters (equivalent to Copy(s, 0, N)) }
function StrHead(const S: string; N: Integer): string;

{ StrPos: find sub in s, return 0-based index; -1 if not found }
function StrPos(const Sub, S: string): Integer;

{ StripUnderscores: return S with all '_' characters removed }
function StripUnderscores(const S: string): string;

{ ParseIntLiteral: convert a Pascal integer-literal token value to Int64.
  Accepts decimal, $hex, %binary, &octal, with optional _ separators.
  Raises EConvertError on invalid input or on values that overflow Int64. }
function ParseIntLiteral(const S: string): Int64;

{ Like ParseIntLiteral but tolerant of UInt64-range values.  AValue holds
  the resulting bit pattern (cast to Int64); AIsUInt64 is True when the
  source value exceeded MaxInt64 (i.e. the bit pattern must be interpreted
  as UInt64).  Raises EConvertError on overflow past UInt64. }
procedure ParseIntOrUInt64Literal(const S: string;
  var AValue: Int64; var AIsUInt64: Boolean);

{ UTF-8 helper routines }

{ Return number of bytes in the UTF-8 sequence that starts at byte I.
  Returns 1 for ASCII, 2 for Cyrillic (U+0080..U+07FF), 0 for invalid. }
function UTF8CharLen(const S: string; I: Integer): Integer;

{ Decode a Unicode codepoint from the UTF-8 sequence starting at byte I.
  Returns the codepoint (e.g. $041F for 'П'), or -1 if the sequence is
  invalid or truncated. }
function UTF8CodePoint(const S: string; I: Integer): Integer;

{ Returns True if the codepoint is a letter (Latin A-Z, a-z, Cyrillic
  А-Я, а-я, Ё, ё) or underscore (_). }
function IsUTF8Letter(CP: Integer): Boolean;

{ Returns True if the codepoint is an ASCII digit 0-9. }
function IsUTF8Digit(CP: Integer): Boolean;

implementation

function StrAt(const S: string; I: Integer): Integer;
begin
  Result := OrdAt(S, I);
end;

function StrCopyFrom(const S: string; From, Count: Integer): string;
begin
  Result := Copy(S, From, Count);
end;

function StrCopyTail(const S: string; From: Integer): string;
begin
  Result := Copy(S, From, MaxInt);
end;

function StrHead(const S: string; N: Integer): string;
begin
  Result := Copy(S, 0, N);
end;

function StrPos(const Sub, S: string): Integer;
begin
  Result := Pos(Sub, S);
end;

function StripUnderscores(const S: string): string;
var
  I: Integer;
begin
  Result := '';
  for I := 0 to Length(S) - 1 do
    if StrAt(S, I) <> Ord('_') then
      Result := Result + Chr(StrAt(S, I));
end;

procedure ParseIntOrUInt64Literal(const S: string;
  var AValue: Int64; var AIsUInt64: Boolean);
var
  I, Len:    Integer;
  Digits:    string;
  C:         Integer;
  Prefix:    Integer;
  Digit:     Integer;
begin
  AValue    := 0;
  AIsUInt64 := False;
  Len := Length(S);
  if Len = 0 then
    raise EConvertError.Create('Empty integer literal');

  Prefix := StrAt(S, 0);

  { Strip underscores from digit portion, validate placement }
  Digits := '';
  if (Prefix = Ord('$')) or (Prefix = Ord('%')) or (Prefix = Ord('&')) then
    I := 1   { skip prefix char }
  else
    I := 0;

  { First digit after prefix must not be underscore }
  if (I < Len) and (StrAt(S, I) = Ord('_')) then
    raise EConvertError.Create('Invalid integer literal: underscore at start of digits in ''' + S + '''');

  while I < Len do
  begin
    C := StrAt(S, I);
    if C <> Ord('_') then
      Digits := Digits + Chr(C);
    { Trailing underscore: this is '_' and next position is end-of-string }
    if (C = Ord('_')) and (I + 1 = Len) then
      raise EConvertError.Create('Invalid integer literal: trailing underscore in ''' + S + '''');
    Inc(I);
  end;

  if Digits = '' then
    raise EConvertError.Create('Invalid integer literal: no digits in ''' + S + '''');

  AValue := 0;
  case Prefix of
    Ord('$'):
      begin
        if Length(Digits) > 16 then
          raise EConvertError.Create('Hexadecimal literal exceeds 64 bits: ''' + S + '''');
        for I := 0 to Length(Digits) - 1 do
        begin
          C := StrAt(Digits, I);
          if (C >= Ord('0')) and (C <= Ord('9')) then
            Digit := C - Ord('0')
          else if (C >= Ord('A')) and (C <= Ord('F')) then
            Digit := C - Ord('A') + 10
          else if (C >= Ord('a')) and (C <= Ord('f')) then
            Digit := C - Ord('a') + 10
          else
            raise EConvertError.Create('Invalid hexadecimal digit in ''' + S + '''');
          AValue := AValue * 16 + Int64(Digit);  { 4-bit shift never overflows when len ≤ 16 }
        end;
      end;
    Ord('%'):
      begin
        if Length(Digits) > 64 then
          raise EConvertError.Create('Binary literal exceeds 64 bits: ''' + S + '''');
        for I := 0 to Length(Digits) - 1 do
        begin
          C := StrAt(Digits, I);
          if (C <> Ord('0')) and (C <> Ord('1')) then
            raise EConvertError.Create('Invalid binary digit in ''' + S + '''');
          AValue := AValue * 2 + Int64(C - Ord('0'));
        end;
      end;
    Ord('&'):
      begin
        for I := 0 to Length(Digits) - 1 do
        begin
          C := StrAt(Digits, I);
          Digit := C - Ord('0');
          if (Digit < 0) or (Digit > 7) then
            raise EConvertError.Create('Invalid octal digit in ''' + S + '''');
          AValue := AValue * 8 + Int64(Digit);
        end;
      end;
  else
    begin
      for I := 0 to Length(Digits) - 1 do
      begin
        C := StrAt(Digits, I);
        Digit := C - Ord('0');
        if (Digit < 0) or (Digit > 9) then
          raise EConvertError.Create('Invalid decimal digit in ''' + S + '''');
        AValue := AValue * 10 + Int64(Digit);
      end;
    end;
  end;

  { When the bit pattern's sign bit is set the unsigned interpretation
    exceeds MaxInt64, so the literal should be treated as UInt64. }
  AIsUInt64 := AValue < 0;
end;

function ParseIntLiteral(const S: string): Int64;
var
  V:   Int64;
  IsU: Boolean;
begin
  ParseIntOrUInt64Literal(S, V, IsU);
  if IsU then
    raise EConvertError.Create('Integer literal exceeds Int64 range: ''' + S + '''');
  Result := V;
end;

{ ------------------------------------------------------------------------ }
{  UTF-8 helper routines                                                    }
{ ------------------------------------------------------------------------ }

function UTF8CharLen(const S: string; I: Integer): Integer;
var
  B: Integer;
begin
  if (I < 0) or (I >= Length(S)) then
  begin
    Result := 0;
    Exit;
  end;
  B := OrdAt(S, I);
  if B <= 127 then
    Result := 1
  else if (B >= $C2) and (B <= $DF) then
  begin
    { 2-byte sequence: need 1 continuation byte }
    if I + 1 < Length(S) then
      Result := 2
    else
      Result := 0;  { truncated }
  end
  else if (B >= $E0) and (B <= $EF) then
  begin
    { 3-byte sequence: need 2 continuation bytes }
    if I + 2 < Length(S) then
      Result := 3
    else
      Result := 0;
  end
  else if (B >= $F0) and (B <= $F4) then
  begin
    { 4-byte sequence: need 3 continuation bytes }
    if I + 3 < Length(S) then
      Result := 4
    else
      Result := 0;
  end
  else
    Result := 0;  { invalid leading byte or continuation byte alone }
end;

function UTF8CodePoint(const S: string; I: Integer): Integer;
var
  B0, B1, B2, B3: Integer;
  Len: Integer;
begin
  Len := Length(S);
  if (I < 0) or (I >= Len) then
  begin
    Result := -1;
    Exit;
  end;
  B0 := OrdAt(S, I);
  if B0 <= 127 then
  begin
    Result := B0;
    Exit;
  end
  else if (B0 >= $C2) and (B0 <= $DF) then
  begin
    if I + 1 >= Len then
    begin
      Result := -1;
      Exit;
    end;
    B1 := OrdAt(S, I + 1);
    if (B1 and $C0) <> $80 then
    begin
      Result := -1;
      Exit;
    end;
    Result := ((B0 and $1F) shl 6) or (B1 and $3F);
  end
  else if (B0 >= $E0) and (B0 <= $EF) then
  begin
    if I + 2 >= Len then
    begin
      Result := -1;
      Exit;
    end;
    B1 := OrdAt(S, I + 1);
    B2 := OrdAt(S, I + 2);
    if ((B1 and $C0) <> $80) or ((B2 and $C0) <> $80) then
    begin
      Result := -1;
      Exit;
    end;
    Result := ((B0 and $0F) shl 12) or ((B1 and $3F) shl 6) or (B2 and $3F);
  end
  else if (B0 >= $F0) and (B0 <= $F4) then
  begin
    if I + 3 >= Len then
    begin
      Result := -1;
      Exit;
    end;
    B1 := OrdAt(S, I + 1);
    B2 := OrdAt(S, I + 2);
    B3 := OrdAt(S, I + 3);
    if ((B1 and $C0) <> $80) or ((B2 and $C0) <> $80) or ((B3 and $C0) <> $80) then
    begin
      Result := -1;
      Exit;
    end;
    Result := ((B0 and $07) shl 18) or ((B1 and $3F) shl 12) or
              ((B2 and $3F) shl 6) or (B3 and $3F);
  end
  else
    Result := -1;  { invalid byte }
end;

function IsUTF8Letter(CP: Integer): Boolean;
begin
  { ASCII letters }
  if ((CP >= 65) and (CP <= 90)) or ((CP >= 97) and (CP <= 122)) then
  begin
    Result := True;
    Exit;
  end;
  { Underscore }
  if CP = 95 then
  begin
    Result := True;
    Exit;
  end;
  { Cyrillic basic: U+0410..U+044F (А-Я, а-я) }
  if (CP >= $0410) and (CP <= $044F) then
  begin
    Result := True;
    Exit;
  end;
  { Ё (U+0401) and ё (U+0451) }
  if (CP = $0401) or (CP = $0451) then
  begin
    Result := True;
    Exit;
  end;
  Result := False;
end;

function IsUTF8Digit(CP: Integer): Boolean;
begin
  Result := (CP >= 48) and (CP <= 57);
end;

end.