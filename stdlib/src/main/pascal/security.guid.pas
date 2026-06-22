{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - RFC 4122 version-4 (random) GUID/UUID generation.

  A v4 GUID is 16 random bytes with the version (4) and variant (RFC 4122)
  bits forced.  Randomness comes from the kernel CSPRNG via getrandom(2)
  (Linux 3.17+, glibc 2.25+); no seeding and no PRNG state.

  NewGuid    -> canonical lowercase string, e.g.
                '3f2504e0-4f89-41d3-9a0c-0305e82c3301'.
  NewGuidRaw -> the 16 raw bytes (as a string), for callers that want the
                binary form. }

unit Security.Guid;

interface

{ A new random (v4) GUID in canonical 8-4-4-4-12 lowercase hex form. }
function NewGuid: string;

{ The 16 raw bytes of a new v4 GUID (version/variant bits already set). }
function NewGuidRaw: string;

implementation

uses
  StrUtils;   { TStringBuilder }

{ getrandom(buf, buflen, flags): fill buf with buflen random bytes from the
  kernel CSPRNG.  flags=0 reads from the same pool as /dev/urandom. }
function c_getrandom(ABuf: Pointer; ALen: Int64; AFlags: Integer): Int64;
  external name 'getrandom';

function NewGuidRaw: string;
var
  Buf: array[0..15] of Byte;
  SB: TStringBuilder;
  I: Integer;
begin
  if c_getrandom(@Buf[0], 16, 0) <> 16 then
  begin
    Result := '';
    Exit;
  end;
  { version 4: high nibble of byte 6 = 0100 }
  Buf[6] := (Buf[6] and $0F) or $40;
  { variant RFC 4122: top two bits of byte 8 = 10 }
  Buf[8] := (Buf[8] and $3F) or $80;

  SB := TStringBuilder.Create();
  for I := 0 to 15 do
    SB.AppendByte(Buf[I]);
  Result := SB.ToString();
  SB.Free();
end;

function HexDigit(AValue: Integer): Byte;
begin
  { 0-9 -> '0'..'9' (48..57), 10-15 -> 'a'..'f' (97..102) }
  if AValue < 10 then
    Result := 48 + AValue
  else
    Result := 87 + AValue;
end;

function NewGuid: string;
var
  Raw: string;
  SB: TStringBuilder;
  I, B: Integer;
begin
  Raw := NewGuidRaw();
  if Raw = '' then
  begin
    Result := '';
    Exit;
  end;
  SB := TStringBuilder.Create();
  for I := 0 to 15 do
  begin
    { hyphens after bytes 4, 6, 8, 10 (the 8-4-4-4-12 grouping) }
    if (I = 4) or (I = 6) or (I = 8) or (I = 10) then
      SB.AppendByte(45);   { '-' }
    B := Byte(Raw[I]);
    SB.AppendByte(HexDigit((B shr 4) and $0F));
    SB.AppendByte(HexDigit(B and $0F));
  end;
  Result := SB.ToString();
  SB.Free();
end;

end.
