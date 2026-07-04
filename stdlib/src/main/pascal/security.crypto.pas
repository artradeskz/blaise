{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - cryptographic hash functions.

  The home for hash/digest primitives (Java's java.security, .NET's
  System.Security.Cryptography).  SHA-1 is provided; further digests and HMAC
  belong here.

  NB: SHA-1 is not collision-resistant and must not be used for new security
  decisions.  It remains required for interop where a protocol mandates it
  (e.g. the WebSocket opening handshake, Git object ids).

  Base64 lives in Encoding.Base64, not here: it is a text encoding, not crypto.
  Compose them at the call site, e.g.  Base64Encode(Sha1(Key + GUID)).

  NB: shifts and 'not' are not masked to 32 bits by the backend, so every
  32-bit operation is wrapped with 'and $FFFFFFFF'. }

unit Security.Crypto;

interface

{ Raw 20-byte SHA-1 digest of S (S treated as raw bytes), returned as a string
  of 20 bytes. }
function Sha1(const AData: string): string;

{ SHA-1 digest as a 40-character lower-case hex string. }
function Sha1Hex(const AData: string): string;

implementation

uses
  Classes, StrUtils;

const
  MASK32 = $FFFFFFFF;

function Rotl32(V: UInt32; ABits: Integer): UInt32;
begin
  Result := ((V shl ABits) or (V shr (32 - ABits))) and MASK32;
end;

function Sha1(const AData: string): string;
var
  H0, H1, H2, H3, H4: UInt32;
  MsgLen, TotalBits: Int64;
  PadLen, I, T, ChunkStart, NumChunks, C: Integer;
  Msg: array[0..63] of Byte;     { current 64-byte chunk }
  W: array[0..79] of UInt32;
  A, B, Cc, D, E, F, K, Temp: UInt32;
  PData: string;
  SB, OutSB: TStringBuilder;
begin
  { Build the padded message:
    original || 0x80 || 0x00... || 64-bit big-endian bit length.
    AppendByte guarantees raw single bytes. }
  MsgLen := Length(AData);
  TotalBits := MsgLen * 8;

  PadLen := 56 - ((MsgLen + 1) mod 64);
  if PadLen < 0 then
    PadLen := PadLen + 64;

  SB := TStringBuilder.Create();
  SB.Append(AData);
  SB.AppendByte(128);
  for I := 1 to PadLen do
    SB.AppendByte(0);
  for I := 7 downto 0 do
    SB.AppendByte((TotalBits shr (I * 8)) and $FF);
  PData := SB.ToString();
  SB.Free();

  H0 := $67452301;
  H1 := $EFCDAB89;
  H2 := $98BADCFE;
  H3 := $10325476;
  H4 := $C3D2E1F0;

  NumChunks := Length(PData) div 64;
  for C := 0 to NumChunks - 1 do
  begin
    ChunkStart := C * 64;
    for I := 0 to 63 do
      Msg[I] := Byte(PData[ChunkStart + I]);

    for T := 0 to 15 do
      W[T] := ((UInt32(Msg[T * 4]) shl 24) or
               (UInt32(Msg[T * 4 + 1]) shl 16) or
               (UInt32(Msg[T * 4 + 2]) shl 8) or
                UInt32(Msg[T * 4 + 3])) and MASK32;
    for T := 16 to 79 do
      W[T] := Rotl32((W[T-3] xor W[T-8] xor W[T-14] xor W[T-16]), 1);

    A := H0; B := H1; Cc := H2; D := H3; E := H4;

    for T := 0 to 79 do
    begin
      if T < 20 then
      begin
        F := (B and Cc) or ((not B) and D);
        K := $5A827999;
      end
      else if T < 40 then
      begin
        F := B xor Cc xor D;
        K := $6ED9EBA1;
      end
      else if T < 60 then
      begin
        F := (B and Cc) or (B and D) or (Cc and D);
        K := $8F1BBCDC;
      end
      else
      begin
        F := B xor Cc xor D;
        K := $CA62C1D6;
      end;
      F := F and MASK32;
      Temp := (Rotl32(A, 5) + F + E + K + W[T]) and MASK32;
      E := D;
      D := Cc;
      Cc := Rotl32(B, 30);
      B := A;
      A := Temp;
    end;

    H0 := (H0 + A) and MASK32;
    H1 := (H1 + B) and MASK32;
    H2 := (H2 + Cc) and MASK32;
    H3 := (H3 + D) and MASK32;
    H4 := (H4 + E) and MASK32;
  end;

  { Emit 20 raw bytes, big-endian. }
  OutSB := TStringBuilder.Create();
  OutSB.AppendByte((H0 shr 24) and $FF); OutSB.AppendByte((H0 shr 16) and $FF);
  OutSB.AppendByte((H0 shr 8) and $FF);  OutSB.AppendByte(H0 and $FF);
  OutSB.AppendByte((H1 shr 24) and $FF); OutSB.AppendByte((H1 shr 16) and $FF);
  OutSB.AppendByte((H1 shr 8) and $FF);  OutSB.AppendByte(H1 and $FF);
  OutSB.AppendByte((H2 shr 24) and $FF); OutSB.AppendByte((H2 shr 16) and $FF);
  OutSB.AppendByte((H2 shr 8) and $FF);  OutSB.AppendByte(H2 and $FF);
  OutSB.AppendByte((H3 shr 24) and $FF); OutSB.AppendByte((H3 shr 16) and $FF);
  OutSB.AppendByte((H3 shr 8) and $FF);  OutSB.AppendByte(H3 and $FF);
  OutSB.AppendByte((H4 shr 24) and $FF); OutSB.AppendByte((H4 shr 16) and $FF);
  OutSB.AppendByte((H4 shr 8) and $FF);  OutSB.AppendByte(H4 and $FF);
  Result := OutSB.ToString();
  OutSB.Free();
end;

function Sha1Hex(const AData: string): string;
var
  Raw: string;
  SB: TStringBuilder;
  I, B: Integer;
const
  Hex = '0123456789abcdef';
begin
  Raw := Sha1(AData);
  SB := TStringBuilder.Create();
  for I := 0 to Length(Raw) - 1 do
  begin
    B := Byte(Raw[I]);
    SB.AppendByte(Byte(Hex[B div 16]));   { Hex is 0-based in Blaise }
    SB.AppendByte(Byte(Hex[B mod 16]));
  end;
  Result := SB.ToString();
  SB.Free();
end;

end.
