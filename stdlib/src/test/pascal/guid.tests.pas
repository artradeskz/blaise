{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for Security.Guid: v4 GUID format, version/variant bits, uniqueness.
  Self-registers via the initialization section. }

unit Guid.Tests;

interface

uses
  blaise.testing, Security.Guid;

type
  TGuidTests = class(TTestCase)
  published
    procedure TestFormat;
    procedure TestVersionAndVariant;
    procedure TestRawLength;
    procedure TestUnique;
  end;

implementation

function IsHexLower(B: Byte): Boolean;
begin
  Result := ((B >= 48) and (B <= 57)) or ((B >= 97) and (B <= 102));
end;

procedure TGuidTests.TestFormat;
var
  G: string;
  I: Integer;
  Ch: Byte;
begin
  G := NewGuid();
  AssertEquals('length', 36, Integer(Length(G)));
  for I := 0 to 35 do
  begin
    Ch := Byte(G[I]);
    if (I = 8) or (I = 13) or (I = 18) or (I = 23) then
      AssertEquals('hyphen at ' + IntToStr(I), 45, Integer(Ch))
    else
      AssertTrue('hex at ' + IntToStr(I), IsHexLower(Ch));
  end;
end;

procedure TGuidTests.TestVersionAndVariant;
var
  G: string;
begin
  G := NewGuid();
  { version nibble: position 14 (after 'xxxxxxxx-xxxx-') must be '4' (=52) }
  AssertEquals('version 4', 52, Integer(Byte(G[14])));
  { variant nibble: position 19 must be one of '8','9','a','b' (56,57,97,98) }
  AssertTrue('variant 8/9/a/b',
    (Byte(G[19]) = 56) or (Byte(G[19]) = 57) or
    (Byte(G[19]) = 97) or (Byte(G[19]) = 98));
end;

procedure TGuidTests.TestRawLength;
var
  R: string;
begin
  R := NewGuidRaw();
  AssertEquals('16 bytes', 16, Integer(Length(R)));
  { version bits in raw byte 6 (index 6): high nibble = 4 }
  AssertEquals('raw version', $40, Integer(Byte(R[6]) and $F0));
  { variant bits in raw byte 8: top two bits = 10 }
  AssertEquals('raw variant', $80, Integer(Byte(R[8]) and $C0));
end;

procedure TGuidTests.TestUnique;
var
  A, B: string;
begin
  A := NewGuid();
  B := NewGuid();
  AssertTrue('two guids differ', A <> B);
end;

initialization
  RegisterTest(TGuidTests);

end.
