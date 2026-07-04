{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for Security.Crypto (SHA-1), including the Base64-composed WebSocket
  handshake.  Self-registers via the initialization section. }

unit Crypto.Tests;

interface

uses
  blaise.testing, Security.Crypto, Encoding.Base64;

type
  TCryptoTests = class(TTestCase)
  published
    procedure TestSha1Hex_KnownVectors;
    procedure TestSha1_DigestLength;
    procedure TestSha1Base64_WebSocketHandshake;
  end;

implementation

procedure TCryptoTests.TestSha1Hex_KnownVectors;
begin
  { FIPS / well-known SHA-1 test vectors. }
  AssertEquals('empty', 'da39a3ee5e6b4b0d3255bfef95601890afd80709', Sha1Hex(''));
  AssertEquals('abc',   'a9993e364706816aba3e25717850c26c9cd0d89d', Sha1Hex('abc'));
  AssertEquals('quick brown fox',
    '2fd4e1c67a2d28fced849ee1bb76e7391b93eb12',
    Sha1Hex('The quick brown fox jumps over the lazy dog'));
end;

procedure TCryptoTests.TestSha1_DigestLength;
begin
  AssertEquals('raw digest is 20 bytes', 20, Length(Sha1('anything')));
end;

procedure TCryptoTests.TestSha1Base64_WebSocketHandshake;
const
  GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
begin
  { RFC 6455 example: Sec-WebSocket-Accept = base64(sha1(key + GUID)). }
  AssertEquals('ws accept',
    's3pPLMBiTxaQ9kYGzzhZRbK+xOo=',
    Base64Encode(Sha1('dGhlIHNhbXBsZSBub25jZQ==' + GUID)));
end;

initialization
  RegisterTest(TCryptoTests);

end.
