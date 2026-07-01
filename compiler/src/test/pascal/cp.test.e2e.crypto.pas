{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.crypto;

{ E2E smoke test for the Security.Crypto stdlib unit.
  Guards against native-backend miscompilation of the hash
  implementations (the Ord(S[I]) precedent). }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ECryptoTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_Sha256Hex_Empty;
  end;

implementation

procedure TE2ECryptoTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-crypto');
end;

procedure TE2ECryptoTests.TestRun_Sha256Hex_Empty;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnAll(
    '''
    program P;
    uses Security.Crypto;
    begin
      WriteLn(Sha256Hex(''));
    end.
    ''',
    'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855' + LineEnding,
    0);
end;

initialization
  RegisterTest(TE2ECryptoTests);

end.
