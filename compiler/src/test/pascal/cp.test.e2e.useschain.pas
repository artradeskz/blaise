{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.useschain;

{ Regression tests for the per-unit visibility / uses-chain lookup.

  - The implicit System unit must always be reachable without an
    explicit `uses` clause in the user program.
  - Builtins like WriteLn, IntToStr, Length must resolve through the
    chain, not via a special-cased compiler hook. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EUsesChainTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_ImplicitSystem_NoUsesClause_WriteLnInt;
    procedure TestRun_ImplicitSystem_NoUsesClause_IntToStr;
    procedure TestRun_ImplicitSystem_NoUsesClause_Length;
  end;

implementation

procedure TE2EUsesChainTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-useschain');
end;

const
  LE = #10;

  SrcWriteLnInt = '''
    program P;
    begin
      WriteLn(42)
    end.
    ''';

  SrcIntToStr = '''
    program P;
    var
      S: string;
    begin
      S := IntToStr(123);
      WriteLn(S)
    end.
    ''';

  SrcLength = '''
    program P;
    var
      S: string;
      N: Integer;
    begin
      S := 'hello';
      N := Length(S);
      WriteLn(N)
    end.
    ''';

procedure TE2EUsesChainTests.TestRun_ImplicitSystem_NoUsesClause_WriteLnInt;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcWriteLnInt, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('writeln(42)', '42' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_ImplicitSystem_NoUsesClause_IntToStr;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcIntToStr, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('IntToStr(123)', '123' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_ImplicitSystem_NoUsesClause_Length;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcLength, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Length(''hello'')', '5' + LE, Output);
end;

initialization
  RegisterTest(TE2EUsesChainTests);

end.
