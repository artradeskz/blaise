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
    { Unit-qualified symbol references 'UnitName.Symbol'. }
    procedure TestRun_QualifiedSystem_CallExprAndStmt;
    procedure TestRun_QualifiedUnit_CallAndVar;
    procedure TestRun_DottedQualifiedUnit_CallAndVar;
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

procedure TE2EUsesChainTests.TestRun_QualifiedSystem_CallExprAndStmt;
const
  Src = '''
    program P;
    begin
      System.WriteLn(System.Length('hello'))
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 'System.WriteLn' (qualified call statement) and 'System.Length(...)'
    (qualified call expression) both resolve via the implicit System unit. }
  AssertTrue(CompileAndRun(Src, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Length(''hello'') = 5', '5' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_QualifiedUnit_CallAndVar;
const
  UnitSrc = '''
    unit qsym;
    interface
    function Add3(N: Integer): Integer;
    var
      GBase: Integer;
    implementation
    function Add3(N: Integer): Integer;
    begin
      Result := N + 3
    end;
    end.
    ''';
  DrvSrc = '''
    program P;
    uses qsym;
    begin
      qsym.GBase := 10;
      WriteLn(qsym.Add3(qsym.GBase))
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Qualified assignment target (qsym.GBase :=), qualified var read
    (qsym.GBase), and qualified function call (qsym.Add3) across a used unit. }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnit('qsym', UnitSrc, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Add3(10) = 13', '13' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_DottedQualifiedUnit_CallAndVar;
const
  UnitSrc = '''
    unit My.Pkg;
    interface
    function Add3(N: Integer): Integer;
    var
      GBase: Integer;
    implementation
    function Add3(N: Integer): Integer;
    begin
      Result := N + 3
    end;
    end.
    ''';
  DrvSrc = '''
    program P;
    uses My.Pkg;
    begin
      My.Pkg.GBase := 10;
      WriteLn(My.Pkg.Add3(My.Pkg.GBase))
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Same as above but through a two-part dotted unit name 'My.Pkg'. }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnit('My.Pkg', UnitSrc, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Add3(10) = 13', '13' + LE, Output);
end;

initialization
  RegisterTest(TE2EUsesChainTests);

end.
