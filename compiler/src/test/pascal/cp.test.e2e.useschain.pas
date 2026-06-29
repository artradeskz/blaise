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
    { Cross-unit const shadowing: two used units export the same const name;
      the unit later in the `uses` clause wins (last-in-uses), and reversing
      the order flips the winner. }
    procedure TestRun_CrossUnitConst_LastWins;
    procedure TestRun_CrossUnitConst_LastWins_Reversed;
    { Unit-qualified const disambiguation: a 'Unit.Foo' reference resolves
      against that specific unit's exports, so it is never shadowed by a
      same-named const in another used unit, regardless of `uses` order. }
    procedure TestRun_CrossUnitConst_QualifiedDisambig;
    { Unit-qualified ancestor in a class declaration: class(Unit.TParent)
      binds to that unit's type so inheritance works across units. }
    procedure TestRun_QualifiedInheritance;
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

const
  UA_Const = '''
    unit ua;
    interface
    const Foo = 100;
    implementation
    end.
    ''';
  UB_Const = '''
    unit ub;
    interface
    const Foo = 200;
    implementation
    end.
    ''';

procedure TE2EUsesChainTests.TestRun_CrossUnitConst_LastWins;
const
  DrvSrc = '''
    program P;
    uses ua, ub;
    begin
      WriteLn(Foo)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Both ua and ub export `Foo`; ub is later in `uses`, so bare Foo = 200. }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnits(UA_Const, UB_Const, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('last-in-uses (ub) wins', '200' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_CrossUnitConst_LastWins_Reversed;
const
  DrvSrc = '''
    program P;
    uses ub, ua;
    begin
      WriteLn(Foo)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Reversed `uses` order: ua is now later, so bare Foo = 100. }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnits(UA_Const, UB_Const, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('last-in-uses (ua) wins', '100' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_CrossUnitConst_QualifiedDisambig;
const
  DrvSrc = '''
    program P;
    uses ua, ub;
    begin
      WriteLn(ua.Foo);
      WriteLn(ub.Foo)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Both ua and ub export `Foo`; qualified references pick each unit's own
    value (ua.Foo = 100, ub.Foo = 200) independent of the bare last-wins rule. }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnits(UA_Const, UB_Const, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('ua.Foo then ub.Foo', '100' + LE + '200' + LE, Output);
end;

procedure TE2EUsesChainTests.TestRun_QualifiedInheritance;
const
  UnitSrc = '''
    unit ua;
    interface
    type
      TParent = class
        function Base: Integer;
      end;
    implementation
    function TParent.Base: Integer;
    begin
      Result := 41
    end;
    end.
    ''';
  DrvSrc = '''
    program P;
    uses ua;
    type
      TChild = class(ua.TParent)
        function Plus1: Integer;
      end;
    function TChild.Plus1: Integer;
    begin
      Result := Base() + 1
    end;
    var
      C: TChild;
    begin
      C := TChild.Create();
      WriteLn(C.Plus1())
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { class(ua.TParent) resolves the qualified ancestor to ua's type; the child
    inherits Base (41) and adds 1 -> 42. }
  AssertTrue('compile+link+run',
    CompileAndRunWithUnit('ua', UnitSrc, DrvSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('inherited Base + 1', '42' + LE, Output);
end;

initialization
  RegisterTest(TE2EUsesChainTests);

end.
