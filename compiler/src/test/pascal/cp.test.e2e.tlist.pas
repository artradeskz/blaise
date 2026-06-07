{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.tlist;

{ E2E tests for TList<T> from generics.collections.
  Distinct from cp.test.e2e.tstack which inlines its own class declaration —
  these tests exercise the *generic instantiation* path end-to-end. They are
  the only e2e coverage of stdlib generic classes, and catch link-time bugs
  in vtable/typeinfo emission for generic instances. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ETListTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_TListString_AddGetCount;
    procedure TestRun_TListInteger_AddGetCount;
    procedure TestRun_TListInteger_IndexOf;
    procedure TestRun_TListString_IndexOf_NotFound;
  end;

implementation

const
  SrcTListString = '''
    program P;
    uses generics.collections;
    var
      L: TList<String>;
    begin
      L := TList<String>.Create();
      L.Add('hello');
      L.Add('world');
      WriteLn(L.Count);
      WriteLn(L.Get(0));
      WriteLn(L.Get(1));
      L.Free()
    end.
    ''';

  SrcTListInteger = '''
    program P;
    uses generics.collections;
    var
      L: TList<Integer>;
    begin
      L := TList<Integer>.Create();
      L.Add(10);
      L.Add(20);
      L.Add(30);
      WriteLn(L.Count);
      WriteLn(L.Get(0));
      WriteLn(L.Get(2));
      L.Free()
    end.
    ''';

  SrcTListIndexOfInteger = '''
    program P;
    uses generics.collections;
    var
      L: TList<Integer>;
    begin
      L := TList<Integer>.Create();
      L.Add(10);
      L.Add(20);
      L.Add(30);
      WriteLn(L.IndexOf(10));
      WriteLn(L.IndexOf(20));
      WriteLn(L.IndexOf(30));
      WriteLn(L.IndexOf(99));
      L.Free()
    end.
    ''';

  SrcTListIndexOfStringNotFound = '''
    program P;
    uses generics.collections;
    var
      L: TList<String>;
    begin
      L := TList<String>.Create();
      L.Add('alpha');
      L.Add('beta');
      WriteLn(L.IndexOf('beta'));
      WriteLn(L.IndexOf('gamma'));
      L.Free()
    end.
    ''';

procedure TE2ETListTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-tlist')
end;

procedure TE2ETListTests.TestRun_TListString_AddGetCount;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+link+run', CompileAndRunWithRTL(SrcTListString, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('Count=2 printed',  Pos('2',     Output) >= 0);
  AssertTrue('Get(0)=hello',     Pos('hello', Output) >= 0);
  AssertTrue('Get(1)=world',     Pos('world', Output) >= 0);
end;

procedure TE2ETListTests.TestRun_TListInteger_AddGetCount;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+link+run', CompileAndRunWithRTL(SrcTListInteger, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('Count=3 printed', Pos('3',  Output) >= 0);
  AssertTrue('Get(0)=10',       Pos('10', Output) >= 0);
  AssertTrue('Get(2)=30',       Pos('30', Output) >= 0);
end;

procedure TE2ETListTests.TestRun_TListInteger_IndexOf;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+link+run', CompileAndRunWithRTL(SrcTListIndexOfInteger, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('IndexOf(10)=0', Pos('0',  Output) >= 0);
  AssertTrue('IndexOf(20)=1', Pos('1',  Output) >= 0);
  AssertTrue('IndexOf(30)=2', Pos('2',  Output) >= 0);
  AssertTrue('IndexOf(99)=-1 (missing)', Pos('-1', Output) >= 0);
end;

procedure TE2ETListTests.TestRun_TListString_IndexOf_NotFound;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+link+run', CompileAndRunWithRTL(SrcTListIndexOfStringNotFound, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('IndexOf(beta)=1',          Pos('1',  Output) >= 0);
  AssertTrue('IndexOf(gamma)=-1',        Pos('-1', Output) >= 0);
end;

initialization
  RegisterTest(TE2ETListTests);

end.
