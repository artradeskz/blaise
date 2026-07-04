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

    { Class elements are RETAINED on store: an object whose only other
      reference was a local in an exited routine must survive in the list
      (decision recorded in language-rationale: collection ownership). }
    procedure TestRun_TList_ClassElements_RetainedAcrossScope;

    { Default array property: List[i] subscript for read and write. }
    procedure TestRun_TList_DefaultProperty_ReadWrite;
    procedure TestRun_TList_DefaultProperty_Polymorphic;
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

const
  SrcTListClassRetain = '''
    program P;
    uses generics.collections;
    type
      TC = class
        N: Integer;
      end;
    procedure Fill(L: TList<TC>; S: TStack<TC>);
    var C: TC;
    begin
      C := TC.Create();
      C.N := 77;
      L.Add(C);
      C := TC.Create();
      C.N := 88;
      S.Push(C);
    end;
    var
      L: TList<TC>;
      S: TStack<TC>;
    begin
      L := TList<TC>.Create();
      S := TStack<TC>.Create();
      Fill(L, S);
      writeln(L.Get(0).N);
      writeln(S.Peek().N);
    end.
    ''';

procedure TE2ETListTests.TestRun_TList_ClassElements_RetainedAcrossScope;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+link+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcTListClassRetain, Output, RCode, False));
  AssertEquals('exit code (qbe)', 0, RCode);
  AssertEquals('retained elements readable (qbe)', '77' + #10 + '88' + #10, Output);
  AssertTrue('compile+link+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcTListClassRetain, Output, RCode, False));
  AssertEquals('exit code (native)', 0, RCode);
  AssertEquals('retained elements readable (native)', '77' + #10 + '88' + #10, Output);
end;

const
  SrcTListDefaultRW = '''
    program P;
    uses Generics.Collections;
    var lst: TList<Integer>;
    begin
      lst := TList<Integer>.Create;
      lst.Add(1); lst.Add(2);
      lst[0] := 100; lst[1] := 200;
      WriteLn(lst[0] + lst[1]);
      lst.Free()
    end.
    ''';

  SrcTListDefaultPoly = '''
    program P;
    uses Generics.Collections;
    type
      TShape = class function Area: Integer; virtual; begin Result := 0 end; end;
      TBox = class(TShape)
        FS: Integer;
        constructor Create(s: Integer); begin FS := s end;
        function Area: Integer; override; begin Result := FS * FS end;
      end;
    var lst: TList<TShape>; i, total: Integer;
    begin
      lst := TList<TShape>.Create;
      lst.Add(TBox.Create(3)); lst.Add(TBox.Create(4));
      total := 0;
      for i := 0 to lst.Count - 1 do total := total + lst[i].Area();
      WriteLn(total);
      lst.Free()
    end.
    ''';

procedure TE2ETListTests.TestRun_TList_DefaultProperty_ReadWrite;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcTListDefaultRW, Output, RCode, False));
  AssertEquals('exit code (qbe)', 0, RCode);
  AssertEquals('List[i] read/write (qbe)', '300' + #10, Output);
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcTListDefaultRW, Output, RCode, False));
  AssertEquals('exit code (native)', 0, RCode);
  AssertEquals('List[i] read/write (native)', '300' + #10, Output);
end;

procedure TE2ETListTests.TestRun_TList_DefaultProperty_Polymorphic;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcTListDefaultPoly, Output, RCode, False));
  AssertEquals('exit code (qbe)', 0, RCode);
  AssertEquals('List[i].Area (qbe)', '25' + #10, Output);
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcTListDefaultPoly, Output, RCode, False));
  AssertEquals('exit code (native)', 0, RCode);
  AssertEquals('List[i].Area (native)', '25' + #10, Output);
end;

initialization
  RegisterTest(TE2ETListTests);

end.
