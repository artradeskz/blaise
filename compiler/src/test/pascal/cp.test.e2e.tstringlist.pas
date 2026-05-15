{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.tstringlist;

{ E2E tests for TStringList from the RTL Classes unit.
  Each test compiles a program that uses Classes, runs it through QBE+cc,
  and asserts on stdout.  Covers: Add/Get, Count, IndexOf, Delete, Insert,
  Clear, Put (Strings[] write), AddStrings, for..in enumerator, Text
  property get/set, Sorted mode, CaseSensitive flag, Duplicates (dupIgnore),
  and ARC correctness across Grow boundaries. }

interface

uses
  classes, bcl.testing, cp.test.e2e.base;

type
  TE2ETStringListTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_AddGet;
    procedure TestRun_Count;
    procedure TestRun_IndexOf_Found;
    procedure TestRun_IndexOf_NotFound;
    procedure TestRun_Delete;
    procedure TestRun_Insert;
    procedure TestRun_Clear;
    procedure TestRun_Put;
    procedure TestRun_AddStrings;
    procedure TestRun_ForIn;
    procedure TestRun_TextGet;
    procedure TestRun_TextSet;
    procedure TestRun_GrowBeyondInitialCapacity;
    procedure TestRun_Sorted_Add_OrderedOutput;
    procedure TestRun_Sorted_Find;
    procedure TestRun_CaseInsensitive_IndexOf;
    procedure TestRun_Duplicates_Ignore;
    procedure TestRun_CustomSort;
    procedure TestRun_CommaText_Get;
    procedure TestRun_CommaText_Set;
    procedure TestRun_CommaText_Quoted;
  end;

implementation

const
  { All test programs use the RTL Classes unit — no inline class definition }
  SrcAddGet =
    '''
    program P;
    uses Classes;
    var L: TStringList;
    begin
      L := TStringList.Create;
      L.Add('alpha');
      L.Add('beta');
      WriteLn(L.Get(0));
      WriteLn(L.Get(1));
      L.Free
    end.
    ''';

  SrcCount =
    '''
    program P;
    uses Classes;
    var L: TStringList;
    begin
      L := TStringList.Create;
      WriteLn(L.Count);
      L.Add('x');
      WriteLn(L.Count);
      L.Add('y');
      WriteLn(L.Count);
      L.Free
    end.
    ''';

  SrcIndexOfFound =
    '''
    program P;
    uses Classes;
    var L: TStringList; I: Integer;
    begin
      L := TStringList.Create;
      L.Add('first');
      L.Add('second');
      L.Add('third');
      I := L.IndexOf('second');
      WriteLn(I);
      L.Free
    end.
    ''';

  SrcIndexOfNotFound =
    '''
    program P;
    uses Classes;
    var L: TStringList; I: Integer;
    begin
      L := TStringList.Create;
      L.Add('foo');
      I := L.IndexOf('bar');
      WriteLn(I);
      L.Free
    end.
    ''';

  SrcDelete =
    '''
    program P;
    uses Classes;
    var L: TStringList;
    begin
      L := TStringList.Create;
      L.Add('a');
      L.Add('b');
      L.Add('c');
      L.Delete(1);
      WriteLn(L.Count);
      WriteLn(L.Get(0));
      WriteLn(L.Get(1));
      L.Free
    end.
    ''';

  SrcInsert =
    '''
    program P;
    uses Classes;
    var L: TStringList;
    begin
      L := TStringList.Create;
      L.Add('first');
      L.Add('third');
      L.Insert(1, 'second');
      WriteLn(L.Count);
      WriteLn(L.Get(0));
      WriteLn(L.Get(1));
      WriteLn(L.Get(2));
      L.Free
    end.
    ''';

  SrcClear =
    '''
    program P;
    uses Classes;
    var L: TStringList;
    begin
      L := TStringList.Create;
      L.Add('one');
      L.Add('two');
      L.Clear;
      WriteLn(L.Count);
      L.Add('new');
      WriteLn(L.Count);
      WriteLn(L.Get(0));
      L.Free
    end.
    ''';

  SrcPut =
    '''
    program P;
    uses Classes;
    var L: TStringList;
    begin
      L := TStringList.Create;
      L.Add('original');
      L.Strings[0] := 'replaced';
      WriteLn(L.Strings[0]);
      L.Free
    end.
    ''';

  SrcAddStrings =
    '''
    program P;
    uses Classes;
    var A, B: TStringList;
    begin
      A := TStringList.Create;
      A.Add('x');
      A.Add('y');
      B := TStringList.Create;
      B.Add('z');
      B.AddStrings(A);
      WriteLn(B.Count);
      WriteLn(B.Get(0));
      WriteLn(B.Get(1));
      WriteLn(B.Get(2));
      A.Free;
      B.Free
    end.
    ''';

  SrcForIn =
    '''
    program P;
    uses Classes;
    var L: TStringList; S: string;
    begin
      L := TStringList.Create;
      L.Add('p');
      L.Add('q');
      L.Add('r');
      for S in L do WriteLn(S);
      L.Free
    end.
    ''';

  SrcTextGet =
    '''
    program P;
    uses Classes;
    var L: TStringList; T: string;
    begin
      L := TStringList.Create;
      L.Add('line1');
      L.Add('line2');
      T := L.Text;
      WriteLn(L.Count);
      { Pos is 0-based in Blaise; >= 0 means found }
      WriteLn(Pos('line1', T) >= 0);
      WriteLn(Pos('line2', T) >= 0);
      L.Free
    end.
    ''';

  SrcTextSet =
    '''
    program P;
    uses Classes;
    var L: TStringList;
    begin
      L := TStringList.Create;
      L.Text := 'hello' + #10 + 'world';
      WriteLn(L.Count);
      WriteLn(L.Get(0));
      WriteLn(L.Get(1));
      L.Free
    end.
    ''';

  SrcGrow =
    '''
    program P;
    uses Classes;
    var L: TStringList; I: Integer;
    begin
      L := TStringList.Create;
      I := 0;
      while I < 10 do
      begin
        L.Add('item' + IntToStr(I));
        I := I + 1
      end;
      WriteLn(L.Count);
      WriteLn(L.Get(0));
      WriteLn(L.Get(9));
      L.Free
    end.
    ''';

  SrcSortedOrder =
    '''
    program P;
    uses Classes;
    var L: TStringList;
    begin
      L := TStringList.Create;
      L.Sorted := True;
      L.Add('gamma');
      L.Add('alpha');
      L.Add('beta');
      WriteLn(L.Get(0));
      WriteLn(L.Get(1));
      WriteLn(L.Get(2));
      L.Free
    end.
    ''';

  SrcSortedFind =
    '''
    program P;
    uses Classes;
    var L: TStringList; Idx: Integer; Found: Boolean;
    begin
      L := TStringList.Create;
      L.Sorted := True;
      L.Add('apple');
      L.Add('cherry');
      L.Add('mango');
      Found := L.Find('cherry', Idx);
      WriteLn(Found);
      WriteLn(Idx);
      Found := L.Find('durian', Idx);
      WriteLn(Found);
      L.Free
    end.
    ''';

  SrcCaseInsensitive =
    '''
    program P;
    uses Classes;
    var L: TStringList; I: Integer;
    begin
      L := TStringList.Create;
      L.CaseSensitive := False;
      L.Add('Hello');
      L.Add('World');
      I := L.IndexOf('hello');
      WriteLn(I);
      I := L.IndexOf('WORLD');
      WriteLn(I);
      L.Free
    end.
    ''';

  SrcDupIgnore =
    '''
    program P;
    uses Classes;
    var L: TStringList;
    begin
      L := TStringList.Create;
      L.Sorted := True;
      L.Duplicates := dupIgnore;
      L.Add('x');
      L.Add('x');
      L.Add('y');
      WriteLn(L.Count);
      WriteLn(L.Get(0));
      WriteLn(L.Get(1));
      L.Free
    end.
    ''';

  SrcCustomSort =
    '''
    program P;
    uses Classes;
    function DescCmp(const A: string; const B: string): Integer;
    begin
      { reverse lexicographic: B vs A }
      Result := CompareStr(B, A)
    end;
    var L: TStringList;
    begin
      L := TStringList.Create;
      L.Add('banana');
      L.Add('apple');
      L.Add('cherry');
      L.CustomSort(@DescCmp);
      WriteLn(L.Get(0));
      WriteLn(L.Get(1));
      WriteLn(L.Get(2));
      L.Free
    end.
    ''';

  SrcCommaTextGet =
    '''
    program P;
    uses Classes;
    var L: TStringList; S: string;
    begin
      L := TStringList.Create;
      L.Add('alpha');
      L.Add('beta');
      L.Add('gamma');
      S := L.CommaText;
      WriteLn(S);
      L.Free
    end.
    ''';

  SrcCommaTextSet =
    '''
    program P;
    uses Classes;
    var L: TStringList;
    begin
      L := TStringList.Create;
      L.CommaText := 'one,two,three';
      WriteLn(L.Count);
      WriteLn(L.Get(0));
      WriteLn(L.Get(1));
      WriteLn(L.Get(2));
      L.Free
    end.
    ''';

  SrcCommaTextQuoted =
    '''
    program P;
    uses Classes;
    var L: TStringList;
    begin
      L := TStringList.Create;
      L.Add('hello world');
      L.Add('foo');
      WriteLn(L.CommaText);
      L.Free
    end.
    ''';

{ ------------------------------------------------------------------ }
{ Setup                                                                }
{ ------------------------------------------------------------------ }

procedure TE2ETStringListTests.SetUp;
begin
  inherited SetUp;
  SetUpScratch('compiler/target/test-e2e-tstringlist')
end;

{ ------------------------------------------------------------------ }
{ Tests                                                                }
{ ------------------------------------------------------------------ }

procedure TE2ETStringListTests.TestRun_AddGet;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcAddGet, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('Get(0)=alpha', 'alpha', Lines.Strings[0]);
    AssertEquals('Get(1)=beta',  'beta',  Lines.Strings[1]);
  finally
    Lines.Free
  end
end;

procedure TE2ETStringListTests.TestRun_Count;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCount, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('count=0 initially', '0', Lines.Strings[0]);
    AssertEquals('count=1 after Add', '1', Lines.Strings[1]);
    AssertEquals('count=2 after Add', '2', Lines.Strings[2]);
  finally
    Lines.Free
  end
end;

procedure TE2ETStringListTests.TestRun_IndexOf_Found;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcIndexOfFound, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('IndexOf(second)=1', '1', Trim(Output));
end;

procedure TE2ETStringListTests.TestRun_IndexOf_NotFound;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcIndexOfNotFound, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('IndexOf(bar)=-1', '-1', Trim(Output));
end;

procedure TE2ETStringListTests.TestRun_Delete;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcDelete, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('count=2 after Delete',  '2', Lines.Strings[0]);
    AssertEquals('Get(0)=a after Delete', 'a', Lines.Strings[1]);
    AssertEquals('Get(1)=c after Delete', 'c', Lines.Strings[2]);
  finally
    Lines.Free
  end
end;

procedure TE2ETStringListTests.TestRun_Insert;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcInsert, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('count=3 after Insert', '3',      Lines.Strings[0]);
    AssertEquals('Get(0)=first',         'first',  Lines.Strings[1]);
    AssertEquals('Get(1)=second',        'second', Lines.Strings[2]);
    AssertEquals('Get(2)=third',         'third',  Lines.Strings[3]);
  finally
    Lines.Free
  end
end;

procedure TE2ETStringListTests.TestRun_Clear;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcClear, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('count=0 after Clear',        '0',   Lines.Strings[0]);
    AssertEquals('count=1 after Add-on-clear', '1',   Lines.Strings[1]);
    AssertEquals('Get(0)=new after clear',     'new', Lines.Strings[2]);
  finally
    Lines.Free
  end
end;

procedure TE2ETStringListTests.TestRun_Put;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcPut, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Strings[0]=replaced', 'replaced', Trim(Output));
end;

procedure TE2ETStringListTests.TestRun_AddStrings;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcAddStrings, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('count=3 after AddStrings', '3', Lines.Strings[0]);
    AssertEquals('B.Get(0)=z',               'z', Lines.Strings[1]);
    AssertEquals('B.Get(1)=x',               'x', Lines.Strings[2]);
    AssertEquals('B.Get(2)=y',               'y', Lines.Strings[3]);
  finally
    Lines.Free
  end
end;

procedure TE2ETStringListTests.TestRun_ForIn;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcForIn, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('for-in yields p', 'p', Lines.Strings[0]);
    AssertEquals('for-in yields q', 'q', Lines.Strings[1]);
    AssertEquals('for-in yields r', 'r', Lines.Strings[2]);
  finally
    Lines.Free
  end
end;

procedure TE2ETStringListTests.TestRun_TextGet;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcTextGet, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('Count=2',             '2', Lines.Strings[0]);
    AssertEquals('Text contains line1', '1', Lines.Strings[1]);
    AssertEquals('Text contains line2', '1', Lines.Strings[2]);
  finally
    Lines.Free
  end
end;

procedure TE2ETStringListTests.TestRun_TextSet;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcTextSet, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('Count=2 after Text set', '2',     Lines.Strings[0]);
    AssertEquals('Get(0)=hello',           'hello', Lines.Strings[1]);
    AssertEquals('Get(1)=world',           'world', Lines.Strings[2]);
  finally
    Lines.Free
  end
end;

procedure TE2ETStringListTests.TestRun_GrowBeyondInitialCapacity;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcGrow, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('Count=10 after 10 adds', '10',    Lines.Strings[0]);
    AssertEquals('Get(0)=item0',           'item0', Lines.Strings[1]);
    AssertEquals('Get(9)=item9',           'item9', Lines.Strings[2]);
  finally
    Lines.Free
  end
end;

procedure TE2ETStringListTests.TestRun_Sorted_Add_OrderedOutput;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcSortedOrder, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('sorted[0]=alpha', 'alpha', Lines.Strings[0]);
    AssertEquals('sorted[1]=beta',  'beta',  Lines.Strings[1]);
    AssertEquals('sorted[2]=gamma', 'gamma', Lines.Strings[2]);
  finally
    Lines.Free
  end
end;

procedure TE2ETStringListTests.TestRun_Sorted_Find;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcSortedFind, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('Find(cherry)=1 (true)',  '1', Lines.Strings[0]);
    AssertEquals('Find(cherry) idx',       '1', Lines.Strings[1]);
    AssertEquals('Find(durian)=0 (false)', '0', Lines.Strings[2]);
  finally
    Lines.Free
  end
end;

procedure TE2ETStringListTests.TestRun_CaseInsensitive_IndexOf;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCaseInsensitive, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('IndexOf(hello case-insensitive)=0', '0', Lines.Strings[0]);
    AssertEquals('IndexOf(WORLD case-insensitive)=1', '1', Lines.Strings[1]);
  finally
    Lines.Free
  end
end;

procedure TE2ETStringListTests.TestRun_Duplicates_Ignore;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcDupIgnore, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('dupIgnore: count=2 (no dup)', '2', Lines.Strings[0]);
    AssertEquals('dupIgnore: Get(0)=x',         'x', Lines.Strings[1]);
    AssertEquals('dupIgnore: Get(1)=y',         'y', Lines.Strings[2]);
  finally
    Lines.Free
  end
end;

procedure TE2ETStringListTests.TestRun_CustomSort;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCustomSort, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('CustomSort desc [0]=cherry', 'cherry', Lines.Strings[0]);
    AssertEquals('CustomSort desc [1]=banana', 'banana', Lines.Strings[1]);
    AssertEquals('CustomSort desc [2]=apple',  'apple',  Lines.Strings[2]);
  finally
    Lines.Free
  end
end;

procedure TE2ETStringListTests.TestRun_CommaText_Get;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCommaTextGet, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('CommaText=alpha,beta,gamma', 'alpha,beta,gamma', Trim(Output));
end;

procedure TE2ETStringListTests.TestRun_CommaText_Set;
var
  Output: string;
  RCode:  Integer;
  Lines:  TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCommaTextSet, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('Count=3 after CommaText set', '3',     Lines.Strings[0]);
    AssertEquals('Get(0)=one',                  'one',   Lines.Strings[1]);
    AssertEquals('Get(1)=two',                  'two',   Lines.Strings[2]);
    AssertEquals('Get(2)=three',                'three', Lines.Strings[3]);
  finally
    Lines.Free
  end
end;

procedure TE2ETStringListTests.TestRun_CommaText_Quoted;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCommaTextQuoted, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  { item with space is quoted, plain item is not }
  AssertEquals('CommaText quoted', '"hello world",foo', Trim(Output));
end;

initialization
  RegisterTest(TE2ETStringListTests);

end.
