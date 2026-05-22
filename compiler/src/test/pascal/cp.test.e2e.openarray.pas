{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.openarray;

{ E2E tests for open-array parameters: compile -> QBE -> cc -> run, assert on
  stdout.  Covers inline array literals (sum, High/Low, Length) and the
  static-array-to-open-array coercion introduced to fix the "No matching
  overload" error when a named static-array variable is passed as an open-array
  argument. }

interface

uses
  classes, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EOpenArrayTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { Inline array literal call site }
    procedure TestRun_OpenArray_Sum;
    procedure TestRun_OpenArray_HighLow;
    procedure TestRun_OpenArray_Length;

    { Static array variable coerced to open-array parameter }
    procedure TestRun_StaticToOpen_Length_ZeroBase;
    procedure TestRun_StaticToOpen_Length_NonZeroBase;
    procedure TestRun_StaticToOpen_Sum;
    procedure TestRun_StaticToOpen_PassToNested;
    procedure TestRun_StaticToOpen_ConstParam_NoMutation;

    { Procedural type as open-array element }
    procedure TestRun_OpenArray_ProcType_CallEach;
  end;

implementation

const
  SrcOpenArraySum =
    '''
    program P;
    function Sum(const A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do
        Result := Result + A[I]
    end;
    begin
      WriteLn(Sum([1, 2, 3, 4, 5]))
    end.
    ''';

  SrcOpenArrayHighLow =
    '''
    program P;
    procedure PrintBounds(const A: array of Integer);
    begin
      WriteLn(Low(A));
      WriteLn(High(A))
    end;
    begin
      PrintBounds([10, 20, 30])
    end.
    ''';

  SrcOpenArrayLength =
    '''
    program P;
    function Count(const A: array of Integer): Integer;
    begin
      Result := Length(A)
    end;
    begin
      WriteLn(Count([10, 20, 30]))
    end.
    ''';

  SrcStaticLenZeroBase =
    '''
    program P;
    procedure PrintLen(const A: array of Integer);
    begin
      WriteLn(Length(A))
    end;
    var B: array[0..4] of Integer;
    begin
      PrintLen(B)
    end.
    ''';

  SrcStaticLenNonZero =
    '''
    program P;
    procedure PrintLen(const A: array of Integer);
    begin
      WriteLn(Length(A))
    end;
    var B: array[3..7] of Integer;
    begin
      PrintLen(B)
    end.
    ''';

  SrcStaticSum =
    '''
    program P;
    function Sum(const A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do
        Result := Result + A[I]
    end;
    var B: array[0..2] of Integer;
    begin
      B[0] := 10;
      B[1] := 20;
      B[2] := 30;
      WriteLn(Sum(B))
    end.
    ''';

  SrcStaticPassNested =
    '''
    program P;
    function Sum(const A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do
        Result := Result + A[I]
    end;
    procedure Process(const A: array of Integer);
    begin
      WriteLn(Sum(A))
    end;
    var B: array[0..2] of Integer;
    begin
      B[0] := 5;
      B[1] := 10;
      B[2] := 15;
      Process(B)
    end.
    ''';

  SrcStaticConstRead =
    '''
    program P;
    function First(const A: array of Integer): Integer;
    begin
      Result := A[0]
    end;
    var B: array[0..2] of Integer;
    begin
      B[0] := 77; B[1] := 88; B[2] := 99;
      WriteLn(First(B));
      WriteLn(Length(B))
    end.
    ''';

{ ------------------------------------------------------------------ }
{ Setup                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EOpenArrayTests.SetUp;
begin
  inherited SetUp;
  SetUpScratch('compiler/target/test-e2e-openarray')
end;

{ ------------------------------------------------------------------ }
{ Tests — inline array literals                                        }
{ ------------------------------------------------------------------ }

procedure TE2EOpenArrayTests.TestRun_OpenArray_Sum;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcOpenArraySum, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Sum([1..5])=15', '15', Trim(Output));
end;

procedure TE2EOpenArrayTests.TestRun_OpenArray_HighLow;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcOpenArrayHighLow, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('Low=0',  '0', Lines.Strings[0]);
    AssertEquals('High=2', '2', Lines.Strings[1]);
  finally
    Lines.Free
  end
end;

procedure TE2EOpenArrayTests.TestRun_OpenArray_Length;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcOpenArrayLength, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Length([10,20,30])=3', '3', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Tests — static array coerced to open-array                          }
{ ------------------------------------------------------------------ }

procedure TE2EOpenArrayTests.TestRun_StaticToOpen_Length_ZeroBase;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcStaticLenZeroBase, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Length(B[0..4])=5', '5', Trim(Output));
end;

procedure TE2EOpenArrayTests.TestRun_StaticToOpen_Length_NonZeroBase;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcStaticLenNonZero, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Length(B[3..7])=5', '5', Trim(Output));
end;

procedure TE2EOpenArrayTests.TestRun_StaticToOpen_Sum;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcStaticSum, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Sum(B[0..2])=60', '60', Trim(Output));
end;

procedure TE2EOpenArrayTests.TestRun_StaticToOpen_PassToNested;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcStaticPassNested, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('nested sum=30', '30', Trim(Output));
end;

procedure TE2EOpenArrayTests.TestRun_StaticToOpen_ConstParam_NoMutation;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcStaticConstRead, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('First(B)=77',   '77', Lines.Strings[0]);
    AssertEquals('Length(B[0..2])=3', '3', Lines.Strings[1]);
  finally
    Lines.Free
  end
end;

{ ------------------------------------------------------------------ }
{ Tests — procedural type as open-array element                      }
{ ------------------------------------------------------------------ }

const
  SrcProcTypeOpenArray =
    '''
    program P;
    type TIntFn = function: Integer;

    function ApplyAll(const Fns: array of TIntFn): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(Fns) do
        Result := Result + Fns[I]();
    end;

    function One: Integer; begin Result := 1; end;
    function Two: Integer; begin Result := 2; end;
    function Three: Integer; begin Result := 3; end;

    var A: array[0..2] of TIntFn;
    begin
      A[0] := @One;
      A[1] := @Two;
      A[2] := @Three;
      WriteLn(ApplyAll(A));
    end.
    ''';

procedure TE2EOpenArrayTests.TestRun_OpenArray_ProcType_CallEach;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcProcTypeOpenArray, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1+2+3=6', '6', Trim(Output));
end;

initialization
  RegisterTest(TE2EOpenArrayTests);

end.
