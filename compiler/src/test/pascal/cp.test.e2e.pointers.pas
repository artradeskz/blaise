{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.pointers;

{ E2E tests for pointer operations: GetMem/FreeMem, typed pointer dereferencing,
  and nil checks. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  TE2EPointersTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_Pointer_GetMem_WriteRead_FreeMem;
    procedure TestRun_Pointer_TypedPointer_Deref;
    procedure TestRun_Pointer_NilCheck;
    procedure TestRun_PCharSubscript_ChrAssignment;
    procedure TestRun_StaticArrayOfPChar_ElementPreservesAllBits;
  end;

implementation

procedure TE2EPointersTests.SetUp;
begin
  inherited SetUp;
  SetUpScratch('compiler/target/test-e2e-pointers');
end;

const
  LE = #10;

  SrcGetMemWriteRead = '''
    program P;
    var P1: ^Integer;
    begin
      P1 := GetMem(4);
      P1^ := 42;
      WriteLn(P1^);
      FreeMem(P1)
    end.
    ''';

  SrcTypedPointerDeref = '''
    program P;
    var
      A: Integer;
      P1: ^Integer;
    begin
      A  := 99;
      P1 := @A;
      WriteLn(P1^)
    end.
    ''';

  SrcPointerNilCheck = '''
    program P;
    var P1: ^Integer;
    begin
      P1 := nil;
      if P1 = nil then
        WriteLn('nil')
      else
        WriteLn('not nil')
    end.
    ''';

  { Regression: assigning a PChar value to Arr[I] of a static
    array-of-PChar used to emit storew (32-bit) instead of storel,
    truncating the heap pointer's high 32 bits to zero. }
  SrcStaticArrayPChar = '''
    program P;
    procedure Print(P: PChar);
    begin
      WriteLn(string(P))
    end;
    var
      Arr: array[0..1] of PChar;
      A, B: PChar;
      I: Integer;
    begin
      A := GetMem(3);
      for I := 0 to 1 do A[I] := Chr(72 + I);
      A[2] := Chr(0);
      B := GetMem(3);
      for I := 0 to 1 do B[I] := Chr(89 + I);
      B[2] := Chr(0);
      Arr[0] := A;
      Arr[1] := B;
      Print(Arr[0]);
      Print(Arr[1]);
      FreeMem(A);
      FreeMem(B)
    end.
    ''';

  { Regression: P[I] := Chr(N) previously stored the low byte of the
    _Chr-allocated string pointer (garbage) instead of N itself. }
  SrcPCharSubscriptChr = '''
    program P;
    var
      P1: PChar;
      I:  Integer;
    begin
      P1 := GetMem(5);
      for I := 0 to 3 do
        P1[I] := Chr(65 + I);
      P1[4] := Chr(0);
      WriteLn(string(P1));
      FreeMem(P1)
    end.
    ''';

procedure TE2EPointersTests.TestRun_Pointer_GetMem_WriteRead_FreeMem;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcGetMemWriteRead, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('42', '42' + LE, Output);
end;

procedure TE2EPointersTests.TestRun_Pointer_TypedPointer_Deref;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTypedPointerDeref, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('99', '99' + LE, Output);
end;

procedure TE2EPointersTests.TestRun_Pointer_NilCheck;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcPointerNilCheck, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('nil', 'nil' + LE, Output);
end;

procedure TE2EPointersTests.TestRun_PCharSubscript_ChrAssignment;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcPCharSubscriptChr, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('ABCD', 'ABCD' + LE, Output);
end;

procedure TE2EPointersTests.TestRun_StaticArrayOfPChar_ElementPreservesAllBits;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStaticArrayPChar, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('two PChar values round-tripped through static array',
    'HI' + LE + 'YZ' + LE, Output);
end;

initialization
  RegisterTest(TE2EPointersTests);

end.
