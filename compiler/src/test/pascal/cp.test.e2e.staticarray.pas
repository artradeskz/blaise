{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.staticarray;

{ E2E tests for static arrays: compile -> QBE -> cc -> run, assert on stdout.
  Covers inline anonymous array declarations (var A: array[L..H] of T) and
  the named array type alias form (type TArr = array[L..H] of T) introduced
  to fix the missing parser branch. }

interface

uses
  classes, bcl.testing, cp.test.e2e.base;

type
  TE2EStaticArrayTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { Inline anonymous declaration (regression: ensure existing behaviour holds) }
    procedure TestRun_AnonymousDecl_ReadWrite;
    procedure TestRun_AnonymousDecl_NonZeroBase;
    procedure TestRun_AnonymousDecl_LowHighLength;

    { Named type alias: type TArr = array[L..H] of T }
    procedure TestRun_TypeAlias_BasicReadWrite;
    procedure TestRun_TypeAlias_NonZeroBase;
    procedure TestRun_TypeAlias_AsParam_Length;
    procedure TestRun_TypeAlias_MultipleVarsShareType;
    procedure TestRun_TypeAlias_GlobalAndLocal;
  end;

implementation

const
  SrcAnonReadWrite =
    '''
    program P;
    var A: array[0..2] of Integer;
    begin
      A[0] := 10;
      A[1] := 20;
      A[2] := 30;
      WriteLn(A[0]);
      WriteLn(A[1]);
      WriteLn(A[2])
    end.
    ''';

  SrcAnonNonZero =
    '''
    program P;
    var A: array[5..7] of Integer;
    begin
      A[5] := 100;
      A[6] := 200;
      A[7] := 300;
      WriteLn(A[5]);
      WriteLn(A[7])
    end.
    ''';

  SrcAnonLowHighLen =
    '''
    program P;
    var A: array[0..4] of Integer;
    begin
      WriteLn(Low(A));
      WriteLn(High(A));
      WriteLn(Length(A))
    end.
    ''';

  SrcAliasBasic =
    '''
    program P;
    type
      TTriple = array[0..2] of Integer;
    var A: TTriple;
    begin
      A[0] := 1;
      A[1] := 2;
      A[2] := 3;
      WriteLn(A[0]);
      WriteLn(A[1]);
      WriteLn(A[2])
    end.
    ''';

  SrcAliasNonZero =
    '''
    program P;
    type
      TSlice = array[3..5] of Integer;
    var S: TSlice;
    begin
      S[3] := 33;
      S[4] := 44;
      S[5] := 55;
      WriteLn(S[3]);
      WriteLn(S[5])
    end.
    ''';

  SrcAliasAsParam =
    '''
    program P;
    type
      TFive = array[0..4] of Integer;
    procedure PrintLen(const A: array of Integer);
    begin
      WriteLn(Length(A))
    end;
    var B: TFive;
    begin
      PrintLen(B)
    end.
    ''';

  SrcAliasMultiVar =
    '''
    program P;
    type
      TPair = array[0..1] of Integer;
    var X, Y: TPair;
    begin
      X[0] := 10; X[1] := 20;
      Y[0] := 30; Y[1] := 40;
      WriteLn(X[0]);
      WriteLn(Y[1])
    end.
    ''';

  SrcAliasGlobalLocal =
    '''
    program P;
    type
      TBuf = array[0..2] of Integer;
    var G: TBuf;
    procedure Fill;
    var L: TBuf;
    begin
      L[0] := 7; L[1] := 8; L[2] := 9;
      G[0] := L[0];
      G[2] := L[2]
    end;
    begin
      Fill;
      WriteLn(G[0]);
      WriteLn(G[2])
    end.
    ''';

{ ------------------------------------------------------------------ }
{ Setup                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EStaticArrayTests.SetUp;
begin
  inherited SetUp;
  SetUpScratch('compiler/target/test-e2e-staticarray')
end;

{ ------------------------------------------------------------------ }
{ Tests — anonymous inline declarations                                }
{ ------------------------------------------------------------------ }

procedure TE2EStaticArrayTests.TestRun_AnonymousDecl_ReadWrite;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcAnonReadWrite, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('A[0]=10', '10', Lines.Strings[0]);
    AssertEquals('A[1]=20', '20', Lines.Strings[1]);
    AssertEquals('A[2]=30', '30', Lines.Strings[2]);
  finally Lines.Free end
end;

procedure TE2EStaticArrayTests.TestRun_AnonymousDecl_NonZeroBase;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcAnonNonZero, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('A[5]=100', '100', Lines.Strings[0]);
    AssertEquals('A[7]=300', '300', Lines.Strings[1]);
  finally Lines.Free end
end;

procedure TE2EStaticArrayTests.TestRun_AnonymousDecl_LowHighLength;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcAnonLowHighLen, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('Low=0',    '0', Lines.Strings[0]);
    AssertEquals('High=4',   '4', Lines.Strings[1]);
    AssertEquals('Length=5', '5', Lines.Strings[2]);
  finally Lines.Free end
end;

{ ------------------------------------------------------------------ }
{ Tests — named type alias                                             }
{ ------------------------------------------------------------------ }

procedure TE2EStaticArrayTests.TestRun_TypeAlias_BasicReadWrite;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcAliasBasic, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('A[0]=1', '1', Lines.Strings[0]);
    AssertEquals('A[1]=2', '2', Lines.Strings[1]);
    AssertEquals('A[2]=3', '3', Lines.Strings[2]);
  finally Lines.Free end
end;

procedure TE2EStaticArrayTests.TestRun_TypeAlias_NonZeroBase;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcAliasNonZero, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('S[3]=33', '33', Lines.Strings[0]);
    AssertEquals('S[5]=55', '55', Lines.Strings[1]);
  finally Lines.Free end
end;

procedure TE2EStaticArrayTests.TestRun_TypeAlias_AsParam_Length;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcAliasAsParam, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Length(TFive)=5', '5', Trim(Output));
end;

procedure TE2EStaticArrayTests.TestRun_TypeAlias_MultipleVarsShareType;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcAliasMultiVar, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('X[0]=10', '10', Lines.Strings[0]);
    AssertEquals('Y[1]=40', '40', Lines.Strings[1]);
  finally Lines.Free end
end;

procedure TE2EStaticArrayTests.TestRun_TypeAlias_GlobalAndLocal;
var Output: string; RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcAliasGlobalLocal, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create;
  try
    Lines.Text := Trim(Output);
    AssertEquals('G[0]=7', '7', Lines.Strings[0]);
    AssertEquals('G[2]=9', '9', Lines.Strings[1]);
  finally Lines.Free end
end;

initialization
  RegisterTest(TE2EStaticArrayTests);

end.
