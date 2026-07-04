{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.jumboset;

{ E2E tests for JUMBO sets (set of an enum with >64 members): compile -> run,
  assert stdout, on BOTH backends (QBE + native) via AssertRunsOnAll.  Covers
  membership across the >64 boundary, Include/Exclude, union/intersection/
  difference, equality, for-in, value params, sret returns, and a jumbo
  constant consumed at runtime. }

interface

uses
  classes, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EJumboSetTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_IncludeMembership_AcrossBoundary;
    procedure TestRun_SetOps_UnionInterDiff;
    procedure TestRun_Equality;
    procedure TestRun_ForIn_CountsMembers;
    procedure TestRun_Param_And_Return;
    procedure TestRun_Constant;
  end;

implementation

const
  LE = #10;

  { 80-member enum shared by the test programs. }
  ENUMHDR =
    '''
    type TBig = (b00,b01,b02,b03,b04,b05,b06,b07,b08,b09,b10,b11,b12,b13,b14,b15,
                 b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,b26,b27,b28,b29,b30,b31,
                 b32,b33,b34,b35,b36,b37,b38,b39,b40,b41,b42,b43,b44,b45,b46,b47,
                 b48,b49,b50,b51,b52,b53,b54,b55,b56,b57,b58,b59,b60,b61,b62,b63,
                 b64,b65,b66,b67,b68,b69,b70,b71,b72,b73,b74,b75,b76,b77,b78,b79);
         TBigSet = set of TBig;
    ''';

procedure TE2EJumboSetTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-jumboset');
end;

procedure TE2EJumboSetTests.TestRun_IncludeMembership_AcrossBoundary;
var Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  Src := 'program P;' + LE + ENUMHDR + LE +
         'var s: TBigSet;' + LE +
         'begin' + LE +
         '  s := [];' + LE +
         '  Include(s, b70);' + LE +
         '  Include(s, b05);' + LE +
         '  WriteLn(b70 in s);' + LE +   { True }
         '  WriteLn(b71 in s);' + LE +   { False }
         '  WriteLn(b05 in s);' + LE +   { True }
         '  Exclude(s, b70);' + LE +
         '  WriteLn(b70 in s)' + LE +    { False }
         'end.';
  AssertRunsOnAll(Src, 'True' + LE + 'False' + LE + 'True' + LE + 'False' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_SetOps_UnionInterDiff;
var Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  Src := 'program P;' + LE + ENUMHDR + LE +
         'var a, b, c: TBigSet;' + LE +
         'begin' + LE +
         '  a := [b05, b70];' + LE +
         '  b := [b05, b40];' + LE +
         '  c := a + b;' + LE +
         '  WriteLn(b05 in c, b40 in c, b70 in c);' + LE +  { True True True }
         '  c := a * b;' + LE +
         '  WriteLn(b05 in c, b40 in c, b70 in c);' + LE +  { True False False }
         '  c := a - b;' + LE +
         '  WriteLn(b05 in c, b70 in c)' + LE +             { False True }
         'end.';
  AssertRunsOnAll(Src,
    'TrueTrueTrue' + LE + 'TrueFalseFalse' + LE + 'FalseTrue' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_Equality;
var Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  Src := 'program P;' + LE + ENUMHDR + LE +
         'var a, b: TBigSet;' + LE +
         'begin' + LE +
         '  a := [b70, b05];' + LE +
         '  b := [b05, b70];' + LE +
         '  WriteLn(a = b);' + LE +      { True }
         '  Include(b, b79);' + LE +
         '  WriteLn(a = b);' + LE +      { False }
         '  WriteLn(a <> b)' + LE +      { True }
         'end.';
  AssertRunsOnAll(Src, 'True' + LE + 'False' + LE + 'True' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_ForIn_CountsMembers;
var Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  Src := 'program P;' + LE + ENUMHDR + LE +
         'var s: TBigSet; e: TBig; n: Integer;' + LE +
         'begin' + LE +
         '  s := [b05, b40, b70, b79];' + LE +
         '  n := 0;' + LE +
         '  for e in s do n := n + 1;' + LE +
         '  WriteLn(n);' + LE +          { 4 }
         '  for e in s do Write(Ord(e), '' '');' + LE +
         '  WriteLn' + LE +
         'end.';
  AssertRunsOnAll(Src, '4' + LE + '5 40 70 79 ' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_Param_And_Return;
var Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  Src := 'program P;' + LE + ENUMHDR + LE +
         'function HasHigh(const x: TBigSet): Boolean;' + LE +
         'begin Result := b70 in x; end;' + LE +
         'function MakeSet: TBigSet;' + LE +
         'begin Result := [b65, b70]; end;' + LE +
         'var s: TBigSet;' + LE +
         'begin' + LE +
         '  s := [b70, b05];' + LE +
         '  WriteLn(HasHigh(s));' + LE +    { True }
         '  s := [b05];' + LE +
         '  WriteLn(HasHigh(s));' + LE +    { False }
         '  s := MakeSet();' + LE +
         '  WriteLn(b65 in s, b70 in s, b05 in s)' + LE +  { True True False }
         'end.';
  AssertRunsOnAll(Src,
    'True' + LE + 'False' + LE + 'TrueTrueFalse' + LE, 0);
end;

procedure TE2EJumboSetTests.TestRun_Constant;
var Src: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  Src := 'program P;' + LE + ENUMHDR + LE +
         'const HIGHS: TBigSet = [b65, b70, b79];' + LE +
         'var s: TBigSet;' + LE +
         'begin' + LE +
         '  s := HIGHS;' + LE +
         '  WriteLn(b65 in s, b70 in s, b79 in s, b00 in s)' + LE +  { True True True False }
         'end.';
  AssertRunsOnAll(Src, 'TrueTrueTrueFalse' + LE, 0);
end;

initialization
  RegisterTest(TE2EJumboSetTests);

end.
