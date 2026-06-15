{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.sets;

{ E2E tests for Pascal `set of <enum>` operations: compile -> run, assert on
  stdout, on BOTH backends (QBE + native) via AssertRunsOnAll.  Covers the
  general set-operation semantics over NAMED set types — membership (`in`),
  Include/Exclude, union/intersection, set-valued constants, set-literal
  arguments, equality, and for-in — for both <=32-member sets and the 33..64
  ("Set64") boundary.

  Related e2e set suites:
    - cp.test.e2e.inlineset  — inline `set of TE` / `set of (a,b,c)` syntax.
    - cp.test.e2e.jumboset   — >64-member ("jumbo") byte-array-bitmap sets.
    - cp.test.e2e.tset       — the TSet<T> generic collection (unrelated). }

interface

uses
  classes, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ESetOpsTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { <= 32-member sets }
    procedure TestRun_Set_Include_Exclude;
    procedure TestRun_Set_InOperator;
    procedure TestRun_Set_UnionIntersect;
    procedure TestRun_Set_ValuedConstant;
    procedure TestRun_Set_LiteralArgument;
    procedure TestRun_Set_EqualityWithLiteral;
    procedure TestRun_Set_ForIn_PrintsMembers;
    procedure TestRun_Set_RangeLiteral_Membership;

    { 33..64-member sets (the QBE 'l' / 64-bit register boundary) }
    procedure TestRun_Set64_InOperator_HighBit;
    procedure TestRun_Set64_IncludeExclude;
    procedure TestRun_Set64_Union;
    procedure TestRun_Set64_ForIn;
  end;

implementation

const
  LE = #10;

  SrcSetIncludeExclude = '''
    program Prg;
    type TColor = (Red, Green, Blue);
         TColors = set of TColor;
    var S: TColors;
    begin
      S := [];
      Include(S, Red);
      Include(S, Blue);
      if Red in S then WriteLn('red');
      if Green in S then WriteLn('green');
      if Blue in S then WriteLn('blue');
      Exclude(S, Red);
      if Red in S then WriteLn('red2')
    end.
    ''';

  SrcSetIn = '''
    program Prg;
    type TDir = (North, South, East, West);
         TDirs = set of TDir;
    var Horizontal: TDirs;
    begin
      Horizontal := [East, West];
      if North in Horizontal then WriteLn('N');
      if East  in Horizontal then WriteLn('E');
      if West  in Horizontal then WriteLn('W')
    end.
    ''';

  SrcSetUnion = '''
    program Prg;
    type TBit = (B0, B1, B2, B3);
         TBits = set of TBit;
    var A, B, C: TBits;
    begin
      A := [B0, B1];
      B := [B1, B2];
      C := A + B;
      if B0 in C then WriteLn('0');
      if B1 in C then WriteLn('1');
      if B2 in C then WriteLn('2');
      if B3 in C then WriteLn('3');
      C := A * B;
      if B1 in C then WriteLn('inter1')
    end.
    ''';

  { Set-valued constants: an inferred-type const and an annotated empty const,
    both used as set values at runtime. }
  SrcSetConst = '''
    program Prg;
    type TDir = (North, South, East, West);
         TDirs = set of TDir;
    const
      Horizontal = [East, West];
      Empty: TDirs = [];
    var S: TDirs;
    begin
      S := Horizontal;
      if North in S then WriteLn('N') else WriteLn('no-N');
      if East  in S then WriteLn('E');
      if West  in S then WriteLn('W');
      S := Empty;
      if East in S then WriteLn('still-E') else WriteLn('cleared')
    end.
    ''';

  { A set literal passed directly as a `set of` argument (both non-empty and
    empty), exercising the set-param ABI (w-width spill) too. }
  SrcSetLiteralArg = '''
    program Prg;
    type TDir = (North, South, East, West);
         TDirs = set of TDir;
    procedure Report(D: TDirs);
    begin
      if North in D then WriteLn('N') else WriteLn('no-N');
      if East  in D then WriteLn('E') else WriteLn('no-E')
    end;
    begin
      Report([East, West]);
      Report([])
    end.
    ''';

  { Set equality: S = [] and S = [literal] comparisons. }
  SrcSetEquality = '''
    program Prg;
    type TDir = (North, South, East, West);
         TDirs = set of TDir;
    var S: TDirs;
    begin
      S := [];
      if S = [] then WriteLn('empty') else WriteLn('not-empty');
      S := [East, West];
      if S = [] then WriteLn('bad-empty') else WriteLn('not-empty2');
      if S = [East, West] then WriteLn('match') else WriteLn('no-match');
      if S <> [East, West] then WriteLn('bad-ne') else WriteLn('equal')
    end.
    ''';

  SrcForInSet = '''
    program Prg;
    type
      TColor = (Red, Green, Blue);
      TColorSet = set of TColor;
    var
      S: TColorSet;
      C: TColor;
    begin
      S := [Red, Blue];
      for C in S do
        WriteLn(Ord(C));
    end.
    ''';

  { Set range literal (issue #105): [m1..m3] and a mixed [m0, m2..m4, m7]. }
  SrcSetRange = '''
    program Prg;
    type
      TC = (m0, m1, m2, m3, m4, m5, m6, m7);
      TCS = set of TC;
    var
      e: TCS;
    begin
      e := [m1..m3];
      if m0 in e then WriteLn('y') else WriteLn('n');
      if m2 in e then WriteLn('y') else WriteLn('n');
      if m3 in e then WriteLn('y') else WriteLn('n');
      if m4 in e then WriteLn('y') else WriteLn('n');
      e := [m0, m2..m4, m7];
      if m1 in e then WriteLn('y') else WriteLn('n');
      if m2 in e then WriteLn('y') else WriteLn('n');
      if m7 in e then WriteLn('y') else WriteLn('n');
    end.
    ''';

  BigEnum64 =
    '''
    type
      TBig = (
        X00, X01, X02, X03, X04, X05, X06, X07,
        X08, X09, X10, X11, X12, X13, X14, X15,
        X16, X17, X18, X19, X20, X21, X22, X23,
        X24, X25, X26, X27, X28, X29, X30, X31,
        X32, X33, X34, X35, X36, X37, X38, X39,
        X40, X41, X42, X43, X44, X45, X46, X47);
      TBigSet = set of TBig;
    ''';

  SrcSet64InOp =
    'program Prg;' + #10 +
    BigEnum64 +
    '''
    var S: TBigSet;
    begin
      S := [X40];
      if X40 in S then WriteLn('yes40') else WriteLn('no40');
      if X00 in S then WriteLn('yes00') else WriteLn('no00');
      if X31 in S then WriteLn('yes31') else WriteLn('no31')
    end.
    ''';

  SrcSet64InclExcl =
    'program Prg;' + #10 +
    BigEnum64 +
    '''
    var S: TBigSet;
    begin
      S := [];
      Include(S, X40);
      Include(S, X01);
      if X40 in S then WriteLn('got40');
      if X01 in S then WriteLn('got01');
      Exclude(S, X40);
      if X40 in S then WriteLn('still40') else WriteLn('gone40')
    end.
    ''';

  SrcSet64UnionE2E =
    'program Prg;' + #10 +
    BigEnum64 +
    '''
    var A, B, C: TBigSet;
    begin
      A := [X00, X01];
      B := [X40, X47];
      C := A + B;
      if X00 in C then WriteLn('0');
      if X01 in C then WriteLn('1');
      if X40 in C then WriteLn('40');
      if X47 in C then WriteLn('47');
      if X02 in C then WriteLn('BAD')
    end.
    ''';

  SrcSet64ForIn =
    'program Prg;' + #10 +
    BigEnum64 +
    '''
    var S: TBigSet; V: TBig;
    begin
      S := [X02, X40, X47];
      for V in S do
        WriteLn(Ord(V))
    end.
    ''';

procedure TE2ESetOpsTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-sets');
end;

procedure TE2ESetOpsTests.TestRun_Set_Include_Exclude;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSetIncludeExclude, 'red' + LE + 'blue' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_InOperator;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSetIn, 'E' + LE + 'W' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_UnionIntersect;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSetUnion,
    '0' + LE + '1' + LE + '2' + LE + 'inter1' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_ValuedConstant;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Horizontal = [East, West]: no-N, E, W; Empty cleared the set. }
  AssertRunsOnAll(SrcSetConst,
    'no-N' + LE + 'E' + LE + 'W' + LE + 'cleared' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_LiteralArgument;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Report([East,West]): no-N, E.  Report([]): no-N, no-E. }
  AssertRunsOnAll(SrcSetLiteralArg,
    'no-N' + LE + 'E' + LE + 'no-N' + LE + 'no-E' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_EqualityWithLiteral;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSetEquality,
    'empty' + LE + 'not-empty2' + LE + 'match' + LE + 'equal' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_ForIn_PrintsMembers;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForInSet, '0' + LE + '2' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set_RangeLiteral_Membership;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { [m1..m3]: m0=n m2=y m3=y m4=n; [m0,m2..m4,m7]: m1=n m2=y m7=y }
  AssertRunsOnAll(SrcSetRange,
    'n' + LE + 'y' + LE + 'y' + LE + 'n' + LE +
    'n' + LE + 'y' + LE + 'y' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set64_InOperator_HighBit;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSet64InOp,
    'yes40' + LE + 'no00' + LE + 'no31' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set64_IncludeExclude;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSet64InclExcl,
    'got40' + LE + 'got01' + LE + 'gone40' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set64_Union;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSet64UnionE2E,
    '0' + LE + '1' + LE + '40' + LE + '47' + LE, 0);
end;

procedure TE2ESetOpsTests.TestRun_Set64_ForIn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSet64ForIn,
    '2' + LE + '40' + LE + '47' + LE, 0);
end;

initialization
  RegisterTest(TE2ESetOpsTests);

end.
