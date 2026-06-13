{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.inlineset;

{ E2E tests for inline set types (set of TEnum / set of (a,b,c)): compile ->
  run on every backend (QBE + native).  Parser/semantic tests live in
  cp.test.inlineset.pas. }

interface

uses
  classes, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EInlineSetTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_NamedEnumSet_Membership;
    procedure TestRun_AnonEnumSet_Membership;
    procedure TestRun_AnonEnumSet_IncludeExclude;
    procedure TestRun_AnonEnumSet_AsParam;
  end;

implementation

procedure TE2EInlineSetTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-inlineset')
end;

procedure TE2EInlineSetTests.TestRun_NamedEnumSet_Membership;
const Src =
  '''
  program P;
  type TE = (alpha, beta, gamma);
  var S: set of TE;
  begin
    S := [alpha, gamma];
    if alpha in S then WriteLn('alpha');
    if beta in S then WriteLn('beta') else WriteLn('no beta')
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, 'alpha' + LE + 'no beta' + LE, 0);
end;

procedure TE2EInlineSetTests.TestRun_AnonEnumSet_Membership;
const Src =
  '''
  program P;
  var S: set of (red, green, blue);
  begin
    S := [red, blue];
    if red in S then WriteLn('red');
    if green in S then WriteLn('green') else WriteLn('no green');
    if blue in S then WriteLn('blue')
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, 'red' + LE + 'no green' + LE + 'blue' + LE, 0);
end;

procedure TE2EInlineSetTests.TestRun_AnonEnumSet_IncludeExclude;
const Src =
  '''
  program P;
  var S: set of (one, two, three);
  begin
    S := [];
    Include(S, two);
    if two in S then WriteLn('two in');
    Exclude(S, two);
    if two in S then WriteLn('still in') else WriteLn('two out')
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, 'two in' + LE + 'two out' + LE, 0);
end;

procedure TE2EInlineSetTests.TestRun_AnonEnumSet_AsParam;
const Src =
  '''
  program P;
  procedure Show(s: set of (lo, mid, hi));
  begin
    if mid in s then WriteLn('mid set') else WriteLn('mid clear')
  end;
  begin
    Show([lo, mid])
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, 'mid set' + LineEnding, 0);
end;

initialization
  RegisterTest(TE2EInlineSetTests);

end.
