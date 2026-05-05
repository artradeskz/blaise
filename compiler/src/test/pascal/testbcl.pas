{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  testbcl — smoke test for the bcl.testing v0 unit (Step 11d).

  Declares one TTestCase fixture with two published methods (one passes,
  one fails), constructs and runs each one against a TTestResultesult, and
  prints a one-line summary plus the failure list.

  This driver intentionally uses direct construction (TFixture.Create
  per method name) rather than relying on metaclass-based enumeration,
  which is the runner's responsibility in Step 11e.  The hot path
  (MethodAddress + procedure-of-object dispatch) is exercised exactly
  the way the runner will exercise it.
}

program testbcl;

{$mode objfpc}{$H+}

uses
  bcl.testing;

type
  TSampleTests = class(TTestCase)
  published
    procedure TestPassing;
    procedure TestFailing;
  end;

procedure TSampleTests.TestPassing;
begin
  Self.AssertEquals(2, 1 + 1, 'integer addition');
  Self.AssertTrue(True, 'true is true');
end;

procedure TSampleTests.TestFailing;
begin
  Self.AssertEquals(42, 1 + 1, 'deliberate failure');
end;

var
  Inst: TSampleTests;
  R:    TTestResult;
  I:    Integer;
begin
  R := TTestResult.Create;
  try
    { Run the passing test. }
    Inst := TSampleTests.Create('TestPassing');
    Inst.Run(R);
    Inst.Free;

    { Run the deliberately failing test. }
    Inst := TSampleTests.Create('TestFailing');
    Inst.Run(R);
    Inst.Free;

    WriteLn(R.Summary);
    if R.NumberOfFailures > 0 then
    begin
      WriteLn('Failures:');
      I := 0;
      while I < R.NumberOfFailures do
      begin
        WriteLn('  ' + R.Failures.Strings[I]);
        I := I + 1
      end;
    end;
  finally
    R.Free;
  end;
end.
