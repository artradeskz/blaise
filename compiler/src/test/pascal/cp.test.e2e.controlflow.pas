{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.controlflow;

{ E2E tests for control flow: for, while, repeat, break, continue. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EControlFlowTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_For_Upward_PrintsRange;
    procedure TestRun_For_Downto_PrintsRange;
    procedure TestRun_While_PrintsRange;
    procedure TestRun_Repeat_PrintsRange;
    procedure TestRun_For_BreakExitsEarly;
    procedure TestRun_For_ContinueSkipsIteration;
    procedure TestRun_Nested_For_Loops;
    procedure TestRun_ExitValue_ReturnsEarly;
  end;

implementation

procedure TE2EControlFlowTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-controlflow');
end;

const
  LE = #10;

  SrcForUp = '''
    program P;
    var I: Integer;
    begin
      for I := 1 to 3 do
        WriteLn(I)
    end.
    ''';

  { Exit(X) function-result shorthand — early returns with a value, including
    a string return (exercises ARC on the returned value), and a fall-through
    case where no Exit(X) fires. }
  SrcExitValue = '''
    program P;
    function Classify(n: Integer): Integer;
    begin
      if n < 0 then Exit(-1);
      if n = 0 then Exit(0);
      Exit(1)
    end;
    function Pick(b: Boolean): string;
    begin
      if b then Exit('yes');
      Result := 'no'
    end;
    begin
      WriteLn(Classify(-9));
      WriteLn(Classify(0));
      WriteLn(Classify(42));
      WriteLn(Pick(True));
      WriteLn(Pick(False))
    end.
    ''';

  SrcForDown = '''
    program P;
    var I: Integer;
    begin
      for I := 3 downto 1 do
        WriteLn(I)
    end.
    ''';

  SrcWhile = '''
    program P;
    var I: Integer;
    begin
      I := 1;
      while I <= 3 do
      begin
        WriteLn(I);
        I := I + 1
      end
    end.
    ''';

  SrcRepeat = '''
    program P;
    var I: Integer;
    begin
      I := 1;
      repeat
        WriteLn(I);
        I := I + 1
      until I > 3
    end.
    ''';

  SrcForBreakE2E = '''
    program P;
    var I: Integer;
    begin
      for I := 1 to 10 do
      begin
        if I = 4 then break;
        WriteLn(I)
      end
    end.
    ''';

  SrcForContinue = '''
    program P;
    var I: Integer;
    begin
      for I := 1 to 5 do
      begin
        if I = 3 then continue;
        WriteLn(I)
      end
    end.
    ''';

  SrcNestedFor = '''
    program P;
    var I, J: Integer;
    begin
      for I := 1 to 2 do
        for J := 1 to 2 do
          WriteLn(I * 10 + J)
    end.
    ''';

procedure TE2EControlFlowTests.TestRun_For_Upward_PrintsRange;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcForUp, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1 2 3', '1' + LE + '2' + LE + '3' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_For_Downto_PrintsRange;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcForDown, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('3 2 1', '3' + LE + '2' + LE + '1' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_While_PrintsRange;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcWhile, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1 2 3', '1' + LE + '2' + LE + '3' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_Repeat_PrintsRange;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRepeat, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1 2 3', '1' + LE + '2' + LE + '3' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_For_BreakExitsEarly;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcForBreakE2E, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1 2 3', '1' + LE + '2' + LE + '3' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_For_ContinueSkipsIteration;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcForContinue, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1 2 4 5', '1' + LE + '2' + LE + '4' + LE + '5' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_Nested_For_Loops;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcNestedFor, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('nested 2x2', '11' + LE + '12' + LE + '21' + LE + '22' + LE, Output);
end;

procedure TE2EControlFlowTests.TestRun_ExitValue_ReturnsEarly;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcExitValue, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  { Classify: -1, 0, 1; Pick: yes (Exit), no (fall-through). }
  AssertEquals('exit-value returns',
    '-1' + LE + '0' + LE + '1' + LE + 'yes' + LE + 'no' + LE, Output);
end;

initialization
  RegisterTest(TE2EControlFlowTests);

end.
