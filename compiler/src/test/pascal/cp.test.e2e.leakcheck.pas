{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.leakcheck;

{ E2E tests for the --debug leak tracker.
  Verifies that _LeakTrackerEnable is activated in debug builds,
  that leaked objects are reported on exit, and that cleanly-released
  objects produce no report. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ELeakCheckTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestDebug_NoLeak_NoReport;
    procedure TestDebug_ExceptionHandlerVar_NoLeakNoOverRelease;
    procedure TestDebug_ConstructorWithArgs_NoDoubleAddRef;
    procedure TestDebug_LeakedObject_ReportedOnExit;
    procedure TestDebug_MultipleLeaks_AllReported;
    procedure TestDebug_CycleRetained_Reported;
    procedure TestRelease_NoReport_WhenDebugOff;
  end;

implementation

procedure TE2ELeakCheckTests.SetUp;
begin
  inherited SetUp;
  SetUpScratch('compiler/target/test-e2e-leakcheck');
end;

const
  LE = #10;

  { A clean program: object is created and properly released by ARC at scope exit. }
  SrcNoLeak = '''
    program P;
    uses blaise_arc;
    type
      TBox = class
        Value: Integer;
      end;
    var
      B: TBox;
    begin
      B := TBox.Create;
      B.Value := 99;
      WriteLn(B.Value)
    end.
    ''';

  { Exception handler variable: `on E: T do` binds the caught exception to E.
    E is a class local that scope-exit ARC releases, so the handler must retain
    the exception on bind.  Without that AddRef the exception (created at rc=0
    by `raise EFoo.Create`) is over-released to a negative refcount — a
    use-after-free.  With the fix it is freed exactly once: no leak, no crash. }
  SrcExceptionHandlerVar = '''
    program P;
    uses blaise_arc;
    type
      Exception = class
        FMessage: string;
      end;
      EFoo = class(Exception) end;
    procedure DoIt;
    begin
      try
        raise EFoo.Create
      except
        on E: EFoo do
          WriteLn('caught')
      end
    end;
    begin
      DoIt;
      WriteLn('done')
    end.
    ''';

  { Constructor with args — must not double-AddRef; object must be clean after scope. }
  SrcConstructorWithArgs = '''
    program P;
    uses blaise_arc;
    type
      TBox = class
        Value: Integer;
        constructor Create(V: Integer);
      end;
    constructor TBox.Create(V: Integer);
    begin
      Self.Value := V
    end;
    var
      B: TBox;
    begin
      B := TBox.Create(42);
      WriteLn(B.Value)
    end.
    ''';

  { Deliberately leaked: object assigned to a raw Pointer, bypassing ARC release. }
  SrcOneLeak = '''
    program P;
    uses blaise_arc;
    type
      TBox = class
        Value: Integer;
      end;
    var
      B: TBox;
      P: Pointer;
    begin
      B := TBox.Create;
      B.Value := 7;
      P := Pointer(B);
      B := nil;
      { P holds the only reference but is an unmanaged Pointer — ARC never
        releases it, so TBox leaks. }
      WriteLn('done')
    end.
    ''';

  { Two distinct classes leaked to verify count and class-name reporting. }
  SrcTwoLeaks = '''
    program P;
    uses blaise_arc;
    type
      TAlpha = class
        X: Integer;
      end;
      TBeta = class
        Y: Integer;
      end;
    var
      A: TAlpha;
      B: TBeta;
      PA, PB: Pointer;
    begin
      A := TAlpha.Create;
      B := TBeta.Create;
      PA := Pointer(A);
      PB := Pointer(B);
      A := nil;
      B := nil;
      WriteLn('done')
    end.
    ''';

  { Reference cycle: each object holds the other — both leak. }
  SrcCycleLeak = '''
    program P;
    uses blaise_arc;
    type
      TNode = class
        Other: TNode;
      end;
    var
      X, Y: TNode;
    begin
      X := TNode.Create;
      Y := TNode.Create;
      X.Other := Y;
      Y.Other := X;
      { X and Y each hold refcount >= 2 due to the cycle; when the local
        vars go out of scope the refcount drops to 1, not 0 — both leak. }
      WriteLn('done')
    end.
    ''';

{ ------------------------------------------------------------------ }

procedure TE2ELeakCheckTests.TestDebug_NoLeak_NoReport;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcNoLeak, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', '99' + LE, Output);
  AssertTrue('no leak report', Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ExceptionHandlerVar_NoLeakNoOverRelease;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(SrcExceptionHandlerVar, Output, ExitCode, True));
  { Clean exit (no abort from a negative-refcount free), expected stdout, and
    no leak report (the exception is freed exactly once). }
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', 'caught' + LE + 'done' + LE, Output);
  AssertTrue('no leak report', Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ConstructorWithArgs_NoDoubleAddRef;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcConstructorWithArgs, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', '42' + LE, Output);
  AssertTrue('no leak report', Pos('Blaise leak report', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_LeakedObject_ReportedOnExit;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcOneLeak, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header present', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('count 1', Pos('1 object(s)', Output) >= 0);
  AssertTrue('class name', Pos('TBox', Output) >= 0);
end;

procedure TE2ELeakCheckTests.TestDebug_MultipleLeaks_AllReported;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcTwoLeaks, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header present', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('count 2', Pos('2 object(s)', Output) >= 0);
  AssertTrue('TAlpha reported', Pos('TAlpha', Output) >= 0);
  AssertTrue('TBeta reported', Pos('TBeta', Output) >= 0);
end;

procedure TE2ELeakCheckTests.TestDebug_CycleRetained_Reported;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcCycleLeak, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header present', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('count 2', Pos('2 object(s)', Output) >= 0);
  AssertTrue('TNode reported', Pos('TNode', Output) >= 0);
end;

procedure TE2ELeakCheckTests.TestRelease_NoReport_WhenDebugOff;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit end;
  { Same leaking source but compiled without debug mode — no report expected. }
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcOneLeak, Output, ExitCode, False));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('no leak report', Pos('Blaise leak report', Output) < 0);
end;

initialization
  RegisterTest(TE2ELeakCheckTests);

end.
