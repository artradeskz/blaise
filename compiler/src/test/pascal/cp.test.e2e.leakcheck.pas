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
    procedure TestDebug_LeakReport_IncludesUnitAndLine;
    procedure TestDebug_LeakReport_IncludesUnitAndLine_Native;
    procedure TestDebug_StringLeak_Reported;
    procedure TestDebug_StringClean_NoReport;

    { obj.Field := MakeClass() consumes the call's +1 — no leak per store. }
    procedure TestDebug_ClassFieldFromCall_NoLeak;
    { Multiple same-named typed handlers share one slot — no over-release. }
    procedure TestDebug_MultiHandlerVar_NoOverRelease;
    { for-in over a TList: GetEnumerator's +1 result must be transferred
      into the loop slot, not re-retained — one enumerator leaked per
      loop otherwise. }
    procedure TestDebug_ForInEnumerator_NoLeak;
    procedure TestDebug_ForInEnumerator_NoLeak_Native;
    { Objects allocated inside generic method bodies must be attributed
      to the unit that DECLARES the template (the line number already
      refers to the template source), not the instantiating unit. }
    procedure TestDebug_GenericAllocSite_ReportsDefiningUnit;
    procedure TestDebug_GenericAllocSite_ReportsDefiningUnit_Native;
    { An interface-returning call passed directly as an argument — Show(Make())
      — hands the callee an owned (+1) fat pointer it borrows; the caller must
      release it after the call or one instance leaks. }
    procedure TestDebug_IntfCallResultArg_NoLeak;
    procedure TestDebug_IntfCallResultArg_NoLeak_Native;
  end;

implementation

procedure TE2ELeakCheckTests.SetUp;
begin
  inherited SetUp();
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
      B := TBox.Create();
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
        raise EFoo.Create()
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
    begin
      B := TBox.Create();
      B.Value := 7;
      _ClassAddRef(Pointer(B));
      { Artificial extra addref: rc=2.  Scope-exit releases B (rc=1),
        but the unbalanced addref keeps the object alive — leak. }
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
    begin
      A := TAlpha.Create();
      B := TBeta.Create();
      _ClassAddRef(Pointer(A));
      _ClassAddRef(Pointer(B));
      { Artificial extra addref on each: scope-exit releases both
        (rc 2->1) but the unbalanced addref keeps them alive. }
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
      X := TNode.Create();
      Y := TNode.Create();
      X.Other := Y;
      Y.Other := X;
      { X and Y each hold refcount >= 2 due to the cycle; when the local
        vars go out of scope the refcount drops to 1, not 0 — both leak. }
      WriteLn('done')
    end.
    ''';

  { Leak with allocation-site info: the report must include the unit name and
    line number where the leaking TBox.Create() call was made. }
  SrcLeakWithSite = '''
    program LeakSite;
    uses blaise_arc;
    type
      TBox = class
        Value: Integer;
      end;
    var
      B: TBox;
    begin
      B := TBox.Create();
      _ClassAddRef(Pointer(B));
      WriteLn('done')
    end.
    ''';

  { Leaked string: concatenation produces a heap-allocated string (non-immortal).
    Extra AddRef prevents scope-exit release from freeing it. }
  SrcStringLeak = '''
    program P;
    uses blaise_arc;
    var
      S: string;
    begin
      S := 'hel' + 'lo';
      _StringAddRef(Pointer(S));
      WriteLn('done')
    end.
    ''';

  { Clean string usage: no leak expected — scope-exit ARC releases properly. }
  SrcStringClean = '''
    program P;
    uses blaise_arc;
    var
      S: string;
    begin
      S := 'hello';
      WriteLn(S)
    end.
    ''';

{ ------------------------------------------------------------------ }

const
  SrcForInEnum = '''
    program P;
    uses generics.collections;
    var
      L: TList<Integer>;
      I, Total: Integer;
    begin
      L := TList<Integer>.Create;
      L.Add(5);
      L.Add(4);
      Total := 0;
      for I in L do
        Total := Total + I;
      WriteLn(Total);
    end.
    ''';

procedure TE2ELeakCheckTests.TestDebug_ForInEnumerator_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(SrcForInEnum, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', '9' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_ForInEnumerator_NoLeak_Native;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebugOn(beNative, SrcForInEnum, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', '9' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

const
  { The enumerator is allocated INSIDE TList<T>.GetEnumerator — a generic
    method body declared in generics.collections.pas.  The extra AddRef
    keeps it alive past scope exit, so the leak report must show its
    allocation site as 'generics.collections:<line>', not '<program>:<line>'. }
  SrcGenericAllocSite = '''
    program LeakGen;
    uses blaise_arc, generics.collections;
    var
      L: TList<Integer>;
      E: TListEnumerator<Integer>;
    begin
      L := TList<Integer>.Create();
      L.Add(1);
      E := L.GetEnumerator();
      _ClassAddRef(Pointer(E));
      WriteLn('done')
    end.
    ''';

procedure TE2ELeakCheckTests.TestDebug_GenericAllocSite_ReportsDefiningUnit;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebugOn(beQBE, SrcGenericAllocSite, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('enumerator class reported', Pos('TListEnumerator', Output) >= 0);
  AssertTrue('defining unit in report, got: ' + Output,
    Pos(' at Generics.Collections:', Output) >= 0);
  AssertTrue('instantiating program NOT in report, got: ' + Output,
    Pos(' at LeakGen:', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_GenericAllocSite_ReportsDefiningUnit_Native;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebugOn(beNative, SrcGenericAllocSite, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('enumerator class reported', Pos('TListEnumerator', Output) >= 0);
  AssertTrue('defining unit in report, got: ' + Output,
    Pos(' at Generics.Collections:', Output) >= 0);
  AssertTrue('instantiating program NOT in report, got: ' + Output,
    Pos(' at LeakGen:', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_NoLeak_NoReport;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
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
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
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
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
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
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcOneLeak, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header present', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('count 1', Pos('1 leak(s)', Output) >= 0);
  AssertTrue('class name', Pos('TBox', Output) >= 0);
end;

procedure TE2ELeakCheckTests.TestDebug_MultipleLeaks_AllReported;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcTwoLeaks, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header present', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('count 2', Pos('2 leak(s)', Output) >= 0);
  AssertTrue('TAlpha reported', Pos('TAlpha', Output) >= 0);
  AssertTrue('TBeta reported', Pos('TBeta', Output) >= 0);
end;

procedure TE2ELeakCheckTests.TestDebug_CycleRetained_Reported;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcCycleLeak, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header present', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('count 2', Pos('2 leak(s)', Output) >= 0);
  AssertTrue('TNode reported', Pos('TNode', Output) >= 0);
end;

procedure TE2ELeakCheckTests.TestRelease_NoReport_WhenDebugOff;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  { Same leaking source but compiled without debug mode — no report expected. }
  AssertTrue('compile+run', CompileAndRunWithRTLDebug(SrcOneLeak, Output, ExitCode, False));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('no leak report', Pos('Blaise leak report', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_LeakReport_IncludesUnitAndLine;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebugOn(beQBE, SrcLeakWithSite, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('class name', Pos('TBox', Output) >= 0);
  AssertTrue('unit name in report', Pos('LeakSite', Output) >= 0);
  AssertTrue('at separator', Pos(' at ', Output) >= 0);
end;

procedure TE2ELeakCheckTests.TestDebug_LeakReport_IncludesUnitAndLine_Native;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebugOn(beNative, SrcLeakWithSite, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('class name', Pos('TBox', Output) >= 0);
  AssertTrue('unit name in report', Pos('LeakSite', Output) >= 0);
  AssertTrue('at separator', Pos(' at ', Output) >= 0);
end;

procedure TE2ELeakCheckTests.TestDebug_StringLeak_Reported;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(SrcStringLeak, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('leak header', Pos('Blaise leak report', Output) >= 0);
  AssertTrue('string tag', Pos('string', Output) >= 0);
end;

procedure TE2ELeakCheckTests.TestDebug_StringClean_NoReport;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebug(SrcStringClean, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertTrue('no leak report', Pos('Blaise leak report', Output) < 0);
end;

const
  SrcClassFieldFromCall = '''
    program P;
    type
      TThing = class N: Integer; end;
      THolder = class Item: TThing; end;
    function MakeThing(): TThing;
    begin
      Result := TThing.Create();
      Result.N := 7;
    end;
    var
      H: THolder;
      I: Integer;
    begin
      H := THolder.Create();
      for I := 1 to 100 do
        H.Item := MakeThing();
      WriteLn(H.Item.N);
    end.
    ''';

  SrcMultiHandlerVar = '''
    program P;
    type
      EBase = class
        FMessage: string;
      end;
      EFoo = class(EBase) end;
    var X: Integer;
    begin
      X := 0;
      try
        raise EFoo.Create()
      except
        on E: EFoo do X := 42;
        on E: EBase do X := 1
      end;
      WriteLn(X)
    end.
    ''';

procedure TE2ELeakCheckTests.TestDebug_ClassFieldFromCall_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcClassFieldFromCall, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', '7' + LE, Output);
  AssertTrue('no leak report (qbe)', Pos('leak', Output) < 0);
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcClassFieldFromCall, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', '7' + LE, Output);
  AssertTrue('no leak report (native)', Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_MultiHandlerVar_NoOverRelease;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run (qbe)',
    CompileAndRunWithRTLDebugOn(beQBE, SrcMultiHandlerVar, Output, ExitCode, True));
  AssertEquals('exit 0 (qbe)', 0, ExitCode);
  AssertEquals('stdout (qbe)', '42' + LE, Output);
  AssertTrue('no leak report (qbe)', Pos('leak', Output) < 0);
  AssertTrue('compile+run (native)',
    CompileAndRunWithRTLDebugOn(beNative, SrcMultiHandlerVar, Output, ExitCode, True));
  AssertEquals('exit 0 (native)', 0, ExitCode);
  AssertEquals('stdout (native)', '42' + LE, Output);
  AssertTrue('no leak report (native)', Pos('leak', Output) < 0);
end;

const
  { Interface-returning call result passed positionally — Show(MakeFoo(42)).
    MakeFoo returns an owned (+1) interface; the borrowing parameter does not
    release it, so the caller must.  One TFoo leaked on native before the
    akIntfConsume hoist released it after the call. }
  SrcIntfCallResultArg = '''
    program P;
    type
      IFoo = interface
        function Val: Integer;
      end;
      TFoo = class(TObject, IFoo)
        FN: Integer;
        function Val: Integer;
      end;
    function TFoo.Val: Integer;
    begin Result := FN end;
    function MakeFoo(N: Integer): IFoo;
    var F: TFoo;
    begin
      F := TFoo.Create();
      F.FN := N;
      Result := F
    end;
    procedure Show(F: IFoo);
    begin
      WriteLn(F.Val())
    end;
    begin
      Show(MakeFoo(42))
    end.
    ''';

procedure TE2ELeakCheckTests.TestDebug_IntfCallResultArg_NoLeak;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebugOn(beQBE, SrcIntfCallResultArg, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', '42' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

procedure TE2ELeakCheckTests.TestDebug_IntfCallResultArg_NoLeak_Native;
var
  Output: string;
  ExitCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run',
    CompileAndRunWithRTLDebugOn(beNative, SrcIntfCallResultArg, Output, ExitCode, True));
  AssertEquals('exit 0', 0, ExitCode);
  AssertEquals('stdout', '42' + LE, Output);
  AssertTrue('no leak report, got: ' + Output, Pos('leak', Output) < 0);
end;

initialization
  RegisterTest(TE2ELeakCheckTests);

end.
