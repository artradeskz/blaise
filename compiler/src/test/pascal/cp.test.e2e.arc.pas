{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.arc;

{ E2E tests for ARC (Automatic Reference Counting) — class and interface
  lifetime, weak references, and valgrind-clean leak-freedom. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EArcTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_ClassArc_NoExplicitFree_Valgrind;
    procedure TestRun_InterfaceArc_CarriesLifetime_Valgrind;
    procedure TestRun_WeakRef_BreaksCycle_Valgrind;
    procedure TestRun_ClassDestroy_FreesBuffer_Valgrind;
    procedure TestRun_TListARC_Valgrind;
    procedure TestRun_IntfValueParam_Retained_Valgrind;
    { Regression: a const string param bound to a freshly-built TEMPORARY must
      stay alive for the whole call.  Under the const-param ARC elision the
      callee skips the retain, so the call site must keep the temporary alive
      (EnsureConstStringRef).  A string LITERAL hides this (it is immortal); a
      concatenation result does not. }
    procedure TestRun_ConstStringTemp_StaysAlive_Valgrind;
    { Caller-side companion to the elision: a +0 concat transient forwarded
      through nested const-string routines and read again afterwards. }
    procedure TestRun_ConstStringParam_TransientRetained_Valgrind;
    { Three instantiations of the same generic class: verifies the Pointer→class
      ARC coercion bug is fixed (the 3rd instantiation no longer uses freed memory). }
    procedure TestRun_ThreeGenericInstances_AllWork;
  end;

implementation

procedure TE2EArcTests.SetUp;
begin
  inherited SetUp;
  SetUpScratch('compiler/target/test-e2e-arc');
end;

const
  LE = #10;

  SrcClassArcNoFree = '''
    program P;
    type
      TInner = class
        V: Integer;
      end;
      TOuter = class
        Child: TInner;
      end;
    var
      A, B: TOuter;
      I:    TInner;
    begin
      A       := TOuter.Create;
      I       := TInner.Create;
      I.V     := 42;
      A.Child := I;
      B       := A;
      WriteLn(B.Child.V)
    end.
    ''';

  SrcInterfaceArcLifetime = '''
    program P;
    type
      IThing = interface
        procedure Emit;
      end;
      TThing = class(TObject, IThing)
        FValue: Integer;
        procedure Emit;
      end;
    procedure TThing.Emit;
    begin
      WriteLn(Self.FValue)
    end;
    var
      T: TThing;
      F: IThing;
    begin
      T        := TThing.Create;
      T.FValue := 17;
      F        := T;
      F.Emit
    end.
    ''';

  SrcWeakCycle = '''
    program P;
    type
      TNode = class
        Value: Integer;
        [Weak] Other: TNode;
      end;
    var
      A, B: TNode;
    begin
      A := TNode.Create;
      B := TNode.Create;
      A.Value := 1;
      B.Value := 2;
      A.Other := B;
      B.Other := A;
      WriteLn(A.Value);
      WriteLn(B.Value)
    end.
    ''';

  SrcDestroyFreesBuffer = '''
    program P;
    type
      TBuf = class
        FData: ^Integer;
        procedure Init;
        procedure Destroy;
      end;
    procedure TBuf.Init;
    begin
      Self.FData := GetMem(4 * SizeOf(Integer))
    end;
    procedure TBuf.Destroy;
    begin
      FreeMem(Self.FData);
      Self.FData := nil
    end;
    var B: TBuf;
    begin
      B := TBuf.Create;
      B.Init;
      WriteLn('ok')
    end.
    ''';

  SrcTListARCValgrind = '''
    program P;
    type
      TList = class
        FData:     ^Integer;
        FCount:    Integer;
        FCapacity: Integer;
        procedure Grow;
        procedure Add(V: Integer);
        function  Get(I: Integer): Integer;
        procedure Destroy;
        property Count: Integer read FCount;
      end;
    procedure TList.Grow;
    var NewCap: Integer;
    begin
      if Self.FCapacity = 0 then NewCap := 4
      else NewCap := Self.FCapacity * 2;
      Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(Integer));
      Self.FCapacity := NewCap
    end;
    procedure TList.Add(V: Integer);
    var Dest: ^Integer;
    begin
      if Self.FCount = Self.FCapacity then Self.Grow;
      Dest  := Self.FData + Self.FCount * SizeOf(Integer);
      Dest^ := V;
      Self.FCount := Self.FCount + 1
    end;
    function TList.Get(I: Integer): Integer;
    var Src: ^Integer;
    begin
      Src    := Self.FData + I * SizeOf(Integer);
      Result := Src^
    end;
    procedure TList.Destroy;
    begin
      FreeMem(Self.FData);
      Self.FData := nil
    end;
    var L: TList;
    begin
      L := TList.Create;
      L.Add(10);
      L.Add(20);
      L.Add(30);
      WriteLn(L.Get(0));
      WriteLn(L.Get(1));
      WriteLn(L.Get(2));
      WriteLn(L.Count)
    end.
    ''';

procedure TE2EArcTests.TestRun_ClassArc_NoExplicitFree_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcClassArcNoFree, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('field reread', '42' + LE, Output);
  if not ValgrindAvailable then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcClassArcNoFree, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('valgrind reported errors or leaks:' + LE + Log);
  end;
end;

procedure TE2EArcTests.TestRun_InterfaceArc_CarriesLifetime_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcInterfaceArcLifetime, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('interface method result', '17' + LE, Output);
  if not ValgrindAvailable then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcInterfaceArcLifetime, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('valgrind reported errors or leaks:' + LE + Log);
  end;
end;

procedure TE2EArcTests.TestRun_WeakRef_BreaksCycle_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcWeakCycle, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('values printed via A/B', '1' + LE + '2' + LE, Output);
  if not ValgrindAvailable then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcWeakCycle, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('valgrind reported errors or leaks:' + LE + Log);
  end;
end;

procedure TE2EArcTests.TestRun_ClassDestroy_FreesBuffer_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcDestroyFreesBuffer, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('stdout', 'ok' + LE, Output);
  if not ValgrindAvailable then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcDestroyFreesBuffer, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('Destroy did not free buffer — valgrind reports:' + LE + Log);
  end;
end;

procedure TE2EArcTests.TestRun_TListARC_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTListARCValgrind, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('stdout',
    '10' + LE + '20' + LE + '30' + LE + '3' + LE, Output);
  if not ValgrindAvailable then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcTListARCValgrind, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('TList FData leaked — valgrind reports:' + LE + Log);
  end;
end;

const
  { Three instantiations of the same generic class implementing a generic
    interface.  The 3rd instantiation previously failed at link time because
    the Pointer→class coercion in FindGeneric emitted no _ClassAddRef, causing
    the template TObject to be prematurely destroyed on the 2nd call.  This
    test verifies all three compile, link, and produce correct output. }
  SrcThreeGenericInstances = '''
    program P;
    type
      IBox<T> = interface
        function  GetValue: T;
        procedure SetValue(V: T);
      end;
      TBox<T> = class(IBox<T>)
        FValue: T;
        function  GetValue: T;
        procedure SetValue(V: T);
        property Value: T read GetValue write SetValue;
      end;
    function TBox<T>.GetValue: T;
    begin
      Result := Self.FValue
    end;
    procedure TBox<T>.SetValue(V: T);
    begin
      Self.FValue := V
    end;
    var
      A: TBox<Integer>;
      B: TBox<Boolean>;
      C: TBox<Integer>;
    begin
      A := TBox<Integer>.Create;
      A.Value := 10;
      B := TBox<Boolean>.Create;
      B.Value := True;
      C := TBox<Integer>.Create;
      C.Value := 30;
      WriteLn(A.Value);
      if B.Value then WriteLn(1) else WriteLn(0);
      WriteLn(C.Value)
    end.
    ''';

const
  { By-value interface param: the callee must retain it on entry, because the
    caller's reference can be dropped during the call.  Here DoSomething nils
    the global F (the caller's sole owner) *before* using MyIntf again.  With
    the entry retain the object survives until DoSomething returns; without it
    the second MyIntf.Get would be a use-after-free.  Valgrind must report no
    error and no leak (the entry retain is balanced by the exit release). }
  SrcIntfValueParamRetained = '''
    program P;
    type
      IThing = interface
        function Get: Integer;
      end;
      TThing = class(TObject, IThing)
        FValue: Integer;
        function Get: Integer;
      end;
    function TThing.Get: Integer;
    begin
      Result := Self.FValue
    end;
    var
      F: IThing;
    procedure DoSomething(MyIntf: IThing);
    begin
      WriteLn(MyIntf.Get);
      F := nil;            { drop the caller's only other reference }
      WriteLn(MyIntf.Get)  { still valid: callee retained it on entry }
    end;
    var
      T: TThing;
    begin
      T := TThing.Create;
      T.FValue := 55;
      F := T;
      DoSomething(F)
    end.
    ''';

procedure TE2EArcTests.TestRun_IntfValueParam_Retained_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntfValueParamRetained, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('stdout', '55' + LE + '55' + LE, Output);
  if not ValgrindAvailable then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcIntfValueParamRetained, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('interface value param not retained — valgrind reports:' + LE + Log);
  end;
end;

const
  { Pass a freshly-concatenated temporary as a const string param, then read
    it inside the callee.  Without the callee-side retain the temporary's
    refcount hits zero at the call site and the string is freed before Use
    reads it — a use-after-free valgrind catches.  A literal would not expose
    this (it is immortal), so the argument must be a built-at-runtime value. }
  SrcConstStringTemp = '''
    program P;
    procedure Use(const S: string);
    begin
      WriteLn(S);
      WriteLn(Length(S))
    end;
    var
      A, B: string;
    begin
      A := 'hello';
      B := 'world';
      Use(A + ' ' + B)
    end.
    ''';

procedure TE2EArcTests.TestRun_ConstStringTemp_StaysAlive_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcConstStringTemp, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('stdout', 'hello world' + LE + '11' + LE, Output);
  if not ValgrindAvailable then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcConstStringTemp, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('const string temp freed mid-call — valgrind reports:' + LE + Log);
  end;
end;

const
  { Caller-side companion to the const-param elision.  A string concat result
    leaves _StringConcat at rc=0 (a "+0 transient").  The callee no longer
    retains the const-string buffer, so the call site must keep it alive for
    the duration of the call.  Process forwards the borrowed buffer to a
    nested const-string routine and reads it again afterwards; without the
    caller-side retain inserted by EnsureConstStringRef the buffer is freed
    mid-call and the trailing WriteLn observes corrupted data (or aborts).

    Valgrind catches the converse regression: an over-retain that never gets
    released would leak the concat buffer. }
  SrcConstStrTransient = '''
    program P;
    procedure Inner(const T: string);
    begin
      WriteLn(T)
    end;
    procedure Process(const S: string);
    begin
      Inner(S);
      Inner(S);
      WriteLn(S)
    end;
    begin
      Process('foo' + 'bar')
    end.
    ''';

procedure TE2EArcTests.TestRun_ConstStringParam_TransientRetained_Valgrind;
var Output: string; RCode: Integer; Log: string; OK: Boolean;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcConstStrTransient, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('stdout', 'foobar' + LE + 'foobar' + LE + 'foobar' + LE, Output);
  if not ValgrindAvailable then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcConstStrTransient, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('const-string transient retain missing — valgrind reports:' + LE + Log);
  end;
end;

procedure TE2EArcTests.TestRun_ThreeGenericInstances_AllWork;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcThreeGenericInstances, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('all three instances produce correct output',
    '10' + LE + '1' + LE + '30' + LE, Output);
end;

initialization
  RegisterTest(TE2EArcTests);

end.
