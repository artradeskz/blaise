{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.threading;

{ E2E tests for TThread and TCriticalSection from the RTL Classes unit.
  Covers: basic thread creation, WaitFor, Terminate flag,
  mutex-based synchronisation via TCriticalSection. }

interface

uses
  classes, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EThreadingTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_Thread_BasicExecute;
    procedure TestRun_Thread_WaitForBlocksUntilDone;
    procedure TestRun_Thread_Terminate_Flag;
    procedure TestRun_Thread_FinishedAfterExecute;
    procedure TestRun_Thread_MultipleThreads;
    procedure TestRun_CriticalSection_MutexProtectsCounter;
    procedure TestRun_Thread_InheritedDestroy_CleanExit;
    procedure TestRun_ThreadVar_MainThread_ReadWrite;
    procedure TestRun_ThreadVar_MixedWithGlobalVar;
    procedure TestRun_PerThreadAllocator_IndependentAllocs;
    procedure TestRun_AtomicARC_SharedObject_NoCorruption;
  end;

implementation

procedure TE2EThreadingTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-threading');
end;

const
  LE = #10;

  SrcBasicExecute =
    '''
    program P;
    uses Classes;
    type
      TMyThread = class(TThread)
      protected
        procedure Execute; override;
      end;
    procedure TMyThread.Execute;
    begin
      WriteLn('worker')
    end;
    var T: TMyThread;
    begin
      T := TMyThread.Create(True);
      T.Start();
      T.WaitFor();
      WriteLn('main')
    end.
    ''';

  SrcWaitForBlocks =
    '''
    program P;
    uses Classes;
    type
      TSlowThread = class(TThread)
      protected
        procedure Execute; override;
      end;
    procedure TSlowThread.Execute;
    var I, Sum: Integer;
    begin
      Sum := 0;
      for I := 0 to 999999 do
        Sum := Sum + 1;
      WriteLn('slow-done')
    end;
    var T: TSlowThread;
    begin
      T := TSlowThread.Create(True);
      T.Start();
      T.WaitFor();
      WriteLn('after-wait')
    end.
    ''';

  SrcTerminateFlag =
    '''
    program P;
    uses Classes;
    type
      TLoopThread = class(TThread)
      protected
        procedure Execute; override;
      end;
    procedure TLoopThread.Execute;
    var I: Integer;
    begin
      { Spin until terminated.  The loop must exit *only* via the terminate
        flag so FTerminated is guaranteed True when read — an early-break
        escape would let the worker finish before the main thread's Terminate
        landed, making the printed flag race between 0 and 1.  The large cap is
        only a safety net so a missed Terminate cannot hang the test forever. }
      I := 0;
      while not Self.FTerminated do
      begin
        I := I + 1;
        if I > 2000000000 then
          break
      end;
      WriteLn(Self.FTerminated)
    end;
    var T: TLoopThread;
    begin
      T := TLoopThread.Create(True);
      T.Start();
      T.Terminate();
      T.WaitFor();
      WriteLn('ok')
    end.
    ''';

  SrcFinishedFlag =
    '''
    program P;
    uses Classes;
    type
      TQuickThread = class(TThread)
      protected
        procedure Execute; override;
      end;
    procedure TQuickThread.Execute;
    begin
    end;
    var T: TQuickThread;
    begin
      T := TQuickThread.Create(True);
      WriteLn(T.FFinished);
      T.Start();
      T.WaitFor();
      WriteLn(T.FFinished)
    end.
    ''';

  SrcMultipleThreads =
    '''
    program P;
    uses Classes;
    type
      TNumThread = class(TThread)
      private
        FNum: Integer;
      protected
        procedure Execute; override;
      end;
    procedure TNumThread.Execute;
    begin
    end;
    var
      A, B, C: TNumThread;
    begin
      A := TNumThread.Create(True);
      B := TNumThread.Create(True);
      C := TNumThread.Create(True);
      A.FNum := 1;
      B.FNum := 2;
      C.FNum := 3;
      A.Start();
      B.Start();
      C.Start();
      A.WaitFor();
      B.WaitFor();
      C.WaitFor();
      WriteLn(A.FNum + B.FNum + C.FNum)
    end.
    ''';

  SrcCriticalSection =
    '''
    program P;
    uses Classes;
    type
      TShared = class
        CS: TCriticalSection;
        Counter: Integer;
      end;
      TIncThread = class(TThread)
        Shared: TShared;
      protected
        procedure Execute; override;
      end;
    procedure TIncThread.Execute;
    var I: Integer;
    begin
      for I := 0 to 999 do
      begin
        Self.Shared.CS.Enter;
        Self.Shared.Counter := Self.Shared.Counter + 1;
        Self.Shared.CS.Leave
      end
    end;
    var
      S: TShared;
      A, B: TIncThread;
    begin
      S := TShared.Create();
      S.Counter := 0;
      S.CS := TCriticalSection.Create();
      A := TIncThread.Create(True);
      B := TIncThread.Create(True);
      A.Shared := S;
      B.Shared := S;
      A.Start();
      B.Start();
      A.WaitFor();
      B.WaitFor();
      WriteLn(S.Counter)
    end.
    ''';

  SrcDestroyCleanExit =
    '''
    program P;
    uses Classes;
    type
      TMyThread = class(TThread)
      protected
        procedure Execute; override;
      end;
    procedure TMyThread.Execute;
    begin
      WriteLn('ran')
    end;
    var T: TMyThread;
    begin
      T := TMyThread.Create(True);
      T.Start();
      T.WaitFor();
      WriteLn('clean')
    end.
    ''';

{ ------------------------------------------------------------------ }
{ Tests                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EThreadingTests.TestRun_Thread_BasicExecute;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcBasicExecute, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', 'worker' + LE + 'main' + LE, Output)
end;

procedure TE2EThreadingTests.TestRun_Thread_WaitForBlocksUntilDone;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcWaitForBlocks, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', 'slow-done' + LE + 'after-wait' + LE, Output)
end;

procedure TE2EThreadingTests.TestRun_Thread_Terminate_Flag;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcTerminateFlag, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', 'True' + LE + 'ok' + LE, Output)
end;

procedure TE2EThreadingTests.TestRun_Thread_FinishedAfterExecute;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcFinishedFlag, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', 'False' + LE + 'True' + LE, Output)
end;

procedure TE2EThreadingTests.TestRun_Thread_MultipleThreads;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcMultipleThreads, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', '6' + LE, Output)
end;

procedure TE2EThreadingTests.TestRun_CriticalSection_MutexProtectsCounter;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCriticalSection, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', '2000' + LE, Output)
end;

procedure TE2EThreadingTests.TestRun_Thread_InheritedDestroy_CleanExit;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcDestroyCleanExit, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', 'ran' + LE + 'clean' + LE, Output)
end;

const
  SrcThreadVarMain =
    '''
    program P;
    threadvar
      Counter: Integer;
    begin
      Counter := 42;
      WriteLn(Counter)
    end.
    ''';

procedure TE2EThreadingTests.TestRun_ThreadVar_MainThread_ReadWrite;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcThreadVarMain, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', '42' + LE, Output)
end;

const
  SrcThreadVarMixed =
    '''
    program P;
    var
      G: Integer;
    threadvar
      T: Integer;
    begin
      G := 10;
      T := 20;
      WriteLn(G + T)
    end.
    ''';

procedure TE2EThreadingTests.TestRun_ThreadVar_MixedWithGlobalVar;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcThreadVarMixed, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', '30' + LE, Output)
end;

const
  SrcPerThreadAlloc =
    '''
    program P;
    uses Classes;
    type
      TAllocThread = class(TThread)
      private
        FOk: Integer;
      protected
        procedure Execute; override;
      end;
    procedure TAllocThread.Execute;
    var
      P1, P2: Pointer;
      I1, I2: ^Integer;
    begin
      P1 := GetMem(32);
      P2 := GetMem(64);
      I1 := P1;
      I2 := P2;
      I1^ := 111;
      I2^ := 222;
      if (I1^ = 111) and (I2^ = 222) then
        Self.FOk := 1
      else
        Self.FOk := 0;
      FreeMem(P2);
      FreeMem(P1)
    end;
    var
      A, B: TAllocThread;
    begin
      A := TAllocThread.Create(True);
      B := TAllocThread.Create(True);
      A.FOk := 0;
      B.FOk := 0;
      A.Start();
      B.Start();
      A.WaitFor();
      B.WaitFor();
      WriteLn(A.FOk + B.FOk)
    end.
    ''';

procedure TE2EThreadingTests.TestRun_PerThreadAllocator_IndependentAllocs;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcPerThreadAlloc, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', '2' + LE, Output)
end;

const
  SrcAtomicARC =
    '''
    program P;
    uses Classes;
    type
      TSharedData = class
        Value: Integer;
      end;
      TArcThread = class(TThread)
        Shared: TSharedData;
      protected
        procedure Execute; override;
      end;
    procedure TArcThread.Execute;
    var
      Local: TSharedData;
      I: Integer;
    begin
      for I := 0 to 999 do
      begin
        Local := Self.Shared;
        if Local.Value <> 42 then
        begin
          WriteLn('CORRUPT');
          Exit
        end;
        Local := nil
      end
    end;
    var
      S: TSharedData;
      A, B, C: TArcThread;
    begin
      S := TSharedData.Create();
      S.Value := 42;
      A := TArcThread.Create(True);
      B := TArcThread.Create(True);
      C := TArcThread.Create(True);
      A.Shared := S;
      B.Shared := S;
      C.Shared := S;
      A.Start();
      B.Start();
      C.Start();
      A.WaitFor();
      B.WaitFor();
      C.WaitFor();
      WriteLn('ok')
    end.
    ''';

procedure TE2EThreadingTests.TestRun_AtomicARC_SharedObject_NoCorruption;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcAtomicARC, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('stdout', 'ok' + LE, Output)
end;

initialization
  RegisterTest(TE2EThreadingTests);

end.
