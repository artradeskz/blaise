{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.recordret;

{ Behavioural coverage for QBE record-by-value return: compile + run
  programs that return records through every reg-return shape (rcInt1
  in widths 1/2/4/8 + rcInt2 16-byte aggregate) and verify the values
  arrive at the caller's destination intact.

  These tests catch bugs that pure IR-shape assertions miss — wrong
  load width, wrong store width, sign-extend confusion, padding-byte
  leakage between fields. }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ERecordReturnTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { rcInt1 1B — single Byte field. }
    procedure TestRun_RcInt1_OneByte_RoundTrip;
    { rcInt1 2B — two Byte fields. }
    procedure TestRun_RcInt1_TwoByte_RoundTrip;
    { rcInt1 4B — two SmallInt fields, negative value catches
      unsigned-load sign loss. }
    procedure TestRun_RcInt1_TwoSmallInt_NegativeValue;
    { rcInt1 8B — two Integer fields, multi-field one-eightbyte. }
    procedure TestRun_RcInt1_TwoInteger_RoundTrip;
    { rcInt1 8B — single Int64, boundary value. }
    procedure TestRun_RcInt1_Int64_MaxValue;
    { rcInt2 16B — two Int64 fields. }
    procedure TestRun_RcInt2_TwoInt64_RoundTrip;
    { rcInt2 16B — Integer + Int64 with tail-pad layout. }
    procedure TestRun_RcInt2_IntegerPlusInt64;
    { rcSSE1 8B — single Double field, xmm0 round-trip. }
    procedure TestRun_RcSSE1_Double_RoundTrip;
    { rcSSE2 16B — two Doubles, xmm0:xmm1. }
    procedure TestRun_RcSSE2_TwoDoubles_RoundTrip;
    { rcIntSSE 16B — Int64 + Double via (rax, xmm0). }
    procedure TestRun_RcIntSSE_Int64Double_RoundTrip;
    { rcSSEInt 16B — Double + Int64 via (xmm0, rax). }
    procedure TestRun_RcSSEInt_DoubleInt64_RoundTrip;
    { rcSSE1 with Single — 4B record via xmm0 as `s`. }
    procedure TestRun_RcSSE1_Single_RoundTrip;
    { Nested record — inner TPoint (8 B int) embedded in 12 B outer → rcInt2. }
    procedure TestRun_RcInt2_NestedRecord_RoundTrip;
    { Two Single fields — 8 B, all-float leaves → rcSSE1. }
    procedure TestRun_RcSSE1_TwoSingle_RoundTrip;
    { Managed-field record stays on sret (string field → no register return). }
    procedure TestRun_ManagedField_StaysSret;
    { Regression: SetLength + indexed store on a dynamic-array FIELD of an
      sret-Result record.  The native backend used to leaq the address of the
      Result pointer slot and add the field offset to it, instead of loading
      the pointer first — corrupting the stack (crash).  Both backends. }
    procedure TestRun_SretResult_DynArrayField_SetLength;
    { Regression: a record-returning METHOD call result passed directly as a
      const-record argument.  EmitArgHoist materialised the sret buffer via
      EmitExprToEax, which has no sret path for method calls (only functions),
      so the argument pointer was garbage and the callee read junk (crash).
      Both backends. }
    procedure TestRun_RecordMethodResult_AsConstArg;
    { Regression: a SCALAR FIELD of a record-returning call result, read inline
      as an argument alongside a const-string argument.  Reading the field via
      EmitExprToEax left the call's sret buffer allocated on the stack, shifting
      %rsp so the already-pushed string argument was reloaded from the wrong
      slot and lost.  Both backends. }
    procedure TestRun_RecordCallFieldArg_WithStringArg;
    { Regression: a FLOAT argument to a function/method that returns a record
      with a managed (dynamic-array) field.  The native sret call path
      materialised every argument via EmitExprToEax (integer-only), so a float
      literal raised "unsupported expression form TFloatLiteral" and a float
      variable would have gone through an integer register.  The sret arg path
      now routes float args through %xmm registers per the SysV ABI.  QBE was
      always correct, so these run on both backends. }
    procedure TestRun_FloatArg_ManagedRecordReturn_Func;
    procedure TestRun_TwoFloatArgs_ManagedRecordReturn_Func;
    procedure TestRun_FloatArg_ManagedRecordReturn_Method;
    { Regression: a method call whose RECEIVER is itself a record-returning
      call — A.Plus(B).Val().  The native backend used the record VALUE (the
      reg-return payload, or the sret buffer's first bytes) as the Self POINTER,
      dereferencing garbage and crashing.  It now materialises the receiver
      result into a stack buffer and passes its address as Self.  QBE was always
      correct; both backends asserted equal. }
    procedure TestRun_ChainedRecvRegReturn_ScalarResult;
    procedure TestRun_ChainedRecvSretReturn_RecordResult;
    procedure TestRun_ChainedRecvManyArgs;
    procedure TestRun_ChainedRecvDoubleChain;
    procedure TestRun_ChainedRecvManagedRecord_TDecimalLike;
    { Regression: a record-returning method that takes an INTERFACE parameter.
      An interface is a fat pointer (obj + itab) occupying TWO integer-register
      slots, but the native sret/record call paths popped one register per
      LOGICAL argument, so the interface's second slot was never loaded — the
      args landed in the wrong registers and (sret case) the stack was left
      unbalanced, crashing.  This is the root cause of the TDecimal.RoundTo /
      Divide / SetScale native crash (they take a const IRoundingStrategy and
      return a record).  Both backends. }
    procedure TestRun_InterfaceArg_SretRecordReturn;
    procedure TestRun_InterfaceArg_RegRecordReturn;
    procedure TestRun_InterfaceArg_IntPlusInterface_RegReturn;
    { Regression: a FREE FUNCTION (not a method) returning a record by value
      (sret) that takes an interface parameter.  EmitSretCall pushed one stack
      slot per logical argument, so the interface's second fat-pointer slot
      (itab) was never pushed/popped — the registers were misaligned and the
      stack unbalanced, crashing.  The method path (EmitMethodSretCall) was
      already fixed; this covers the free-function path.  Both backends. }
    procedure TestRun_InterfaceArg_FreeFunc_SretReturn;
    procedure TestRun_InterfaceArg_FreeFunc_IntThenInterface;
  end;

implementation

procedure TE2ERecordReturnTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-recordret');
end;

const
  LE = #10;

  SrcOneByte = '''
    program P;
    type TB = record C: Byte; end;
    function MakeIt(V: Byte): TB;
    begin
      Result.C := V
    end;
    var R: TB;
    begin
      R := MakeIt(200);
      WriteLn(R.C)
    end.
    ''';

  SrcTwoByte = '''
    program P;
    type T2B = record A, B: Byte; end;
    function MakeIt(A, B: Byte): T2B;
    begin
      Result.A := A;
      Result.B := B
    end;
    var R: T2B;
    begin
      R := MakeIt(7, 250);
      WriteLn(R.A, ' ', R.B)
    end.
    ''';

  SrcTwoSmallIntNeg = '''
    program P;
    type TS = record A, B: SmallInt; end;
    function MakeIt(A, B: SmallInt): TS;
    begin
      Result.A := A;
      Result.B := B
    end;
    var R: TS;
    begin
      R := MakeIt(-1, -32000);
      WriteLn(R.A, ' ', R.B)
    end.
    ''';

  SrcTwoInteger = '''
    program P;
    type TXY = record X, Y: Integer; end;
    function MakeIt(X, Y: Integer): TXY;
    begin
      Result.X := X;
      Result.Y := Y
    end;
    var R: TXY;
    begin
      R := MakeIt(123456, -789012);
      WriteLn(R.X, ' ', R.Y)
    end.
    ''';

  SrcInt64Max = '''
    program P;
    type TI = record V: Int64; end;
    function MakeIt(V: Int64): TI;
    begin
      Result.V := V
    end;
    var R: TI;
    begin
      R := MakeIt(9223372036854775807);
      WriteLn(R.V)
    end.
    ''';

  SrcTwoInt64 = '''
    program P;
    type T2 = record A, B: Int64; end;
    function MakeIt(A, B: Int64): T2;
    begin
      Result.A := A;
      Result.B := B
    end;
    var R: T2;
    begin
      R := MakeIt(111111111111, 222222222222);
      WriteLn(R.A, ' ', R.B)
    end.
    ''';

  SrcOneDouble = '''
    program P;
    type TF = record V: Double; end;
    function MakeIt(V: Double): TF;
    begin
      Result.V := V
    end;
    var R: TF;
    begin
      R := MakeIt(3.5);
      WriteLn(R.V)
    end.
    ''';

  SrcTwoDouble = '''
    program P;
    type T2D = record A, B: Double; end;
    function MakeIt(A, B: Double): T2D;
    begin
      Result.A := A;
      Result.B := B
    end;
    var R: T2D;
    begin
      R := MakeIt(1.5, -2.5);
      WriteLn(R.A);
      WriteLn(R.B)
    end.
    ''';

  SrcOneSingle = '''
    program P;
    type TF = record V: Single; end;
    function MakeIt(V: Single): TF;
    begin
      Result.V := V
    end;
    var R: TF;
    begin
      R := MakeIt(2.5);
      WriteLn(R.V)
    end.
    ''';

  SrcIntSSE = '''
    program P;
    type TM = record I: Int64; D: Double; end;
    function MakeIt(I: Int64; D: Double): TM;
    begin
      Result.I := I;
      Result.D := D
    end;
    var R: TM;
    begin
      R := MakeIt(42, 3.5);
      WriteLn(R.I);
      WriteLn(R.D)
    end.
    ''';

  SrcSSEInt = '''
    program P;
    type TM = record D: Double; I: Int64; end;
    function MakeIt(D: Double; I: Int64): TM;
    begin
      Result.D := D;
      Result.I := I
    end;
    var R: TM;
    begin
      R := MakeIt(-1.5, 99);
      WriteLn(R.D);
      WriteLn(R.I)
    end.
    ''';

  SrcMixIntInt64 = '''
    program P;
    type TM = record X: Integer; Y: Int64; end;
    function MakeIt(X: Integer; Y: Int64): TM;
    begin
      Result.X := X;
      Result.Y := Y
    end;
    var R: TM;
    begin
      R := MakeIt(42, 1000000000000);
      WriteLn(R.X, ' ', R.Y)
    end.
    ''';

procedure TE2ERecordReturnTests.TestRun_RcInt1_OneByte_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcOneByte, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('200', '200' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcInt1_TwoByte_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTwoByte, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('two-byte fields', '7 250' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcInt1_TwoSmallInt_NegativeValue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTwoSmallIntNeg, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  { Negative SmallInts must survive the rcInt1 round-trip even though
    the eightbyte load is unsigned — sign restoration happens at field
    access time via LoadInstrFor on the destination buffer. }
  AssertEquals('negative SmallInts', '-1 -32000' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcInt1_TwoInteger_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTwoInteger, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('two integers', '123456 -789012' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcInt1_Int64_MaxValue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInt64Max, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Int64 max', '9223372036854775807' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcInt2_TwoInt64_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTwoInt64, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('two int64s', '111111111111 222222222222' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcInt2_IntegerPlusInt64;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcMixIntInt64, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('mixed Integer+Int64', '42 1000000000000' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcSSE1_Double_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcOneDouble, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('3.5 via xmm0', '3.5', Trim(Output));
end;

procedure TE2ERecordReturnTests.TestRun_RcSSE2_TwoDoubles_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTwoDouble, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1.5 + -2.5 via xmm0:xmm1', '1.5' + LE + '-2.5', Trim(Output));
end;

procedure TE2ERecordReturnTests.TestRun_RcIntSSE_Int64Double_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntSSE, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Int64+Double via (rax, xmm0)', '42' + LE + '3.5', Trim(Output));
end;

procedure TE2ERecordReturnTests.TestRun_RcSSEInt_DoubleInt64_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcSSEInt, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Double+Int64 via (xmm0, rax)', '-1.5' + LE + '99', Trim(Output));
end;

procedure TE2ERecordReturnTests.TestRun_RcSSE1_Single_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcOneSingle, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('2.5 via xmm0 as s', '2.5', Trim(Output));
end;

procedure TE2ERecordReturnTests.TestRun_RcInt2_NestedRecord_RoundTrip;
const
  Src = '''
    program P;
    type
      TInner = record X, Y: Integer; end;
      TOuter = record A: TInner; B: Integer; end;
    function MakeIt(X, Y, B: Integer): TOuter;
    begin
      Result.A.X := X;
      Result.A.Y := Y;
      Result.B := B
    end;
    var R: TOuter;
    begin
      R := MakeIt(10, 20, 30);
      WriteLn(R.A.X, ' ', R.A.Y, ' ', R.B)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('nested record fields', '10 20 30' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_RcSSE1_TwoSingle_RoundTrip;
const
  Src = '''
    program P;
    type T2S = record A, B: Single; end;
    function MakeIt(A, B: Single): T2S;
    begin
      Result.A := A;
      Result.B := B
    end;
    var R: T2S;
    begin
      R := MakeIt(1.5, -2.5);
      WriteLn(R.A);
      WriteLn(R.B)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('two Singles via xmm0', '1.5' + LE + '-2.5', Trim(Output));
end;

procedure TE2ERecordReturnTests.TestRun_ManagedField_StaysSret;
const
  Src = '''
    program P;
    type TS = record S: string; end;
    function MakeIt(S: string): TS;
    begin
      Result.S := S
    end;
    var R: TS;
    begin
      R := MakeIt('hello');
      WriteLn(R.S)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('managed field stays on sret', 'hello' + LE, Output);
end;

procedure TE2ERecordReturnTests.TestRun_SretResult_DynArrayField_SetLength;
const
  Src = '''
    program P;
    type
      TRec = record
        Name: string;
        Cands: array of string;
      end;
    function Make: TRec;
    begin
      Result.Name := 'linker';
      SetLength(Result.Cands, 2);
      Result.Cands[0] := 'cc';
      Result.Cands[1] := 'clang'
    end;
    var R: TRec;
    begin
      R := Make();
      WriteLn(R.Name);
      WriteLn(R.Cands[0]);
      WriteLn(R.Cands[1])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'linker' + LE + 'cc' + LE + 'clang' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_RecordMethodResult_AsConstArg;
const
  Src = '''
    program P;
    type
      TR = record A, B: Integer; end;
      TFoo = class
        function MakeR: TR;
        procedure Run;
      end;
    function Sum(const R: TR): Integer;
    begin
      Result := R.A + R.B
    end;
    function TFoo.MakeR: TR;
    begin
      Result.A := 1;
      Result.B := 2
    end;
    procedure TFoo.Run;
    begin
      WriteLn(Sum(Self.MakeR()))
    end;
    var F: TFoo;
    begin
      F := TFoo.Create();
      F.Run();
      F.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '3' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_RecordCallFieldArg_WithStringArg;
const
  Src = '''
    program P;
    type TR = record A, B: Integer; end;
    function MakeR: TR;
    begin
      Result.A := 1;
      Result.B := 2
    end;
    procedure Check(const Msg: string; Expected, Actual: Integer);
    begin
      WriteLn(Msg, ' ', Expected, ' ', Actual)
    end;
    begin
      Check('vals', 1, MakeR().A)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'vals 1 1' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_FloatArg_ManagedRecordReturn_Func;
const
  Src = '''
    program P;
    type TR = record X: Double; M: array of UInt32; end;
    function Make(V: Double): TR;
    begin Result.X := V end;
    var R: TR;
    begin
      R := Make(0.25);
      WriteLn(R.X)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '0.25' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_TwoFloatArgs_ManagedRecordReturn_Func;
const
  Src = '''
    program P;
    type TR = record X, Y: Double; M: array of UInt32; end;
    function Make2(A, B: Double): TR;
    begin Result.X := A; Result.Y := B end;
    var R: TR;
    begin
      R := Make2(0.25, 0.75);
      WriteLn(R.X, ' ', R.Y)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '0.25 0.75' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_FloatArg_ManagedRecordReturn_Method;
const
  Src = '''
    program P;
    type
      TR = record X: Double; M: array of UInt32; end;
      TMaker = class
        function Make(V: Double): TR;
      end;
    function TMaker.Make(V: Double): TR;
    begin Result.X := V end;
    var K: TMaker; R: TR;
    begin
      K := TMaker.Create;
      R := K.Make(0.25);
      WriteLn(R.X);
      K.Free
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '0.25' + LE, 0);
end;

{ ------------------------------------------------------------------ }
{ Chained record-call receiver (A.Plus(B).Method())                   }
{ ------------------------------------------------------------------ }

procedure TE2ERecordReturnTests.TestRun_ChainedRecvRegReturn_ScalarResult;
const
  Src = '''
    program P;
    type
      TR = record
        V: Integer;
        function Plus(const B: TR): TR;
        function Val: Integer;
      end;
    function TR.Plus(const B: TR): TR; begin Result.V := Self.V + B.V end;
    function TR.Val: Integer; begin Result := Self.V end;
    var A, B: TR; N: Integer;
    begin
      A.V := 10; B.V := 5;
      N := A.Plus(B).Val();
      WriteLn(N)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '15' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_ChainedRecvSretReturn_RecordResult;
const
  { The OUTER method (Scale) itself returns a record via sret, and its receiver
    is the transient result of Plus — exercises the sret-call receiver path. }
  Src = '''
    program P;
    type
      TR = record
        V: Integer;
        function Plus(const B: TR): TR;
        function Scale(F: Integer): TR;
        function Val: Integer;
      end;
    function TR.Plus(const B: TR): TR; begin Result.V := Self.V + B.V end;
    function TR.Scale(F: Integer): TR; begin Result.V := Self.V * F end;
    function TR.Val: Integer; begin Result := Self.V end;
    var A, B, C: TR;
    begin
      A.V := 10; B.V := 5;
      C := A.Plus(B).Scale(2);
      WriteLn(C.Val())
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '30' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_ChainedRecvManyArgs;
const
  { >5 user args forces the overflow (stack-arg) call path with a chained
    record-call receiver. }
  Src = '''
    program P;
    type
      TR = record
        V: Integer;
        function Plus(const B: TR): TR;
        function Sum6(A1,A2,A3,A4,A5,A6: Integer): Integer;
      end;
    function TR.Plus(const B: TR): TR; begin Result.V := Self.V + B.V end;
    function TR.Sum6(A1,A2,A3,A4,A5,A6: Integer): Integer;
    begin Result := Self.V + A1+A2+A3+A4+A5+A6 end;
    var A, B: TR; N: Integer;
    begin
      A.V := 10; B.V := 5;
      N := A.Plus(B).Sum6(1,2,3,4,5,6);
      WriteLn(N)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '36' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_ChainedRecvDoubleChain;
const
  { Nested chain: the receiver of .Plus(A) is itself A.Plus(B).  Catches a
    %rsp-drift bug where the forwarded sret destination was resolved after a
    push had already moved the stack. }
  Src = '''
    program P;
    type
      TR = record
        V: Integer;
        function Plus(const B: TR): TR;
        function Val: Integer;
      end;
    function TR.Plus(const B: TR): TR; begin Result.V := Self.V + B.V end;
    function TR.Val: Integer; begin Result := Self.V end;
    var A, B: TR; N: Integer;
    begin
      A.V := 10; B.V := 5;
      N := A.Plus(B).Plus(A).Val();
      WriteLn(N)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '25' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_ChainedRecvManagedRecord_TDecimalLike;
const
  { A managed-field record (dynamic array) returned by value, then chained —
    the shape TDecimal uses.  Single and double chain both checked. }
  Src = '''
    program P;
    type
      TR = record
        V: Integer;
        M: array of UInt32;
        function Plus(const B: TR): TR;
        function Val: Integer;
      end;
    function TR.Plus(const B: TR): TR;
    begin SetLength(Result.M, 1); Result.M[0] := 0; Result.V := Self.V + B.V end;
    function TR.Val: Integer; begin Result := Self.V end;
    var A, B: TR;
    begin
      A.V := 10; B.V := 5;
      WriteLn(A.Plus(B).Val());
      WriteLn(A.Plus(B).Plus(A).Val())
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '15' + LE + '25' + LE, 0);
end;

{ ------------------------------------------------------------------ }
{ Record-returning method with an interface (fat-pointer) parameter   }
{ ------------------------------------------------------------------ }

procedure TE2ERecordReturnTests.TestRun_InterfaceArg_SretRecordReturn;
const
  { Managed field -> sret return; the interface param must occupy two arg
    register slots (obj + itab). }
  Src = '''
    program P;
    type
      IThing = interface function Val: Integer; end;
      TThing = class(TObject, IThing) function Val: Integer; end;
      TR = record
        V: Integer;
        M: array of UInt32;
        function Scale(N: Integer; const S: IThing): TR;
      end;
    function TThing.Val: Integer; begin Result := 7 end;
    function TR.Scale(N: Integer; const S: IThing): TR;
    begin SetLength(Result.M, 1); Result.V := Self.V * N + S.Val() end;
    var A, R: TR; T: IThing;
    begin
      A.V := 10; T := TThing.Create;
      R := A.Scale(2, T);
      WriteLn(R.V)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '27' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_InterfaceArg_RegRecordReturn;
const
  { No managed field -> register-return record; same interface-slot accounting
    applies on the register-return call path. }
  Src = '''
    program P;
    type
      IThing = interface function Val: Integer; end;
      TThing = class(TObject, IThing) function Val: Integer; end;
      TR = record
        V: Integer;
        function Scale(N: Integer; const S: IThing): TR;
      end;
    function TThing.Val: Integer; begin Result := 7 end;
    function TR.Scale(N: Integer; const S: IThing): TR;
    begin Result.V := Self.V * N + S.Val() end;
    var A, R: TR; T: IThing;
    begin
      A.V := 10; T := TThing.Create;
      R := A.Scale(2, T);
      WriteLn(R.V)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '27' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_InterfaceArg_IntPlusInterface_RegReturn;
const
  { A scalar arg BEFORE the interface arg checks the register ordering:
    N -> %rdx, obj(S) -> %rcx, itab(S) -> %r8. }
  Src = '''
    program P;
    type
      IThing = interface function Tag: Integer; end;
      TThing = class(TObject, IThing)
        FT: Integer;
        function Tag: Integer;
      end;
      TR = record
        V: Integer;
        function Combine(N: Integer; const S: IThing): Integer;
      end;
    function TThing.Tag: Integer; begin Result := Self.FT end;
    function TR.Combine(N: Integer; const S: IThing): Integer;
    begin Result := Self.V + N * 100 + S.Tag() end;
    var A: TR; T: TThing; N: Integer;
    begin
      A.V := 1;
      T := TThing.Create; T.FT := 9;
      N := A.Combine(2, T);
      WriteLn(N)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '210' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_InterfaceArg_FreeFunc_SretReturn;
const
  Src = '''
    program P;
    type
      IThing = interface function V: Integer; end;
      TT = class(TObject, IThing) function V: Integer; end;
      TR = record A: Integer; M: array of UInt32; end;
    function TT.V: Integer; begin Result := 7 end;
    function Mk(const S: IThing): TR;
    begin SetLength(Result.M, 1); Result.A := S.V() end;
    var R: TR; T: IThing;
    begin
      T := TT.Create;
      R := Mk(T);
      WriteLn(R.A)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '7' + LE, 0);
end;

procedure TE2ERecordReturnTests.TestRun_InterfaceArg_FreeFunc_IntThenInterface;
const
  { A scalar arg before the interface arg pins the register ordering for the
    free-function sret path: N -> %rsi, obj(S) -> %rdx, itab(S) -> %rcx
    (sret buffer is %rdi). }
  Src = '''
    program P;
    type
      IThing = interface function V: Integer; end;
      TT = class(TObject, IThing) function V: Integer; end;
      TR = record A: Integer; M: array of UInt32; end;
    function TT.V: Integer; begin Result := 7 end;
    function Mk(N: Integer; const S: IThing): TR;
    begin SetLength(Result.M, 1); Result.A := N + S.V() end;
    var R: TR; T: IThing;
    begin
      T := TT.Create;
      R := Mk(5, T);
      WriteLn(R.A)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '12' + LE, 0);
end;

initialization
  RegisterTest(TE2ERecordReturnTests);

end.
