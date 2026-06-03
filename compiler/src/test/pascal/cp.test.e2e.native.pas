{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.native;

{ E2E tests for the native code-generation backend (--backend native).

  These compile a program with TCodeGenNative (no QBE), link with cc, and run.
  The correctness oracle is parity with the QBE path on the same source; as the
  backend grows, tests here mirror the behaviour the QBE e2e suites already
  cover, run through the native path.

  Milestone coverage:
    M1 — empty program compiles, links, and exits 0.
    M2 — integer arithmetic (+ - * div mod, nesting, precedence) and
         Write/WriteLn of integers.
    M3 — control flow: if/else, while, repeat, and the comparison operators
         (= <> < > <= >=).
    M4 — program-global integer variables (declare, assign, read) and the for
         loop (to / downto, nesting, end-expression evaluated once), plus
         counter-driven while/repeat.
    M5 — user procedures/functions: integer value parameters, integer/void
         return via Result, locals in a stack frame, direct calls (including
         in expressions and nested), recursion, and for loops over a local.
         Also: the wider integer family — Byte, Word, SmallInt, Int64 (and
         signed/unsigned cousins) as globals, locals, parameters and return
         values; mixed-width arithmetic (Int64 promotion); and explicit
         type-cast conversions Byte(X) / Word(X) / Int64(X) that
         truncate/extend correctly.
         Also: var/out parameters — pass by reference (pointer passing),
         read/write through the pointer, pass-through to another var param,
         and wider-int var params (Int64, Byte). }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ENativeTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_Native_EmptyProgram_ExitsZero;
    procedure TestRun_Native_IntArithmetic_WriteLn;
    procedure TestRun_Native_DivModAndNesting;
    procedure TestRun_Native_WriteNoNewline;
    procedure TestRun_Native_IfElse;
    procedure TestRun_Native_ComparisonsAndNestedIf;
    procedure TestRun_Native_Repeat;
    procedure TestRun_Native_VarsAndForLoop;
    procedure TestRun_Native_DownToAndNestedFor;
    procedure TestRun_Native_CounterLoops;
    procedure TestRun_Native_ForEndEvaluatedOnce;
    procedure TestRun_Native_FunctionsAndCalls;
    procedure TestRun_Native_Recursion;
    procedure TestRun_Native_ForLoopOverLocal;
    procedure TestRun_Native_WiderIntGlobals;
    procedure TestRun_Native_Int64Arithmetic;
    procedure TestRun_Native_WiderIntParamsAndReturn;
    procedure TestRun_Native_TypeCastConversions;
    procedure TestRun_Native_SignednessAndWraparound;
    procedure TestRun_Native_WriteUnsigned32;
    procedure TestRun_Native_VarParamSwap;
    procedure TestRun_Native_VarParamPassThrough;
    procedure TestRun_Native_VarParamWiderInt;
    procedure TestRun_Native_OutParam;
    procedure TestRun_Native_ForBreak;
    procedure TestRun_Native_WhileContinue;
    procedure TestRun_Native_ExitFromFunction;
    procedure TestRun_Native_ExitValueShorthand;
    procedure TestRun_Native_SevenArgs;
    procedure TestRun_Native_EightArgs;
    procedure TestRun_Native_IndirectCall_BareProc;
    procedure TestRun_Native_IndirectCall_BareFunc;
    procedure TestRun_Native_Record_GlobalReadWrite;
    procedure TestRun_Native_Record_LocalReadWrite;
    procedure TestRun_Native_Record_AsParam;
    procedure TestRun_Native_StaticArray_GlobalReadWrite;
    procedure TestRun_Native_StaticArray_LocalReadWrite;
    procedure TestRun_Native_StaticArray_NonZeroLow;
    { TODO M7: method-pointer calls require class support }
    procedure TestRun_Native_IndirectCall_MethodPtr;
    { TODO M7: record-returning function — deferred until sret/aggregate support }
    procedure TestRun_Native_RecordReturnFunction;

    { M6 — floats }
    procedure TestRun_Native_Double_GlobalReadWrite;
    procedure TestRun_Native_Double_LocalReadWrite;
    procedure TestRun_Native_Double_Arithmetic;
    procedure TestRun_Native_Double_Comparison;
    procedure TestRun_Native_Double_WriteLn;
    procedure TestRun_Native_Single_GlobalReadWrite;
    procedure TestRun_Native_Double_FuncParam;
    procedure TestRun_Native_Double_FuncReturn;
  end;

implementation

procedure TE2ENativeTests.SetUp;
begin
  inherited SetUp;
  SetUpScratch('compiler/target/test-e2e-native');
end;

const
  LE = #10;

  SrcEmpty = '''
    program P;
    begin
    end.
    ''';

  SrcArith = '''
    program P;
    begin
      WriteLn(2 + 3 * 4);
      WriteLn(100 - 58)
    end.
    ''';

  SrcDivMod = '''
    program P;
    begin
      WriteLn(20 div 6);
      WriteLn(20 mod 6);
      WriteLn((2 + 3) * (10 - 4));
      WriteLn(7 - 10)
    end.
    ''';

  SrcWriteNoNL = '''
    program P;
    begin
      Write(1);
      Write(2);
      WriteLn(3)
    end.
    ''';

  SrcIfElse = '''
    program P;
    begin
      if 5 > 3 then WriteLn(1) else WriteLn(0);
      if 2 > 9 then WriteLn(1) else WriteLn(0);
      if 4 = 4 then WriteLn(44)
    end.
    ''';

  SrcComparisons = '''
    program P;
    begin
      if 3 < 5 then WriteLn(11);
      if 5 <= 5 then WriteLn(22);
      if 6 >= 9 then WriteLn(33) else WriteLn(44);
      if 7 <> 8 then WriteLn(55);
      if (2 + 2) = 4 then
        if 10 > 1 then WriteLn(66)
    end.
    ''';

  { while with a false condition never runs; repeat runs once then exits when
    the until condition is true.  (Counter-driven loops arrive with M4 locals.) }
  SrcRepeat = '''
    program P;
    begin
      while 3 > 5 do WriteLn(999);
      repeat WriteLn(8) until 1 = 1
    end.
    ''';

  SrcVarsForLoop = '''
    program P;
    var i, sum: Integer;
    begin
      sum := 0;
      for i := 1 to 5 do
        sum := sum + i;
      WriteLn(sum)
    end.
    ''';

  SrcDownToNested = '''
    program P;
    var i, j, total: Integer;
    begin
      for i := 5 downto 1 do Write(i);
      WriteLn(0);
      total := 0;
      for i := 1 to 3 do
        for j := 1 to 3 do
          total := total + 1;
      WriteLn(total)
    end.
    ''';

  SrcCounterLoops = '''
    program P;
    var n: Integer;
    begin
      n := 0;
      while n < 3 do
      begin
        Write(n);
        n := n + 1
      end;
      WriteLn(9);
      n := 0;
      repeat
        n := n + 2
      until n >= 6;
      WriteLn(n)
    end.
    ''';

  SrcForEndOnce = '''
    program P;
    var i, limit, count: Integer;
    begin
      limit := 3;
      count := 0;
      for i := 1 to limit do
      begin
        count := count + 1;
        limit := limit + 10
      end;
      WriteLn(count)
    end.
    ''';

  SrcFunctions = '''
    program P;
    function Square(x: Integer): Integer;
    begin
      Result := x * x
    end;
    function Sum3(a, b, c: Integer): Integer;
    begin
      Result := a + b + c
    end;
    procedure PrintTwice(n: Integer);
    begin
      WriteLn(n);
      WriteLn(n)
    end;
    begin
      WriteLn(Square(6));
      WriteLn(Sum3(1, 2, 3));
      PrintTwice(9);
      WriteLn(Square(Square(2)));
      WriteLn(Square(3) + Sum3(10, 20, 30))
    end.
    ''';

  SrcRecursion = '''
    program P;
    function Fact(n: Integer): Integer;
    begin
      if n <= 1 then
        Result := 1
      else
        Result := n * Fact(n - 1)
    end;
    begin
      WriteLn(Fact(5));
      WriteLn(Fact(1))
    end.
    ''';

  SrcForOverLocal = '''
    program P;
    function SumTo(n: Integer): Integer;
    var i, s: Integer;
    begin
      s := 0;
      for i := 1 to n do s := s + i;
      Result := s
    end;
    begin
      WriteLn(SumTo(10));
      WriteLn(SumTo(100))
    end.
    ''';

  { Wider integer family as program globals: declare, assign, read, and
    WriteLn each.  Byte/Word/SmallInt are stored narrow but read back to the
    full ordinal value; Int64 holds a value beyond 32 bits. }
  SrcWiderIntGlobals = '''
    program P;
    var
      b: Byte;
      w: Word;
      s: SmallInt;
      big: Int64;
    begin
      b := 200;
      w := 50000;
      s := -1000;
      big := 5000000000;
      WriteLn(b);
      WriteLn(w);
      WriteLn(s);
      WriteLn(big)
    end.
    ''';

  { Int64 arithmetic must use 64-bit operations: a product that overflows 32
    bits, and addition past the 32-bit boundary. }
  SrcInt64Arith = '''
    program P;
    var a, b, r: Int64;
    begin
      a := 100000;
      b := 100000;
      r := a * b;
      WriteLn(r);
      r := 4000000000 + 4000000000;
      WriteLn(r);
      r := r div 1000000;
      WriteLn(r)
    end.
    ''';

  { Wider-int parameters and return values across a call boundary. }
  SrcWiderIntParams = '''
    program P;
    function AddBytes(x, y: Byte): Integer;
    begin
      Result := x + y
    end;
    function ScaleBig(n: Int64): Int64;
    begin
      Result := n * 3
    end;
    function ClampWord(w: Word): Word;
    begin
      Result := w
    end;
    begin
      WriteLn(AddBytes(200, 100));
      WriteLn(ScaleBig(2000000000));
      WriteLn(ClampWord(40000))
    end.
    ''';

  { Explicit type-cast conversions truncate (narrowing) and extend (widening)
    exactly like the QBE backend: Byte(X) keeps the low 8 bits, Word(X) the
    low 16; Int64(X) widens a 32-bit value. }
  SrcTypeCasts = '''
    program P;
    var i: Integer;
    var big: Int64;
    begin
      i := 300;
      WriteLn(Byte(i));
      i := 70000;
      WriteLn(Word(i));
      i := 1000000;
      big := Int64(i) * Int64(i);
      WriteLn(big)
    end.
    ''';

  { Signedness on read-back: a SmallInt holding a value whose 16-bit pattern
    is negative reads back sign-extended; a Word with the same low-16 bits
    reads back as the large unsigned ordinal. }
  SrcSignedness = '''
    program P;
    var s: SmallInt;
    var w: Word;
    begin
      s := -2;
      w := 65534;
      WriteLn(s);
      WriteLn(w);
      WriteLn(s + 5)
    end.
    ''';

  { A Cardinal/UInt32 value above 2^31 must print as the large unsigned value,
    not a negative signed wrap. }
  SrcWriteUnsigned32 = '''
    program P;
    var c: Cardinal;
    begin
      c := 3000000000;
      WriteLn(c)
    end.
    ''';

  { Var/out parameter support (M5 continuation). }

  SrcVarParamSwap = '''
    program P;
    procedure Swap(var A, B: Integer);
    var T: Integer;
    begin
      T := A; A := B; B := T
    end;
    var X, Y: Integer;
    begin
      X := 3; Y := 7;
      Swap(X, Y);
      WriteLn(X);
      WriteLn(Y)
    end.
    ''';

  { Pass a var param through to another var param (pointer forwarding). }
  SrcVarParamPassThrough = '''
    program P;
    procedure Inc10(var N: Integer);
    begin
      N := N + 10
    end;
    procedure DoubleInc(var V: Integer);
    begin
      Inc10(V);
      Inc10(V)
    end;
    var X: Integer;
    begin
      X := 5;
      DoubleInc(X);
      WriteLn(X)
    end.
    ''';

  { Var params with wider integer types. }
  SrcVarParamWiderInt = '''
    program P;
    procedure SetBig(var B: Int64);
    begin
      B := 9000000000
    end;
    procedure SetByte(var V: Byte);
    begin
      V := 255
    end;
    var Big: Int64;
    var Small: Byte;
    begin
      Big := 0;
      Small := 0;
      SetBig(Big);
      SetByte(Small);
      WriteLn(Big);
      WriteLn(Small)
    end.
    ''';

  { Out parameter (same ABI as var — pointer passing). }
  SrcOutParam = '''
    program P;
    procedure Init(out X, Y: Integer);
    begin
      X := 42;
      Y := 99
    end;
    var A, B: Integer;
    begin
      A := 0; B := 0;
      Init(A, B);
      WriteLn(A);
      WriteLn(B)
    end.
    ''';

  { Break/continue/exit support. }

  SrcForBreak = '''
    program P;
    var I, Last: Integer;
    begin
      Last := 0;
      for I := 1 to 100 do
      begin
        Last := I;
        if I = 5 then break
      end;
      WriteLn(Last)
    end.
    ''';

  SrcWhileContinue = '''
    program P;
    var I, Sum: Integer;
    begin
      I := 0;
      Sum := 0;
      while I < 10 do
      begin
        I := I + 1;
        if I mod 2 = 0 then continue;
        Sum := Sum + I
      end;
      WriteLn(Sum)
    end.
    ''';

  SrcExitFunc = '''
    program P;
    function FirstPositive(X: Integer): Integer;
    begin
      if X > 0 then
      begin Result := X; exit end;
      Result := 0 - X
    end;
    begin
      WriteLn(FirstPositive(7));
      WriteLn(FirstPositive(0 - 9))
    end.
    ''';

  SrcExitValue = '''
    program P;
    function Clamp(X, Lo, Hi: Integer): Integer;
    begin
      if X < Lo then Exit(Lo);
      if X > Hi then Exit(Hi);
      Result := X
    end;
    begin
      WriteLn(Clamp(5, 1, 10));
      WriteLn(Clamp(0 - 3, 1, 10));
      WriteLn(Clamp(99, 1, 10))
    end.
    ''';

  { 7 integer args: first 6 in registers, 7th on the stack. }
  SrcSevenArgs = '''
    program P;
    function Sum7(A, B, C, D, E, F, G: Integer): Integer;
    begin
      Result := A + B + C + D + E + F + G
    end;
    begin
      WriteLn(Sum7(1, 2, 3, 4, 5, 6, 7))
    end.
    ''';

  { 8 integer args: first 6 in registers, 7th and 8th on the stack. }
  SrcEightArgs = '''
    program P;
    function Sum8(A, B, C, D, E, F, G, H: Integer): Integer;
    begin
      Result := A + B + C + D + E + F + G + H
    end;
    function Diff8(A, B, C, D, E, F, G, H: Integer): Integer;
    begin
      Result := A - B - C - D - E - F - G - H
    end;
    begin
      WriteLn(Sum8(1, 2, 3, 4, 5, 6, 7, 8));
      WriteLn(Diff8(100, 1, 2, 3, 4, 5, 6, 7))
    end.
    ''';

  { Bare procedural-type (no 'of object'): assign a procedure to a variable
    and call through it.  WriteLn is not callable via a proc var in the test
    harness, so we use a user-defined Print procedure. }
  SrcIndirectBareProc = '''
    program P;
    type
      TProc = procedure(X: Integer);
    procedure PrintIt(X: Integer);
    begin
      WriteLn(X)
    end;
    var F: TProc;
    begin
      F := @PrintIt;
      F(42);
      F(99)
    end.
    ''';

  { Bare function pointer: assign a function to a variable and call it in
    an expression. }
  SrcIndirectBareFunc = '''
    program P;
    type
      TFunc = function(A, B: Integer): Integer;
    function Add(A, B: Integer): Integer;
    begin
      Result := A + B
    end;
    function Mul(A, B: Integer): Integer;
    begin
      Result := A * B
    end;
    var F: TFunc;
    begin
      F := @Add;
      WriteLn(F(3, 4));
      F := @Mul;
      WriteLn(F(3, 4))
    end.
    ''';

  { Method pointer ('of object'): the variable holds a (Code, Data) pair;
    calling it must pass Data as Self.  Uses TMethod + MethodAddress + a cast
    to bind the method pointer, matching the established e2e pattern. }
  SrcIndirectMethodPtr = '''
    program P;
    type
      TCounter = class
        FVal: Integer;
      published
        procedure Add(N: Integer);
        function  Get: Integer;
      end;
      TAddProc = procedure(N: Integer) of object;
    procedure TCounter.Add(N: Integer);
    begin
      Self.FVal := Self.FVal + N
    end;
    function TCounter.Get: Integer;
    begin
      Result := Self.FVal
    end;
    var
      C:  TCounter;
      M:  TMethod;
      P:  TAddProc;
    begin
      C      := TCounter.Create;
      M.Code := MethodAddress(C, 'Add');
      M.Data := C;
      P      := TAddProc(M);
      P(10);
      P(5);
      WriteLn(C.Get())
    end.
    ''';

  { Record global: declare a record type, write fields from main, read back. }
  SrcRecordGlobal = '''
    program P;
    type
      TPoint = record
        X: Integer;
        Y: Integer;
      end;
    var Pt: TPoint;
    begin
      Pt.X := 3;
      Pt.Y := 7;
      WriteLn(Pt.X);
      WriteLn(Pt.Y);
      WriteLn(Pt.X + Pt.Y)
    end.
    ''';

  { Record local inside a function. }
  SrcRecordLocal = '''
    program P;
    type
      TRect = record
        W: Integer;
        H: Integer;
      end;
    function Area(W, H: Integer): Integer;
    var R: TRect;
    begin
      R.W := W;
      R.H := H;
      Result := R.W * R.H
    end;
    begin
      WriteLn(Area(4, 5));
      WriteLn(Area(6, 7))
    end.
    ''';

  { Record fields passed as scalar parameters and result. }
  SrcRecordParam = '''
    program P;
    type
      TPoint = record
        X: Integer;
        Y: Integer;
      end;
    function ManhattanDist(X1, Y1, X2, Y2: Integer): Integer;
    var DX, DY: Integer;
    begin
      DX := X2 - X1;
      DY := Y2 - Y1;
      if DX < 0 then DX := 0 - DX;
      if DY < 0 then DY := 0 - DY;
      Result := DX + DY
    end;
    var P1, P2: TPoint;
    begin
      P1.X := 1; P1.Y := 2;
      P2.X := 4; P2.Y := 6;
      WriteLn(ManhattanDist(P1.X, P1.Y, P2.X, P2.Y))
    end.
    ''';

  { Static array global: declare at program level, write elements, read back. }
  SrcStaticArrayGlobal = '''
    program P;
    var A: array[0..4] of Integer;
    begin
      A[0] := 10;
      A[2] := 30;
      A[4] := 50;
      WriteLn(A[0]);
      WriteLn(A[2]);
      WriteLn(A[4]);
      WriteLn(A[0] + A[2] + A[4])
    end.
    ''';

  { Static array local inside a function. }
  SrcStaticArrayLocal = '''
    program P;
    function SumArray: Integer;
    var
      B: array[0..2] of Integer;
    begin
      B[0] := 1;
      B[1] := 2;
      B[2] := 3;
      Result := B[0] + B[1] + B[2]
    end;
    begin
      WriteLn(SumArray())
    end.
    ''';

  { Static array with non-zero lower bound: A[1..3]. }
  SrcStaticArrayNonZeroLow = '''
    program P;
    var C: array[1..3] of Integer;
    begin
      C[1] := 100;
      C[2] := 200;
      C[3] := 300;
      WriteLn(C[1] + C[2] + C[3])
    end.
    ''';

  { TODO M7: a function that returns a record value.  The QBE backend handles
    this via the sret convention (hidden first pointer param); the native backend
    must do the same once aggregate/sret support lands in M7.  Until then this
    test is expected to fail on the native path with "only integer-family or void
    return supported". }
  SrcRecordReturnFunction = '''
    program P;
    type TPoint = record X: Integer; Y: Integer; end;
    function MakePoint(X, Y: Integer): TPoint;
    begin
      Result.X := X;
      Result.Y := Y
    end;
    var Pt: TPoint;
    begin
      Pt := MakePoint(3, 7);
      WriteLn(Pt.X);
      WriteLn(Pt.Y)
    end.
    ''';

  { M6 — float source programs }

  SrcDoubleGlobal = '''
    program P;
    var D: Double;
    begin
      D := 3.14;
      WriteLn(D)
    end.
    ''';

  SrcDoubleLocal = '''
    program P;
    procedure ShowDouble;
    var D: Double;
    begin
      D := 2.5;
      WriteLn(D)
    end;
    begin
      ShowDouble
    end.
    ''';

  SrcDoubleArith = '''
    program P;
    var A, B: Double;
    begin
      A := 10.0;
      B := 3.0;
      WriteLn(A + B);
      WriteLn(A - B);
      WriteLn(A * B);
      WriteLn(A / B)
    end.
    ''';

  SrcDoubleCompare = '''
    program P;
    var A, B: Double;
    begin
      A := 1.5;
      B := 2.5;
      if A < B then
        WriteLn(1)
      else
        WriteLn(0);
      if A = B then
        WriteLn(1)
      else
        WriteLn(0)
    end.
    ''';

  SrcDoubleWriteLn = '''
    program P;
    var D: Double;
    begin
      D := 1.5;
      WriteLn(D);
      WriteLn(D + 1.0)
    end.
    ''';

  SrcSingleGlobal = '''
    program P;
    var S: Single;
    begin
      S := 1.5;
      WriteLn(S)
    end.
    ''';

  SrcDoubleFuncParam = '''
    program P;
    function Scale(V: Double; Factor: Double): Double;
    begin
      Result := V * Factor
    end;
    begin
      WriteLn(Scale(3.0, 2.0))
    end.
    ''';

  SrcDoubleFuncReturn = '''
    program P;
    function Half(V: Double): Double;
    begin
      Result := V / 2.0
    end;
    var D: Double;
    begin
      D := Half(7.0);
      WriteLn(D)
    end.
    ''';

{ Every test below runs its source through BOTH backends (beQBE, beNative)
  and asserts identical stdout/exit on each — the native backend's whole
  correctness model is parity with QBE on the same source, so this exercises
  both code generators against one hand-written expected value.  As native
  gains features, more suites can adopt AssertRunsOnBoth; until then this
  suite covers the integer-family subset native supports. }

procedure TE2ENativeTests.TestRun_Native_EmptyProgram_ExitsZero;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcEmpty, '', 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntArithmetic_WriteLn;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcArith, '14' + LE + '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_DivModAndNesting;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcDivMod,
    '3' + LE + '2' + LE + '30' + LE + '-3' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_WriteNoNewline;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcWriteNoNL, '123' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IfElse;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcIfElse, '1' + LE + '0' + LE + '44' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ComparisonsAndNestedIf;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcComparisons,
    '11' + LE + '22' + LE + '44' + LE + '55' + LE + '66' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Repeat;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcRepeat, '8' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_VarsAndForLoop;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcVarsForLoop, '15' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_DownToAndNestedFor;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcDownToNested, '543210' + LE + '9' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_CounterLoops;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  { while writes 0,1,2 (Write, no newline), then WriteLn(9) -> "0129"; repeat
    counts 0->2->4->6 and WriteLn(n) -> "6". }
  AssertRunsOnBoth(SrcCounterLoops, '0129' + LE + '6' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ForEndEvaluatedOnce;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcForEndOnce, '3' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_FunctionsAndCalls;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  { Square(6)=36; Sum3(1,2,3)=6; PrintTwice(9)=9,9; Square(Square(2))=16;
    Square(3)+Sum3(10,20,30)=9+60=69 }
  AssertRunsOnBoth(SrcFunctions,
    '36' + LE + '6' + LE + '9' + LE + '9' + LE + '16' + LE + '69' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Recursion;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcRecursion, '120' + LE + '1' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ForLoopOverLocal;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcForOverLocal, '55' + LE + '5050' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_WiderIntGlobals;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcWiderIntGlobals,
    '200' + LE + '50000' + LE + '-1000' + LE + '5000000000' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Int64Arithmetic;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  { 100000*100000 = 10000000000; 4e9+4e9 = 8000000000; /1e6 = 8000 }
  AssertRunsOnBoth(SrcInt64Arith,
    '10000000000' + LE + '8000000000' + LE + '8000' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_WiderIntParamsAndReturn;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  { AddBytes(200,100)=300; ScaleBig(2e9)*3=6000000000; ClampWord(40000)=40000 }
  AssertRunsOnBoth(SrcWiderIntParams,
    '300' + LE + '6000000000' + LE + '40000' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TypeCastConversions;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  { Byte(300)=44 (300 mod 256); Word(70000)=4464 (70000 mod 65536);
    Int64(1000000)^2 = 1000000000000 }
  AssertRunsOnBoth(SrcTypeCasts,
    '44' + LE + '4464' + LE + '1000000000000' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SignednessAndWraparound;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  { SmallInt -2 reads back -2; Word 65534 reads back 65534; -2 + 5 = 3 }
  AssertRunsOnBoth(SrcSignedness, '-2' + LE + '65534' + LE + '3' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_WriteUnsigned32;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcWriteUnsigned32, '3000000000' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_VarParamSwap;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcVarParamSwap, '7' + LE + '3' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_VarParamPassThrough;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcVarParamPassThrough, '25' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_VarParamWiderInt;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcVarParamWiderInt,
    '9000000000' + LE + '255' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_OutParam;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcOutParam, '42' + LE + '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ForBreak;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcForBreak, '5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_WhileContinue;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  { Sum of odd numbers 1..9: 1+3+5+7+9 = 25 }
  AssertRunsOnBoth(SrcWhileContinue, '25' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ExitFromFunction;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcExitFunc, '7' + LE + '9' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ExitValueShorthand;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  { Clamp(5,1,10)=5; Clamp(-3,1,10)=1; Clamp(99,1,10)=10 }
  AssertRunsOnBoth(SrcExitValue, '5' + LE + '1' + LE + '10' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SevenArgs;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  { 1+2+3+4+5+6+7 = 28 }
  AssertRunsOnBoth(SrcSevenArgs, '28' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_EightArgs;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  { 1+2+3+4+5+6+7+8 = 36; 100-1-2-3-4-5-6-7 = 72 }
  AssertRunsOnBoth(SrcEightArgs, '36' + LE + '72' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IndirectCall_BareProc;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcIndirectBareProc, '42' + LE + '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IndirectCall_BareFunc;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  { F = Add: 3+4 = 7; F = Mul: 3*4 = 12 }
  AssertRunsOnBoth(SrcIndirectBareFunc, '7' + LE + '12' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Record_GlobalReadWrite;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcRecordGlobal, '3' + LE + '7' + LE + '10' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Record_LocalReadWrite;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcRecordLocal, '20' + LE + '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Record_AsParam;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  { |4-1| + |6-2| = 3 + 4 = 7 }
  AssertRunsOnBoth(SrcRecordParam, '7' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_StaticArray_GlobalReadWrite;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStaticArrayGlobal, '10' + LE + '30' + LE + '50' + LE + '90' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_StaticArray_LocalReadWrite;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStaticArrayLocal, '6' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_StaticArray_NonZeroLow;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  { 100 + 200 + 300 = 600 }
  AssertRunsOnBoth(SrcStaticArrayNonZeroLow, '600' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IndirectCall_MethodPtr;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  { QBE path must work (SrcIndirectMethodPtr uses TMethod/TCounter which
    require the RTL, so use CompileAndRunWithRTL). }
  AssertTrue('[qbe] compile+run',
    CompileAndRunWithRTL(SrcIndirectMethodPtr, Output, RCode));
  AssertEquals('[qbe] exit 0', 0, RCode);
  AssertEquals('[qbe] output', '15' + LE, Output);
  { Native path deferred to M7: requires class allocation, field access, and
    method-pointer call dispatch (load Code→%r10, Data→%rdi, shift args). }
  Ignore('TODO M7: method-pointer calls require class support not yet in native backend');
end;

procedure TE2ENativeTests.TestRun_Native_RecordReturnFunction;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  { QBE path must work. }
  AssertTrue('[qbe] compile+run', CompileAndRun(SrcRecordReturnFunction, Output, RCode));
  AssertEquals('[qbe] exit 0', 0, RCode);
  AssertEquals('[qbe] output', '3' + LE + '7' + LE, Output);
  { Native path deferred to M7 (sret / aggregate return not yet implemented). }
  Ignore('TODO M7: record-returning function not yet supported on native backend');
end;

{ ------------------------------------------------------------------ }
{ M6 — float parity                                                    }
{ ------------------------------------------------------------------ }

procedure TE2ENativeTests.TestRun_Native_Double_GlobalReadWrite;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcDoubleGlobal, '3.14' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Double_LocalReadWrite;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcDoubleLocal, '2.5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Double_Arithmetic;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcDoubleArith, '13' + LE + '7' + LE + '30' + LE + '3.33333333333333' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Double_Comparison;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcDoubleCompare, '1' + LE + '0' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Double_WriteLn;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcDoubleWriteLn, '1.5' + LE + '2.5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Single_GlobalReadWrite;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcSingleGlobal, '1.5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Double_FuncParam;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  { Scale(3.0, 2.0) = 6.0 }
  AssertRunsOnBoth(SrcDoubleFuncParam, '6' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Double_FuncReturn;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  { Half(7.0) = 3.5 }
  AssertRunsOnBoth(SrcDoubleFuncReturn, '3.5' + LE, 0);
end;

initialization
  RegisterTest(TE2ENativeTests);

end.
