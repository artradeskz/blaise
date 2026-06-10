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
    procedure TestRun_Native_TenArgs;
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
    procedure TestRun_Native_Record_NestedFieldAssign;
    { M6 — floats }
    procedure TestRun_Native_Double_GlobalReadWrite;
    procedure TestRun_Native_Double_LocalReadWrite;
    procedure TestRun_Native_Double_Arithmetic;
    procedure TestRun_Native_Double_Comparison;
    procedure TestRun_Native_Double_WriteLn;
    procedure TestRun_Native_Single_GlobalReadWrite;
    procedure TestRun_Native_Double_FuncParam;
    procedure TestRun_Native_Double_FuncReturn;

    { M7c — string operations }
    procedure TestRun_Native_String_WriteLnLiteral;
    procedure TestRun_Native_String_AssignAndWrite;
    procedure TestRun_Native_String_Concat;
    procedure TestRun_Native_String_Length;
    procedure TestRun_Native_String_Pos;
    procedure TestRun_Native_String_Copy;
    procedure TestRun_Native_String_UpperCase;
    procedure TestRun_Native_String_IntToStr;
    procedure TestRun_Native_String_StrToInt;
    procedure TestRun_Native_String_Param;
    procedure TestRun_Native_String_FuncReturn;
    procedure TestRun_Native_String_Delete;
    procedure TestRun_Native_String_SetLength;
    procedure TestRun_Native_String_Subscript;
    procedure TestRun_Native_String_SameText;
    procedure TestRun_Native_String_Format_IntArg;
    procedure TestRun_Native_String_Format_StrArg;
    procedure TestRun_Native_String_Format_MixedArgs;
    procedure TestRun_Native_String_ConcatWithInt;
    procedure TestRun_Native_String_ChrConcat;

    { M7d — exception handling }
    procedure TestRun_Native_TryFinally_Normal;
    procedure TestRun_Native_TryFinally_NestedNormal;
    procedure TestRun_Native_TryFinally_ExitUnwind;
    procedure TestRun_Native_TryFinally_BreakUnwind;
    procedure TestRun_Native_TryExcept_Bare;
    procedure TestRun_Native_TryExcept_TypedHandler;
    procedure TestRun_Native_TryExcept_SubclassMatch;
    procedure TestRun_Native_TryExcept_BareRaisePropagate;
    procedure TestRun_Native_TryExcept_ElseBody;
    procedure TestRun_Native_ExitThroughNestedFinally;

    { M7e — open arrays and dynamic arrays }
    procedure TestRun_Native_OpenArray_Sum;
    procedure TestRun_Native_OpenArray_HighLow;
    procedure TestRun_Native_OpenArray_Length;
    procedure TestRun_Native_StaticToOpen_Length;
    procedure TestRun_Native_StaticToOpen_Sum;
    procedure TestRun_Native_StaticToOpen_PassToNested;
    procedure TestRun_Native_DynArray_SetLengthAndAccess;
    procedure TestRun_Native_DynArray_LengthAndHigh;

    { M7f — interface dispatch through itab }
    procedure TestRun_Native_Interface_ZeroArgDispatch;
    procedure TestRun_Native_Interface_ArgDispatch;
    procedure TestRun_Native_Interface_ProcDispatch;
    procedure TestRun_Native_Interface_IntfToIntfCopy;
    procedure TestRun_Native_Interface_AsCast;
    procedure TestRun_Native_Interface_NilClear;
    { Regression (issue #64): interface-typed field with same name as a
      program-level global of a different type }
    procedure TestRun_Native_InterfaceField_ShadowsGlobal;
    { Interface parameters — fat pointer passing through all call sites }
    procedure TestRun_Native_IntfParam_Proc;
    procedure TestRun_Native_IntfParam_Method;
    procedure TestRun_Native_IntfParam_Constructor;
    procedure TestRun_Native_IntfParam_Inherited;
    procedure TestRun_Native_IntfParam_ClassExpr;

    { M8 — inherited calls }
    procedure TestRun_Native_Inherited_Proc;
    procedure TestRun_Native_Inherited_FuncSetsResult;
    { M8 — var/out params to a method call }
    procedure TestRun_Native_MethodVarParam_Mutates;
    procedure TestRun_Native_MethodVarParam_Swap;

    { Array field access }
    procedure TestRun_Native_RecordArrayField_StaticRead;

    { ARC on class fields }
    procedure TestRun_Native_ArcClassField_StoreAndRead;
    procedure TestRun_Native_ArcStringField_StoreAndRead;
    procedure TestRun_Native_ArcClassAssignNil_Destroys;
    { ARC for dyn-array / interface / nested-record fields, owned-return stores,
      and implicit-Self managed-field stores (native-backend parity with QBE). }
    procedure TestRun_Native_ArcDynArrayField_StoreAndRead;
    procedure TestRun_Native_ArcInterfaceField_AssignAndDispatch;
    procedure TestRun_Native_IntfFieldDispatch;
    procedure TestRun_Native_IntfFieldReadIntoLocal;
    procedure TestRun_Native_RetValSurvivesArcRelease;
    procedure TestRun_Native_IntfArgToMethod;
    procedure TestRun_Native_ArcNestedRecordField_FullCleanup;
    procedure TestRun_Native_ArcStringReturnToField_NoDoubleRetain;
    procedure TestRun_Native_ArcImplicitSelfStringField_Reassign;

    { ARC value param retain/release }
    procedure TestRun_Native_ArcValueParam_String;
    procedure TestRun_Native_ArcValueParam_Class;

    { Address-of expressions }
    procedure TestRun_Native_AddrOf_LocalVariable;
    procedure TestRun_Native_AddrOf_StaticArrayElement;
    procedure TestRun_Native_AddrOf_DynArrayElement;
    procedure TestRun_Native_AddrOf_RecordFieldArrayElem;
    procedure TestRun_Native_AddrOf_MethodPointer;

    { Bitwise NOT }
    procedure TestRun_Native_BitwiseNot_Integer;
    procedure TestRun_Native_BitwiseNot_Bitmask;

    { SizeOf }
    procedure TestRun_Native_SizeOf_Record;
    procedure TestRun_Native_SizeOf_GenericRecord;

    { Generics }
    procedure TestRun_Native_GenericRecord_Method;
    procedure TestRun_Native_GenericClass_Method;
    procedure TestRun_Native_GenericFunc_Standalone;
    procedure TestRun_Native_GenericClass_Interface;

    { Multi-unit whole-program native path (TX86_64Backend.EmitUnit/AppendProgram). }
    procedure TestRun_Native_MultiUnit_PlainFunction;
    procedure TestRun_Native_MultiUnit_StringFunction;
    procedure TestRun_Native_MultiUnit_Class;
    procedure TestRun_Native_MultiUnit_Interface;
    procedure TestRun_Native_MultiUnit_GlobalsAndInit;

    { By-value record params (memcpy + ARC on managed leaves). }
    procedure TestRun_Native_RecordParam_ReadOnly;
    procedure TestRun_Native_RecordParam_Mutate;
    procedure TestRun_Native_RecordParam_ThreeStrings;
    procedure TestRun_Native_RecordParam_IntOnly;
    procedure TestRun_Native_RecordParam_InlineSretArg;
    procedure TestRun_Native_RecordParam_ConstSkipsArc;
    procedure TestRun_Native_ShortCircuit_AndSkipsRhs;
    procedure TestRun_Native_ShortCircuit_OrSkipsRhs;
    procedure TestRun_Native_ShortCircuit_AndNilGuard;
    procedure TestRun_Native_ProceduralParam;
    procedure TestRun_Native_IsExpr_Class;
    procedure TestRun_Native_AsExpr_Class;
    procedure TestRun_Native_SupportsExpr;
    procedure TestRun_Native_IndirectFuncCallExpr;

    { Gap #6 — builtins }
    procedure TestRun_Native_Builtin_Ord;
    procedure TestRun_Native_Builtin_Assigned;
    procedure TestRun_Native_Builtin_Abs;
    procedure TestRun_Native_Builtin_Halt;
    procedure TestRun_Native_Builtin_RoundTrunc;
    procedure TestRun_Native_Builtin_CompareStr;
    procedure TestRun_Native_Builtin_UpCase;
    procedure TestRun_Native_Builtin_Int64ToStr;

    { Gap #5 — nested (local) procedures }
    procedure TestRun_Native_NestedProc_ReadCapture;
    procedure TestRun_Native_NestedProc_WriteCapture;

    { Trig / math builtins with Single dispatch }
    procedure TestRun_Native_Builtin_SinCos;
    procedure TestRun_Native_Builtin_SqrtDouble;

    { Typed-pointer float writes }
    procedure TestRun_Native_DoublePtrWrite;
    procedure TestRun_Native_SinglePtrWrite_NoAdjacentClobber;

    { Inc/Dec on non-simple-variable arguments }
    procedure TestRun_Native_IncDec_RecordField;
    procedure TestRun_Native_IncDec_PtrDeref;

    { Type-cast on pointer-sized types }
    procedure TestRun_Native_TypeCast_PointerClass;

    { Property reads via getter methods }
    procedure TestRun_Native_PropertyRead_Simple;
    procedure TestRun_Native_PropertyRead_Indexed;

    { Property writes via setter methods }
    procedure TestRun_Native_PropertyWrite_Simple;
    procedure TestRun_Native_PropertyWrite_Indexed;

    { Built-in class access }
    procedure TestRun_Native_ClassName;

    { Method call >5 user args }
    procedure TestRun_Native_MethodCall_ManyArgs;

    { Implicit-Self class field access — FInner.FVal inside a method }
    procedure TestRun_Native_ImplicitSelf_ClassField;

    { Implicit-Self property getter call inside a method }
    procedure TestRun_Native_ImplicitSelf_PropertyGetter;

    { Const array data emission + ConstArraySymbol reference }
    procedure TestRun_Native_ConstArray_StringElements;

    { Virtual method dispatch in expression context }
    procedure TestRun_Native_VirtualDispatch_Expr;
  end;

implementation

procedure TE2ENativeTests.SetUp;
begin
  inherited SetUp();
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

  { 10 integer args: first 6 in registers, 7th–10th on the stack. }
  SrcTenArgs = '''
    program P;
    function Sum10(A, B, C, D, E, F, G, H, I, J: Integer): Integer;
    begin
      Result := A + B + C + D + E + F + G + H + I + J
    end;
    begin
      WriteLn(Sum10(1, 2, 3, 4, 5, 6, 7, 8, 9, 10))
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
      C      := TCounter.Create();
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

  SrcSizeOfRecord = '''
    program P;
    type
      TPoint = record
        X: Integer;
        Y: Integer;
      end;
    begin
      WriteLn(SizeOf(TPoint))
    end.
    ''';

  SrcSizeOfGenericRecord = '''
    program P;
    type
      TPair<T1, T2> = record
        First: T1;
        Second: T2;
      end;
    var
      A: TPair<Integer, Integer>;
      B: TPair<Integer, Int64>;
    begin
      WriteLn(SizeOf(A));
      WriteLn(SizeOf(B))
    end.
    ''';

  SrcNestedRecordFieldAssign = '''
    program P;
    type
      TDate = record
        Year: Integer;
        Month: Integer;
        Day: Integer;
        function Sum: Integer;
      end;
      TDateTime = record
        Date: TDate;
        Hour: Integer;
      end;
    function TDate.Sum: Integer;
    begin
      Result := Self.Year + Self.Month + Self.Day
    end;
    var
      DT: TDateTime;
      D: TDate;
    begin
      DT.Date.Year := 2026;
      DT.Date.Month := 6;
      DT.Date.Day := 5;
      DT.Hour := 14;
      D := DT.Date;
      WriteLn(D.Sum());
      WriteLn(DT.Date.Sum())
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
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcEmpty, '', 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntArithmetic_WriteLn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcArith, '14' + LE + '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_DivModAndNesting;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcDivMod,
    '3' + LE + '2' + LE + '30' + LE + '-3' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_WriteNoNewline;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcWriteNoNL, '123' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IfElse;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcIfElse, '1' + LE + '0' + LE + '44' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ComparisonsAndNestedIf;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcComparisons,
    '11' + LE + '22' + LE + '44' + LE + '55' + LE + '66' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Repeat;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcRepeat, '8' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_VarsAndForLoop;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcVarsForLoop, '15' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_DownToAndNestedFor;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcDownToNested, '543210' + LE + '9' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_CounterLoops;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { while writes 0,1,2 (Write, no newline), then WriteLn(9) -> "0129"; repeat
    counts 0->2->4->6 and WriteLn(n) -> "6". }
  AssertRunsOnBoth(SrcCounterLoops, '0129' + LE + '6' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ForEndEvaluatedOnce;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcForEndOnce, '3' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_FunctionsAndCalls;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Square(6)=36; Sum3(1,2,3)=6; PrintTwice(9)=9,9; Square(Square(2))=16;
    Square(3)+Sum3(10,20,30)=9+60=69 }
  AssertRunsOnBoth(SrcFunctions,
    '36' + LE + '6' + LE + '9' + LE + '9' + LE + '16' + LE + '69' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Recursion;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcRecursion, '120' + LE + '1' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ForLoopOverLocal;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcForOverLocal, '55' + LE + '5050' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_WiderIntGlobals;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcWiderIntGlobals,
    '200' + LE + '50000' + LE + '-1000' + LE + '5000000000' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Int64Arithmetic;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 100000*100000 = 10000000000; 4e9+4e9 = 8000000000; /1e6 = 8000 }
  AssertRunsOnBoth(SrcInt64Arith,
    '10000000000' + LE + '8000000000' + LE + '8000' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_WiderIntParamsAndReturn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { AddBytes(200,100)=300; ScaleBig(2e9)*3=6000000000; ClampWord(40000)=40000 }
  AssertRunsOnBoth(SrcWiderIntParams,
    '300' + LE + '6000000000' + LE + '40000' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TypeCastConversions;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Byte(300)=44 (300 mod 256); Word(70000)=4464 (70000 mod 65536);
    Int64(1000000)^2 = 1000000000000 }
  AssertRunsOnBoth(SrcTypeCasts,
    '44' + LE + '4464' + LE + '1000000000000' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SignednessAndWraparound;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { SmallInt -2 reads back -2; Word 65534 reads back 65534; -2 + 5 = 3 }
  AssertRunsOnBoth(SrcSignedness, '-2' + LE + '65534' + LE + '3' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_WriteUnsigned32;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcWriteUnsigned32, '3000000000' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_VarParamSwap;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcVarParamSwap, '7' + LE + '3' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_VarParamPassThrough;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcVarParamPassThrough, '25' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_VarParamWiderInt;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcVarParamWiderInt,
    '9000000000' + LE + '255' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_OutParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcOutParam, '42' + LE + '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ForBreak;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcForBreak, '5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_WhileContinue;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Sum of odd numbers 1..9: 1+3+5+7+9 = 25 }
  AssertRunsOnBoth(SrcWhileContinue, '25' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ExitFromFunction;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcExitFunc, '7' + LE + '9' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ExitValueShorthand;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Clamp(5,1,10)=5; Clamp(-3,1,10)=1; Clamp(99,1,10)=10 }
  AssertRunsOnBoth(SrcExitValue, '5' + LE + '1' + LE + '10' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SevenArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 1+2+3+4+5+6+7 = 28 }
  AssertRunsOnBoth(SrcSevenArgs, '28' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_EightArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 1+2+3+4+5+6+7+8 = 36; 100-1-2-3-4-5-6-7 = 72 }
  AssertRunsOnBoth(SrcEightArgs, '36' + LE + '72' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TenArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 1+2+3+4+5+6+7+8+9+10 = 55 }
  AssertRunsOnBoth(SrcTenArgs, '55' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IndirectCall_BareProc;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcIndirectBareProc, '42' + LE + '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IndirectCall_BareFunc;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { F = Add: 3+4 = 7; F = Mul: 3*4 = 12 }
  AssertRunsOnBoth(SrcIndirectBareFunc, '7' + LE + '12' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Record_GlobalReadWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcRecordGlobal, '3' + LE + '7' + LE + '10' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Record_LocalReadWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcRecordLocal, '20' + LE + '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Record_AsParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { |4-1| + |6-2| = 3 + 4 = 7 }
  AssertRunsOnBoth(SrcRecordParam, '7' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_StaticArray_GlobalReadWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStaticArrayGlobal, '10' + LE + '30' + LE + '50' + LE + '90' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_StaticArray_LocalReadWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStaticArrayLocal, '6' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_StaticArray_NonZeroLow;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 100 + 200 + 300 = 600 }
  AssertRunsOnBoth(SrcStaticArrayNonZeroLow, '600' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IndirectCall_MethodPtr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcIndirectMethodPtr, '15' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecordReturnFunction;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcRecordReturnFunction, '3' + LE + '7' + LE, 0);
end;

{ ------------------------------------------------------------------ }
{ M6 — float parity                                                    }
{ ------------------------------------------------------------------ }

procedure TE2ENativeTests.TestRun_Native_Double_GlobalReadWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcDoubleGlobal, '3.14' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Double_LocalReadWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcDoubleLocal, '2.5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Double_Arithmetic;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcDoubleArith, '13' + LE + '7' + LE + '30' + LE + '3.33333333333333' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Double_Comparison;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcDoubleCompare, '1' + LE + '0' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Double_WriteLn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcDoubleWriteLn, '1.5' + LE + '2.5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Single_GlobalReadWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcSingleGlobal, '1.5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Double_FuncParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Scale(3.0, 2.0) = 6.0 }
  AssertRunsOnBoth(SrcDoubleFuncParam, '6' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Double_FuncReturn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Half(7.0) = 3.5 }
  AssertRunsOnBoth(SrcDoubleFuncReturn, '3.5' + LE, 0);
end;

{ ------------------------------------------------------------------ }
{ M7c — string operations                                              }
{ ------------------------------------------------------------------ }

const
  SrcStrWriteLnLiteral = '''
    program P;
    begin
      WriteLn('hello')
    end.
    ''';

  SrcStrAssignAndWrite = '''
    program P;
    var S: string;
    begin
      S := 'world';
      WriteLn(S)
    end.
    ''';

  SrcStrConcat = '''
    program P;
    var A, B, C: string;
    begin
      A := 'foo';
      B := 'bar';
      C := A + B;
      WriteLn(C)
    end.
    ''';

  { Chr(N) returns a one-character heap String.  Assigning and concatenating it
    must lower to _Chr (string pointer), not treat N as the pointer itself (the
    latter crashed: a raw integer fed into _StringAddRef). }
  SrcChrConcat = '''
    program P;
    var
      S: string;
      I: Integer;
    begin
      S := 'A' + Chr(66) + 'C';
      WriteLn(S);
      S := '';
      I := 65;
      while I < 70 do
      begin
        S := S + Chr(I);
        I := I + 1
      end;
      WriteLn(S)
    end.
    ''';

  SrcStrLength = '''
    program P;
    var S: string;
    begin
      S := 'hello';
      WriteLn(Length(S))
    end.
    ''';

  SrcStrPos = '''
    program P;
    var S, Sub: string;
    begin
      S   := 'hello world';
      Sub := 'world';
      WriteLn(Pos(Sub, S))
    end.
    ''';

  SrcStrCopy = '''
    program P;
    var S, T: string;
    begin
      S := 'hello';
      T := Copy(S, 1, 3);
      WriteLn(T)
    end.
    ''';

  SrcStrUpperCase = '''
    program P;
    var S: string;
    begin
      S := 'hello';
      WriteLn(UpperCase(S))
    end.
    ''';

  SrcStrIntToStr = '''
    program P;
    var S: string;
    begin
      S := IntToStr(42);
      WriteLn(S)
    end.
    ''';

  SrcStrStrToInt = '''
    program P;
    var N: Integer;
    begin
      N := StrToInt('123');
      WriteLn(N)
    end.
    ''';

  SrcStrParam = '''
    program P;
    function Greet(Name: string): string;
    begin
      Result := 'Hello ' + Name
    end;
    begin
      WriteLn(Greet('World'))
    end.
    ''';

  SrcStrFuncReturn = '''
    program P;
    function Twice(S: string): string;
    begin
      Result := S + S
    end;
    begin
      WriteLn(Twice('ab'))
    end.
    ''';

  SrcStrDelete = '''
    program P;
    var S: string;
    begin
      S := 'Hello World';
      Delete(S, 5, 6);
      WriteLn(S)
    end.
    ''';

  SrcStrSetLength = '''
    program P;
    var S: string;
    begin
      S := 'Hello';
      SetLength(S, 3);
      WriteLn(S)
    end.
    ''';

  SrcStrSubscript = '''
    program P;
    var S: string;
    begin
      S := 'ABC';
      WriteLn(S[0]);
      WriteLn(S[1]);
      WriteLn(S[2])
    end.
    ''';

procedure TE2ENativeTests.TestRun_Native_String_WriteLnLiteral;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStrWriteLnLiteral, 'hello' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_AssignAndWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStrAssignAndWrite, 'world' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Concat;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStrConcat, 'foobar' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Length;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStrLength, '5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Pos;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Pos is 0-based in Blaise: 'world' starts at index 6 }
  AssertRunsOnBoth(SrcStrPos, '6' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Copy;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Copy('hello', 1, 3) = 'ell' }
  AssertRunsOnBoth(SrcStrCopy, 'ell' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_UpperCase;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStrUpperCase, 'HELLO' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_IntToStr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStrIntToStr, '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_StrToInt;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStrStrToInt, '123' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Param;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStrParam, 'Hello World' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_FuncReturn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStrFuncReturn, 'abab' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Delete;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStrDelete, 'Hello' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_SetLength;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStrSetLength, 'Hel' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Subscript;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { S[0]='A'=65, S[1]='B'=66, S[2]='C'=67 }
  AssertRunsOnBoth(SrcStrSubscript,
    '65' + LE + '66' + LE + '67' + LE, 0);
end;

const
  SrcStrSameText = '''
    program P;
    var S, T: string;
    begin
      S := 'Hello';
      T := 'hello';
      WriteLn(SameText(S, T))
    end.
    ''';

  SrcFormatIntArg = '''
    program P;
    var S: string;
    begin
      S := Format('val=%d', 42);
      WriteLn(S)
    end.
    ''';

  SrcFormatStrArg = '''
    program P;
    var S: string;
    begin
      S := Format('hello %s', 'world');
      WriteLn(S)
    end.
    ''';

  SrcFormatMixedArgs = '''
    program P;
    var S: string;
    begin
      S := Format('%s=%d', 'Alice', 30);
      WriteLn(S)
    end.
    ''';

  SrcConcatWithInt = '''
    program P;
    begin
      WriteLn('x=' + IntToStr(7))
    end.
    ''';

procedure TE2ENativeTests.TestRun_Native_String_SameText;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStrSameText, 'True' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Format_IntArg;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcFormatIntArg, 'val=42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Format_StrArg;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcFormatStrArg, 'hello world' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Format_MixedArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcFormatMixedArgs, 'Alice=30' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_ConcatWithInt;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcConcatWithInt, 'x=7' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_ChrConcat;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcChrConcat, 'ABC' + LE + 'ABCDE' + LE, 0);
end;

{ M7d — exception handling source programs }
const
  SrcExcBase =
    '''
        program P;
        type
          Exception = class
            FMessage: string;
            property Message: string read FMessage;
          end;
          EFoo = class(Exception) end;
          EBar = class(EFoo) end;
    ''';

  SrcTryFinallyNormal = '''
    program P;
    begin
      try
        WriteLn('in_try')
      finally
        WriteLn('in_finally')
      end
    end.
    ''';

  SrcTryFinallyNested = '''
    program P;
    begin
      try
        try
          WriteLn('inner_try')
        finally
          WriteLn('inner_fin')
        end
      finally
        WriteLn('outer_fin')
      end
    end.
    ''';

  SrcExitThroughFinally = '''
    program P;
    procedure Run;
    begin
      try
        WriteLn('in_try');
        Exit;
        WriteLn('unreached')
      finally
        WriteLn('in_finally')
      end
    end;
    begin
      Run();
      WriteLn('after')
    end.
    ''';

  SrcBreakThroughFinally = '''
    program P;
    var I: Integer;
    begin
      for I := 0 to 3 do
      begin
        try
          if I = 2 then Break;
          WriteLn('iter')
        finally
          WriteLn('fin')
        end
      end;
      WriteLn('done')
    end.
    ''';

  SrcTryExceptBare = '''
    program P;
    var X: Integer;
    begin
      X := 0;
      try
        X := 1
      except
        X := 99
      end;
      WriteLn(X)
    end.
    ''';

  SrcTypedExcept =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          X := 0;
          try
            raise EFoo.Create()
          except
            on E: EFoo do X := 42;
            on E: Exception do X := 1
          end;
          WriteLn(X)
        end.
    ''';

  SrcSubclassMatch =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          X := 0;
          try
            raise EBar.Create()
          except
            on E: EFoo do X := 7
          end;
          WriteLn(X)
        end.
    ''';

  SrcBareRaisePropagate =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          X := 0;
          try
            try
              raise EFoo.Create()
            except
              on E: EFoo do begin X := 1; raise end
            end
          except
            on E: EFoo do X := 2
          end;
          WriteLn(X)
        end.
    ''';

  SrcElseBody =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          X := 0;
          try
            raise EFoo.Create()
          except
            on E: EBar do X := 9
            else X := 5
          end;
          WriteLn(X)
        end.
    ''';

  SrcExitNestedFinally = '''
    program P;
    procedure Run;
    begin
      try
        try
          Exit
        finally
          WriteLn('inner_fin')
        end
      finally
        WriteLn('outer_fin')
      end
    end;
    begin
      Run();
      WriteLn('after')
    end.
    ''';

procedure TE2ENativeTests.TestRun_Native_TryFinally_Normal;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcTryFinallyNormal, 'in_try' + LE + 'in_finally' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TryFinally_NestedNormal;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcTryFinallyNested,
    'inner_try' + LE + 'inner_fin' + LE + 'outer_fin' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TryFinally_ExitUnwind;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcExitThroughFinally,
    'in_try' + LE + 'in_finally' + LE + 'after' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TryFinally_BreakUnwind;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcBreakThroughFinally,
    'iter' + LE + 'fin' + LE +
    'iter' + LE + 'fin' + LE +
    'fin' + LE + 'done' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TryExcept_Bare;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcTryExceptBare, '1' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TryExcept_TypedHandler;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcTypedExcept, '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TryExcept_SubclassMatch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcSubclassMatch, '7' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TryExcept_BareRaisePropagate;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcBareRaisePropagate, '2' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TryExcept_ElseBody;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcElseBody, '5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ExitThroughNestedFinally;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcExitNestedFinally,
    'inner_fin' + LE + 'outer_fin' + LE + 'after' + LE, 0);
end;

{ M7e — open arrays and dynamic arrays }

const
  SrcOASum =
    '''
    program P;
    function Sum(const A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do
        Result := Result + A[I]
    end;
    begin
      WriteLn(Sum([1, 2, 3, 4, 5]))
    end.
    ''';

  SrcOAHighLow =
    '''
    program P;
    procedure PrintBounds(const A: array of Integer);
    begin
      WriteLn(Low(A));
      WriteLn(High(A))
    end;
    begin
      PrintBounds([10, 20, 30])
    end.
    ''';

  SrcOALength =
    '''
    program P;
    function Count(const A: array of Integer): Integer;
    begin
      Result := Length(A)
    end;
    begin
      WriteLn(Count([10, 20, 30]))
    end.
    ''';

  SrcStaticToOpenLen =
    '''
    program P;
    procedure PrintLen(const A: array of Integer);
    begin
      WriteLn(Length(A))
    end;
    var B: array[0..4] of Integer;
    begin
      PrintLen(B)
    end.
    ''';

  SrcStaticToOpenSum =
    '''
    program P;
    function Sum(const A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do
        Result := Result + A[I]
    end;
    var B: array[0..2] of Integer;
    begin
      B[0] := 10;
      B[1] := 20;
      B[2] := 30;
      WriteLn(Sum(B))
    end.
    ''';

  SrcStaticToOpenNested =
    '''
    program P;
    function Sum(const A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do
        Result := Result + A[I]
    end;
    procedure Process(const A: array of Integer);
    begin
      WriteLn(Sum(A))
    end;
    var B: array[0..2] of Integer;
    begin
      B[0] := 5;
      B[1] := 10;
      B[2] := 15;
      Process(B)
    end.
    ''';

  SrcDynArrayBasic =
    '''
    program P;
    var A: array of Integer;
        I: Integer;
    begin
      SetLength(A, 3);
      A[0] := 10;
      A[1] := 20;
      A[2] := 30;
      for I := 0 to High(A) do
        WriteLn(A[I])
    end.
    ''';

  SrcDynArrayLenHigh =
    '''
    program P;
    var A: array of Integer;
    begin
      SetLength(A, 5);
      WriteLn(Length(A));
      WriteLn(High(A))
    end.
    ''';

  { M7f — interface dispatch.  Each program assigns a class instance to an
    interface variable (class->interface, via the static itab) and dispatches a
    method through the fat pointer; the native backend must match the QBE
    oracle. }
  SrcIntfZeroArg =
    '''
    program P;
    type
      IGreeter = interface
        function Greet: Integer;
      end;
      TGreeter = class(TObject, IGreeter)
        function Greet: Integer;
      end;
    function TGreeter.Greet: Integer;
    begin Result := 42 end;
    var
      G: IGreeter;
      T: TGreeter;
    begin
      T := TGreeter.Create();
      G := T;
      WriteLn(G.Greet())
    end.
    ''';

  SrcIntfArg =
    '''
    program P;
    type
      IShape = interface
        function Area(Scale: Integer): Integer;
      end;
      TBox = class(TObject, IShape)
        function Area(Scale: Integer): Integer;
      end;
    function TBox.Area(Scale: Integer): Integer;
    begin Result := 10 * Scale end;
    var
      S: IShape;
      B: TBox;
    begin
      B := TBox.Create();
      S := B;
      WriteLn(S.Area(3))
    end.
    ''';

  SrcIntfProc =
    '''
    program P;
    type
      IShape = interface
        procedure Describe;
      end;
      TBox = class(TObject, IShape)
        procedure Describe;
      end;
    procedure TBox.Describe;
    begin WriteLn('box') end;
    var
      S: IShape;
      B: TBox;
    begin
      B := TBox.Create();
      S := B;
      S.Describe()
    end.
    ''';

  SrcIntfCopy =
    '''
    program P;
    type
      IShape = interface
        function Area: Integer;
      end;
      TBox = class(TObject, IShape)
        function Area: Integer;
      end;
    function TBox.Area: Integer;
    begin Result := 21 end;
    var
      S, S2: IShape;
      B: TBox;
    begin
      B := TBox.Create();
      S := B;
      S2 := S;
      WriteLn(S2.Area)
    end.
    ''';

  SrcIntfAsCast =
    '''
    program P;
    type
      IShape = interface
        function Area: Integer;
      end;
      IColor = interface
        function Code: Integer;
      end;
      TBox = class(TObject, IShape, IColor)
        function Area: Integer;
        function Code: Integer;
      end;
    function TBox.Area: Integer;
    begin Result := 7 end;
    function TBox.Code: Integer;
    begin Result := 99 end;
    var
      S: IShape;
      C: IColor;
      B: TBox;
    begin
      B := TBox.Create();
      S := B;
      C := B as IColor;
      WriteLn(S.Area());
      WriteLn(C.Code())
    end.
    ''';

  SrcIntfNilClear =
    '''
    program P;
    type
      IGreeter = interface
        function Greet: Integer;
      end;
      TGreeter = class(TObject, IGreeter)
        function Greet: Integer;
      end;
    function TGreeter.Greet: Integer;
    begin Result := 5 end;
    var
      G: IGreeter;
      T: TGreeter;
    begin
      T := TGreeter.Create();
      G := T;
      WriteLn(G.Greet());
      G := nil;
      WriteLn(13)
    end.
    ''';

  { Regression (issue #64): interface-typed field 'im' in a class with a
    same-named global of a different type. }
  SrcNativeIntfFieldShadowsGlobal = '''
    program P;
    type
      Iprinter = interface
        procedure print;
      end;
      Toutput = class(TObject, Iprinter)
        procedure print;
      end;
      Tmi = class
        im: Iprinter;
        constructor create(am: Iprinter);
        procedure use;
      end;
    procedure Toutput.print;
    begin
      WriteLn('printed');
    end;
    constructor Tmi.Create(am: Iprinter);
    begin
      im := am;
    end;
    procedure Tmi.use;
    begin
      im.print;
    end;
    var
      im: Tmi;
    begin
      im := Tmi.Create(Toutput.Create());
      im.use;
    end.
    ''';

  { Interface params: passing interface fat pointers to procedures, methods,
    constructors, and inherited calls.  Each program passes an interface value
    as an argument and verifies correct dispatch through the received fat pointer. }

  { 1. Interface arg to a standalone procedure. }
  SrcNativeIntfParamProc = '''
    program P;
    type
      IPrinter = interface
        procedure Print;
      end;
      TDoc = class(TObject, IPrinter)
        procedure Print;
      end;
    procedure TDoc.Print;
    begin WriteLn('doc') end;
    procedure UsePrinter(P: IPrinter);
    begin P.Print() end;
    var
      D: TDoc;
      I: IPrinter;
    begin
      D := TDoc.Create();
      I := D;
      UsePrinter(I)
    end.
    ''';

  { 2. Interface arg to a class method. }
  SrcNativeIntfParamMethod = '''
    program P;
    type
      IPrinter = interface
        procedure Print;
      end;
      TDoc = class(TObject, IPrinter)
        procedure Print;
      end;
      TRunner = class
        procedure Run(P: IPrinter);
      end;
    procedure TDoc.Print;
    begin WriteLn('method') end;
    procedure TRunner.Run(P: IPrinter);
    begin P.Print() end;
    var
      D: TDoc;
      I: IPrinter;
      R: TRunner;
    begin
      D := TDoc.Create();
      I := D;
      R := TRunner.Create();
      R.Run(I)
    end.
    ''';

  { 3. Interface arg to a constructor. }
  SrcNativeIntfParamCtor = '''
    program P;
    type
      IPrinter = interface
        procedure Print;
      end;
      TDoc = class(TObject, IPrinter)
        procedure Print;
      end;
      THolder = class
        FP: IPrinter;
        constructor Create(P: IPrinter);
        procedure Use;
      end;
    procedure TDoc.Print;
    begin WriteLn('ctor') end;
    constructor THolder.Create(P: IPrinter);
    begin FP := P end;
    procedure THolder.Use;
    begin FP.Print() end;
    var
      D: TDoc;
      I: IPrinter;
      H: THolder;
    begin
      D := TDoc.Create();
      I := D;
      H := THolder.Create(I);
      H.Use()
    end.
    ''';

  { 4. Interface arg to an inherited call. }
  SrcNativeIntfParamInherited = '''
    program P;
    type
      IPrinter = interface
        procedure Print;
      end;
      TDoc = class(TObject, IPrinter)
        procedure Print;
      end;
      TBase = class
        procedure Use(P: IPrinter); virtual;
      end;
      TChild = class(TBase)
        procedure Use(P: IPrinter); override;
      end;
    procedure TDoc.Print;
    begin WriteLn('inherited') end;
    procedure TBase.Use(P: IPrinter);
    begin P.Print() end;
    procedure TChild.Use(P: IPrinter);
    begin inherited Use(P) end;
    var
      D: TDoc;
      I: IPrinter;
      C: TChild;
    begin
      D := TDoc.Create();
      I := D;
      C := TChild.Create();
      C.Use(I)
    end.
    ''';

  { 5. Passing a class expression directly as an interface parameter. }
  SrcNativeIntfParamClassExpr = '''
    program P;
    type
      IPrinter = interface
        procedure Print;
      end;
      TDoc = class(TObject, IPrinter)
        procedure Print;
      end;
    procedure TDoc.Print;
    begin WriteLn('class-expr') end;
    procedure UsePrinter(P: IPrinter);
    begin P.Print() end;
    begin
      UsePrinter(TDoc.Create())
    end.
    ''';

  { M8 — inherited calls.  An override that chains to the parent body via
    `inherited` must dispatch statically to the parent method. }
  SrcInheritedProc = '''
    program P;
    type
      TBase = class
        procedure Hello; virtual;
      end;
      TDer = class(TBase)
        procedure Hello; override;
      end;
    procedure TBase.Hello;
    begin WriteLn('base') end;
    procedure TDer.Hello;
    begin
      inherited Hello();
      WriteLn('derived')
    end;
    var D: TDer;
    begin
      D := TDer.Create();
      D.Hello()
    end.
    ''';

  { A value-returning `inherited Calc(N)` statement seeds Result with the
    parent's return value (which the override then adjusts). }
  SrcInheritedFunc = '''
    program P;
    type
      TBase = class
        function Calc(N: Integer): Integer; virtual;
      end;
      TDer = class(TBase)
        function Calc(N: Integer): Integer; override;
      end;
    function TBase.Calc(N: Integer): Integer;
    begin Result := N * 2 end;
    function TDer.Calc(N: Integer): Integer;
    begin
      inherited Calc(N);
      Result := Result + 1
    end;
    var D: TDer;
    begin
      D := TDer.Create();
      WriteLn(D.Calc(10))
    end.
    ''';

  { M8 — a var/out parameter to a method call must pass the caller's address so
    the mutation is visible after the call. }
  SrcMethodVarParam = '''
    program P;
    type
      TFoo = class
        procedure Bump(var X: Integer);
      end;
    procedure TFoo.Bump(var X: Integer);
    begin X := X + 1 end;
    var
      F: TFoo;
      N: Integer;
    begin
      F := TFoo.Create();
      N := 5;
      F.Bump(N);
      WriteLn(N)
    end.
    ''';

  SrcMethodVarSwap = '''
    program P;
    type
      TSwapper = class
        procedure Swap(var A, B: Integer);
      end;
    procedure TSwapper.Swap(var A, B: Integer);
    var T: Integer;
    begin T := A; A := B; B := T end;
    var
      S: TSwapper;
      X, Y: Integer;
    begin
      S := TSwapper.Create();
      X := 3; Y := 7;
      S.Swap(X, Y);
      WriteLn(X);
      WriteLn(Y)
    end.
    ''';

  SrcRecordStaticArrayField = '''
    program P;
    type
      TRec = record
        X: Integer;
        Arr: array[0..1] of Integer;
      end;
    function MakeRec: TRec;
    begin
      Result.X := 99
    end;
    function ReadAt(var R: TRec; I: Integer): Integer;
    begin
      Result := R.Arr[I]
    end;
    var R: TRec;
    begin
      R := MakeRec();
      WriteLn(R.X);
      WriteLn(ReadAt(R, 0));
      WriteLn(ReadAt(R, 1))
    end.
    ''';

  SrcArcClassField = '''
    program P;
    type
      TChild = class
        X: Integer;
      end;
      TParent = class
        Child: TChild;
      end;
    var
      Pa: TParent;
      C: TChild;
    begin
      Pa := TParent.Create();
      C := TChild.Create();
      C.X := 42;
      Pa.Child := C;
      C := Pa.Child;
      WriteLn(C.X)
    end.
    ''';

  SrcArcStringField = '''
    program P;
    type
      THolder = class
        S: string;
      end;
    var H: THolder;
    begin
      H := THolder.Create();
      H.S := 'hello';
      WriteLn(H.S)
    end.
    ''';

  SrcArcClassAssignNil = '''
    program P;
    type
      TThing = class
        destructor Destroy; override;
      end;
    destructor TThing.Destroy;
    begin
      WriteLn('destroyed');
      inherited Destroy
    end;
    var O: TThing;
    begin
      O := TThing.Create();
      O := nil;
      WriteLn('done')
    end.
    ''';

  SrcArcValueParamString = '''
    program P;
    procedure PrintIt(S: string);
    begin
      WriteLn(S)
    end;
    var Msg: string;
    begin
      Msg := 'arc-ok';
      PrintIt(Msg);
      WriteLn(Msg)
    end.
    ''';

  SrcArcValueParamClass = '''
    program P;
    type
      TObj = class
        X: Integer;
      end;
    procedure PrintX(O: TObj);
    begin
      WriteLn(O.X)
    end;
    var Obj: TObj;
    begin
      Obj := TObj.Create();
      Obj.X := 7;
      PrintX(Obj);
      WriteLn(Obj.X)
    end.
    ''';

  { Value-returning function whose return value must survive the epilogue ARC
    release pass.  A function returning Integer but taking an ARC (class) value
    param releases that param on exit (_ClassRelease clobbers %rax); the Result
    must be loaded into %rax AFTER that release, not before.  Previously the
    native backend loaded Result first and returned garbage (e.g. 3 not 55). }
  SrcRetValSurvivesArcRelease = '''
    program P;
    type
      TGreeter = class
        function Greet: Integer;
      end;
      TUser = class
        function Use(O: TGreeter): Integer;
      end;
    function TGreeter.Greet: Integer; begin Result := 55 end;
    function TUser.Use(O: TGreeter): Integer;
    begin
      Result := O.Greet()
    end;
    var T: TGreeter; U: TUser;
    begin
      T := TGreeter.Create();
      U := TUser.Create();
      WriteLn(U.Use(T))
    end.
    ''';

  { Interface value argument passed to a method, dispatched inside the callee.
    Exercises the fat-pointer arg ABI at a method call site AND the
    return-value-survives-release fix (the callee releases the interface param). }
  SrcIntfArgToMethod = '''
    program P;
    type
      IGreeter = interface
        function Greet: Integer;
      end;
      TGreeter = class(TObject, IGreeter)
        function Greet: Integer;
      end;
      TUser = class
        function Use(G: IGreeter): Integer;
      end;
    function TGreeter.Greet: Integer; begin Result := 55 end;
    function TUser.Use(G: IGreeter): Integer;
    begin
      Result := G.Greet()
    end;
    var T: TGreeter; I: IGreeter; U: TUser;
    begin
      T := TGreeter.Create();
      I := T;
      U := TUser.Create();
      WriteLn(U.Use(I))
    end.
    ''';

  { Dyn-array field inside a class: the field must be ARC-refcounted on store
    and released when the holder is destroyed (f74e5cc).  Observed by reading an
    element back after the field assignment — a dropped/garbled buffer would
    diverge from the QBE backend's output. }
  SrcArcDynArrayField = '''
    program P;
    type
      THolder = class
        Data: array of Integer;
      end;
    var
      H: THolder;
      A: array of Integer;
    begin
      H := THolder.Create();
      SetLength(A, 3);
      A[0] := 11;
      A[1] := 22;
      A[2] := 33;
      H.Data := A;
      WriteLn(H.Data[1])
    end.
    ''';

  { Interface field inside a class: assign a class instance into the field
    (935bd52).  The fat pointer (obj+itab) must be stored whole with ARC on the
    obj slot, and released when the holder is destroyed.  Observed via the
    implementing class's destructor, which must fire exactly once when the holder
    is released — proving the field stored a refcounted obj and that field
    cleanup releases it.  (Dispatch directly through a non-Self interface field
    is a separate, pre-existing native gap not covered here.) }
  { Dispatch a method directly through an interface stored in a (non-Self)
    class field — H.G.Greet() — including a method that takes an argument.  The
    receiver's fat pointer must be loaded from the field's contiguous memory. }
  SrcIntfFieldDispatch = '''
    program P;
    type
      IShape = interface
        function Area(Scale: Integer): Integer;
      end;
      TBox = class(TObject, IShape)
        function Area(Scale: Integer): Integer;
      end;
      THolder = class
        S: IShape;
      end;
    function TBox.Area(Scale: Integer): Integer;
    begin Result := 10 * Scale end;
    var H: THolder;
    begin
      H := THolder.Create();
      H.S := TBox.Create();
      WriteLn(H.S.Area(3));
      WriteLn(H.S.Area(5))
    end.
    ''';

  { Read an interface OUT of a field into an interface local (G := H.G), then
    dispatch on the local.  Exercises the interface-to-interface assignment with
    a field-access source. }
  SrcIntfFieldReadIntoLocal = '''
    program P;
    type
      IShape = interface
        function Area(Scale: Integer): Integer;
      end;
      TBox = class(TObject, IShape)
        function Area(Scale: Integer): Integer;
      end;
      THolder = class
        S: IShape;
      end;
    function TBox.Area(Scale: Integer): Integer;
    begin Result := 10 * Scale end;
    var H: THolder; G: IShape;
    begin
      H := THolder.Create();
      H.S := TBox.Create();
      G := H.S;
      WriteLn(G.Area(4))
    end.
    ''';

  SrcArcInterfaceField = '''
    program P;
    type
      IGreeter = interface
        function Greet: Integer;
      end;
      TGreeter = class(TObject, IGreeter)
        function Greet: Integer;
        destructor Destroy; override;
      end;
      THolder = class
        G: IGreeter;
      end;
    function TGreeter.Greet: Integer;
    begin
      Result := 77
    end;
    destructor TGreeter.Destroy;
    begin
      WriteLn('greeter-gone');
      inherited Destroy
    end;
    var
      H: THolder;
      G: IGreeter;
    begin
      H := THolder.Create();
      G := TGreeter.Create();
      H.G := G;
      G := nil;
      WriteLn('mid');
      H := nil;
      WriteLn('end')
    end.
    ''';

  { Nested record field whose own field is a managed class reference.  When the
    parent class is destroyed, _FieldCleanup must recurse through the record
    field and release the inner class — firing its destructor exactly once
    (f74e5cc nested-record recursion). }
  SrcArcNestedRecordField = '''
    program P;
    type
      TInner = class
        destructor Destroy; override;
      end;
      TRec = record
        Obj: TInner;
      end;
      THolder = class
        R: TRec;
      end;
    destructor TInner.Destroy;
    begin
      WriteLn('inner-gone');
      inherited Destroy
    end;
    var H: THolder;
    begin
      H := THolder.Create();
      H.R.Obj := TInner.Create();
      WriteLn('before');
      H := nil;
      WriteLn('after')
    end.
    ''';

  { A function returning a String, its +1 result assigned straight into a class
    field.  The field store must consume the transferred reference (no extra
    AddRef), so the buffer is freed exactly once — observed indirectly by the
    program completing and printing the value identically on both backends
    (96514ee).  A double-retain would leak; a missing retain would free early
    and corrupt the read-back. }
  SrcArcStringReturnToField = '''
    program P;
    type
      THolder = class
        S: string;
      end;
    function MakeMsg: string;
    begin
      Result := 'built'
    end;
    var H: THolder;
    begin
      H := THolder.Create();
      H.S := MakeMsg();
      WriteLn(H.S);
      WriteLn(H.S)
    end.
    ''';

  { Implicit-Self string field assigned inside a method: FName := value must
    retain the new value and release the old, so reassigning the field does not
    leak or use-after-free (ARC on the ImplicitSelfField path). }
  SrcArcImplicitSelfStringField = '''
    program P;
    type
      THolder = class
        Name: string;
        procedure SetName(const V: string);
      end;
    procedure THolder.SetName(const V: string);
    begin
      Name := V
    end;
    var H: THolder;
    begin
      H := THolder.Create();
      H.SetName('first');
      H.SetName('second');
      WriteLn(H.Name)
    end.
    ''';

  SrcAddrOfLocalVar = '''
    program P;
    var
      X: Integer;
      P: ^Integer;
    begin
      X := 42;
      P := @X;
      P^ := 99;
      WriteLn(X)
    end.
    ''';

  SrcAddrOfStaticArrayElem = '''
    program P;
    var
      A: array[0..3] of Integer;
      P: ^Integer;
    begin
      A[0] := 10;
      A[1] := 20;
      A[2] := 30;
      A[3] := 40;
      P := @A[2];
      WriteLn(P^)
    end.
    ''';

  SrcAddrOfDynArrayElem = '''
    program P;
    var
      A: array of Integer;
      P: ^Integer;
    begin
      SetLength(A, 3);
      A[0] := 100;
      A[1] := 200;
      A[2] := 300;
      P := @A[1];
      WriteLn(P^)
    end.
    ''';

  SrcAddrOfRecFieldArrElem = '''
    program P;
    type
      TRec = record
        Items: array of Integer;
      end;
    var
      A: array of Integer;
      R: TRec;
      P: ^Integer;
    begin
      SetLength(A, 3);
      A[0] := 5;
      A[1] := 15;
      A[2] := 25;
      R.Items := A;
      P := @R.Items[2];
      WriteLn(P^)
    end.
    ''';

  SrcAddrOfMethodPtr = '''
    program P;
    type
      TAddProc = procedure(A, B: Integer) of object;
      TCalc = class
        procedure Add(A, B: Integer);
        begin
          WriteLn(A + B)
        end;
      end;
    var
      C: TCalc;
      F: TAddProc;
    begin
      C := TCalc.Create();
      F := @C.Add;
      F(3, 4)
    end.
    ''';

  SrcBitwiseNotInt = '''
    program P;
    var I: Integer;
    begin
      I := 0;
      WriteLn(not I)
    end.
    ''';

  SrcBitwiseNotBitmask = '''
    program P;
    const MASK = 3;
    var Flags: Integer;
    begin
      Flags := 7;
      Flags := Flags and (not MASK);
      WriteLn(Flags)
    end.
    ''';

  SrcGenericRecordMethod = '''
    program P;
    type
      THolder<T> = record
        Value: T;
        function GetValue: T;
        begin
          Result := Self.Value
        end;
      end;
    var
      H: THolder<Integer>;
    begin
      H.Value := 42;
      WriteLn(H.GetValue())
    end.
    ''';

  SrcGenericClassMethod = '''
    program P;
    type
      TBox<T> = class
        FVal: T;
        procedure SetVal(AVal: T);
        begin
          Self.FVal := AVal
        end;
        function GetVal: T;
        begin
          Result := Self.FVal
        end;
      end;
    var
      B: TBox<Integer>;
    begin
      B := TBox<Integer>.Create();
      B.SetVal(99);
      WriteLn(B.GetVal())
    end.
    ''';

  SrcGenericFuncStandalone = '''
    program P;
    function Identity<T>(X: T): T;
    begin
      Result := X
    end;
    begin
      WriteLn(Identity<Integer>(7))
    end.
    ''';

  SrcGenericClassInterface = '''
    program P;
    type
      IValue = interface
        function GetValue: Integer;
      end;
      TBox<T> = class(TObject, IValue)
        FVal: T;
        procedure SetVal(AVal: T);
        begin
          Self.FVal := AVal
        end;
        function GetValue: Integer;
        begin
          Result := Self.FVal
        end;
      end;
    var
      V: IValue;
      B: TBox<Integer>;
    begin
      B := TBox<Integer>.Create();
      B.SetVal(55);
      V := B;
      WriteLn(V.GetValue())
    end.
    ''';

procedure TE2ENativeTests.TestRun_Native_OpenArray_Sum;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcOASum, '15' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_OpenArray_HighLow;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcOAHighLow, '0' + LE + '2' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_OpenArray_Length;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcOALength, '3' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_StaticToOpen_Length;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStaticToOpenLen, '5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_StaticToOpen_Sum;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStaticToOpenSum, '60' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_StaticToOpen_PassToNested;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcStaticToOpenNested, '30' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_DynArray_SetLengthAndAccess;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcDynArrayBasic, '10' + LE + '20' + LE + '30' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_DynArray_LengthAndHigh;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcDynArrayLenHigh, '5' + LE + '4' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Interface_ZeroArgDispatch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcIntfZeroArg, '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Interface_ArgDispatch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcIntfArg, '30' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Interface_ProcDispatch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcIntfProc, 'box' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Interface_IntfToIntfCopy;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcIntfCopy, '21' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Interface_AsCast;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcIntfAsCast, '7' + LE + '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Interface_NilClear;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcIntfNilClear, '5' + LE + '13' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Inherited_Proc;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcInheritedProc, 'base' + LE + 'derived' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Inherited_FuncSetsResult;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcInheritedFunc, '21' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_MethodVarParam_Mutates;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcMethodVarParam, '6' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_MethodVarParam_Swap;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcMethodVarSwap, '7' + LE + '3' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_InterfaceField_ShadowsGlobal;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcNativeIntfFieldShadowsGlobal, 'printed' + LE, 0);
end;


procedure TE2ENativeTests.TestRun_Native_IntfParam_Proc;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcNativeIntfParamProc, 'doc' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfParam_Method;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcNativeIntfParamMethod, 'method' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfParam_Constructor;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcNativeIntfParamCtor, 'ctor' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfParam_Inherited;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcNativeIntfParamInherited, 'inherited' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfParam_ClassExpr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcNativeIntfParamClassExpr, 'class-expr' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecordArrayField_StaticRead;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcRecordStaticArrayField, '99' + LE + '0' + LE + '0' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcClassField_StoreAndRead;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcArcClassField, '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcStringField_StoreAndRead;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcArcStringField, 'hello' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcClassAssignNil_Destroys;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcArcClassAssignNil, 'destroyed' + LE + 'done' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcDynArrayField_StoreAndRead;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcArcDynArrayField, '22' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcInterfaceField_AssignAndDispatch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcArcInterfaceField,
    'mid' + LE + 'greeter-gone' + LE + 'end' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfFieldDispatch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcIntfFieldDispatch, '30' + LE + '50' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfFieldReadIntoLocal;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcIntfFieldReadIntoLocal, '40' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RetValSurvivesArcRelease;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcRetValSurvivesArcRelease, '55' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfArgToMethod;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcIntfArgToMethod, '55' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcNestedRecordField_FullCleanup;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcArcNestedRecordField,
    'before' + LE + 'inner-gone' + LE + 'after' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcStringReturnToField_NoDoubleRetain;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcArcStringReturnToField, 'built' + LE + 'built' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcImplicitSelfStringField_Reassign;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcArcImplicitSelfStringField, 'second' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcValueParam_String;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcArcValueParamString, 'arc-ok' + LE + 'arc-ok' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcValueParam_Class;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcArcValueParamClass, '7' + LE + '7' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_AddrOf_LocalVariable;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcAddrOfLocalVar, '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_AddrOf_StaticArrayElement;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcAddrOfStaticArrayElem, '30' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_AddrOf_DynArrayElement;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcAddrOfDynArrayElem, '200' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_AddrOf_RecordFieldArrayElem;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcAddrOfRecFieldArrElem, '25' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_AddrOf_MethodPointer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcAddrOfMethodPtr, '7' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_BitwiseNot_Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcBitwiseNotInt, '-1' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_BitwiseNot_Bitmask;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcBitwiseNotBitmask, '4' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_GenericRecord_Method;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcGenericRecordMethod, '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_GenericClass_Method;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcGenericClassMethod, '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_GenericFunc_Standalone;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcGenericFuncStandalone, '7' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_GenericClass_Interface;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcGenericClassInterface, '55' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SizeOf_Record;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcSizeOfRecord, '8' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SizeOf_GenericRecord;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcSizeOfGenericRecord, '8' + LE + '16' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Record_NestedFieldAssign;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcNestedRecordFieldAssign, '2037' + LE + '2037' + LE, 0);
end;

{ ------------------------------------------------------------------ }
{ Multi-unit whole-program native path.  Each test compiles a user unit
  plus a program that uses it on BOTH backends and asserts the native
  stdout/exit-code equal the QBE oracle's (differential testing). }
{ ------------------------------------------------------------------ }

procedure TE2ENativeTests.TestRun_Native_MultiUnit_PlainFunction;
var
  UnitSrc, ProgSrc, NOut, QOut: string;
  NCode, QCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  UnitSrc :=
    'unit mu_pf;' + LE +
    'interface' + LE +
    'function Doubled(X: Integer): Integer;' + LE +
    'implementation' + LE +
    'function Doubled(X: Integer): Integer;' + LE +
    'begin Result := X * 2; end;' + LE +
    'end.' + LE;
  ProgSrc :=
    'program P;' + LE +
    'uses mu_pf;' + LE +
    'begin WriteLn(Doubled(21)); end.' + LE;
  AssertTrue('native compile+run',
    CompileAndRunWithUnitNative('mu_pf', UnitSrc, ProgSrc, NOut, NCode));
  AssertTrue('qbe compile+run',
    CompileAndRunWithUnit('mu_pf', UnitSrc, ProgSrc, QOut, QCode));
  AssertEquals('stdout parity', QOut, NOut);
  AssertEquals('exit parity', QCode, NCode);
  AssertEquals('value', '42' + LE, NOut);
end;

procedure TE2ENativeTests.TestRun_Native_MultiUnit_StringFunction;
var
  UnitSrc, ProgSrc, NOut, QOut: string;
  NCode, QCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  UnitSrc :=
    'unit mu_sf;' + LE +
    'interface' + LE +
    'function Greeting(const AName: string): string;' + LE +
    'implementation' + LE +
    'function Greeting(const AName: string): string;' + LE +
    'begin Result := ''Hello, '' + AName + ''!''; end;' + LE +
    'end.' + LE;
  ProgSrc :=
    'program P;' + LE +
    'uses mu_sf;' + LE +
    'begin WriteLn(Greeting(''World'')); end.' + LE;
  AssertTrue('native compile+run',
    CompileAndRunWithUnitNative('mu_sf', UnitSrc, ProgSrc, NOut, NCode));
  AssertTrue('qbe compile+run',
    CompileAndRunWithUnit('mu_sf', UnitSrc, ProgSrc, QOut, QCode));
  AssertEquals('stdout parity', QOut, NOut);
  AssertEquals('exit parity', QCode, NCode);
  AssertEquals('value', 'Hello, World!' + LE, NOut);
end;

procedure TE2ENativeTests.TestRun_Native_MultiUnit_Class;
var
  UnitSrc, ProgSrc, NOut, QOut: string;
  NCode, QCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  UnitSrc :=
    'unit mu_cl;' + LE +
    'interface' + LE +
    'type' + LE +
    '  TCounter = class' + LE +
    '  private FValue: Integer;' + LE +
    '  public' + LE +
    '    constructor Create(AStart: Integer);' + LE +
    '    procedure Bump;' + LE +
    '    function Value: Integer;' + LE +
    '    function Describe: string; virtual;' + LE +
    '  end;' + LE +
    'implementation' + LE +
    'constructor TCounter.Create(AStart: Integer); begin FValue := AStart; end;' + LE +
    'procedure TCounter.Bump; begin FValue := FValue + 1; end;' + LE +
    'function TCounter.Value: Integer; begin Result := FValue; end;' + LE +
    'function TCounter.Describe: string; begin Result := ''Counter''; end;' + LE +
    'end.' + LE;
  ProgSrc :=
    'program P;' + LE +
    'uses mu_cl;' + LE +
    'var C: TCounter;' + LE +
    'begin' + LE +
    '  C := TCounter.Create(10);' + LE +
    '  C.Bump(); C.Bump();' + LE +
    '  WriteLn(C.Describe(), '' = '', C.Value());' + LE +
    '  C.Free();' + LE +
    'end.' + LE;
  AssertTrue('native compile+run',
    CompileAndRunWithUnitNative('mu_cl', UnitSrc, ProgSrc, NOut, NCode));
  AssertTrue('qbe compile+run',
    CompileAndRunWithUnit('mu_cl', UnitSrc, ProgSrc, QOut, QCode));
  AssertEquals('stdout parity', QOut, NOut);
  AssertEquals('exit parity', QCode, NCode);
  AssertEquals('value', 'Counter = 12' + LE, NOut);
end;

procedure TE2ENativeTests.TestRun_Native_MultiUnit_Interface;
var
  UnitSrc, ProgSrc, NOut, QOut: string;
  NCode, QCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  UnitSrc :=
    'unit mu_if;' + LE +
    'interface' + LE +
    'type' + LE +
    '  ISpeaker = interface' + LE +
    '    function Speak: string;' + LE +
    '  end;' + LE +
    '  TDog = class(TObject, ISpeaker) public function Speak: string; end;' + LE +
    '  TCat = class(TObject, ISpeaker) public function Speak: string; end;' + LE +
    'implementation' + LE +
    'function TDog.Speak: string; begin Result := ''Woof''; end;' + LE +
    'function TCat.Speak: string; begin Result := ''Meow''; end;' + LE +
    'end.' + LE;
  ProgSrc :=
    'program P;' + LE +
    'uses mu_if;' + LE +
    'var S: ISpeaker;' + LE +
    'begin' + LE +
    '  S := TDog.Create(); WriteLn(S.Speak());' + LE +
    '  S := TCat.Create(); WriteLn(S.Speak());' + LE +
    'end.' + LE;
  AssertTrue('native compile+run',
    CompileAndRunWithUnitNative('mu_if', UnitSrc, ProgSrc, NOut, NCode));
  AssertTrue('qbe compile+run',
    CompileAndRunWithUnit('mu_if', UnitSrc, ProgSrc, QOut, QCode));
  AssertEquals('stdout parity', QOut, NOut);
  AssertEquals('exit parity', QCode, NCode);
  AssertEquals('value', 'Woof' + LE + 'Meow' + LE, NOut);
end;

procedure TE2ENativeTests.TestRun_Native_MultiUnit_GlobalsAndInit;
var
  UnitSrc, ProgSrc, NOut, QOut: string;
  NCode, QCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  UnitSrc :=
    'unit mu_gi;' + LE +
    'interface' + LE +
    'var GCounter: Integer; GLabel: string;' + LE +
    'procedure Increment;' + LE +
    'implementation' + LE +
    'procedure Increment; begin GCounter := GCounter + 1; end;' + LE +
    'initialization' + LE +
    '  GCounter := 100;' + LE +
    '  GLabel := ''configured'';' + LE +
    'end.' + LE;
  ProgSrc :=
    'program P;' + LE +
    'uses mu_gi;' + LE +
    'begin' + LE +
    '  WriteLn(GLabel, '' '', GCounter);' + LE +
    '  Increment(); Increment();' + LE +
    '  WriteLn(GCounter);' + LE +
    'end.' + LE;
  AssertTrue('native compile+run',
    CompileAndRunWithUnitNative('mu_gi', UnitSrc, ProgSrc, NOut, NCode));
  AssertTrue('qbe compile+run',
    CompileAndRunWithUnit('mu_gi', UnitSrc, ProgSrc, QOut, QCode));
  AssertEquals('stdout parity', QOut, NOut);
  AssertEquals('exit parity', QCode, NCode);
  AssertEquals('value', 'configured 100' + LE + '102' + LE, NOut);
end;

{ --- By-value record param tests ------------------------------------------ }

procedure TE2ENativeTests.TestRun_Native_RecordParam_ReadOnly;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type TRec = record S: string; end;'
    + 'procedure Show(R: TRec);'
    + 'begin WriteLn(''in: '', R.S) end;'
    + 'var W: TRec;'
    + 'begin'
    + '  W.S := ''heap-'' + ''allocated'';'
    + '  Show(W);'
    + '  WriteLn(''out: '', W.S)'
    + 'end.',
    'in: heap-allocated' + LE + 'out: heap-allocated' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecordParam_Mutate;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type TR = record S: string; end;'
    + 'procedure Mutate(R: TR); begin R.S := ''new'' end;'
    + 'var W: TR;'
    + 'begin'
    + '  W.S := ''heap-'' + ''allocated'';'
    + '  Mutate(W);'
    + '  WriteLn(W.S)'
    + 'end.',
    'heap-allocated' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecordParam_ThreeStrings;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type TR = record A: string; B: string; C: string; end;'
    + 'procedure Mutate(R: TR); begin R.A := ''changed'' end;'
    + 'var W: TR;'
    + 'begin'
    + '  W.A := ''heap-'' + ''one'';'
    + '  W.B := ''heap-'' + ''two'';'
    + '  W.C := ''heap-'' + ''three'';'
    + '  Mutate(W);'
    + '  WriteLn(W.A)'
    + 'end.',
    'heap-one' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecordParam_IntOnly;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type TR = record A: Integer; B: Integer; end;'
    + 'procedure Show(R: TR); begin WriteLn(R.A + R.B) end;'
    + 'var W: TR;'
    + 'begin W.A := 40; W.B := 2; Show(W) end.',
    '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecordParam_InlineSretArg;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type TInner = record N: string; end;'
    + '     TOuter = record S: string; Inner: TInner; end;'
    + 'function MakeOuter: TOuter;'
    + 'begin Result.S := ''outer-'' + ''heap''; Result.Inner.N := ''inner-'' + ''heap'' end;'
    + 'procedure Consume(R: TOuter);'
    + 'begin WriteLn(R.S, ''|'', R.Inner.N) end;'
    + 'begin'
    + '  Consume(MakeOuter())'
    + 'end.',
    'outer-heap|inner-heap' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecordParam_ConstSkipsArc;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type TR = record S: string; end;'
    + 'procedure Show(const R: TR);'
    + 'begin WriteLn(R.S) end;'
    + 'var W: TR;'
    + 'begin'
    + '  W.S := ''heap-'' + ''text'';'
    + '  Show(W);'
    + '  WriteLn(W.S)'
    + 'end.',
    'heap-text' + LE + 'heap-text' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ShortCircuit_AndSkipsRhs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'var X: Integer;'
    + 'begin'
    + '  X := 5;'
    + '  if (X > 3) and (X < 10) then'
    + '    WriteLn(''both'')'
    + '  else'
    + '    WriteLn(''nope'');'
    + '  if (X > 100) and (X < 200) then'
    + '    WriteLn(''bad'')'
    + '  else'
    + '    WriteLn(''skipped'')'
    + 'end.',
    'both' + LE + 'skipped' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ShortCircuit_OrSkipsRhs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'var X: Integer;'
    + 'begin'
    + '  X := 5;'
    + '  if (X = 5) or (X = 99) then'
    + '    WriteLn(''first-true'')'
    + '  else'
    + '    WriteLn(''nope'');'
    + '  if (X = 99) or (X = 5) then'
    + '    WriteLn(''second-true'')'
    + '  else'
    + '    WriteLn(''nope'')'
    + 'end.',
    'first-true' + LE + 'second-true' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ShortCircuit_AndNilGuard;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type TFoo = class'
    + '  public'
    + '    N: Integer;'
    + '    constructor Create(AVal: Integer);'
    + '  end;'
    + 'constructor TFoo.Create(AVal: Integer);'
    + 'begin N := AVal end;'
    + 'var Obj: TFoo;'
    + 'begin'
    + '  Obj := nil;'
    + '  if (Obj <> nil) and (Obj.N = 42) then'
    + '    WriteLn(''bad'')'
    + '  else'
    + '    WriteLn(''nil-guarded'');'
    + '  Obj := TFoo.Create(42);'
    + '  if (Obj <> nil) and (Obj.N = 42) then'
    + '    WriteLn(''found'')'
    + '  else'
    + '    WriteLn(''bad'')'
    + 'end.',
    'nil-guarded' + LE + 'found' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ProceduralParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type TIntFunc = function(X: Integer): Integer;'
    + 'function Twice(X: Integer): Integer;'
    + 'begin Result := X * 2 end;'
    + 'function Apply(F: TIntFunc; V: Integer): Integer;'
    + 'begin Result := F(V) end;'
    + 'begin'
    + '  WriteLn(Apply(@Twice, 21))'
    + 'end.',
    '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IsExpr_Class;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type'
    + '  TBase = class public N: Integer; end;'
    + '  TChild = class(TBase) public S: string; end;'
    + 'var Obj: TBase;'
    + 'begin'
    + '  Obj := TChild.Create();'
    + '  if Obj is TChild then WriteLn(''child-yes'') else WriteLn(''child-no'');'
    + '  if Obj is TBase then WriteLn(''base-yes'') else WriteLn(''base-no'');'
    + '  Obj := TBase.Create();'
    + '  if Obj is TChild then WriteLn(''child-yes'') else WriteLn(''child-no'')'
    + 'end.',
    'child-yes' + LE + 'base-yes' + LE + 'child-no' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_AsExpr_Class;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type'
    + '  TBase = class public N: Integer; end;'
    + '  TChild = class(TBase) public S: string; end;'
    + 'var B: TBase; C: TChild;'
    + 'begin'
    + '  B := TChild.Create();'
    + '  TChild(B).S := ''hello'';'
    + '  C := TChild(B as TChild);'
    + '  WriteLn(C.S)'
    + 'end.',
    'hello' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SupportsExpr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type'
    + '  IGreet = interface procedure Greet; end;'
    + '  TFoo = class(IGreet) public procedure Greet; end;'
    + 'procedure TFoo.Greet; begin WriteLn(''hi'') end;'
    + 'var Obj: TFoo;'
    + 'begin'
    + '  Obj := TFoo.Create();'
    + '  if Supports(Obj, IGreet) then WriteLn(''supports'') else WriteLn(''no'')'
    + 'end.',
    'supports' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IndirectFuncCallExpr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type TMapper = function(X: Integer): Integer;'
    + 'function Triple(X: Integer): Integer;'
    + 'begin Result := X * 3 end;'
    + 'var Fns: array[0..0] of TMapper;'
    + 'begin'
    + '  Fns[0] := @Triple;'
    + '  WriteLn(Fns[0](7))'
    + 'end.',
    '21' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_Ord;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type TColor = (Red, Green, Blue);'
    + 'var C: TColor;'
    + 'begin'
    + '  C := Blue;'
    + '  WriteLn(Ord(C));'
    + '  WriteLn(Ord(''A''))'
    + 'end.',
    '2' + LE + '65' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_Assigned;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type TObj = class end;'
    + 'var O: TObj;'
    + 'begin'
    + '  O := nil;'
    + '  if Assigned(O) then WriteLn(''yes'') else WriteLn(''no'');'
    + '  O := TObj.Create();'
    + '  if Assigned(O) then WriteLn(''yes'') else WriteLn(''no'')'
    + 'end.',
    'no' + LE + 'yes' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_Abs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'begin'
    + '  WriteLn(Abs(-42));'
    + '  WriteLn(Abs(7));'
    + '  WriteLn(Abs(0))'
    + 'end.',
    '42' + LE + '7' + LE + '0' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_Halt;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'begin'
    + '  WriteLn(''before'');'
    + '  Halt(42);'
    + '  WriteLn(''after'')'
    + 'end.',
    'before' + LE, 42);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_RoundTrunc;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'var D: Double;'
    + 'begin'
    + '  D := 3.7;'
    + '  WriteLn(Round(D));'
    + '  WriteLn(Trunc(D))'
    + 'end.',
    '4' + LE + '3' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_CompareStr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'begin'
    + '  if CompareStr(''abc'', ''abc'') = 0 then WriteLn(''eq'') else WriteLn(''ne'');'
    + '  if CompareStr(''abc'', ''abd'') < 0 then WriteLn(''lt'') else WriteLn(''ge'')'
    + 'end.',
    'eq' + LE + 'lt' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_UpCase;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'begin'
    + '  WriteLn(UpCase(97));'
    + '  WriteLn(UpCase(90))'
    + 'end.',
    'A' + LE + 'Z' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_Int64ToStr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'var N: Int64;'
    + 'begin'
    + '  N := 9876543210;'
    + '  WriteLn(Int64ToStr(N))'
    + 'end.',
    '9876543210' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_NestedProc_ReadCapture;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'procedure Outer;'
    + 'var X: Integer;'
    + '  procedure Inner;'
    + '  begin WriteLn(X) end;'
    + 'begin'
    + '  X := 42;'
    + '  Inner()'
    + 'end;'
    + 'begin'
    + '  Outer()'
    + 'end.',
    '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_NestedProc_WriteCapture;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'procedure Outer;'
    + 'var X: Integer;'
    + '  procedure Inner;'
    + '  begin X := 99 end;'
    + 'begin'
    + '  X := 0;'
    + '  Inner();'
    + '  WriteLn(X)'
    + 'end;'
    + 'begin'
    + '  Outer()'
    + 'end.',
    '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_SinCos;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'var R: Integer;'
    + 'begin'
    + '  R := Round(Sin(0.0));'
    + '  WriteLn(IntToStr(R));'
    + '  R := Round(Cos(0.0));'
    + '  WriteLn(IntToStr(R))'
    + 'end.',
    '0' + LE + '1' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_SqrtDouble;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'var R: Integer;'
    + 'begin'
    + '  R := Round(Sqrt(4.0));'
    + '  WriteLn(IntToStr(R))'
    + 'end.',
    '2' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_DoublePtrWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'var D: Double; PD: ^Double;'
    + 'begin'
    + '  D := 0.0;'
    + '  PD := @D;'
    + '  PD^ := 3.14;'
    + '  WriteLn(D)'
    + 'end.',
    '3.14' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SinglePtrWrite_NoAdjacentClobber;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'var A: Single; B: Single; PA: ^Single;'
    + 'begin'
    + '  A := 0.0;'
    + '  B := 9.5;'
    + '  PA := @A;'
    + '  PA^ := 1.25;'
    + '  WriteLn(B)'
    + 'end.',
    '9.5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IncDec_RecordField;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type TRec = record X: Integer; Y: Integer; end;'
    + 'var R: TRec;'
    + 'begin'
    + '  R.X := 10;'
    + '  R.Y := 100;'
    + '  Inc(R.X);'
    + '  Inc(R.Y, 5);'
    + '  Dec(R.X, 3);'
    + '  WriteLn(R.X);'
    + '  WriteLn(R.Y)'
    + 'end.',
    '8' + LE + '105' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IncDec_PtrDeref;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'var N: Integer;'
    + 'var P: ^Integer;'
    + 'begin'
    + '  N := 20;'
    + '  P := @N;'
    + '  Inc(P^);'
    + '  Inc(P^, 4);'
    + '  WriteLn(N)'
    + 'end.',
    '25' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TypeCast_PointerClass;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'var N: Integer; P: Pointer;'
    + 'begin'
    + '  N := 42;'
    + '  P := Pointer(N);'
    + '  WriteLn(Integer(P))'
    + 'end.',
    '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_PropertyRead_Simple;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type TBox = class'
    + ' FVal: Integer;'
    + ' constructor Create(V: Integer);'
    + ' function GetVal: Integer;'
    + ' property Val: Integer read GetVal;'
    + 'end;'
    + 'constructor TBox.Create(V: Integer);'
    + 'begin FVal := V end;'
    + 'function TBox.GetVal: Integer;'
    + 'begin Result := FVal end;'
    + 'var B: TBox;'
    + 'begin'
    + '  B := TBox.Create(99);'
    + '  WriteLn(B.Val);'
    + '  B.Free '
    + 'end.',
    '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_PropertyRead_Indexed;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type TArr = class'
    + ' FA: Integer; FB: Integer;'
    + ' constructor Create;'
    + ' function GetItem(I: Integer): Integer;'
    + ' property Items[I: Integer]: Integer read GetItem;'
    + 'end;'
    + 'constructor TArr.Create;'
    + 'begin FA := 10; FB := 30 end;'
    + 'function TArr.GetItem(I: Integer): Integer;'
    + 'begin if I = 0 then Result := FA else Result := FB end;'
    + 'var A: TArr;'
    + 'begin'
    + '  A := TArr.Create;'
    + '  WriteLn(A.Items[0]);'
    + '  WriteLn(A.Items[1]);'
    + '  A.Free '
    + 'end.',
    '10' + LE + '30' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_PropertyWrite_Simple;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type TBox = class'
    + ' FVal: Integer;'
    + ' procedure SetVal(V: Integer);'
    + ' function GetVal: Integer;'
    + ' property Val: Integer read GetVal write SetVal;'
    + 'end;'
    + 'procedure TBox.SetVal(V: Integer);'
    + 'begin FVal := V end;'
    + 'function TBox.GetVal: Integer;'
    + 'begin Result := FVal end;'
    + 'var B: TBox;'
    + 'begin'
    + '  B := TBox.Create;'
    + '  B.Val := 42;'
    + '  WriteLn(B.Val);'
    + '  B.Free '
    + 'end.',
    '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_PropertyWrite_Indexed;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type TArr = class'
    + ' FA: Integer; FB: Integer;'
    + ' procedure SetItem(I: Integer; V: Integer);'
    + ' function GetItem(I: Integer): Integer;'
    + ' property Items[I: Integer]: Integer read GetItem write SetItem;'
    + 'end;'
    + 'procedure TArr.SetItem(I: Integer; V: Integer);'
    + 'begin if I = 0 then FA := V else FB := V end;'
    + 'function TArr.GetItem(I: Integer): Integer;'
    + 'begin if I = 0 then Result := FA else Result := FB end;'
    + 'var A: TArr;'
    + 'begin'
    + '  A := TArr.Create;'
    + '  A.Items[0] := 10;'
    + '  A.Items[1] := 30;'
    + '  WriteLn(A.Items[0]);'
    + '  WriteLn(A.Items[1]);'
    + '  A.Free '
    + 'end.',
    '10' + LE + '30' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ClassName;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type TFoo = class end;'
    + 'var F: TFoo;'
    + 'begin'
    + '  F := TFoo.Create;'
    + '  WriteLn(F.ClassName);'
    + '  F.Free '
    + 'end.',
    'TFoo' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_MethodCall_ManyArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(
    'program P;'
    + 'type TCalc = class'
    + ' function Sum6(A: Integer; B: Integer; C: Integer;'
    + ' D: Integer; E: Integer; F: Integer): Integer;'
    + 'end;'
    + 'function TCalc.Sum6(A: Integer; B: Integer; C: Integer;'
    + ' D: Integer; E: Integer; F: Integer): Integer;'
    + 'begin Result := A + B + C + D + E + F end;'
    + 'var Obj: TCalc;'
    + 'begin'
    + '  Obj := TCalc.Create;'
    + '  WriteLn(Obj.Sum6(1, 2, 3, 4, 5, 6));'
    + '  Obj.Free '
    + 'end.',
    '21' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ImplicitSelf_ClassField;
begin
  AssertRunsOnBoth(
    'program T;'
    + 'type '
    + '  TInner = class FVal: Integer; end; '
    + '  TOuter = class '
    + '    FInner: TInner; '
    + '    function GetVal(): Integer; '
    + '  end; '
    + 'function TOuter.GetVal(): Integer; '
    + 'begin Result := FInner.FVal end; '
    + 'var I: TInner; O: TOuter; '
    + 'begin '
    + '  I := TInner.Create; '
    + '  I.FVal := 42; '
    + '  O := TOuter.Create; '
    + '  O.FInner := I; '
    + '  WriteLn(O.GetVal()); '
    + '  O.Free; '
    + '  I.Free '
    + 'end.',
    '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ImplicitSelf_PropertyGetter;
begin
  AssertRunsOnBoth(
    'program T;'
    + 'type '
    + '  TMyObj = class '
    + '  private '
    + '    FVal: Integer; '
    + '    function GetVal: Integer; '
    + '  public '
    + '    property Val: Integer read GetVal; '
    + '    procedure Show; '
    + '  end; '
    + 'function TMyObj.GetVal: Integer; '
    + 'begin Result := FVal end; '
    + 'procedure TMyObj.Show; '
    + 'begin WriteLn(Val) end; '
    + 'var O: TMyObj; '
    + 'begin '
    + '  O := TMyObj.Create; '
    + '  O.FVal := 99; '
    + '  O.Show; '
    + '  O.Free '
    + 'end.',
    '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ConstArray_StringElements;
begin
  AssertRunsOnBoth(
    'program T;'
    + 'const '
    + '  Regs: array[0..2] of string = (''ax'', ''bx'', ''cx''); '
    + 'var I: Integer; '
    + 'begin '
    + '  for I := 0 to 2 do '
    + '    WriteLn(Regs[I]) '
    + 'end.',
    'ax' + LE + 'bx' + LE + 'cx' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_VirtualDispatch_Expr;
begin
  AssertRunsOnBoth(
    'program T;'
    + 'type '
    + '  TBase = class '
    + '    function GetVal(): Integer; virtual; abstract; '
    + '  end; '
    + '  TChild = class(TBase) '
    + '    function GetVal(): Integer; override; '
    + '  end; '
    + 'function TChild.GetVal(): Integer; '
    + 'begin Result := 42 end; '
    + 'var B: TBase; '
    + 'begin '
    + '  B := TChild.Create; '
    + '  WriteLn(B.GetVal()); '
    + '  B.Free '
    + 'end.',
    '42' + LE, 0);
end;

initialization
  RegisterTest(TE2ENativeTests);

end.
