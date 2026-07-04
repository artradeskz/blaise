{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.misc;

{ E2E tests for miscellaneous features: boolean ops, WriteLn, constants,
  procedural types, default parameters, var/const params, type casts,
  sets, and for..in. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EMiscTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { Boolean, WriteLn, break/exit }
    procedure TestRun_BooleanOps_AllExpressions;
    procedure TestRun_WriteLn_BoolVar_PrintsTrueOrFalse;
    procedure TestRun_WriteLn_BoolExpr_PrintsTrueOrFalse;
    procedure TestRun_MultiArgWriteLn_PrintsAllArgs;
    procedure TestRun_ForBreak_StopsAtFiveHalt;
    procedure TestRun_ExitFromFunction_ReturnsImmediately;
    procedure TestRun_ChainedRecordField_LoadsInner;

    { Constants }
    procedure TestRun_Const_IntegerConst;
    procedure TestRun_Const_StringConst;
    procedure TestRun_Const_NegativeConst;
    procedure TestRun_Const_CompileTimeExpression;
    procedure TestRun_Const_LocalArrayInFunction;

    { Procedural types }
    procedure TestRun_ProcType_CallViaVariable;
    procedure TestRun_ProcType_OfObject_Dispatch;

    { Default parameters }
    procedure TestRun_DefaultParam_OmitLast;
    procedure TestRun_DefaultParam_OmitMultiple;

    { var / const params }
    procedure TestRun_VarParam_SwapIntegers;
    procedure TestRun_VarParam_ModifyString;
    procedure TestRun_ConstParam_CanRead;

    { Type casts }
    procedure TestRun_TypeCast_IntegerByte;
    procedure TestRun_TypeCast_PointerInteger;
    procedure TestRun_WriteUnsigned32_PrintsUnsigned;

    { Set `set of` operation e2e tests moved to cp.test.e2e.sets. }

    { for..in }
    procedure TestRun_ForIn_String_ByteVar_PrintsBytes;
    procedure TestRun_ForIn_String_IntegerVar_PrintsCodePoints;
    procedure TestRun_ForIn_String_IntegerVar_CodePoints_TwoByte;
    procedure TestRun_ForIn_String_IntegerVar_CodePoints_ThreeByte;
    procedure TestRun_ForIn_Array_Integer_PrintsElements;
    procedure TestRun_ForIn_ClassEnumerator_PrintsElements;

    { Nested procedures }
    procedure TestRun_NestedProc_MutatesCapturedVar;

    { Diamond operator: TFoo<> infers type args from LHS }
    procedure TestRun_Diamond_SingleArg_WorksAtRuntime;
    procedure TestRun_Diamond_TwoArgs_WorksAtRuntime;

    { Address-of array field element }
    procedure TestRun_AddrOf_DynArrayFieldElement;

    { Generic records }
    procedure TestRun_GenericRecord_FieldStore_Prints;
    procedure TestRun_GenericRecord_WithMethod_Prints;
    procedure TestRun_GenericRecord_TwoParams_Prints;
    procedure TestRun_GenericRecord_StringField_Prints;
    procedure TestRun_BitwiseNot_Integer;
    procedure TestRun_BitwiseNot_Byte;
    procedure TestRun_BitwiseNot_Int64;
    procedure TestRun_BitwiseNot_Bitmask;
    procedure TestRun_WriteLn_StdErr_NotOnStdout;

    { function-of-object called through a variable must load Data (Self)
      from the TMethod block and shift user args right. }
    procedure TestRun_FunctionOfObject_IndirectCall;

    { @(class-field dynamic-array)[idx] as a USED pointer must load the
      instance pointer first (loadl), not treat the class variable's slot
      as the instance.  Regression for the QBE codegen bug where
      @Obj.Arr[I] computed `add $Obj, off` instead of
      `loadl $Obj; add .., off`, producing a garbage address that
      segfaulted when dereferenced (e.g. passed to memcpy). }
    procedure TestRun_AddrOfClassFieldDynArrayElem_LoadsInstance;

    { inherited Method() in EXPRESSION position — calling an inherited
      function and using its result (Result := inherited F() + ...). Was a
      parser gap (inherited only worked as a statement). }
    procedure TestRun_InheritedFunctionCall_InExpression;

    { (expr as T).Field := value — a parenthesised cast as an assignment
      TARGET. Was a parser gap (statements could not start with '('). }
    procedure TestRun_ParenCastAsAssignmentTarget;

    { Nested generic type arguments: TList<TList<Integer>>. Was a parser gap
      (type-arg list did not recurse, in both type and constructor position). }
    procedure TestRun_NestedGenericTypeArgs;

    { Named integer subrange type (issue #130 bug1): the type-decl parser had
      no integer-literal subrange case.  A named subrange aliases the narrowest
      standard integer type and carries no range checking. }
    procedure TestRun_Subrange_NamedType;
    procedure TestRun_Subrange_InRecordAndArray;

    { forward; in a program decl section (issue #130 bug2): the forward decl
      used to swallow the following implementation as a nested-proc body. }
    procedure TestRun_Forward_MutualRecursion;

    { Large / 64-bit integer constants (issue #133): a hex value above 32 bits
      was truncated (inferred Integer); a value above High(Int64) was rejected.
      Untyped consts now widen by magnitude; typed Int64/UInt64 accept the full
      64-bit bit pattern. }
    procedure TestRun_Const_LargeHex_NotTruncated;
    procedure TestRun_Const_Int64BitPattern;
    procedure TestRun_Const_UInt64BitPattern;
    procedure TestRun_Const_UntypedAboveInt64_IsUInt64;

    { Conditional compilation (issue #131): predefined BLAISE, DEFINE/UNDEF,
      IFDEF/IFNDEF/ELSE/ENDIF, nesting. }
    procedure TestRun_Ifdef_PredefinedBlaise;
    procedure TestRun_Ifdef_DefineUndefIfndefNested;
  end;

implementation

procedure TE2EMiscTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-misc');
end;

const
  LE = #10;

  SrcBoolOps = '''
    program Prg;
    var A, B: Boolean;
    begin
      A := True;
      B := False;
      if A and not B then WriteLn('t1');
      if A or B then WriteLn('t2');
      if not (A and B) then WriteLn('t3')
    end.
    ''';

  SrcWriteLnBoolVar = '''
    program Prg;
    var B: Boolean;
    begin
      B := True;
      WriteLn(B);
      B := False;
      WriteLn(B)
    end.
    ''';

  SrcWriteLnBoolExpr = '''
    program Prg;
    begin
      WriteLn(3 > 2);
      WriteLn(1 = 2)
    end.
    ''';

  SrcMultiArg = '''
    program Prg;
    var I, J, K: Integer;
    begin
      I := 1; J := 2; K := 3;
      WriteLn(I, J, K)
    end.
    ''';

  SrcForBreak = '''
    program Prg;
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

  SrcExitFunc = '''
    program Prg;
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

  SrcChainedRecord = '''
    program Prg;
    type
      TInner = record Value: Integer; end;
      TOuter = record I: TInner; end;
    var O: TOuter; N: Integer;
    begin
      N := O.I.Value;
      WriteLn(N)
    end.
    ''';

  SrcConstInt = '''
    program Prg;
    const MaxVal = 100;
    var X: Integer;
    begin
      X := MaxVal + 1;
      WriteLn(X)
    end.
    ''';

  SrcConstStr = '''
    program Prg;
    const Greeting = 'Hello';
    begin
      WriteLn(Greeting)
    end.
    ''';

  SrcConstNeg = '''
    program Prg;
    const MinVal = -10;
    var X: Integer;
    begin
      X := MinVal * 2;
      WriteLn(X)
    end.
    ''';

  { issue #96 — const declared with a compile-time formula (precedence,
    parentheses, division, and a forward reference to a prior const). }
  SrcConstExpr = '''
    program Prg;
    const
      A = 2 * 3;
      B = 2 + 3 * 4;
      C = (2 + 3) * 4;
      D = 100 div 7;
      Base = 10;
      E = Base * 2 + 1;
    begin
      WriteLn(A);
      WriteLn(B);
      WriteLn(C);
      WriteLn(D);
      WriteLn(E)
    end.
    ''';

  { Regression: typed array constant declared inside a function body was
    referenced as $Name but never emitted as a data item, producing a
    link error.  Exercises the full toolchain (codegen + QBE + ld). }
  SrcConstLocalArrayInFunc = '''
    program Prg;
    function DaysInMonth(M: Integer): Integer;
    const
      Days: array[1..12] of Integer = (31,28,31,30,31,30,31,31,30,31,30,31);
    begin
      Result := Days[M]
    end;
    begin
      WriteLn(DaysInMonth(1));
      WriteLn(DaysInMonth(2));
      WriteLn(DaysInMonth(12))
    end.
    ''';

  SrcProcTypeVar = '''
    program Prg;
    type TFn = function(X: Integer): Integer;
    function Twice(X: Integer): Integer;
    begin Result := X * 2 end;
    var F: TFn;
    begin
      F := @Twice;
      WriteLn(F(7))
    end.
    ''';

  SrcProcTypeOfObject = '''
    program Prg;
    type
      TProc = procedure of object;
      TFoo = class
        FVal: Integer;
        procedure Print;
      end;
    procedure TFoo.Print;
    begin WriteLn(FVal) end;
    var
      Obj: TFoo;
      M: TProc;
    begin
      Obj := TFoo.Create();
      Obj.FVal := 55;
      M := @Obj.Print;
      M;
      Obj.Free()
    end.
    ''';

  SrcDefaultParam = '''
    program Prg;
    function Add(A: Integer; B: Integer = 10): Integer;
    begin Result := A + B end;
    begin
      WriteLn(Add(5));
      WriteLn(Add(5, 20))
    end.
    ''';

  SrcDefaultParamMulti = '''
    program Prg;
    function Greet(Name: string; Prefix: string = 'Hello';
                   Suffix: string = '!'): string;
    begin Result := Prefix + ' ' + Name + Suffix end;
    begin
      WriteLn(Greet('World'));
      WriteLn(Greet('Ada', 'Hi'))
    end.
    ''';

  SrcVarParamSwap = '''
    program Prg;
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

  SrcVarParamString = '''
    program Prg;
    procedure Append(var S: string; const T: string);
    begin
      S := S + T
    end;
    var R: string;
    begin
      R := 'Hello';
      Append(R, ' World');
      WriteLn(R)
    end.
    ''';

  SrcConstParam = '''
    program Prg;
    function Twice(const X: Integer): Integer;
    begin Result := X * 2 end;
    begin
      WriteLn(Twice(21))
    end.
    ''';

  SrcTypeCastIntByte = '''
    program Prg;
    var I: Integer; B: Byte;
    begin
      I := 300;
      B := Byte(I);
      WriteLn(B)
    end.
    ''';

  SrcTypeCastPointerInt = '''
    program Prg;
    var I: Integer; P1: Pointer;
    begin
      I  := 42;
      P1 := Pointer(I);
      WriteLn(Integer(P1))
    end.
    ''';

  { A Cardinal/UInt32 value above 2^31 must print as the large unsigned value,
    not a negative signed wrap.  3000000000 fits in UInt32 but is negative as a
    signed Int32. }
  SrcWriteUnsigned32 = '''
    program Prg;
    var c: Cardinal;
    begin
      c := 3000000000;
      WriteLn(c)
    end.
    ''';

  SrcForInStringByte = '''
    program Prg;
    var
      S: string;
      B: Byte;
    begin
      S := 'Hi';
      for B in S do
        WriteLn(B)
    end.
    ''';

  SrcForInStringInteger = '''
    program Prg;
    var
      S: string;
      I: Integer;
    begin
      S := 'Hi';
      for I in S do
        WriteLn(I)
    end.
    ''';

  { 'Aâ' = A (65) + â (U+00E2, codepoint 226, 2 UTF-8 bytes) }
  SrcForInStringCP2Byte = '''
    program Prg;
    var
      S: string;
      I: Integer;
    begin
      S := 'Aâ';
      for I in S do
        WriteLn(I)
    end.
    ''';

  { '€X' = € (U+20AC, codepoint 8364, 3 UTF-8 bytes) + X (88) }
  SrcForInStringCP3Byte = '''
    program Prg;
    var
      S: string;
      I: Integer;
    begin
      S := '€X';
      for I in S do
        WriteLn(I)
    end.
    ''';

  SrcForInArrayInteger = '''
    program Prg;
    var
      A: array[0..2] of Integer;
      X: Integer;
    begin
      A[0] := 10;
      A[1] := 20;
      A[2] := 30;
      for X in A do
        WriteLn(X)
    end.
    ''';

  SrcForInClassEnum = '''
    program Prg;
    type
      TRangeEnum = class
        FCurrent: Integer;
        FLast: Integer;
        constructor Create(AFirst, ALast: Integer);
        function MoveNext: Boolean;
        function GetCurrent: Integer;
        property Current: Integer read GetCurrent;
      end;
      TRange = class
        FFirst: Integer;
        FLast: Integer;
        constructor Create(AFirst, ALast: Integer);
        function GetEnumerator: TRangeEnum;
      end;
    constructor TRangeEnum.Create(AFirst, ALast: Integer);
    begin
      FCurrent := AFirst - 1;
      FLast := ALast;
    end;
    function TRangeEnum.MoveNext: Boolean;
    begin
      FCurrent := FCurrent + 1;
      Result := FCurrent <= FLast;
    end;
    function TRangeEnum.GetCurrent: Integer;
    begin
      Result := FCurrent;
    end;
    constructor TRange.Create(AFirst, ALast: Integer);
    begin
      FFirst := AFirst;
      FLast := ALast;
    end;
    function TRange.GetEnumerator: TRangeEnum;
    begin
      Result := TRangeEnum.Create(FFirst, FLast);
    end;
    var
      R: TRange;
      N: Integer;
    begin
      R := TRange.Create(3, 5);
      for N in R do
        WriteLn(N);
      R.Free();
    end.
    ''';

procedure TE2EMiscTests.TestRun_BooleanOps_AllExpressions;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcBoolOps, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('all three branches fire',
    't1' + LE + 't2' + LE + 't3' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_WriteLn_BoolVar_PrintsTrueOrFalse;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcWriteLnBoolVar, 'True' + LE + 'False' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_WriteLn_BoolExpr_PrintsTrueOrFalse;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcWriteLnBoolExpr, 'True' + LE + 'False' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_MultiArgWriteLn_PrintsAllArgs;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcMultiArg, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('three values concatenated with trailing newline',
    '123' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_ForBreak_StopsAtFiveHalt;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForBreak, '5' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ExitFromFunction_ReturnsImmediately;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcExitFunc, '7' + LE + '9' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ChainedRecordField_LoadsInner;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcChainedRecord, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('chained read of zero-initialised field', '0' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Const_IntegerConst;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcConstInt, '101' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Const_StringConst;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcConstStr, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Hello', 'Hello' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Const_LocalArrayInFunction;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcConstLocalArrayInFunc, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Jan Feb Dec days',
    '31' + LE + '28' + LE + '31' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Const_NegativeConst;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcConstNeg, '-20' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Const_CompileTimeExpression;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { A=6, B=14 (precedence), C=20 (parens), D=14 (div), E=21 (named-ref). }
  AssertRunsOnAll(SrcConstExpr,
    '6' + LE + '14' + LE + '20' + LE + '14' + LE + '21' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ProcType_CallViaVariable;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcProcTypeVar, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('14', '14' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_ProcType_OfObject_Dispatch;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcProcTypeOfObject, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('55', '55' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_DefaultParam_OmitLast;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDefaultParam, '15' + LE + '25' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_DefaultParam_OmitMultiple;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcDefaultParamMulti, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('greetings', 'Hello World!' + LE + 'Hi Ada!' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_VarParam_SwapIntegers;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVarParamSwap, '7' + LE + '3' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_VarParam_ModifyString;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcVarParamString, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Hello World', 'Hello World' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_ConstParam_CanRead;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcConstParam, '42' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_TypeCast_IntegerByte;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcTypeCastIntByte, '44' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_TypeCast_PointerInteger;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTypeCastPointerInt, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('42', '42' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_WriteUnsigned32_PrintsUnsigned;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcWriteUnsigned32, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('3000000000 (unsigned, not negative)', '3000000000' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_ForIn_String_ByteVar_PrintsBytes;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForInStringByte, '72' + LE + '105' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ForIn_String_IntegerVar_PrintsCodePoints;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForInStringInteger, '72' + LE + '105' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ForIn_String_IntegerVar_CodePoints_TwoByte;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForInStringCP2Byte,
    '65' + LE + '226' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ForIn_String_IntegerVar_CodePoints_ThreeByte;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForInStringCP3Byte,
    '8364' + LE + '88' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ForIn_Array_Integer_PrintsElements;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForInArrayInteger, '10' + LE + '20' + LE + '30' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ForIn_ClassEnumerator_PrintsElements;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForInClassEnum, '3' + LE + '4' + LE + '5' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_NestedProc_MutatesCapturedVar;
const
  Src =
    '''
        program Prg;
        procedure Outer;
        var x: Integer;
          procedure Inner;
          begin
            x := x + 10;
            WriteLn(IntToStr(x))
          end;
        begin
          x := 5;
          WriteLn(IntToStr(x));
          Inner;
          WriteLn(IntToStr(x))
        end;
        begin
          Outer
        end.
        ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('x=5, inner mutates to 15, outer sees 15',
    '5' + LE + '15' + LE + '15' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Diamond_SingleArg_WorksAtRuntime;
const
  Src = '''
    program Prg;
    type
      TBox<T> = class
        FValue: T;
        function  GetValue: T;
        begin Result := Self.FValue end;
        procedure SetValue(V: T);
        begin Self.FValue := V end;
      end;
    var B: TBox<Integer>;
    begin
      B := TBox<>.Create();
      B.SetValue(99);
      WriteLn(B.GetValue())
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '99' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Diamond_TwoArgs_WorksAtRuntime;
const
  Src = '''
    program Prg;
    type
      TPair<K, V> = class
        FKey: K;
        FVal: V;
        function  GetKey: K;
        begin Result := Self.FKey end;
        function  GetVal: V;
        begin Result := Self.FVal end;
        procedure SetKey(K2: K);
        begin Self.FKey := K2 end;
        procedure SetVal(V2: V);
        begin Self.FVal := V2 end;
      end;
    var P: TPair<Integer, Integer>;
    begin
      P := TPair<>.Create();
      P.SetKey(3);
      P.SetVal(7);
      WriteLn(P.GetKey());
      WriteLn(P.GetVal())
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '3' + LE + '7' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_AddrOf_DynArrayFieldElement;
const Src = '''
    program Prg;
    type
      THolder = record Items: array of Integer; end;
    var
      A: array of Integer;
      H: THolder;
      P: ^Integer;
    begin
      SetLength(A, 3);
      A[0] := 10;
      A[1] := 20;
      A[2] := 30;
      H.Items := A;
      P := @H.Items[1];
      WriteLn(P^)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '20' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_GenericRecord_FieldStore_Prints;
const Src = '''
    program Prg;
    type
      TMyVal<T> = record
        Value: T;
      end;
    var V: TMyVal<Integer>;
    begin
      V.Value := 9;
      WriteLn(V.Value)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '9' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_GenericRecord_WithMethod_Prints;
const Src = '''
    program Prg;
    type
      TMyVal<T> = record
        Value: T;
        function GetValue: T;
        begin
          Result := Self.Value
        end;
      end;
    var V: TMyVal<Integer>;
    begin
      V.Value := 42;
      WriteLn(V.GetValue())
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '42' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_GenericRecord_TwoParams_Prints;
const Src = '''
    program Prg;
    type
      TPair<K, V> = record
        Key: K;
        Val: V;
      end;
    var P: TPair<Integer, Integer>;
    begin
      P.Key := 10;
      P.Val := 20;
      WriteLn(P.Key);
      WriteLn(P.Val)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '10' + LE + '20' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_GenericRecord_StringField_Prints;
const Src = '''
    program Prg;
    type
      TMyVal<T> = record
        Value: T;
      end;
    var V: TMyVal<string>;
    begin
      V.Value := 'hello';
      WriteLn(V.Value)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', 'hello' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_BitwiseNot_Integer;
const Src = '''
    program Prg;
    var I: Integer;
    begin
      I := 0;
      WriteLn(not I)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '-1' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_BitwiseNot_Byte;
const Src = '''
    program Prg;
    var B: Byte;
    begin
      B := 0;
      WriteLn(not B)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '-1' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_BitwiseNot_Int64;
const Src = '''
    program Prg;
    var I: Int64;
    begin
      I := 0;
      WriteLn(not I)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '-1' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_BitwiseNot_Bitmask;
const Src = '''
    program Prg;
    const MASK = 3;
    var Flags: Integer;
    begin
      Flags := 7;
      Flags := Flags and (not MASK);
      WriteLn(Flags)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '4' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_WriteLn_StdErr_NotOnStdout;
const Src = '''
    program Prg;
    begin
      WriteLn(StdErr, 'error msg');
      WriteLn('ok')
    end.
    ''';
var
  Output: string;
  RCode:  Integer;
  BE:     TBackend;
  BName:  string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  for BE := Low(TBackend) to High(TBackend) do
  begin
    BName := BackendName(BE);
    AssertTrue('[' + BName + '] compile+run',
      Self.CompileAndRunOn(BE, Src, Output, RCode));
    AssertEquals('[' + BName + '] exit code', 0, RCode);
    AssertTrue('[' + BName + '] fd not printed as integer prefix',
      Pos('2error', Output) = -1)
  end
end;

const
  SrcFuncOfObjectIndirect = '''
    program Prg;
    type
      TFn = function(N: Integer): Integer of object;
      TC = class
        FBase: Integer;
        function AddBase(N: Integer): Integer;
      end;
    function TC.AddBase(N: Integer): Integer;
    begin
      Result := FBase + N;
    end;
    var
      C: TC;
      F: TFn;
      X: Integer;
    begin
      C := TC.Create();
      C.FBase := 100;
      F := @C.AddBase;
      writeln(F(23));
      X := F(7) + F(8);
      writeln(X);
    end.
    ''';

procedure TE2EMiscTests.TestRun_FunctionOfObject_IndirectCall;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcFuncOfObjectIndirect, '123' + LE + '215' + LE, 0);
end;

const
  { @(class-field dynamic array)[idx] used as a real pointer: write through
    it (memcpy), then read the bytes back.  Under the old QBE codegen the
    element address was computed off the class variable's slot instead of
    the loaded instance pointer, so the memcpy scribbled garbage / crashed.
    Runs on BOTH backends. }
  SrcAddrClassFieldDynArr = '''
    program Prg;
    procedure CopyBytes(Dst, Src: Pointer; N: Int64); external name 'memcpy';
    type
      TBuf = class
        Data: array of Byte;
        Count: Integer;
      end;
    var
      B: TBuf;
    begin
      B := TBuf.Create();
      SetLength(B.Data, 8);
      B.Count := 0;
      CopyBytes(@B.Data[B.Count], PChar('Hi'), 2);
      B.Count := 2;
      CopyBytes(@B.Data[B.Count], PChar('!!'), 2);
      WriteLn(Chr(B.Data[0]), Chr(B.Data[1]), Chr(B.Data[2]), Chr(B.Data[3]));
      B.Free();
    end.
    ''';

procedure TE2EMiscTests.TestRun_AddrOfClassFieldDynArrayElem_LoadsInstance;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcAddrClassFieldDynArr, 'Hi!!' + LE, 0);
end;

const
  { inherited as an expression: the overriding function adds to the parent's
    result.  Exercises a value-returning inherited call plus inherited with an
    argument (inherited Scale(F)). }
  SrcInheritedExprCall = '''
    program Prg;
    type
      TBase = class
        function V: Integer; virtual;
        begin Result := 5 end;
        function Scale(F: Integer): Integer; virtual;
        begin Result := F * 10 end;
      end;
      TDerived = class(TBase)
        function V: Integer; override;
        begin Result := inherited V() + 100 end;
        function Scale(F: Integer): Integer; override;
        begin Result := inherited Scale(F) + 1 end;
      end;
    var D: TDerived;
    begin
      D := TDerived.Create();
      WriteLn(D.V());
      WriteLn(D.Scale(3));
      D.Free()
    end.
    ''';

procedure TE2EMiscTests.TestRun_InheritedFunctionCall_InExpression;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInheritedExprCall, '105' + LE + '31' + LE, 0);
end;

const
  { Assign through a parenthesised cast: (a as TB).FX := 42.  The statement
    parser must accept a leading '(' as an assignment lvalue. }
  SrcParenCastTarget = '''
    program Prg;
    type
      TBase = class end;
      TDerived = class(TBase) FX: Integer; end;
    var a: TBase;
    begin
      a := TDerived.Create();
      (a as TDerived).FX := 42;
      WriteLn((a as TDerived).FX);
      a.Free()
    end.
    ''';

procedure TE2EMiscTests.TestRun_ParenCastAsAssignmentTarget;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcParenCastTarget, '42' + LE, 0);
end;

const
  { Nested generic type args, in both var-type and constructor position. }
  SrcNestedGeneric = '''
    program Prg;
    type TBox<T> = class
      FV: T;
      procedure SetV(V: T); begin FV := V end;
      function GetV: T; begin Result := FV end;
    end;
    var outer: TBox<TBox<Integer>>; inner: TBox<Integer>;
    begin
      inner := TBox<Integer>.Create();
      inner.SetV(7);
      outer := TBox<TBox<Integer>>.Create();
      outer.SetV(inner);
      WriteLn(outer.GetV().GetV());
      outer.Free();
      inner.Free()
    end.
    ''';

procedure TE2EMiscTests.TestRun_NestedGenericTypeArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcNestedGeneric, '7' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Subrange_NamedType;
const
  Src = '''
    program P;
    type TByte = 0..255;
    var b: TByte;
    begin b := 5; WriteLn(b) end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '5' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Subrange_InRecordAndArray;
const
  { A subrange as a record field and as an array element type, plus a negative
    subrange — exercises that the aliased base type sizes layout correctly. }
  Src = '''
    program P;
    type
      TByte = 0..255;
      TIdx  = -10..10;
      TRec  = record b: TByte; i: TIdx; end;
    var
      r: TRec;
      a: array[0..2] of TByte;
    begin
      r.b := 200; r.i := -7;
      a[0] := 1; a[1] := 250; a[2] := 99;
      WriteLn(r.b, ' ', r.i, ' ', a[1])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '200 -7 250' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Ifdef_PredefinedBlaise;
const
  { The headline cross-compiler use case: BLAISE is predefined. }
  Src = '''
    program P;
    begin
      {$IFDEF BLAISE}
      WriteLn('blaise')
      {$ELSE}
      WriteLn('other')
      {$ENDIF}
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'blaise' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Ifdef_DefineUndefIfndefNested;
const
  { DEFINE/UNDEF, IFNDEF, a predefined CPU/OS symbol, and nesting together. }
  Src = '''
    program P;
    {$DEFINE FOO}
    {$UNDEF FOO}
    begin
      {$IFDEF FOO}WriteLn('foo'){$ELSE}WriteLn('no-foo'){$ENDIF};
      {$IFNDEF BAR}WriteLn('no-bar'){$ENDIF};
      {$IFDEF LINUX}
        {$IFDEF BLAISE}WriteLn('linux-blaise'){$ENDIF}
      {$ENDIF}
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'no-foo' + LE + 'no-bar' + LE + 'linux-blaise' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Const_LargeHex_NotTruncated;
const
  { $080808080808 = 8830587504648, needs 64 bits — must not truncate to 32. }
  Src = '''
    program P;
    const DECI = $080808080808;
    begin WriteLn(DECI) end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '8830587504648' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Const_Int64BitPattern;
const
  { $8080808080808080 as Int64 is the bit pattern -9187201950435737472. }
  Src = '''
    program P;
    const A: Int64 = $8080808080808080;
    begin WriteLn(A) end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '-9187201950435737472' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Const_UInt64BitPattern;
const
  { Same bits as UInt64 = 9259542123273814144. }
  Src = '''
    program P;
    const A: UInt64 = $8080808080808080;
    begin WriteLn(A) end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '9259542123273814144' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Const_UntypedAboveInt64_IsUInt64;
const
  { An untyped literal above High(Int64) types as UInt64 (matches Delphi). }
  Src = '''
    program P;
    const A = $8080808080808080;
    begin WriteLn(A) end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '9259542123273814144' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Forward_MutualRecursion;
const
  { Mutually-recursive routines via a forward; declaration in the program's
    decl section.  Asserts the recursion actually computes parity, not just
    that it compiles. }
  Src = '''
    program P;
    function IsEven(n: Integer): Boolean; forward;
    function IsOdd(n: Integer): Boolean;
    begin if n = 0 then Result := False else Result := IsEven(n - 1) end;
    function IsEven(n: Integer): Boolean;
    begin if n = 0 then Result := True else Result := IsOdd(n - 1) end;
    begin
      WriteLn(IsEven(10), ' ', IsEven(7), ' ', IsOdd(7), ' ', IsOdd(4))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'True False True False' + LE, 0);
end;

initialization
  RegisterTest(TE2EMiscTests);

end.

