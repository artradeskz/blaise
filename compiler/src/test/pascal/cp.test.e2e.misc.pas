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

    { Sets }
    procedure TestRun_Set_Include_Exclude;
    procedure TestRun_Set_InOperator;
    procedure TestRun_Set_UnionIntersect;
    procedure TestRun_Set_ValuedConstant;
    procedure TestRun_Set_LiteralArgument;

    { for..in }
    procedure TestRun_ForIn_String_ByteVar_PrintsBytes;
    procedure TestRun_ForIn_String_IntegerVar_PrintsBytes;
    procedure TestRun_ForIn_Array_Integer_PrintsElements;
    procedure TestRun_ForIn_ClassEnumerator_PrintsElements;
    procedure TestRun_ForIn_Set_PrintsMembers;

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
  end;

implementation

procedure TE2EMiscTests.SetUp;
begin
  inherited SetUp;
  SetUpScratch('compiler/target/test-e2e-misc');
end;

const
  LE = #10;

  SrcBoolOps = '''
    program P;
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
    program P;
    var B: Boolean;
    begin
      B := True;
      WriteLn(B);
      B := False;
      WriteLn(B)
    end.
    ''';

  SrcWriteLnBoolExpr = '''
    program P;
    begin
      WriteLn(3 > 2);
      WriteLn(1 = 2)
    end.
    ''';

  SrcMultiArg = '''
    program P;
    var I, J, K: Integer;
    begin
      I := 1; J := 2; K := 3;
      WriteLn(I, J, K)
    end.
    ''';

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

  SrcChainedRecord = '''
    program P;
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
    program P;
    const MaxVal = 100;
    var X: Integer;
    begin
      X := MaxVal + 1;
      WriteLn(X)
    end.
    ''';

  SrcConstStr = '''
    program P;
    const Greeting = 'Hello';
    begin
      WriteLn(Greeting)
    end.
    ''';

  SrcConstNeg = '''
    program P;
    const MinVal = -10;
    var X: Integer;
    begin
      X := MinVal * 2;
      WriteLn(X)
    end.
    ''';

  { Regression: typed array constant declared inside a function body was
    referenced as $Name but never emitted as a data item, producing a
    link error.  Exercises the full toolchain (codegen + QBE + ld). }
  SrcConstLocalArrayInFunc = '''
    program P;
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
    program P;
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
    program P;
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
      Obj := TFoo.Create;
      Obj.FVal := 55;
      M := @Obj.Print;
      M;
      Obj.Free
    end.
    ''';

  SrcDefaultParam = '''
    program P;
    function Add(A: Integer; B: Integer = 10): Integer;
    begin Result := A + B end;
    begin
      WriteLn(Add(5));
      WriteLn(Add(5, 20))
    end.
    ''';

  SrcDefaultParamMulti = '''
    program P;
    function Greet(Name: string; Prefix: string = 'Hello';
                   Suffix: string = '!'): string;
    begin Result := Prefix + ' ' + Name + Suffix end;
    begin
      WriteLn(Greet('World'));
      WriteLn(Greet('Ada', 'Hi'))
    end.
    ''';

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

  SrcVarParamString = '''
    program P;
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
    program P;
    function Twice(const X: Integer): Integer;
    begin Result := X * 2 end;
    begin
      WriteLn(Twice(21))
    end.
    ''';

  SrcTypeCastIntByte = '''
    program P;
    var I: Integer; B: Byte;
    begin
      I := 300;
      B := Byte(I);
      WriteLn(B)
    end.
    ''';

  SrcTypeCastPointerInt = '''
    program P;
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
    program P;
    var c: Cardinal;
    begin
      c := 3000000000;
      WriteLn(c)
    end.
    ''';

  SrcSetIncludeExclude = '''
    program P;
    type TColor = (Red, Green, Blue);
         TColors = set of TColor;
    var S: TColors;
    begin
      S := [];
      Include(S, Red);
      Include(S, Blue);
      if Red in S then WriteLn('red');
      if Green in S then WriteLn('green');
      if Blue in S then WriteLn('blue');
      Exclude(S, Red);
      if Red in S then WriteLn('red2')
    end.
    ''';

  SrcSetIn = '''
    program P;
    type TDir = (North, South, East, West);
         TDirs = set of TDir;
    var Horizontal: TDirs;
    begin
      Horizontal := [East, West];
      if North in Horizontal then WriteLn('N');
      if East  in Horizontal then WriteLn('E');
      if West  in Horizontal then WriteLn('W')
    end.
    ''';

  SrcSetUnion = '''
    program P;
    type TBit = (B0, B1, B2, B3);
         TBits = set of TBit;
    var A, B, C: TBits;
    begin
      A := [B0, B1];
      B := [B1, B2];
      C := A + B;
      if B0 in C then WriteLn('0');
      if B1 in C then WriteLn('1');
      if B2 in C then WriteLn('2');
      if B3 in C then WriteLn('3');
      C := A * B;
      if B1 in C then WriteLn('inter1')
    end.
    ''';

  { Set-valued constants: an inferred-type const and an annotated empty const,
    both used as set values at runtime. }
  SrcSetConst = '''
    program P;
    type TDir = (North, South, East, West);
         TDirs = set of TDir;
    const
      Horizontal = [East, West];
      Empty: TDirs = [];
    var S: TDirs;
    begin
      S := Horizontal;
      if North in S then WriteLn('N') else WriteLn('no-N');
      if East  in S then WriteLn('E');
      if West  in S then WriteLn('W');
      S := Empty;
      if East in S then WriteLn('still-E') else WriteLn('cleared')
    end.
    ''';

  { A set literal passed directly as a `set of` argument (both non-empty and
    empty), exercising the set-param ABI (w-width spill) too. }
  SrcSetLiteralArg = '''
    program P;
    type TDir = (North, South, East, West);
         TDirs = set of TDir;
    procedure Report(D: TDirs);
    begin
      if North in D then WriteLn('N') else WriteLn('no-N');
      if East  in D then WriteLn('E') else WriteLn('no-E')
    end;
    begin
      Report([East, West]);
      Report([])
    end.
    ''';

  SrcForInStringByte = '''
    program P;
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
    program P;
    var
      S: string;
      I: Integer;
    begin
      S := 'Hi';
      for I in S do
        WriteLn(I)
    end.
    ''';

  SrcForInArrayInteger = '''
    program P;
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
    program P;
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
      R.Free;
    end.
    ''';

  SrcForInSet = '''
    program P;
    type
      TColor = (Red, Green, Blue);
      TColorSet = set of TColor;
    var
      S: TColorSet;
      C: TColor;
    begin
      S := [Red, Blue];
      for C in S do
        WriteLn(Ord(C));
    end.
    ''';

procedure TE2EMiscTests.TestRun_BooleanOps_AllExpressions;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcBoolOps, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('all three branches fire',
    't1' + LE + 't2' + LE + 't3' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_WriteLn_BoolVar_PrintsTrueOrFalse;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcWriteLnBoolVar, 'True' + LE + 'False' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_WriteLn_BoolExpr_PrintsTrueOrFalse;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcWriteLnBoolExpr, 'True' + LE + 'False' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_MultiArgWriteLn_PrintsAllArgs;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcMultiArg, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('three values concatenated with trailing newline',
    '123' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_ForBreak_StopsAtFiveHalt;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcForBreak, '5' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ExitFromFunction_ReturnsImmediately;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcExitFunc, '7' + LE + '9' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ChainedRecordField_LoadsInner;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcChainedRecord, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('chained read of zero-initialised field', '0' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Const_IntegerConst;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcConstInt, '101' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Const_StringConst;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcConstStr, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Hello', 'Hello' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Const_LocalArrayInFunction;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcConstLocalArrayInFunc, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Jan Feb Dec days',
    '31' + LE + '28' + LE + '31' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Const_NegativeConst;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcConstNeg, '-20' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ProcType_CallViaVariable;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcProcTypeVar, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('14', '14' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_ProcType_OfObject_Dispatch;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcProcTypeOfObject, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('55', '55' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_DefaultParam_OmitLast;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcDefaultParam, '15' + LE + '25' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_DefaultParam_OmitMultiple;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcDefaultParamMulti, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('greetings', 'Hello World!' + LE + 'Hi Ada!' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_VarParam_SwapIntegers;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcVarParamSwap, '7' + LE + '3' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_VarParam_ModifyString;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcVarParamString, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Hello World', 'Hello World' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_ConstParam_CanRead;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcConstParam, '42' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_TypeCast_IntegerByte;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcTypeCastIntByte, '44' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_TypeCast_PointerInteger;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTypeCastPointerInt, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('42', '42' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_WriteUnsigned32_PrintsUnsigned;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcWriteUnsigned32, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('3000000000 (unsigned, not negative)', '3000000000' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Set_Include_Exclude;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcSetIncludeExclude, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('red blue', 'red' + LE + 'blue' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Set_InOperator;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcSetIn, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('E W', 'E' + LE + 'W' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Set_UnionIntersect;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcSetUnion, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('union 0 1 2, intersect 1',
    '0' + LE + '1' + LE + '2' + LE + 'inter1' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Set_ValuedConstant;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcSetConst, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  { Horizontal = [East, West]: no-N, E, W; Empty cleared the set. }
  AssertEquals('set const',
    'no-N' + LE + 'E' + LE + 'W' + LE + 'cleared' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Set_LiteralArgument;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcSetLiteralArg, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  { Report([East,West]): no-N, E.  Report([]): no-N, no-E. }
  AssertEquals('set literal arg',
    'no-N' + LE + 'E' + LE + 'no-N' + LE + 'no-E' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_ForIn_String_ByteVar_PrintsBytes;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcForInStringByte, '72' + LE + '105' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ForIn_String_IntegerVar_PrintsBytes;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcForInStringInteger, '72' + LE + '105' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ForIn_Array_Integer_PrintsElements;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcForInArrayInteger, '10' + LE + '20' + LE + '30' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ForIn_ClassEnumerator_PrintsElements;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcForInClassEnum, '3' + LE + '4' + LE + '5' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ForIn_Set_PrintsMembers;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcForInSet, '0' + LE + '2' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_NestedProc_MutatesCapturedVar;
const
  Src =
    '''
        program P;
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
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('x=5, inner mutates to 15, outer sees 15',
    '5' + LE + '15' + LE + '15' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Diamond_SingleArg_WorksAtRuntime;
const
  Src = '''
    program P;
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
      B := TBox<>.Create;
      B.SetValue(99);
      WriteLn(B.GetValue())
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '99' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Diamond_TwoArgs_WorksAtRuntime;
const
  Src = '''
    program P;
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
      P := TPair<>.Create;
      P.SetKey(3);
      P.SetVal(7);
      WriteLn(P.GetKey());
      WriteLn(P.GetVal())
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '3' + LE + '7' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_AddrOf_DynArrayFieldElement;
const Src = '''
    program P;
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
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '20' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_GenericRecord_FieldStore_Prints;
const Src = '''
    program P;
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
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '9' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_GenericRecord_WithMethod_Prints;
const Src = '''
    program P;
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
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '42' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_GenericRecord_TwoParams_Prints;
const Src = '''
    program P;
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
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '10' + LE + '20' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_GenericRecord_StringField_Prints;
const Src = '''
    program P;
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
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', 'hello' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_BitwiseNot_Integer;
const Src = '''
    program P;
    var I: Integer;
    begin
      I := 0;
      WriteLn(not I)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '-1' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_BitwiseNot_Byte;
const Src = '''
    program P;
    var B: Byte;
    begin
      B := 0;
      WriteLn(not B)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '-1' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_BitwiseNot_Int64;
const Src = '''
    program P;
    var I: Int64;
    begin
      I := 0;
      WriteLn(not I)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '-1' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_BitwiseNot_Bitmask;
const Src = '''
    program P;
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
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '4' + LE, Output);
end;

initialization
  RegisterTest(TE2EMiscTests);

end.

