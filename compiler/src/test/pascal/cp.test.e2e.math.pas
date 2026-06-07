{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.math;

{ E2E tests for math compiler builtins and the Math RTL unit.

  Compiler builtins (no unit needed):
    Sqrt, Ceil, Floor, Round, Trunc, Ln, Log2, Log10, Power,
    Sin, Cos, Tan, ArcTan, ArcTan2, ArcSin, ArcCos, Sinh, Cosh, Tanh,
    IsNaN, IsInfinite.

  Math RTL unit (requires 'uses Math'):
    Min, Max, Sign, DivMod, InRange, EnsureRange, Pi. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EMathTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { --- Compiler builtins --- }

    { Sqrt }
    procedure TestRun_Sqrt_PositiveDouble;
    procedure TestRun_Sqrt_Zero;

    { Ceil / Floor / Round / Trunc }
    procedure TestRun_Ceil_Positive;
    procedure TestRun_Ceil_Negative;
    procedure TestRun_Floor_Positive;
    procedure TestRun_Floor_Negative;
    procedure TestRun_Round_HalfUp;
    procedure TestRun_Round_HalfDown;
    procedure TestRun_Trunc_Positive;
    procedure TestRun_Trunc_Negative;

    { Ln / Log2 / Log10 }
    procedure TestRun_Ln_E;
    procedure TestRun_Log2_PowerOfTwo;
    procedure TestRun_Log10_Hundred;

    { Power }
    procedure TestRun_Power_Square;
    procedure TestRun_Power_Zero_Exp;

    { Sin / Cos / Tan / ArcTan }
    procedure TestRun_Sin_Zero;
    procedure TestRun_Cos_Zero;
    procedure TestRun_Tan_Zero;
    procedure TestRun_ArcTan_Zero;

    { ArcTan2 }
    procedure TestRun_ArcTan2_OneOne;

    { ArcSin / ArcCos / Sinh / Cosh / Tanh }
    procedure TestRun_ArcSin_Zero;
    procedure TestRun_ArcCos_One;
    procedure TestRun_Sinh_Zero;
    procedure TestRun_Cosh_Zero;
    procedure TestRun_Tanh_Zero;

    { IsNaN / IsInfinite }
    procedure TestRun_IsNaN_NaN;
    procedure TestRun_IsNaN_Normal;
    procedure TestRun_IsInfinite_Inf;
    procedure TestRun_IsInfinite_Normal;

    { --- Math RTL unit --- }

    { Min / Max -- Integer }
    procedure TestRun_Min_Integer_Picks_Smaller;
    procedure TestRun_Max_Integer_Picks_Larger;
    procedure TestRun_Min_Integer_Equal;

    { Min / Max -- Double }
    procedure TestRun_Min_Double_Picks_Smaller;
    procedure TestRun_Max_Double_Picks_Larger;

    { Sign }
    procedure TestRun_Sign_Positive;
    procedure TestRun_Sign_Negative;
    procedure TestRun_Sign_Zero;

    { DivMod }
    procedure TestRun_DivMod_Basic;
    procedure TestRun_DivMod_Exact;

    { InRange }
    procedure TestRun_InRange_Inside;
    procedure TestRun_InRange_AtBoundary;
    procedure TestRun_InRange_Outside;

    { EnsureRange }
    procedure TestRun_EnsureRange_Inside;
    procedure TestRun_EnsureRange_ClampLow;
    procedure TestRun_EnsureRange_ClampHigh;

    { Pi constant }
    procedure TestRun_Pi_Approx;

    { Int64 → Double promotion }
    procedure TestRun_Int64MulDouble_LargeValue;

    { DoubleToStr }
    procedure TestRun_DoubleToStr_Pi;
    procedure TestRun_DoubleToStr_Zero;
    procedure TestRun_DoubleToStr_Negative;
    procedure TestRun_DoubleToStr_SmallFractions;
    procedure TestRun_DoubleToStr_ExponentialSmall;
    procedure TestRun_DoubleToStr_ExponentialLarge;
    procedure TestRun_DoubleToStr_LargeInteger;
    procedure TestRun_DoubleToStr_VerySmallPositive;

    { StrToDouble }
    procedure TestRun_StrToDouble_Simple;
    procedure TestRun_StrToDouble_Negative;
    procedure TestRun_StrToDouble_ScientificPos;
    procedure TestRun_StrToDouble_ScientificNeg;
    procedure TestRun_StrToDouble_LargeMantissa;
    procedure TestRun_StrToDouble_Zero;
    procedure TestRun_StrToDouble_RoundTrip;

    { Abs }
    procedure TestRun_AbsInt_Positive;
    procedure TestRun_AbsInt_Negative;

    { Integer → Double/Single implicit assignment }
    procedure TestRun_IntAssignDouble;
    procedure TestRun_IntAssignSingle;
    procedure TestRun_Int64AssignDouble;

    { Mixed Single/Double arithmetic }
    procedure TestRun_SingleMulDouble;
    procedure TestRun_SingleAddSingle;
    procedure TestRun_SingleCompareSingle;

    { Real division `/` with Integer operands yields a float }
    procedure TestRun_RealDiv_IntegerOperands_RoundTrunc;
    procedure TestRun_RealDiv_TenOverFour_Half;

    { WriteLn(Double) / WriteLn(Single) — direct float output without DoubleToStr }
    procedure TestRun_WriteLn_Double_Direct;
    procedure TestRun_WriteLn_Single_Direct;
  end;

implementation

procedure TE2EMathTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-math');
end;

{ ------------------------------------------------------------------ }
{ Sqrt                                                                 }
{ ------------------------------------------------------------------ }

procedure TE2EMathTests.TestRun_Sqrt_PositiveDouble;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Double;
    begin
      R := Sqrt(4.0);
      WriteLn(DoubleToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('sqrt(4)', '2', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Sqrt_Zero;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Double;
    begin
      R := Sqrt(0.0);
      WriteLn(DoubleToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('sqrt(0)', '0', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Ceil / Floor / Round / Trunc                                         }
{ ------------------------------------------------------------------ }

procedure TE2EMathTests.TestRun_Ceil_Positive;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Ceil(2.3);
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('ceil(2.3)', '3', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Ceil_Negative;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Ceil(-2.7);
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('ceil(-2.7)', '-2', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Floor_Positive;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Floor(2.9);
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('floor(2.9)', '2', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Floor_Negative;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Floor(-2.3);
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('floor(-2.3)', '-3', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Round_HalfUp;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Round(2.5);
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('round(2.5)', '3', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Round_HalfDown;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Round(-2.5);
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('round(-2.5)', '-3', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Trunc_Positive;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Trunc(3.9);
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('trunc(3.9)', '3', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Trunc_Negative;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Trunc(-3.9);
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('trunc(-3.9)', '-3', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Ln / Log2 / Log10                                                    }
{ ------------------------------------------------------------------ }

procedure TE2EMathTests.TestRun_Ln_E;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Round(Ln(2.71828182845904523536));
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('ln(e) approx 1', '1', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Log2_PowerOfTwo;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Round(Log2(8.0));
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('log2(8)', '3', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Log10_Hundred;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Round(Log10(100.0));
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('log10(100)', '2', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Power                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EMathTests.TestRun_Power_Square;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Round(Power(3.0, 2.0));
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('power(3,2)', '9', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Power_Zero_Exp;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Round(Power(5.0, 0.0));
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('power(5,0)', '1', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Trig                                                                 }
{ ------------------------------------------------------------------ }

procedure TE2EMathTests.TestRun_Sin_Zero;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Round(Sin(0.0));
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('sin(0)', '0', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Cos_Zero;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Round(Cos(0.0));
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('cos(0)', '1', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Tan_Zero;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Round(Tan(0.0));
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('tan(0)', '0', Trim(Output));
end;

procedure TE2EMathTests.TestRun_ArcTan_Zero;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Round(ArcTan(0.0));
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('arctan(0)', '0', Trim(Output));
end;

procedure TE2EMathTests.TestRun_ArcTan2_OneOne;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Double;
    begin
      { ArcTan2(1, 1) = pi/4, roughly 0.785 -- verify positive and < 1 }
      R := ArcTan2(1.0, 1.0);
      if (R > 0.7) and (R < 0.8) then WriteLn('ok') else WriteLn('fail')
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('arctan2(1,1)', 'ok', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ ArcSin / ArcCos / Sinh / Cosh / Tanh                                }
{ ------------------------------------------------------------------ }

procedure TE2EMathTests.TestRun_ArcSin_Zero;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Round(ArcSin(0.0));
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('arcsin(0)', '0', Trim(Output));
end;

procedure TE2EMathTests.TestRun_ArcCos_One;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Round(ArcCos(1.0));
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('arccos(1)', '0', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Sinh_Zero;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Round(Sinh(0.0));
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('sinh(0)', '0', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Cosh_Zero;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Round(Cosh(0.0));
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('cosh(0)', '1', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Tanh_Zero;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var R: Integer;
    begin
      R := Round(Tanh(0.0));
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('tanh(0)', '0', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ IsNaN / IsInfinite                                                   }
{ ------------------------------------------------------------------ }

procedure TE2EMathTests.TestRun_IsNaN_NaN;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var X: Double;
    begin
      X := 0.0 / 0.0;
      if IsNaN(X) then WriteLn('yes') else WriteLn('no')
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('isnan(0/0)', 'yes', Trim(Output));
end;

procedure TE2EMathTests.TestRun_IsNaN_Normal;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var X: Double;
    begin
      X := 42.0;
      if IsNaN(X) then WriteLn('yes') else WriteLn('no')
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('isnan(42)', 'no', Trim(Output));
end;

procedure TE2EMathTests.TestRun_IsInfinite_Inf;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var X: Double;
    begin
      X := 1.0 / 0.0;
      if IsInfinite(X) then WriteLn('yes') else WriteLn('no')
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('isinfinite(1/0)', 'yes', Trim(Output));
end;

procedure TE2EMathTests.TestRun_IsInfinite_Normal;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var X: Double;
    begin
      X := 42.0;
      if IsInfinite(X) then WriteLn('yes') else WriteLn('no')
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('isinfinite(42)', 'no', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Min / Max -- Integer                                                  }
{ ------------------------------------------------------------------ }

procedure TE2EMathTests.TestRun_Min_Integer_Picks_Smaller;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Math;
    var A, B: Integer;
    begin A := 7; B := 3; WriteLn(IntToStr(Min(A, B))) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('min(7,3)', '3', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Max_Integer_Picks_Larger;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Math;
    var A, B: Integer;
    begin A := 7; B := 3; WriteLn(IntToStr(Max(A, B))) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('max(7,3)', '7', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Min_Integer_Equal;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Math;
    var A, B: Integer;
    begin A := 5; B := 5; WriteLn(IntToStr(Min(A, B))) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('min(5,5)', '5', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Min / Max -- Double                                                   }
{ ------------------------------------------------------------------ }

procedure TE2EMathTests.TestRun_Min_Double_Picks_Smaller;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Math;
    var A, B, R: Double;
    begin
      A := 1.5;
      B := 2.5;
      R := Min(A, B);
      if R = 1.5 then WriteLn('ok') else WriteLn('fail')
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('min(1.5,2.5)', 'ok', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Max_Double_Picks_Larger;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Math;
    var A, B, R: Double;
    begin
      A := 1.5;
      B := 2.5;
      R := Max(A, B);
      if R = 2.5 then WriteLn('ok') else WriteLn('fail')
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('max(1.5,2.5)', 'ok', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Sign                                                                 }
{ ------------------------------------------------------------------ }

procedure TE2EMathTests.TestRun_Sign_Positive;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Math;
    var X: Integer;
    begin X := 42; WriteLn(IntToStr(Sign(X))) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('sign(42)', '1', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Sign_Negative;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Math;
    var X: Integer;
    begin X := -7; WriteLn(IntToStr(Sign(X))) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('sign(-7)', '-1', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Sign_Zero;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Math;
    var X: Integer;
    begin X := 0; WriteLn(IntToStr(Sign(X))) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('sign(0)', '0', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ DivMod                                                               }
{ ------------------------------------------------------------------ }

procedure TE2EMathTests.TestRun_DivMod_Basic;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Math;
    var Q, R: Integer;
    begin
      DivMod(17, 5, Q, R);
      WriteLn(IntToStr(Q));
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('divmod(17,5)', '3' + #10 + '2', Trim(Output));
end;

procedure TE2EMathTests.TestRun_DivMod_Exact;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Math;
    var Q, R: Integer;
    begin
      DivMod(12, 4, Q, R);
      WriteLn(IntToStr(Q));
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('divmod(12,4)', '3' + #10 + '0', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ InRange                                                              }
{ ------------------------------------------------------------------ }

procedure TE2EMathTests.TestRun_InRange_Inside;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Math;
    var V, Lo, Hi: Integer;
    begin
      V := 5; Lo := 1; Hi := 10;
      if InRange(V, Lo, Hi) then WriteLn('yes') else WriteLn('no')
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('inrange(5,1,10)', 'yes', Trim(Output));
end;

procedure TE2EMathTests.TestRun_InRange_AtBoundary;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Math;
    var V, Lo, Hi: Integer;
    begin
      V := 1; Lo := 1; Hi := 10;
      if InRange(V, Lo, Hi) then WriteLn('yes') else WriteLn('no')
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('inrange(1,1,10)', 'yes', Trim(Output));
end;

procedure TE2EMathTests.TestRun_InRange_Outside;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Math;
    var V, Lo, Hi: Integer;
    begin
      V := 11; Lo := 1; Hi := 10;
      if InRange(V, Lo, Hi) then WriteLn('yes') else WriteLn('no')
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('inrange(11,1,10)', 'no', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ EnsureRange                                                          }
{ ------------------------------------------------------------------ }

procedure TE2EMathTests.TestRun_EnsureRange_Inside;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Math;
    var V, Lo, Hi: Integer;
    begin V := 5; Lo := 1; Hi := 10; WriteLn(IntToStr(EnsureRange(V, Lo, Hi))) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('ensurerange(5,1,10)', '5', Trim(Output));
end;

procedure TE2EMathTests.TestRun_EnsureRange_ClampLow;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Math;
    var V, Lo, Hi: Integer;
    begin V := -3; Lo := 1; Hi := 10; WriteLn(IntToStr(EnsureRange(V, Lo, Hi))) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('ensurerange(-3,1,10)', '1', Trim(Output));
end;

procedure TE2EMathTests.TestRun_EnsureRange_ClampHigh;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Math;
    var V, Lo, Hi: Integer;
    begin V := 15; Lo := 1; Hi := 10; WriteLn(IntToStr(EnsureRange(V, Lo, Hi))) end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('ensurerange(15,1,10)', '10', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Pi constant                                                          }
{ ------------------------------------------------------------------ }

procedure TE2EMathTests.TestRun_Pi_Approx;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses Math;
    var R: Integer;
    begin
      { Pi is approximately 3.14159 -- Round gives 3 }
      R := Round(Pi);
      WriteLn(IntToStr(R))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('round(pi)', '3', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Int64MulDouble_LargeValue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var M: Int64; D: Double;
    begin
      M := 123456789012345;
      D := M * 1.0;
      WriteLn(DoubleToStr(D))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('Int64*Double', '123456789012345', Trim(Output));
end;

procedure TE2EMathTests.TestRun_DoubleToStr_Pi;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var D: Double;
    begin
      D := 3.14159;
      WriteLn(DoubleToStr(D))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('DoubleToStr(3.14159)', '3.14159', Trim(Output));
end;

procedure TE2EMathTests.TestRun_DoubleToStr_Zero;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    begin
      WriteLn(DoubleToStr(0.0))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('DoubleToStr(0.0)', '0', Trim(Output));
end;

procedure TE2EMathTests.TestRun_DoubleToStr_Negative;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var D: Double;
    begin
      D := -42.5;
      WriteLn(DoubleToStr(D))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('DoubleToStr(-42.5)', '-42.5', Trim(Output));
end;

procedure TE2EMathTests.TestRun_DoubleToStr_SmallFractions;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    begin
      WriteLn(DoubleToStr(0.1));
      WriteLn(DoubleToStr(0.2));
      WriteLn(DoubleToStr(0.3))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('fractions', '0.1' + LineEnding + '0.2' + LineEnding + '0.3',
    Trim(Output));
end;

procedure TE2EMathTests.TestRun_DoubleToStr_ExponentialSmall;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    begin
      WriteLn(DoubleToStr(1e-10));
      WriteLn(DoubleToStr(1e-100))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('small exp', '1e-10' + LineEnding + '1e-100', Trim(Output));
end;

procedure TE2EMathTests.TestRun_DoubleToStr_ExponentialLarge;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    begin
      WriteLn(DoubleToStr(1e+100));
      WriteLn(DoubleToStr(1e+308))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('large exp', '1e+100' + LineEnding + '1e+308', Trim(Output));
end;

procedure TE2EMathTests.TestRun_DoubleToStr_LargeInteger;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    begin
      WriteLn(DoubleToStr(1000000.0));
      WriteLn(DoubleToStr(99999999999999.0))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('large int', '1000000' + LineEnding + '99999999999999',
    Trim(Output));
end;

procedure TE2EMathTests.TestRun_DoubleToStr_VerySmallPositive;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    begin
      WriteLn(DoubleToStr(0.0001))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('DoubleToStr(0.0001)', '0.0001', Trim(Output));
end;

procedure TE2EMathTests.TestRun_StrToDouble_Simple;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var D: Double; S: String;
    begin
      S := '3.14';
      D := StrToDouble(S);
      WriteLn(DoubleToStr(D))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('StrToDouble(3.14)', '3.14', Trim(Output));
end;

procedure TE2EMathTests.TestRun_StrToDouble_Negative;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var D: Double; S: String;
    begin
      S := '-1.5';
      D := StrToDouble(S);
      WriteLn(DoubleToStr(D))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('StrToDouble(-1.5)', '-1.5', Trim(Output));
end;

procedure TE2EMathTests.TestRun_StrToDouble_ScientificPos;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var D: Double; S: String;
    begin
      S := '1e10';
      D := StrToDouble(S);
      WriteLn(DoubleToStr(D))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('StrToDouble(1e10)', '10000000000', Trim(Output));
end;

procedure TE2EMathTests.TestRun_StrToDouble_ScientificNeg;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var D: Double; S: String;
    begin
      S := '1e-10';
      D := StrToDouble(S);
      WriteLn(DoubleToStr(D))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('StrToDouble(1e-10)', '1e-10', Trim(Output));
end;

procedure TE2EMathTests.TestRun_StrToDouble_LargeMantissa;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var D: Double; S: String;
    begin
      S := '1234567890.12345';
      D := StrToDouble(S);
      WriteLn(DoubleToStr(D))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('StrToDouble large mantissa', '1234567890.12345', Trim(Output));
end;

procedure TE2EMathTests.TestRun_StrToDouble_Zero;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var D: Double; S: String;
    begin
      S := '0';
      D := StrToDouble(S);
      WriteLn(DoubleToStr(D))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('StrToDouble(0)', '0', Trim(Output));
end;

procedure TE2EMathTests.TestRun_StrToDouble_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var D: Double;
    begin
      D := StrToDouble(DoubleToStr(3.14159265358979));
      WriteLn(DoubleToStr(D))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('roundtrip pi', '3.14159265358979', Trim(Output));
end;

procedure TE2EMathTests.TestRun_AbsInt_Positive;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    begin
      WriteLn(Abs(42))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('Abs(42)', '42', Trim(Output));
end;

procedure TE2EMathTests.TestRun_AbsInt_Negative;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    begin
      WriteLn(Abs(-7))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('Abs(-7)', '7', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Integer → Double/Single implicit assignment                          }
{ ------------------------------------------------------------------ }

procedure TE2EMathTests.TestRun_IntAssignDouble;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var D: Double;
    begin
      D := 4345;
      WriteLn(DoubleToStr(D))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('4345 as Double', '4345', Trim(Output));
end;

procedure TE2EMathTests.TestRun_IntAssignSingle;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var S: Single;
        D: Double;
    begin
      S := 42;
      D := S;
      WriteLn(DoubleToStr(D))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('42 as Single→Double', '42', Trim(Output));
end;

procedure TE2EMathTests.TestRun_Int64AssignDouble;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var N: Int64;
        D: Double;
    begin
      N := 123456789;
      D := N;
      WriteLn(DoubleToStr(D))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('123456789 as Double', '123456789', Trim(Output));
end;

procedure TE2EMathTests.TestRun_SingleMulDouble;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var S: Single;
        D: Double;
    begin
      S := 3.5;
      D := S * 2.0;
      WriteLn(DoubleToStr(D))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('3.5*2.0', '7', Trim(Output));
end;

procedure TE2EMathTests.TestRun_SingleAddSingle;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var A, B, C: Single;
        D: Double;
    begin
      A := 1.5;
      B := 2.5;
      C := A + B;
      D := C;
      WriteLn(DoubleToStr(D))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('1.5+2.5', '4', Trim(Output));
end;

procedure TE2EMathTests.TestRun_SingleCompareSingle;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var A, B: Single;
    begin
      A := 1.5;
      B := 2.5;
      if A < B then
        WriteLn('less')
      else
        WriteLn('not less')
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('1.5<2.5', 'less', Trim(Output));
end;

procedure TE2EMathTests.TestRun_RealDiv_IntegerOperands_RoundTrunc;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var X, Y, Z: Integer;
    begin
      X := 3;
      Y := 10;
      Z := Round(Y / X);
      WriteLn(IntToStr(Z));
      Z := Trunc(Y / X);
      WriteLn(IntToStr(Z))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('Round(10/3) and Trunc(10/3)', '3' + LineEnding + '3', Trim(Output));
end;

procedure TE2EMathTests.TestRun_RealDiv_TenOverFour_Half;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var X, Y: Integer; D: Double;
    begin
      X := 4;
      Y := 10;
      D := Y / X;
      WriteLn(DoubleToStr(D))
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('10/4', '2.5', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ WriteLn(Double) / WriteLn(Single) direct float output              }
{ ------------------------------------------------------------------ }

procedure TE2EMathTests.TestRun_WriteLn_Double_Direct;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var D: Double;
    begin
      D := 3.14;
      WriteLn(D)
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('WriteLn(Double)', '3.14', Trim(Output));
end;

procedure TE2EMathTests.TestRun_WriteLn_Single_Direct;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(
    '''
    program P;
    var S: Single;
    begin
      S := 1.5;
      WriteLn(S)
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('WriteLn(Single)', '1.5', Trim(Output));
end;

initialization
  RegisterTest(TE2EMathTests);

end.
