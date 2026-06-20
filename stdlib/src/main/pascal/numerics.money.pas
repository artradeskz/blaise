{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Numerics.Money;

{ Blaise StdLib — currency-aware monetary amounts.

  TMoney is a thin VALUE-TYPE wrapper that layers an ISO-4217 currency tag onto
  an exact TDecimal amount (see Numerics.Decimal).  It is the money type; the
  numeric core (TDecimal) stays currency- and locale-agnostic, matching the
  universal pattern of Moneta (Java), the money gem (Ruby) and rusty-money
  (Rust), each of which wraps a decimal rather than baking currency into the
  numeric type.  See docs/language-rationale.adoc.

  Design:

    - Currency is an ISO-4217 alphabetic code held as a string ('USD', 'JPY',
      'KWD').  This is open-ended: a code the built-in registry does not know is
      still accepted and uses the fallback scale (2).  The code is upper-cased
      on construction so 'usd' and 'USD' are the same currency.

    - Each currency has a default minor-unit scale: JPY 0, USD 2, KWD 3, and a
      fallback of 2 for unknown codes.  Every TMoney is NORMALISED to its
      currency's scale on construction and after every arithmetic operation,
      using banker's rounding (rmHalfEven) — the recommended money default.
      So MoneyFromStr('1.005', 'USD') stores 1.00, and a JPY amount never
      carries a fraction.

    - Mismatched-currency arithmetic RAISES EMoneyMismatch.  Add, Subtract and
      Compare across different currencies are programming errors, not silent
      conversions (there is no exchange-rate concept here — that is a higher
      policy layer).

    - Immutable value semantics: every operation returns a fresh TMoney and
      never mutates Self.  Scaling by a quantity (Multiply) keeps the same
      currency and re-normalises to its scale.

  Construction uses free functions (MoneyFromStr / MoneyFromDecimal /
  MoneyFromInt / MoneyZero), following the Numerics.Decimal and DateUtils
  house style.  Queries and arithmetic are record methods. }

interface

uses
  SysUtils, Numerics.Decimal;

type
  { Base class for all errors raised by this unit. }
  EMoneyError = class(Exception);

  { Raised when an operation combines two TMoney values of different
    currencies (e.g. USD + JPY). }
  EMoneyMismatch = class(EMoneyError);

  { ------------------------------------------------------------------ }
  { TMoney — a decimal amount tagged with an ISO-4217 currency          }
  { ------------------------------------------------------------------ }

  { A monetary amount in a single currency.  See the unit header for the
    design rationale.  The amount is always held at the currency's default
    scale (banker's-rounded on every operation). }
  TMoney = record
    { The exact amount, normalised to the currency's default scale. }
    FAmount:   TDecimal;
    { ISO-4217 alphabetic currency code, upper-case (e.g. 'USD'). }
    FCurrency: string;

    { The amount as an exact TDecimal (at the currency scale).
      @returns the monetary amount. }
    function Amount: TDecimal;

    { The ISO-4217 currency code (upper-case).
      @returns the currency code string. }
    function CurrencyCode: string;

    { Tests whether the amount is exactly zero.
      @returns True iff the amount is zero. }
    function IsZero: Boolean;

    { Sign of the amount.
      @returns -1 if negative, 0 if zero, +1 if positive. }
    function Sign: Integer;

    { Sum of Self and B.  Both must be the same currency; the result is in that
      currency, normalised to its scale.
      @param B the amount to add.
      @returns Self + B.
      @raises EMoneyMismatch if the currencies differ. }
    function Add(const B: TMoney): TMoney;

    { Difference Self - B.  Both must be the same currency.
      @param B the amount to subtract.
      @returns Self - B.
      @raises EMoneyMismatch if the currencies differ. }
    function Subtract(const B: TMoney): TMoney;

    { Arithmetic negation (-Self), same currency and scale.
      @returns the amount with opposite sign. }
    function Negate: TMoney;

    { Scales the amount by a dimensionless TDecimal factor (e.g. unit price *
      quantity, or amount * tax-rate), re-normalising to the currency scale with
      banker's rounding.  The currency is preserved.
      @param Factor the multiplier.
      @returns Self * Factor at the currency scale. }
    function Multiply(const Factor: TDecimal): TMoney;

    { Scales the amount by an integer quantity.  Exact (no rounding needed
      beyond the existing scale).  The currency is preserved.
      @param Quantity the integer multiplier.
      @returns Self * Quantity. }
    function MultiplyInt(Quantity: Integer): TMoney;

    { Three-way comparison by amount.  Both must be the same currency.
      @param B the amount to compare against.
      @returns -1 if Self < B, 0 if equal, +1 if Self > B.
      @raises EMoneyMismatch if the currencies differ. }
    function Compare(const B: TMoney): Integer;

    { Value equality: same currency AND equal amount.  Unlike Compare, this does
      NOT raise on a currency mismatch — two amounts in different currencies are
      simply not equal.
      @param B the amount to compare against.
      @returns True iff same currency and equal amount. }
    function Equals(const B: TMoney): Boolean;

    { The bare amount as a plain decimal string at the currency scale, with no
      currency code (e.g. '19.99').  Never scientific notation.
      @returns the amount string. }
    function AmountString: string;

    { Amount followed by a space and the currency code (e.g. '19.99 USD').
      @returns the formatted monetary string. }
    function ToString: string;
  end;

{ ------------------------------------------------------------------ }
{ Construction (free functions, house style)                          }
{ ------------------------------------------------------------------ }

{ Builds a TMoney from a decimal literal string and a currency code.  The
  amount is parsed exactly (see DecFromStr) then normalised to the currency's
  default scale with banker's rounding.
  @param AAmount  the decimal literal (e.g. '19.99', '-0.005').
  @param ACurrency the ISO-4217 code (case-insensitive; stored upper-case).
  @returns the money value.
  @raises EDecimalParse if AAmount is malformed. }
function MoneyFromStr(const AAmount, ACurrency: string): TMoney;

{ Builds a TMoney from an existing TDecimal amount and a currency code.  The
  amount is normalised to the currency's default scale (banker's rounding).
  @param AAmount  the decimal amount.
  @param ACurrency the ISO-4217 code (case-insensitive; stored upper-case).
  @returns the money value. }
function MoneyFromDecimal(const AAmount: TDecimal; const ACurrency: string): TMoney;

{ Builds a TMoney from a whole-unit integer amount and a currency code
  (e.g. MoneyFromInt(5, 'USD') = 5.00 USD).
  @param AAmount  the whole-unit integer amount.
  @param ACurrency the ISO-4217 code (case-insensitive; stored upper-case).
  @returns the money value. }
function MoneyFromInt(AAmount: Integer; const ACurrency: string): TMoney;

{ A zero amount in the given currency, at the currency scale.
  @param ACurrency the ISO-4217 code (case-insensitive; stored upper-case).
  @returns zero money in that currency. }
function MoneyZero(const ACurrency: string): TMoney;

{ ------------------------------------------------------------------ }
{ Currency registry                                                   }
{ ------------------------------------------------------------------ }

{ The default minor-unit scale (number of fraction digits) for a currency code.
  Known: JPY 0, USD/EUR/GBP/AUD/CAD/CHF/CNY 2, KWD/BHD/OMR 3.  Unknown codes
  return the fallback scale 2.  The lookup is case-insensitive.
  @param ACurrency the ISO-4217 code.
  @returns the default fraction-digit count for that currency. }
function CurrencyScale(const ACurrency: string): Integer;

implementation

const
  { Fallback minor-unit scale for currencies the registry does not list. }
  cDefaultScale = 2;

function CurrencyScale(const ACurrency: string): Integer;
var
  C: string;
begin
  C := UpperCase(ACurrency);
  { Zero-decimal currencies. }
  if (C = 'JPY') or (C = 'KRW') or (C = 'CLP') or (C = 'ISK') or
     (C = 'VND') or (C = 'XAF') or (C = 'XOF') or (C = 'PYG') then
    Result := 0
  { Three-decimal currencies. }
  else if (C = 'KWD') or (C = 'BHD') or (C = 'OMR') or (C = 'TND') or
          (C = 'JOD') or (C = 'IQD') or (C = 'LYD') then
    Result := 3
  { Everything else (USD, EUR, GBP, ...) uses two. }
  else
    Result := cDefaultScale;
end;

{ Normalises ADec to ACurrency's scale with banker's rounding and pairs it with
  the upper-cased code.  Central constructor used by every public builder so the
  invariant "FAmount is always at the currency scale" holds in one place. }
function MakeMoney(const ADec: TDecimal; const ACurrency: string): TMoney;
var
  Code: string;
  Norm: TDecimal;
begin
  Code := UpperCase(ACurrency);
  Norm := ADec.RoundTo(CurrencyScale(Code), rmHalfEven);
  Result.FAmount := Norm;
  Result.FCurrency := Code;
end;

function MoneyFromStr(const AAmount, ACurrency: string): TMoney;
begin
  Result := MakeMoney(DecFromStr(AAmount), ACurrency);
end;

function MoneyFromDecimal(const AAmount: TDecimal; const ACurrency: string): TMoney;
begin
  Result := MakeMoney(AAmount, ACurrency);
end;

function MoneyFromInt(AAmount: Integer; const ACurrency: string): TMoney;
begin
  Result := MakeMoney(DecFromInt(AAmount), ACurrency);
end;

function MoneyZero(const ACurrency: string): TMoney;
begin
  Result := MakeMoney(DecFromInt(0), ACurrency);
end;

{ Raises EMoneyMismatch when A and B are different currencies.  AOp names the
  operation for the message. }
procedure RequireSameCurrency(const A, B: TMoney; const AOp: string);
begin
  if A.FCurrency <> B.FCurrency then
    raise EMoneyMismatch.Create('Numerics.Money: cannot ' + AOp +
      ' different currencies (' + A.FCurrency + ' and ' + B.FCurrency + ')');
end;

function TMoney.Amount: TDecimal;
begin
  Result := Self.FAmount;
end;

function TMoney.CurrencyCode: string;
begin
  Result := Self.FCurrency;
end;

function TMoney.IsZero: Boolean;
begin
  Result := Self.FAmount.IsZero();
end;

function TMoney.Sign: Integer;
begin
  Result := Self.FAmount.Sign();
end;

function TMoney.Add(const B: TMoney): TMoney;
var
  Sum: TDecimal;
begin
  RequireSameCurrency(Self, B, 'add');
  Sum := Self.FAmount.Add(B.FAmount);
  Result := MakeMoney(Sum, Self.FCurrency);
end;

function TMoney.Subtract(const B: TMoney): TMoney;
var
  Diff: TDecimal;
begin
  RequireSameCurrency(Self, B, 'subtract');
  Diff := Self.FAmount.Subtract(B.FAmount);
  Result := MakeMoney(Diff, Self.FCurrency);
end;

function TMoney.Negate: TMoney;
var
  Neg: TDecimal;
begin
  Neg := Self.FAmount.Negate();
  Result := MakeMoney(Neg, Self.FCurrency);
end;

function TMoney.Multiply(const Factor: TDecimal): TMoney;
var
  Prod: TDecimal;
begin
  Prod := Self.FAmount.Multiply(Factor);
  Result := MakeMoney(Prod, Self.FCurrency);
end;

function TMoney.MultiplyInt(Quantity: Integer): TMoney;
var
  Prod: TDecimal;
begin
  Prod := Self.FAmount.Multiply(DecFromInt(Quantity));
  Result := MakeMoney(Prod, Self.FCurrency);
end;

function TMoney.Compare(const B: TMoney): Integer;
begin
  RequireSameCurrency(Self, B, 'compare');
  Result := Self.FAmount.Compare(B.FAmount);
end;

function TMoney.Equals(const B: TMoney): Boolean;
begin
  if Self.FCurrency <> B.FCurrency then
    Result := False
  else
    Result := Self.FAmount.Equals(B.FAmount);
end;

function TMoney.AmountString: string;
begin
  Result := Self.FAmount.ToString();
end;

function TMoney.ToString: string;
begin
  Result := Self.FAmount.ToString() + ' ' + Self.FCurrency;
end;

end.
