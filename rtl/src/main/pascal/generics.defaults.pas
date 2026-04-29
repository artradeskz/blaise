{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

unit Generics.Defaults;

// Blaise RTL — generic comparison and equality interfaces.
// Mirrors FPC's Generics.Defaults and Delphi's System.Generics.Defaults for
// source-level compatibility.
//
// NOTE: This file is compiled by the Blaise compiler, not FPC.

interface

type
  { Equality comparison: Equals returns True iff A = B;
    GetHashCode returns a hash suitable for use in hash tables. }
  IEqualityComparer<T> = interface
    function Equals(A, B: T): Boolean;
    function GetHashCode(Value: T): Integer;
  end;

  { Ordering comparison: Compare returns negative if A < B,
    zero if A = B, positive if A > B. }
  IComparer<T> = interface
    function Compare(A, B: T): Integer;
  end;

  { Concrete equality comparer for Integer }
  TIntegerEqualityComparer = class(IEqualityComparer<Integer>)
    function Equals(A, B: Integer): Boolean;
    function GetHashCode(Value: Integer): Integer;
  end;

  { Concrete ordering comparer for Integer }
  TIntegerComparer = class(IComparer<Integer>)
    function Compare(A, B: Integer): Integer;
  end;

implementation

function TIntegerEqualityComparer.Equals(A, B: Integer): Boolean;
begin
  Result := A = B
end;

function TIntegerEqualityComparer.GetHashCode(Value: Integer): Integer;
begin
  Result := Value
end;

function TIntegerComparer.Compare(A, B: Integer): Integer;
begin
  if A < B then
    Result := -1
  else if A > B then
    Result := 1
  else
    Result := 0
end;

end.
