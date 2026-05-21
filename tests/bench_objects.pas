{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

program BenchObjects;

{ Temporary micro-benchmark — TObjectList vs TList<TObject>.

  For each container we measure:
    1. Bulk insert      — 1_000_000 Adds of fresh TItem instances
    2. Sequential read  — Get(i) + read FValue for every index
    3. Random read      — 1_000_000 indexed reads in a pseudo-random pattern
    4. Linear search    — 1000 lookups on the 1M-item list (we look for
                          objects we know are present; pointer equality)
    5. for..in iterate  — checksum across all items (TObjectList only;
                          TList<TObject>.GetEnumerator returns Current as
                          the element type which round-trips fine here)

  All times are wall-clock milliseconds via TInstant.Subtract.
  Run from the project root:

    compiler/target/blaise --source tests/bench_objects.pas --output /tmp/bench_objects
    /tmp/bench_objects

  NOTE: split from tests/bench_strings.pas — see that file's header for
  the compiler limitation that forces the split. }

uses
  Contnrs,
  Generics.Collections,
  DateUtils,
  SysUtils;

const
  N_BIG    = 1000000;
  N_RANDOM = 1000000;
  N_SEARCH =    1000;

type
  TItem = class
    FValue: Integer;
  end;

var
  GRand: Integer;

procedure SeedRand(S: Integer);
begin
  GRand := S
end;

function NextRand: Integer;
begin
  GRand  := GRand * 1103515245 + 12345;
  Result := (GRand shr 16) and $7FFFFFFF
end;

function ElapsedMs(Start: TInstant): Int64;
var
  Now: TInstant;
  D:   TDuration;
begin
  Now    := InstantNow;
  D      := Now.Subtract(Start);
  Result := D.TotalMilliseconds
end;

function PadRight(const S: string; Width: Integer): string;
var
  N: Integer;
begin
  Result := S;
  N      := Width - Length(S);
  while N > 0 do
  begin
    Result := Result + ' ';
    N      := N - 1
  end
end;

function PadLeft(const S: string; Width: Integer): string;
var
  N: Integer;
begin
  Result := S;
  N      := Width - Length(S);
  while N > 0 do
  begin
    Result := ' ' + Result;
    N      := N - 1
  end
end;

procedure Report(const ALabel: string; AMs: Int64);
begin
  WriteLn('  ' + PadRight(ALabel, 50) + PadLeft(IntToStr(AMs), 6) + ' ms')
end;

procedure BenchTObjectList;
var
  OL:     TObjectList;
  I:      Integer;
  Idx:    Integer;
  T0:     TInstant;
  Item:   TItem;
  Sum:    Int64;
  Hits:   Integer;
  Needle: TItem;
begin
  WriteLn('TObjectList(OwnsObjects=True)');

  { 1. Bulk insert }
  OL := TObjectList.Create(True);
  T0 := InstantNow;
  for I := 0 to N_BIG - 1 do
  begin
    Item := TItem.Create;
    Item.FValue := I;
    OL.Add(Item)
  end;
  Report('insert 1_000_000', ElapsedMs(T0));

  { 2. Sequential read }
  T0  := InstantNow;
  Sum := 0;
  for I := 0 to OL.Count - 1 do
  begin
    Item := TItem(OL.Get(I));
    Sum  := Sum + Item.FValue
  end;
  Report('sequential Get(i) x Count (sum=' + IntToStr(Sum) + ')',
    ElapsedMs(T0));

  { 3. Random read }
  SeedRand(42);
  T0  := InstantNow;
  Sum := 0;
  for I := 0 to N_RANDOM - 1 do
  begin
    Idx  := NextRand mod N_BIG;
    Item := TItem(OL.Get(Idx));
    Sum  := Sum + Item.FValue
  end;
  Report('random  Get(i)  x 1_000_000', ElapsedMs(T0));

  { 4. IndexOf — search for known objects (pointer-equality match) }
  SeedRand(7);
  T0   := InstantNow;
  Hits := 0;
  for I := 0 to N_SEARCH - 1 do
  begin
    Idx    := NextRand mod N_BIG;
    Needle := TItem(OL.Get(Idx));
    if OL.IndexOf(Needle) >= 0 then
      Hits := Hits + 1
  end;
  Report('IndexOf x 1000 (hits=' + IntToStr(Hits) + ')',
    ElapsedMs(T0));

  OL.Free;
  WriteLn
end;

procedure BenchGenericListObject;
var
  L:      TList<TObject>;
  I:      Integer;
  J:      Integer;
  Idx:    Integer;
  T0:     TInstant;
  Obj:    TObject;
  Item:   TItem;
  Sum:    Int64;
  Hits:   Integer;
  Needle: TObject;
  Found:  Boolean;
begin
  WriteLn('TList<TObject> (manual Free)');

  { 1. Bulk insert }
  L  := TList<TObject>.Create;
  T0 := InstantNow;
  for I := 0 to N_BIG - 1 do
  begin
    Item := TItem.Create;
    Item.FValue := I;
    L.Add(Item)
  end;
  Report('insert 1_000_000', ElapsedMs(T0));

  { 2. Sequential read }
  T0  := InstantNow;
  Sum := 0;
  for I := 0 to L.Count - 1 do
  begin
    Item := TItem(L.Get(I));
    Sum  := Sum + Item.FValue
  end;
  Report('sequential Get(i) x Count (sum=' + IntToStr(Sum) + ')',
    ElapsedMs(T0));

  { 3. Random read }
  SeedRand(42);
  T0  := InstantNow;
  Sum := 0;
  for I := 0 to N_RANDOM - 1 do
  begin
    Idx  := NextRand mod N_BIG;
    Item := TItem(L.Get(Idx));
    Sum  := Sum + Item.FValue
  end;
  Report('random  Get(i)  x 1_000_000', ElapsedMs(T0));

  { 4. Hand-rolled IndexOf — pointer equality }
  SeedRand(7);
  T0   := InstantNow;
  Hits := 0;
  for I := 0 to N_SEARCH - 1 do
  begin
    Idx    := NextRand mod N_BIG;
    Needle := L.Get(Idx);
    Found  := False;
    for J := 0 to L.Count - 1 do
      if L.Get(J) = Needle then
      begin
        Found := True;
        break
      end;
    if Found then
      Hits := Hits + 1
  end;
  Report('hand-rolled scan x 1000 (hits=' + IntToStr(Hits) + ')',
    ElapsedMs(T0));

  { Manually release each item since TList<TObject> is not owning. }
  for I := 0 to L.Count - 1 do
  begin
    Obj := L.Get(I);
    Obj.Free
  end;
  L.Free;
  WriteLn
end;

begin
  WriteLn('=== Blaise list micro-benchmark - objects ===');
  WriteLn('N_BIG=' + IntToStr(N_BIG) +
          '  N_RANDOM=' + IntToStr(N_RANDOM) +
          '  N_SEARCH=' + IntToStr(N_SEARCH));
  WriteLn;
  BenchTObjectList;
  BenchGenericListObject
end.
