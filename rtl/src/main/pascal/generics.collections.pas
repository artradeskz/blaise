{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

unit Generics.Collections;

// Blaise RTL — generic collections (mirrors Delphi's System.Generics.Collections
// and FPC's Generics.Collections for source-level compatibility).
//
// NOTE: This file is compiled by the Blaise compiler, not FPC.

interface

type
  TList<T> = class
    FData:     ^T;
    FCount:    Integer;
    FCapacity: Integer;
    procedure Grow;
    procedure Add(Value: T);
    function  Get(AIndex: Integer): T;
    procedure Delete(AIndex: Integer);
    procedure Clear;
    procedure Destroy;
    property Count: Integer read FCount;
  end;

  { Generic dictionary: linear-scan key table backed by two parallel arrays.
    Key equality uses the '=' operator on the monomorphized type, so integer,
    boolean and pointer key types work out of the box.  String keys require
    content-aware equality which is deferred. }
  TDictionary<K, V> = class
    FKeys:     ^K;
    FValues:   ^V;
    FCount:    Integer;
    FCapacity: Integer;
    procedure Grow;
    function  FindKey(Key: K): Integer;
    procedure Add(Key: K; Value: V);
    function  TryGetValue(Key: K; var Value: V): Boolean;
    function  ContainsKey(Key: K): Boolean;
    procedure Remove(Key: K);
    procedure Destroy;
    property Count: Integer read FCount;
  end;

implementation

{ ------------------------------------------------------------------ }
{ TList<T>                                                             }
{ ------------------------------------------------------------------ }

procedure TList<T>.Grow;
var
  NewCap: Integer;
  OldCap: Integer;
begin
  OldCap := Self.FCapacity;
  if OldCap = 0 then
    NewCap := 4
  else
    NewCap := OldCap * 2;
  Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(T));
  ZeroMem(Self.FData + OldCap * SizeOf(T), (NewCap - OldCap) * SizeOf(T));
  Self.FCapacity := NewCap
end;

procedure TList<T>.Add(Value: T);
var
  Dest: ^T;
begin
  if Self.FCount = Self.FCapacity then
    Self.Grow;
  Dest        := Self.FData + Self.FCount * SizeOf(T);
  Dest^       := Value;
  Self.FCount := Self.FCount + 1
end;

function TList<T>.Get(AIndex: Integer): T;
var
  Src: ^T;
begin
  Src    := Self.FData + AIndex * SizeOf(T);
  Result := Src^
end;

procedure TList<T>.Delete(AIndex: Integer);
var
  Src: ^T;
  Dst: ^T;
  I:   Integer;
begin
  I := AIndex;
  while I < Self.FCount - 1 do
  begin
    Dst  := Self.FData + I * SizeOf(T);
    Src  := Self.FData + (I + 1) * SizeOf(T);
    Dst^ := Src^;
    I    := I + 1
  end;
  Self.FCount := Self.FCount - 1
end;

procedure TList<T>.Clear;
begin
  Self.FCount := 0
end;

procedure TList<T>.Destroy;
begin
  FreeMem(Self.FData);
  Self.FData     := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

{ ------------------------------------------------------------------ }
{ TDictionary<K, V>                                                    }
{ ------------------------------------------------------------------ }

procedure TDictionary<K, V>.Grow;
var
  NewCap: Integer;
  OldCap: Integer;
begin
  OldCap := Self.FCapacity;
  if OldCap = 0 then
    NewCap := 8
  else
    NewCap := OldCap * 2;
  Self.FKeys     := ReallocMem(Self.FKeys,   NewCap * SizeOf(K));
  ZeroMem(Self.FKeys + OldCap * SizeOf(K), (NewCap - OldCap) * SizeOf(K));
  Self.FValues   := ReallocMem(Self.FValues, NewCap * SizeOf(V));
  ZeroMem(Self.FValues + OldCap * SizeOf(V), (NewCap - OldCap) * SizeOf(V));
  Self.FCapacity := NewCap
end;

function TDictionary<K, V>.FindKey(Key: K): Integer;
var
  I:   Integer;
  Ptr: ^K;
begin
  Result := -1;
  I      := 0;
  while I < Self.FCount do
  begin
    Ptr := Self.FKeys + I * SizeOf(K);
    if Ptr^ = Key then
    begin
      Result := I;
      break
    end;
    I := I + 1
  end
end;

procedure TDictionary<K, V>.Add(Key: K; Value: V);
var
  Idx:  Integer;
  KPtr: ^K;
  VPtr: ^V;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    { Update existing entry }
    VPtr  := Self.FValues + Idx * SizeOf(V);
    VPtr^ := Value
  end
  else
  begin
    { Insert new entry }
    if Self.FCount = Self.FCapacity then
      Self.Grow;
    KPtr  := Self.FKeys   + Self.FCount * SizeOf(K);
    VPtr  := Self.FValues + Self.FCount * SizeOf(V);
    KPtr^ := Key;
    VPtr^ := Value;
    Self.FCount := Self.FCount + 1
  end
end;

function TDictionary<K, V>.TryGetValue(Key: K; var Value: V): Boolean;
var
  Idx:  Integer;
  VPtr: ^V;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    VPtr   := Self.FValues + Idx * SizeOf(V);
    Value  := VPtr^;
    Result := True
  end
  else
    Result := False
end;

function TDictionary<K, V>.ContainsKey(Key: K): Boolean;
begin
  Result := Self.FindKey(Key) >= 0
end;

procedure TDictionary<K, V>.Remove(Key: K);
var
  Idx:  Integer;
  I:    Integer;
  KDst: ^K;
  KSrc: ^K;
  VDst: ^V;
  VSrc: ^V;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    { Compact: shift entries after Idx one slot left }
    I := Idx;
    while I < Self.FCount - 1 do
    begin
      KDst  := Self.FKeys   + I * SizeOf(K);
      KSrc  := Self.FKeys   + (I + 1) * SizeOf(K);
      VDst  := Self.FValues + I * SizeOf(V);
      VSrc  := Self.FValues + (I + 1) * SizeOf(V);
      KDst^ := KSrc^;
      VDst^ := VSrc^;
      I     := I + 1
    end;
    Self.FCount := Self.FCount - 1
  end
end;

procedure TDictionary<K, V>.Destroy;
begin
  FreeMem(Self.FKeys);
  FreeMem(Self.FValues);
  Self.FKeys     := nil;
  Self.FValues   := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

end.
