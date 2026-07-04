{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Generics.Collections;

// Blaise RTL — generic collections (mirrors Delphi's System.Generics.Collections
// and FPC's Generics.Collections for source-level compatibility).
//
// NOTE: This file is compiled by the Blaise compiler, not FPC.

interface

type
  { Generic forward enumerator for TList<T>.  Holds a pointer to the list's
    backing buffer and the count at the time GetEnumerator was called.
    MoveNext advances the cursor; Current returns the element at the cursor. }
  TListEnumerator<T> = class
    FData:  ^T;
    FIndex: Integer;
    FCount: Integer;
    constructor Create(AData: ^T; ACount: Integer);
    function MoveNext: Boolean;
    function GetCurrent: T;
    property Current: T read GetCurrent;
  end;

  TList<T> = class
    FData:     ^T;
    FCount:    Integer;
    FCapacity: Integer;
    procedure Grow;
    procedure Add(Value: T);
    function  Get(AIndex: Integer): T;
    procedure SetItem(AIndex: Integer; Value: T);
    function  IndexOf(Value: T): Integer;
    procedure Delete(AIndex: Integer);
    procedure Clear;
    procedure Destroy;
    function  GetEnumerator: TListEnumerator<T>;
    property Count: Integer read FCount;
    { Default array property — enables List[i] for read and write. }
    property Items[AIndex: Integer]: T read Get write SetItem; default;
  end;

  { Generic LIFO stack backed by a dynamic array.  Push/Pop/Peek operate on
    the top of the stack; Count reflects the number of items currently held. }
  TStack<T> = class
    FData:     ^T;
    FCount:    Integer;
    FCapacity: Integer;
    procedure Grow;
    procedure Push(Value: T);
    function  Pop: T;
    function  Peek: T;
    procedure Clear;
    procedure Destroy;
    property Count: Integer read FCount;
  end;

  { Generic FIFO queue backed by a dynamic circular-buffer array.
    Enqueue appends to the tail; Dequeue removes from the head.
    The buffer doubles when full, preserving insertion order. }
  TQueue<T> = class
    FData:     ^T;
    FCount:    Integer;
    FCapacity: Integer;
    FHead:     Integer;
    FTail:     Integer;
    procedure Grow;
    procedure Enqueue(Value: T);
    function  Dequeue: T;
    function  Peek: T;
    procedure Clear;
    procedure Destroy;
    property Count: Integer read FCount;
  end;

  { Generic unordered set backed by a dynamic array.  Membership tests use a
    lazy hash index once the set is large enough (see GCHashOf); small sets
    keep the linear scan.  Include adds an element only if not already
    present; Exclude removes it. }
  TSet<T> = class
    FData:      ^T;
    FCount:     Integer;
    FCapacity:  Integer;
    FHashSlots: ^Integer;
    FHashCap:   Integer;
    procedure Grow;
    procedure HashInvalidate;
    procedure HashInsertIdx(AIdx: Integer);
    procedure HashRebuild;
    function  IndexOf(Value: T): Integer;
    procedure Include(Value: T);
    procedure Exclude(Value: T);
    function  Contains(Value: T): Boolean;
    procedure Clear;
    procedure Destroy;
    property Count: Integer read FCount;
  end;

  { Generic map interface: common contract for dictionary-like types. }
  IMap<K, V> = interface
    procedure Add(Key: K; Value: V);
    function  TryGetValue(Key: K; var Value: V): Boolean;
    function  ContainsKey(Key: K): Boolean;
    procedure Remove(Key: K);
    function  GetCount: Integer;
  end;

  { Generic dictionary backed by two parallel arrays (insertion-ordered
    storage).  Key lookup uses a lazy open-addressing hash index once the
    dictionary is large enough; small dictionaries keep the linear scan.
    Key equality uses the '=' operator on the monomorphized type (content
    equality for string keys); hashing dispatches through the GCHashOf
    overloads, so a key type needs a matching GCHashOf to instantiate. }
  TDictionary<K, V> = class(IMap<K, V>)
    FKeys:      ^K;
    FValues:    ^V;
    FCount:     Integer;
    FCapacity:  Integer;
    FHashSlots: ^Integer;
    FHashCap:   Integer;
    procedure Grow;
    procedure HashInvalidate;
    procedure HashInsertIdx(AIdx: Integer);
    procedure HashRebuild;
    function  FindKey(Key: K): Integer;
    procedure Add(Key: K; Value: V);
    function  GetItem(Key: K): V;
    procedure SetItem(Key: K; Value: V);
    function  TryGetValue(Key: K; var Value: V): Boolean;
    function  ContainsKey(Key: K): Boolean;
    procedure Remove(Key: K);
    function  GetCount: Integer;
    procedure Destroy;
    property Count: Integer read FCount;
    property Items[Key: K]: V read GetItem write SetItem; default;
  end;

  { Generic insertion-ordered map.  Entries are stored in the order they were
    first added; iteration and indexed access preserve that order.  Like
    TDictionary it uses linear-scan equality, so it is suitable for small maps
    where insertion order matters (e.g. preserving configuration file order,
    deterministic output). }
  TOrderedDictionary<K, V> = class(IMap<K, V>)
    FKeys:      ^K;
    FValues:    ^V;
    FCount:     Integer;
    FCapacity:  Integer;
    FHashSlots: ^Integer;
    FHashCap:   Integer;
    procedure Grow;
    procedure HashInvalidate;
    procedure HashInsertIdx(AIdx: Integer);
    procedure HashRebuild;
    function  FindKey(Key: K): Integer;
    procedure Add(Key: K; Value: V);
    function  GetItem(Key: K): V;
    procedure SetItem(Key: K; Value: V);
    function  TryGetValue(Key: K; var Value: V): Boolean;
    function  ContainsKey(Key: K): Boolean;
    procedure Remove(Key: K);
    function  GetKey(AIndex: Integer): K;
    function  GetValue(AIndex: Integer): V;
    function  GetCount: Integer;
    procedure Destroy;
    property Count: Integer read FCount;
    property Items[Key: K]: V read GetItem write SetItem; default;
    property Keys[Index: Integer]: K read GetKey;
    property Values[Index: Integer]: V read GetValue;
  end;

{ Key hashing for the generic containers.  Monomorphisation resolves
  GCHashOf(Key) against these overloads per instantiation, so each key type
  gets a content-appropriate hash: strings hash their bytes (matching the
  content semantics of '=' on strings), integers and pointers mix their
  value.  Instantiating a keyed container with a type that has no matching
  overload is a compile-time error — add an overload here for new key types. }
function GCHashOf(AValue: string): Integer; overload;
function GCHashOf(AValue: Integer): Integer; overload;
function GCHashOf(AValue: Int64): Integer; overload;
function GCHashOf(AValue: Pointer): Integer; overload;
function GCHashOf(AValue: Boolean): Integer; overload;

const
  { Below this size a linear scan beats building a hash table.  Interface
    visibility because generic bodies are analysed at their instantiation
    site. }
  GCHashThreshold = 16;

implementation

{ ------------------------------------------------------------------ }
{ GCHashOf — key hashing overloads                                     }
{ ------------------------------------------------------------------ }

function GCHashOf(AValue: string): Integer; overload;
var
  I: Integer;
begin
  { FNV-1a over the bytes; case-sensitive to match '=' on strings. }
  Result := -2128831035;   { FNV offset basis 2166136261 as signed 32-bit }
  for I := 0 to Length(AValue) - 1 do
    Result := (Result xor Ord(AValue[I])) * 16777619;
end;

function GCHashOf(AValue: Integer): Integer; overload;
begin
  { Knuth multiplicative mix (2654435761 as signed 32-bit). }
  Result := AValue * -1640531527;
end;

function GCHashOf(AValue: Int64): Integer; overload;
begin
  Result := Integer(AValue xor (AValue shr 32)) * -1640531527;
end;

function GCHashOf(AValue: Pointer): Integer; overload;
begin
  Result := GCHashOf(Int64(AValue));
end;

function GCHashOf(AValue: Boolean): Integer; overload;
begin
  if AValue then
    Result := 1
  else
    Result := 0;
end;

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
    Self.Grow();
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

procedure TList<T>.SetItem(AIndex: Integer; Value: T);
var
  Dest: ^T;
begin
  { The ^T := Value store carries the compiler's ARC discipline for a managed
    T — the previous element is released and the new one retained. }
  Dest  := Self.FData + AIndex * SizeOf(T);
  Dest^ := Value
end;

function TList<T>.IndexOf(Value: T): Integer;
var
  I:   Integer;
  Ptr: ^T;
begin
  Result := -1;
  I      := 0;
  while I < Self.FCount do
  begin
    Ptr := Self.FData + I * SizeOf(T);
    if Ptr^ = Value then
    begin
      Result := I;
      break
    end;
    I := I + 1
  end
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

function TList<T>.GetEnumerator: TListEnumerator<T>;
begin
  Result := TListEnumerator<T>.Create(Self.FData, Self.FCount)
end;

{ ------------------------------------------------------------------ }
{ TListEnumerator<T>                                                   }
{ ------------------------------------------------------------------ }

constructor TListEnumerator<T>.Create(AData: ^T; ACount: Integer);
begin
  Self.FData  := AData;
  Self.FIndex := -1;
  Self.FCount := ACount
end;

function TListEnumerator<T>.MoveNext: Boolean;
begin
  Self.FIndex := Self.FIndex + 1;
  Result      := Self.FIndex < Self.FCount
end;

function TListEnumerator<T>.GetCurrent: T;
var
  Ptr: ^T;
begin
  Ptr    := Self.FData + Self.FIndex * SizeOf(T);
  Result := Ptr^
end;

{ ------------------------------------------------------------------ }
{ TStack<T>                                                            }
{ ------------------------------------------------------------------ }

procedure TStack<T>.Grow;
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

procedure TStack<T>.Push(Value: T);
var
  Dest: ^T;
begin
  if Self.FCount = Self.FCapacity then
    Self.Grow();
  Dest        := Self.FData + Self.FCount * SizeOf(T);
  Dest^       := Value;
  Self.FCount := Self.FCount + 1
end;

function TStack<T>.Pop: T;
var
  Src: ^T;
begin
  Self.FCount := Self.FCount - 1;
  Src         := Self.FData + Self.FCount * SizeOf(T);
  Result      := Src^
end;

function TStack<T>.Peek: T;
var
  Src: ^T;
begin
  Src    := Self.FData + (Self.FCount - 1) * SizeOf(T);
  Result := Src^
end;

procedure TStack<T>.Clear;
begin
  Self.FCount := 0
end;

procedure TStack<T>.Destroy;
begin
  FreeMem(Self.FData);
  Self.FData     := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

{ ------------------------------------------------------------------ }
{ TQueue<T>                                                            }
{ ------------------------------------------------------------------ }

procedure TQueue<T>.Grow;
var
  NewCap: Integer;
  OldCap: Integer;
  NewData: ^T;
  I: Integer;
  Src: ^T;
  Dst: ^T;
begin
  OldCap  := Self.FCapacity;
  if OldCap = 0 then
    NewCap := 4
  else
    NewCap := OldCap * 2;
  NewData := GetMem(NewCap * SizeOf(T));
  ZeroMem(NewData, NewCap * SizeOf(T));
  I := 0;
  while I < Self.FCount do
  begin
    Src  := Self.FData + ((Self.FHead + I) mod OldCap) * SizeOf(T);
    Dst  := NewData + I * SizeOf(T);
    Dst^ := Src^;
    I    := I + 1
  end;
  FreeMem(Self.FData);
  Self.FData     := NewData;
  Self.FHead     := 0;
  Self.FTail     := Self.FCount;
  Self.FCapacity := NewCap
end;

procedure TQueue<T>.Enqueue(Value: T);
var
  Dest: ^T;
begin
  if Self.FCount = Self.FCapacity then
    Self.Grow();
  Dest        := Self.FData + Self.FTail * SizeOf(T);
  Dest^       := Value;
  Self.FTail  := (Self.FTail + 1) mod Self.FCapacity;
  Self.FCount := Self.FCount + 1
end;

function TQueue<T>.Dequeue: T;
var
  Src: ^T;
begin
  Src         := Self.FData + Self.FHead * SizeOf(T);
  Result      := Src^;
  Self.FHead  := (Self.FHead + 1) mod Self.FCapacity;
  Self.FCount := Self.FCount - 1
end;

function TQueue<T>.Peek: T;
var
  Src: ^T;
begin
  Src    := Self.FData + Self.FHead * SizeOf(T);
  Result := Src^
end;

procedure TQueue<T>.Clear;
begin
  Self.FCount := 0;
  Self.FHead  := 0;
  Self.FTail  := 0
end;

procedure TQueue<T>.Destroy;
begin
  FreeMem(Self.FData);
  Self.FData     := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0;
  Self.FHead     := 0;
  Self.FTail     := 0
end;

{ ------------------------------------------------------------------ }
{ TSet<T>                                                              }
{ ------------------------------------------------------------------ }

procedure TSet<T>.Grow;
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

procedure TSet<T>.HashInvalidate;
begin
  if Self.FHashSlots <> nil then
  begin
    FreeMem(Self.FHashSlots);
    Self.FHashSlots := nil;
  end;
  Self.FHashCap := 0;
end;

procedure TSet<T>.HashInsertIdx(AIdx: Integer);
var
  Slot:  Integer;
  SlotP: ^Integer;
  EPtr:  ^T;
begin
  EPtr := Self.FData + AIdx * SizeOf(T);
  Slot := GCHashOf(EPtr^) and (Self.FHashCap - 1);
  while True do
  begin
    SlotP := Self.FHashSlots + Slot * SizeOf(Integer);
    if SlotP^ = -1 then
    begin
      SlotP^ := AIdx;
      Exit;
    end;
    Slot := (Slot + 1) and (Self.FHashCap - 1);
  end;
end;

procedure TSet<T>.HashRebuild;
var
  Cap: Integer;
  I:   Integer;
  P:   ^Integer;
begin
  Cap := 16;
  while Cap < Self.FCount * 2 do
    Cap := Cap * 2;
  if Self.FHashSlots <> nil then
    FreeMem(Self.FHashSlots);
  Self.FHashSlots := GetMem(Cap * SizeOf(Integer));
  Self.FHashCap   := Cap;
  for I := 0 to Cap - 1 do
  begin
    P  := Self.FHashSlots + I * SizeOf(Integer);
    P^ := -1;
  end;
  for I := 0 to Self.FCount - 1 do
    Self.HashInsertIdx(I);
end;

function TSet<T>.IndexOf(Value: T): Integer;
var
  I:     Integer;
  Ptr:   ^T;
  Slot:  Integer;
  SlotP: ^Integer;
begin
  if Self.FCount >= GCHashThreshold then
  begin
    if Self.FHashCap = 0 then
      Self.HashRebuild();
    Slot := GCHashOf(Value) and (Self.FHashCap - 1);
    while True do
    begin
      SlotP := Self.FHashSlots + Slot * SizeOf(Integer);
      if SlotP^ = -1 then
        Exit(-1);
      Ptr := Self.FData + SlotP^ * SizeOf(T);
      if Ptr^ = Value then
        Exit(SlotP^);
      Slot := (Slot + 1) and (Self.FHashCap - 1);
    end;
  end;
  Result := -1;
  I      := 0;
  while I < Self.FCount do
  begin
    Ptr := Self.FData + I * SizeOf(T);
    if Ptr^ = Value then
    begin
      Result := I;
      break
    end;
    I := I + 1
  end
end;

procedure TSet<T>.Include(Value: T);
var
  Dest: ^T;
begin
  if Self.IndexOf(Value) >= 0 then
    Exit;
  if Self.FCount = Self.FCapacity then
    Self.Grow();
  Dest        := Self.FData + Self.FCount * SizeOf(T);
  Dest^       := Value;
  Self.FCount := Self.FCount + 1;
  if Self.FHashCap > 0 then
  begin
    if Self.FCount * 2 > Self.FHashCap then
      Self.HashInvalidate()
    else
      Self.HashInsertIdx(Self.FCount - 1);
  end;
end;

procedure TSet<T>.Exclude(Value: T);
var
  Idx: Integer;
  I:   Integer;
  Dst: ^T;
  Src: ^T;
begin
  Idx := Self.IndexOf(Value);
  if Idx < 0 then
    Exit;
  I := Idx;
  while I < Self.FCount - 1 do
  begin
    Dst  := Self.FData + I * SizeOf(T);
    Src  := Self.FData + (I + 1) * SizeOf(T);
    Dst^ := Src^;
    I    := I + 1
  end;
  Self.FCount := Self.FCount - 1;
  { Indexes shifted — rebuild lazily on the next lookup. }
  Self.HashInvalidate()
end;

function TSet<T>.Contains(Value: T): Boolean;
begin
  Result := Self.IndexOf(Value) >= 0
end;

procedure TSet<T>.Clear;
begin
  Self.FCount := 0;
  Self.HashInvalidate()
end;

procedure TSet<T>.Destroy;
begin
  Self.HashInvalidate();
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

procedure TDictionary<K, V>.HashInvalidate;
begin
  if Self.FHashSlots <> nil then
  begin
    FreeMem(Self.FHashSlots);
    Self.FHashSlots := nil;
  end;
  Self.FHashCap := 0;
end;

procedure TDictionary<K, V>.HashInsertIdx(AIdx: Integer);
var
  Slot:  Integer;
  SlotP: ^Integer;
  KPtr:  ^K;
begin
  KPtr := Self.FKeys + AIdx * SizeOf(K);
  Slot := GCHashOf(KPtr^) and (Self.FHashCap - 1);
  while True do
  begin
    SlotP := Self.FHashSlots + Slot * SizeOf(Integer);
    if SlotP^ = -1 then
    begin
      SlotP^ := AIdx;
      Exit;
    end;
    Slot := (Slot + 1) and (Self.FHashCap - 1);
  end;
end;

{ Keys are unique, so occupancy equals FCount; rebuilt at <= 50% load so
  an empty slot terminates every probe chain. }
procedure TDictionary<K, V>.HashRebuild;
var
  Cap: Integer;
  I:   Integer;
  P:   ^Integer;
begin
  Cap := 16;
  while Cap < Self.FCount * 2 do
    Cap := Cap * 2;
  if Self.FHashSlots <> nil then
    FreeMem(Self.FHashSlots);
  Self.FHashSlots := GetMem(Cap * SizeOf(Integer));
  Self.FHashCap   := Cap;
  for I := 0 to Cap - 1 do
  begin
    P  := Self.FHashSlots + I * SizeOf(Integer);
    P^ := -1;
  end;
  for I := 0 to Self.FCount - 1 do
    Self.HashInsertIdx(I);
end;

function TDictionary<K, V>.FindKey(Key: K): Integer;
var
  I:     Integer;
  Ptr:   ^K;
  Slot:  Integer;
  SlotP: ^Integer;
begin
  if Self.FCount >= GCHashThreshold then
  begin
    if Self.FHashCap = 0 then
      Self.HashRebuild();
    Slot := GCHashOf(Key) and (Self.FHashCap - 1);
    while True do
    begin
      SlotP := Self.FHashSlots + Slot * SizeOf(Integer);
      if SlotP^ = -1 then
        Exit(-1);
      Ptr := Self.FKeys + SlotP^ * SizeOf(K);
      if Ptr^ = Key then
        Exit(SlotP^);
      Slot := (Slot + 1) and (Self.FHashCap - 1);
    end;
  end;
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
      Self.Grow();
    KPtr  := Self.FKeys   + Self.FCount * SizeOf(K);
    VPtr  := Self.FValues + Self.FCount * SizeOf(V);
    KPtr^ := Key;
    VPtr^ := Value;
    Self.FCount := Self.FCount + 1;
    { Keep the hash live across appends; past 50% load drop it and let the
      next lookup rebuild at double size. }
    if Self.FHashCap > 0 then
    begin
      if Self.FCount * 2 > Self.FHashCap then
        Self.HashInvalidate()
      else
        Self.HashInsertIdx(Self.FCount - 1);
    end;
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
    Self.FCount := Self.FCount - 1;
    { Indexes shifted — rebuild lazily on the next lookup. }
    Self.HashInvalidate()
  end
end;

function TDictionary<K, V>.GetItem(Key: K): V;
var
  Idx:  Integer;
  VPtr: ^V;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    VPtr   := Self.FValues + Idx * SizeOf(V);
    Result := VPtr^
  end
  else
    Halt(1)
end;

procedure TDictionary<K, V>.SetItem(Key: K; Value: V);
begin
  Self.Add(Key, Value)
end;

function TDictionary<K, V>.GetCount: Integer;
begin
  Result := Self.FCount
end;

procedure TDictionary<K, V>.Destroy;
begin
  Self.HashInvalidate();
  FreeMem(Self.FKeys);
  FreeMem(Self.FValues);
  Self.FKeys     := nil;
  Self.FValues   := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

{ ------------------------------------------------------------------ }
{ TOrderedDictionary<K, V>                                             }
{ ------------------------------------------------------------------ }

procedure TOrderedDictionary<K, V>.Grow;
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

procedure TOrderedDictionary<K, V>.HashInvalidate;
begin
  if Self.FHashSlots <> nil then
  begin
    FreeMem(Self.FHashSlots);
    Self.FHashSlots := nil;
  end;
  Self.FHashCap := 0;
end;

procedure TOrderedDictionary<K, V>.HashInsertIdx(AIdx: Integer);
var
  Slot:  Integer;
  SlotP: ^Integer;
  KPtr:  ^K;
begin
  KPtr := Self.FKeys + AIdx * SizeOf(K);
  Slot := GCHashOf(KPtr^) and (Self.FHashCap - 1);
  while True do
  begin
    SlotP := Self.FHashSlots + Slot * SizeOf(Integer);
    if SlotP^ = -1 then
    begin
      SlotP^ := AIdx;
      Exit;
    end;
    Slot := (Slot + 1) and (Self.FHashCap - 1);
  end;
end;

procedure TOrderedDictionary<K, V>.HashRebuild;
var
  Cap: Integer;
  I:   Integer;
  P:   ^Integer;
begin
  Cap := 16;
  while Cap < Self.FCount * 2 do
    Cap := Cap * 2;
  if Self.FHashSlots <> nil then
    FreeMem(Self.FHashSlots);
  Self.FHashSlots := GetMem(Cap * SizeOf(Integer));
  Self.FHashCap   := Cap;
  for I := 0 to Cap - 1 do
  begin
    P  := Self.FHashSlots + I * SizeOf(Integer);
    P^ := -1;
  end;
  for I := 0 to Self.FCount - 1 do
    Self.HashInsertIdx(I);
end;

function TOrderedDictionary<K, V>.FindKey(Key: K): Integer;
var
  I:     Integer;
  Ptr:   ^K;
  Slot:  Integer;
  SlotP: ^Integer;
begin
  if Self.FCount >= GCHashThreshold then
  begin
    if Self.FHashCap = 0 then
      Self.HashRebuild();
    Slot := GCHashOf(Key) and (Self.FHashCap - 1);
    while True do
    begin
      SlotP := Self.FHashSlots + Slot * SizeOf(Integer);
      if SlotP^ = -1 then
        Exit(-1);
      Ptr := Self.FKeys + SlotP^ * SizeOf(K);
      if Ptr^ = Key then
        Exit(SlotP^);
      Slot := (Slot + 1) and (Self.FHashCap - 1);
    end;
  end;
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

procedure TOrderedDictionary<K, V>.Add(Key: K; Value: V);
var
  Idx:  Integer;
  KPtr: ^K;
  VPtr: ^V;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    VPtr  := Self.FValues + Idx * SizeOf(V);
    VPtr^ := Value
  end
  else
  begin
    if Self.FCount = Self.FCapacity then
      Self.Grow();
    KPtr  := Self.FKeys   + Self.FCount * SizeOf(K);
    VPtr  := Self.FValues + Self.FCount * SizeOf(V);
    KPtr^ := Key;
    VPtr^ := Value;
    Self.FCount := Self.FCount + 1;
    if Self.FHashCap > 0 then
    begin
      if Self.FCount * 2 > Self.FHashCap then
        Self.HashInvalidate()
      else
        Self.HashInsertIdx(Self.FCount - 1);
    end;
  end
end;

function TOrderedDictionary<K, V>.TryGetValue(Key: K; var Value: V): Boolean;
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

function TOrderedDictionary<K, V>.ContainsKey(Key: K): Boolean;
begin
  Result := Self.FindKey(Key) >= 0
end;

procedure TOrderedDictionary<K, V>.Remove(Key: K);
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
    Self.FCount := Self.FCount - 1;
    { Indexes shifted — rebuild lazily on the next lookup. }
    Self.HashInvalidate()
  end
end;

function TOrderedDictionary<K, V>.GetKey(AIndex: Integer): K;
var
  Ptr: ^K;
begin
  Ptr    := Self.FKeys + AIndex * SizeOf(K);
  Result := Ptr^
end;

function TOrderedDictionary<K, V>.GetValue(AIndex: Integer): V;
var
  Ptr: ^V;
begin
  Ptr    := Self.FValues + AIndex * SizeOf(V);
  Result := Ptr^
end;

function TOrderedDictionary<K, V>.GetItem(Key: K): V;
var
  Idx:  Integer;
  VPtr: ^V;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    VPtr   := Self.FValues + Idx * SizeOf(V);
    Result := VPtr^
  end
  else
    Halt(1)
end;

procedure TOrderedDictionary<K, V>.SetItem(Key: K; Value: V);
begin
  Self.Add(Key, Value)
end;

function TOrderedDictionary<K, V>.GetCount: Integer;
begin
  Result := Self.FCount
end;

procedure TOrderedDictionary<K, V>.Destroy;
begin
  Self.HashInvalidate();
  FreeMem(Self.FKeys);
  FreeMem(Self.FValues);
  Self.FKeys     := nil;
  Self.FValues   := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

end.
