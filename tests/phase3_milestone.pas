{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

program Phase3Milestone;

{ Phase 3 milestone: exercises TList<Integer> and TDictionary<string,Integer>.
  Must produce correct output and zero valgrind leaks. }

type
  TIntList = class
    FData:     ^Integer;
    FCount:    Integer;
    FCapacity: Integer;
    procedure Grow;
    procedure Add(Value: Integer);
    function  Get(AIndex: Integer): Integer;
    procedure Delete(AIndex: Integer);
    procedure Destroy;
    property Count: Integer read FCount;
  end;

  TStrIntDict = class
    FKeys:     ^string;
    FValues:   ^Integer;
    FCount:    Integer;
    FCapacity: Integer;
    procedure Grow;
    function  FindKey(Key: string): Integer;
    procedure Add(Key: string; Value: Integer);
    function  TryGetValue(Key: string; var Value: Integer): Boolean;
    function  ContainsKey(Key: string): Boolean;
    procedure Remove(Key: string);
    procedure Destroy;
    property Count: Integer read FCount;
  end;

procedure TIntList.Grow;
var
  NewCap: Integer;
begin
  if Self.FCapacity = 0 then
    NewCap := 4
  else
    NewCap := Self.FCapacity * 2;
  Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(Integer));
  Self.FCapacity := NewCap
end;

procedure TIntList.Add(Value: Integer);
var
  Dest: ^Integer;
begin
  if Self.FCount = Self.FCapacity then
    Self.Grow;
  Dest        := Self.FData + Self.FCount * SizeOf(Integer);
  Dest^       := Value;
  Self.FCount := Self.FCount + 1
end;

function TIntList.Get(AIndex: Integer): Integer;
var
  Src: ^Integer;
begin
  Src    := Self.FData + AIndex * SizeOf(Integer);
  Result := Src^
end;

procedure TIntList.Delete(AIndex: Integer);
var
  Src: ^Integer;
  Dst: ^Integer;
  I:   Integer;
begin
  I := AIndex;
  while I < Self.FCount - 1 do
  begin
    Dst  := Self.FData + I * SizeOf(Integer);
    Src  := Self.FData + (I + 1) * SizeOf(Integer);
    Dst^ := Src^;
    I    := I + 1
  end;
  Self.FCount := Self.FCount - 1
end;

procedure TIntList.Destroy;
begin
  FreeMem(Self.FData);
  Self.FData     := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

procedure TStrIntDict.Grow;
var
  NewCap: Integer;
  OldCap: Integer;
begin
  OldCap := Self.FCapacity;
  if OldCap = 0 then
    NewCap := 8
  else
    NewCap := OldCap * 2;
  Self.FKeys   := ReallocMem(Self.FKeys,   NewCap * SizeOf(string));
  { Zero-init new string slots so ARC Release of "old" value is safe }
  ZeroMem(Self.FKeys + OldCap * SizeOf(string),
          (NewCap - OldCap) * SizeOf(string));
  Self.FValues := ReallocMem(Self.FValues, NewCap * SizeOf(Integer));
  Self.FCapacity := NewCap
end;

function TStrIntDict.FindKey(Key: string): Integer;
var
  I:   Integer;
  Ptr: ^string;
begin
  Result := -1;
  I      := 0;
  while I < Self.FCount do
  begin
    Ptr := Self.FKeys + I * SizeOf(string);
    if Ptr^ = Key then
    begin
      Result := I;
      break
    end;
    I := I + 1
  end
end;

procedure TStrIntDict.Add(Key: string; Value: Integer);
var
  Idx:  Integer;
  KPtr: ^string;
  VPtr: ^Integer;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    VPtr  := Self.FValues + Idx * SizeOf(Integer);
    VPtr^ := Value
  end
  else
  begin
    if Self.FCount = Self.FCapacity then
      Self.Grow;
    KPtr  := Self.FKeys   + Self.FCount * SizeOf(string);
    VPtr  := Self.FValues + Self.FCount * SizeOf(Integer);
    KPtr^ := Key;
    VPtr^ := Value;
    Self.FCount := Self.FCount + 1
  end
end;

function TStrIntDict.TryGetValue(Key: string; var Value: Integer): Boolean;
var
  Idx:  Integer;
  VPtr: ^Integer;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    VPtr   := Self.FValues + Idx * SizeOf(Integer);
    Value  := VPtr^;
    Result := True
  end
  else
    Result := False
end;

function TStrIntDict.ContainsKey(Key: string): Boolean;
begin
  Result := Self.FindKey(Key) >= 0
end;

procedure TStrIntDict.Remove(Key: string);
var
  Idx:  Integer;
  I:    Integer;
  KDst: ^string;
  KSrc: ^string;
  VDst: ^Integer;
  VSrc: ^Integer;
begin
  Idx := Self.FindKey(Key);
  if Idx >= 0 then
  begin
    I := Idx;
    while I < Self.FCount - 1 do
    begin
      KDst  := Self.FKeys   + I * SizeOf(string);
      KSrc  := Self.FKeys   + (I + 1) * SizeOf(string);
      VDst  := Self.FValues + I * SizeOf(Integer);
      VSrc  := Self.FValues + (I + 1) * SizeOf(Integer);
      KDst^ := KSrc^;
      VDst^ := VSrc^;
      I     := I + 1
    end;
    { Release the duplicate last string slot left behind by the shift }
    KDst := Self.FKeys + (Self.FCount - 1) * SizeOf(string);
    KDst^ := nil;
    Self.FCount := Self.FCount - 1
  end
end;

procedure TStrIntDict.Destroy;
var
  I:   Integer;
  Ptr: ^string;
begin
  { Release all stored strings before freeing the backing store }
  I := 0;
  while I < Self.FCount do
  begin
    Ptr  := Self.FKeys + I * SizeOf(string);
    Ptr^ := nil;
    I    := I + 1
  end;
  FreeMem(Self.FKeys);
  FreeMem(Self.FValues);
  Self.FKeys     := nil;
  Self.FValues   := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

var
  List:  TIntList;
  Dict:  TStrIntDict;
  V:     Integer;
  Found: Boolean;

begin
  { --- TList<Integer> --- }
  List := TIntList.Create;
  List.Add(10);
  List.Add(20);
  List.Add(30);
  List.Add(40);
  List.Add(50);

  WriteLn('list.count=', List.Count);    { 5 }
  WriteLn('list[0]=', List.Get(0));      { 10 }
  WriteLn('list[4]=', List.Get(4));      { 50 }

  List.Delete(1);
  WriteLn('count_after_delete=', List.Count);    { 4 }
  WriteLn('list[1]_after_delete=', List.Get(1)); { 30 }

  List.Free;

  { --- TDictionary<string,Integer> --- }
  Dict := TStrIntDict.Create;
  Dict.Add('alpha', 1);
  Dict.Add('beta',  2);
  Dict.Add('gamma', 3);
  Dict.Add('delta', 4);

  WriteLn('dict.count=', Dict.Count);     { 4 }

  Found := Dict.TryGetValue('beta', V);
  WriteLn('beta=', V);                    { 2 }

  Found := Dict.ContainsKey('gamma');
  WriteLn('has_gamma=', Found);           { 1 }

  Dict.Add('beta', 99);
  Found := Dict.TryGetValue('beta', V);
  WriteLn('beta_after_update=', V);       { 99 }

  Dict.Remove('alpha');
  WriteLn('count_after_remove=', Dict.Count);  { 3 }
  Found := Dict.ContainsKey('alpha');
  WriteLn('has_alpha_after_remove=', Found);   { 0 }

  Dict.Free
end.
