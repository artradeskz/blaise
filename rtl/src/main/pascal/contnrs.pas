{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

unit Contnrs;

// Blaise RTL — Contnrs unit.
//
// Provides TObjectList, matching the FPC contnrs unit layout so that
// compiler source using "uses Contnrs" and TObjectList works unchanged.

interface

type
  { ------------------------------------------------------------------ }
  { TObjectList                                                          }
  { ------------------------------------------------------------------ }

  TObjectList = class
    FData:        ^Pointer;
    FCount:       Integer;
    FCapacity:    Integer;
    FOwnsObjects: Boolean;
    procedure Grow;
    constructor Create(AOwnsObjects: Boolean);
    procedure   Destroy;
    function    Add(AObject: Pointer): Integer;
    function    Get(AIndex: Integer): Pointer;
    procedure   Put(AIndex: Integer; AObject: Pointer);
    function    IndexOf(AObject: Pointer): Integer;
    procedure   Delete(AIndex: Integer);
    function    Extract(AIndex: Integer): Pointer;
    procedure   Clear;
    property Count: Integer read FCount;
    property Items[Index: Integer]: Pointer read Get write Put;
  end;

implementation

{ ================================================================== }
{ TObjectList                                                          }
{ ================================================================== }

procedure TObjectList.Grow;
var
  NewCap: Integer;
begin
  if Self.FCapacity = 0 then
    NewCap := 4
  else
    NewCap := Self.FCapacity * 2;
  Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(Pointer));
  Self.FCapacity := NewCap
end;

constructor TObjectList.Create(AOwnsObjects: Boolean);
begin
  Self.FOwnsObjects := AOwnsObjects
end;

procedure TObjectList.Destroy;
begin
  FreeMem(Self.FData);
  Self.FData     := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

function TObjectList.Add(AObject: Pointer): Integer;
var
  Dest: ^Pointer;
begin
  if Self.FCount = Self.FCapacity then
    Self.Grow;
  Dest        := Self.FData + Self.FCount * SizeOf(Pointer);
  Dest^       := AObject;
  Self.FCount := Self.FCount + 1;
  Result      := Self.FCount - 1
end;

function TObjectList.Get(AIndex: Integer): Pointer;
var
  Src: ^Pointer;
begin
  Src    := Self.FData + AIndex * SizeOf(Pointer);
  Result := Src^
end;

procedure TObjectList.Put(AIndex: Integer; AObject: Pointer);
var
  Dest: ^Pointer;
begin
  Dest  := Self.FData + AIndex * SizeOf(Pointer);
  Dest^ := AObject
end;

function TObjectList.IndexOf(AObject: Pointer): Integer;
var
  I:   Integer;
  Src: ^Pointer;
begin
  I      := 0;
  Result := -1;
  while I < Self.FCount do
  begin
    Src := Self.FData + I * SizeOf(Pointer);
    if Src^ = AObject then
    begin
      Result := I;
      break
    end;
    I := I + 1
  end
end;

procedure TObjectList.Delete(AIndex: Integer);
var
  I:   Integer;
  Dst: ^Pointer;
  Src: ^Pointer;
begin
  I := AIndex;
  while I < Self.FCount - 1 do
  begin
    Dst  := Self.FData + I * SizeOf(Pointer);
    Src  := Self.FData + (I + 1) * SizeOf(Pointer);
    Dst^ := Src^;
    I    := I + 1
  end;
  Self.FCount := Self.FCount - 1
end;

procedure TObjectList.Clear;
begin
  Self.FCount := 0
end;

function TObjectList.Extract(AIndex: Integer): Pointer;
var
  I:   Integer;
  Src: ^Pointer;
  Dst: ^Pointer;
begin
  Src    := Self.FData + AIndex * SizeOf(Pointer);
  Result := Src^;
  I := AIndex;
  while I < Self.FCount - 1 do
  begin
    Dst  := Self.FData + I * SizeOf(Pointer);
    Src  := Self.FData + (I + 1) * SizeOf(Pointer);
    Dst^ := Src^;
    I    := I + 1
  end;
  Self.FCount := Self.FCount - 1
end;

end.
