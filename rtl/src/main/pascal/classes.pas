{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

unit Classes;

// Blaise RTL — Classes unit.
//
// Provides TStringList with a method-based API compatible with the Blaise
// compiler source for self-hosting.  TObjectList has been moved to the
// Contnrs unit to match FPC's layout.
//
// Design notes:
//   - TObjectList has been moved to the Contnrs unit (uses Contnrs).
//   - TDuplicates is replaced by Integer constants: dupAccept=0, dupIgnore=1,
//     dupError=2 (enums are not yet supported in Blaise).
//   - TStringList stores strings as ^string; ARC is emitted by the compiler
//     for pointer-dereference writes (EmitPointerWrite). ZeroMem is used to
//     zero-initialise newly grown string slots so no garbage is ever released.
//   - Text property: getter = GetText (lines joined by #10, no trailing newline);
//     setter = Clear + SplitIntoList(AText, Ord(#10), Self).
//   - LoadFromFile/SaveToFile use the ReadFile/WriteFile built-ins.

interface

const
  dupAccept = 0;
  dupIgnore = 1;
  dupError  = 2;

type
  { ------------------------------------------------------------------ }
  { TStringList                                                          }
  { ------------------------------------------------------------------ }

  TStringList = class
    FStrings:       ^string;
    FObjects:       ^Pointer;
    FCount:         Integer;
    FCapacity:      Integer;
    FCaseSensitive: Boolean;
    FSorted:        Boolean;
    FDuplicates:    Integer;
    procedure Grow;
    function  Compare(S1: string; S2: string): Integer;
    function  FindSorted(S: string; var Idx: Integer): Boolean;
    constructor Create;
    procedure   Destroy;
    function    Add(S: string): Integer;
    procedure   AddObject(S: string; AObject: Pointer);
    function    Find(S: string; var Index: Integer): Boolean;
    function    IndexOf(S: string): Integer;
    function    Get(AIndex: Integer): string;
    procedure   Put(AIndex: Integer; S: string);
    function    GetObject(AIndex: Integer): Pointer;
    procedure   SetObject(AIndex: Integer; AObject: Pointer);
    procedure   Delete(AIndex: Integer);
    procedure   Clear;
    procedure   Insert(AIndex: Integer; S: string);
    procedure   AddStrings(ASource: TStringList);
    function    GetText: string;
    procedure   SetText(AText: string);
    procedure   LoadFromFile(APath: string);
    procedure   SaveToFile(APath: string);
    property Count:         Integer read FCount;
    property CaseSensitive: Boolean read FCaseSensitive write FCaseSensitive;
    property Sorted:        Boolean read FSorted        write FSorted;
    property Duplicates:    Integer read FDuplicates    write FDuplicates;
    property Text:          string  read GetText        write SetText;
    property Strings[Index: Integer]: string  read Get  write Put;
    property Objects[Index: Integer]: Pointer read GetObject write SetObject;
  end;

procedure SplitIntoList(const S: string; ASep: Integer; AList: TStringList);

implementation

procedure SplitIntoList(const S: string; ASep: Integer; AList: TStringList);
var
  I:     Integer;
  Start: Integer;
  SLo:   Integer;
  SHi:   Integer;
begin
  AList.Clear;
  Start := 1;
  I     := 1;
  while I <= Length(S) do
  begin
    if OrdAt(S, I) = ASep then
    begin
      { Trim surrounding spaces }
      SLo := Start;
      SHi := I - 1;
      while (SLo <= SHi) and (OrdAt(S, SLo) = 32) do SLo := SLo + 1;
      while (SHi >= SLo) and (OrdAt(S, SHi) = 32) do SHi := SHi - 1;
      AList.Add(Copy(S, SLo, SHi - SLo + 1));
      Start := I + 1;
    end;
    I := I + 1;
  end;
  if Start <= Length(S) then
  begin
    SLo := Start;
    SHi := Length(S);
    while (SLo <= SHi) and (OrdAt(S, SLo) = 32) do SLo := SLo + 1;
    while (SHi >= SLo) and (OrdAt(S, SHi) = 32) do SHi := SHi - 1;
    AList.Add(Copy(S, SLo, SHi - SLo + 1));
  end;
end;


{ ================================================================== }
{ TStringList                                                          }
{ ================================================================== }

procedure TStringList.Grow;
var
  NewCap: Integer;
  OldCap: Integer;
begin
  OldCap := Self.FCapacity;
  if OldCap = 0 then
    NewCap := 4
  else
    NewCap := OldCap * 2;
  Self.FStrings  := ReallocMem(Self.FStrings, NewCap * SizeOf(string));
  Self.FObjects  := ReallocMem(Self.FObjects, NewCap * SizeOf(Pointer));
  { Zero-initialise new string slots so ARC release of "old" value is safe }
  ZeroMem(Self.FStrings + OldCap * SizeOf(string),
          (NewCap - OldCap) * SizeOf(string));
  Self.FCapacity := NewCap
end;

function TStringList.Compare(S1: string; S2: string): Integer;
begin
  if Self.FCaseSensitive then
    Result := CompareStr(S1, S2)
  else
    Result := CompareText(S1, S2)
end;

function TStringList.FindSorted(S: string; var Idx: Integer): Boolean;
var
  Lo:   Integer;
  Hi:   Integer;
  Mid:  Integer;
  Cmp:  Integer;
  Ptr:  ^string;
  MStr: string;
begin
  Lo := 0;
  Hi := Self.FCount - 1;
  while Lo <= Hi do
  begin
    Mid  := (Lo + Hi) div 2;
    Ptr  := Self.FStrings + Mid * SizeOf(string);
    MStr := Ptr^;
    Cmp  := Self.Compare(S, MStr);
    if Cmp = 0 then
    begin
      Idx    := Mid;
      Result := True;
      Exit
    end
    else if Cmp < 0 then
      Hi := Mid - 1
    else
      Lo := Mid + 1
  end;
  Idx    := Lo;
  Result := False
end;

constructor TStringList.Create;
begin
  Self.FCaseSensitive := True;
  Self.FSorted        := False;
  Self.FDuplicates    := dupAccept
end;

procedure TStringList.Destroy;
var
  I:   Integer;
  Ptr: ^string;
begin
  { Release all strings before freeing the backing store }
  I := 0;
  while I < Self.FCount do
  begin
    Ptr  := Self.FStrings + I * SizeOf(string);
    Ptr^ := nil;
    I    := I + 1
  end;
  FreeMem(Self.FStrings);
  FreeMem(Self.FObjects);
  Self.FStrings  := nil;
  Self.FObjects  := nil;
  Self.FCount    := 0;
  Self.FCapacity := 0
end;

function TStringList.Add(S: string): Integer;
var
  Idx:  Integer;
  StrP: ^string;
  ObjP: ^Pointer;
begin
  if Self.FSorted then
  begin
    Self.FindSorted(S, Idx);
    if (Self.FDuplicates = dupIgnore) and
       (Idx < Self.FCount) then
    begin
      { Check for exact match at Idx }
      StrP := Self.FStrings + Idx * SizeOf(string);
      if Self.Compare(S, StrP^) = 0 then
      begin
        Result := Idx;
        Exit
      end
    end;
    Self.Insert(Idx, S);
    Result := Idx
  end
  else
  begin
    if Self.FCount = Self.FCapacity then
      Self.Grow;
    StrP        := Self.FStrings + Self.FCount * SizeOf(string);
    ObjP        := Self.FObjects + Self.FCount * SizeOf(Pointer);
    StrP^       := S;
    ObjP^       := nil;
    Result      := Self.FCount;
    Self.FCount := Self.FCount + 1
  end
end;

procedure TStringList.AddObject(S: string; AObject: Pointer);
var
  Idx:  Integer;
  ObjP: ^Pointer;
begin
  Idx  := Self.Add(S);
  ObjP := Self.FObjects + Idx * SizeOf(Pointer);
  ObjP^ := AObject
end;

function TStringList.Find(S: string; var Index: Integer): Boolean;
var
  I:    Integer;
  Ptr:  ^string;
begin
  if Self.FSorted then
    Result := Self.FindSorted(S, Index)
  else
  begin
    { Linear search for unsorted list }
    I := 0;
    while I < Self.FCount do
    begin
      Ptr := Self.FStrings + I * SizeOf(string);
      if Self.Compare(S, Ptr^) = 0 then
      begin
        Index  := I;
        Result := True;
        Exit
      end;
      I := I + 1
    end;
    Index  := -1;
    Result := False
  end
end;

function TStringList.IndexOf(S: string): Integer;
var
  Idx: Integer;
begin
  if Self.Find(S, Idx) then
    Result := Idx
  else
    Result := -1
end;

function TStringList.Get(AIndex: Integer): string;
var
  Ptr: ^string;
begin
  Ptr    := Self.FStrings + AIndex * SizeOf(string);
  Result := Ptr^
end;

procedure TStringList.Put(AIndex: Integer; S: string);
var
  Ptr: ^string;
begin
  Ptr  := Self.FStrings + AIndex * SizeOf(string);
  Ptr^ := S
end;

function TStringList.GetObject(AIndex: Integer): Pointer;
var
  Ptr: ^Pointer;
begin
  Ptr    := Self.FObjects + AIndex * SizeOf(Pointer);
  Result := Ptr^
end;

procedure TStringList.SetObject(AIndex: Integer; AObject: Pointer);
var
  Ptr: ^Pointer;
begin
  Ptr  := Self.FObjects + AIndex * SizeOf(Pointer);
  Ptr^ := AObject
end;

procedure TStringList.Delete(AIndex: Integer);
var
  I:    Integer;
  SDst: ^string;
  SSrc: ^string;
  ODst: ^Pointer;
  OSrc: ^Pointer;
begin
  I := AIndex;
  while I < Self.FCount - 1 do
  begin
    SDst  := Self.FStrings + I * SizeOf(string);
    SSrc  := Self.FStrings + (I + 1) * SizeOf(string);
    ODst  := Self.FObjects + I * SizeOf(Pointer);
    OSrc  := Self.FObjects + (I + 1) * SizeOf(Pointer);
    SDst^ := SSrc^;
    ODst^ := OSrc^;
    I     := I + 1
  end;
  { Release the last (duplicate) string slot and clear the object slot }
  SDst  := Self.FStrings + (Self.FCount - 1) * SizeOf(string);
  SDst^ := nil;
  ODst  := Self.FObjects + (Self.FCount - 1) * SizeOf(Pointer);
  ODst^ := nil;
  Self.FCount := Self.FCount - 1
end;

procedure TStringList.Clear;
var
  I:   Integer;
  Ptr: ^string;
begin
  I := 0;
  while I < Self.FCount do
  begin
    Ptr  := Self.FStrings + I * SizeOf(string);
    Ptr^ := nil;
    I    := I + 1
  end;
  Self.FCount := 0
end;

procedure TStringList.Insert(AIndex: Integer; S: string);
var
  I:    Integer;
  SDst: ^string;
  SSrc: ^string;
  ODst: ^Pointer;
  OSrc: ^Pointer;
  Ptr:  ^string;
  OPtr: ^Pointer;
begin
  if Self.FCount = Self.FCapacity then
    Self.Grow;
  { Shift elements right from FCount-1 down to AIndex }
  I := Self.FCount;
  while I > AIndex do
  begin
    SDst  := Self.FStrings + I * SizeOf(string);
    SSrc  := Self.FStrings + (I - 1) * SizeOf(string);
    ODst  := Self.FObjects + I * SizeOf(Pointer);
    OSrc  := Self.FObjects + (I - 1) * SizeOf(Pointer);
    SDst^ := SSrc^;
    ODst^ := OSrc^;
    I     := I - 1
  end;
  { Zero the source slot that was shifted (now duplicated at AIndex+1) }
  SSrc  := Self.FStrings + AIndex * SizeOf(string);
  SSrc^ := nil;  { release the "old" value ARC wrote there during shift }
  { Write the new string at AIndex }
  Ptr   := Self.FStrings + AIndex * SizeOf(string);
  OPtr  := Self.FObjects + AIndex * SizeOf(Pointer);
  Ptr^  := S;
  OPtr^ := nil;
  Self.FCount := Self.FCount + 1
end;

procedure TStringList.AddStrings(ASource: TStringList);
var
  I: Integer;
begin
  I := 0;
  while I < ASource.FCount do
  begin
    Self.Add(ASource.Get(I));
    I := I + 1
  end;
end;

function TStringList.GetText: string;
var
  I:   Integer;
  Ptr: ^string;
  Sep: string;
begin
  Result := '';
  Sep    := '';
  I := 0;
  while I < Self.FCount do
  begin
    Ptr    := Self.FStrings + I * SizeOf(string);
    Result := Result + Sep + Ptr^;
    Sep    := #10;
    I      := I + 1
  end
end;

procedure TStringList.SetText(AText: string);
begin
  Self.Clear;
  SplitIntoList(AText, Ord(#10), Self)
end;

procedure TStringList.LoadFromFile(APath: string);
begin
  Self.SetText(ReadFile(APath))
end;

procedure TStringList.SaveToFile(APath: string);
begin
  if Self.FCount > 0 then
    WriteFile(APath, Self.GetText + #10)
  else
    WriteFile(APath, '')
end;

end.
