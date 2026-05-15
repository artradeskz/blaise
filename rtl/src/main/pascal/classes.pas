{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Classes;

// Blaise RTL — Classes unit.
//
// Provides TComponent, TStringList with a method-based API compatible with
// the Blaise compiler source for self-hosting.  TObjectList has been moved
// to the Contnrs unit to match FPC's layout.
//
// Design notes:
//   - TObjectList has been moved to the Contnrs unit (uses Contnrs).
//   - TDuplicates is a proper Pascal enum (dupAccept, dupIgnore, dupError).
//   - TStringList stores strings as ^string; ARC is emitted by the compiler
//     for pointer-dereference writes (EmitPointerWrite). ZeroMem is used to
//     zero-initialise newly grown string slots so no garbage is ever released.
//   - Text property: getter = GetText (lines joined by #10, no trailing newline);
//     setter = Clear + SplitIntoList(AText, Ord(#10), Self).
//   - LoadFromFile/SaveToFile use the ReadFile/WriteFile built-ins.
//   - TComponent: minimal owner-component pattern (Name, Owner, Components[]).
//     Children list uses a raw ^Pointer array (same pattern as TStringList) to
//     avoid a circular dependency with generics.collections in this unit.
//   - TStringListSortCompare: function type for CustomSort.
//   - CommaText: getter joins items with commas, quoting items that contain
//     commas or spaces; setter splits on commas respecting double-quote groups.

interface

type
  TDuplicates = (dupAccept, dupIgnore, dupError);

  TStringListSortCompare = function(const A: string; const B: string): Integer;

  { ------------------------------------------------------------------ }
  { TComponent                                                           }
  { ------------------------------------------------------------------ }

  TComponent = class
  private
    FName:     string;
    FOwner:    TComponent;
    FChildren: ^Pointer;
    FChildCap: Integer;
    FChildCnt: Integer;
    procedure GrowChildren;
    procedure AddComponent(AComp: TComponent);
    procedure RemoveComponent(AComp: TComponent);
    function  GetComponent(AIndex: Integer): TComponent;
  public
    constructor Create(AOwner: TComponent);
    procedure   Destroy;
    property Name:           string     read FName     write FName;
    property Owner:          TComponent read FOwner;
    property ComponentCount: Integer    read FChildCnt;
    property Components[Index: Integer]: TComponent read GetComponent;
  end;

  { ------------------------------------------------------------------ }
  { TStringListEnumerator                                                }
  { ------------------------------------------------------------------ }

  TStringListEnumerator = class
    FList:  TStringList;
    FIndex: Integer;
    constructor Create(AList: TStringList);
    function MoveNext: Boolean;
    function GetCurrent: string;
    property Current: string read GetCurrent;
  end;

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
    FDuplicates:    TDuplicates;
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
    function    GetEnumerator: TStringListEnumerator;
    procedure   CustomSort(ACompare: TStringListSortCompare);
    function    GetCommaText: string;
    procedure   SetCommaText(const S: string);
    property Count:         Integer read FCount;
    property CaseSensitive: Boolean read FCaseSensitive write FCaseSensitive;
    property Sorted:        Boolean read FSorted        write FSorted;
    property Duplicates:    TDuplicates read FDuplicates write FDuplicates;
    property Text:          string  read GetText        write SetText;
    property CommaText:     string  read GetCommaText   write SetCommaText;
    property Strings[Index: Integer]: string  read Get  write Put;
    property Objects[Index: Integer]: Pointer read GetObject write SetObject;
  end;

procedure SplitIntoList(const S: string; ASep: Integer; AList: TStringList);

implementation

{ ================================================================== }
{ TComponent                                                           }
{ ================================================================== }

procedure TComponent.GrowChildren;
var
  NewCap: Integer;
  OldCap: Integer;
begin
  OldCap := Self.FChildCap;
  if OldCap = 0 then
    NewCap := 4
  else
    NewCap := OldCap * 2;
  Self.FChildren := ReallocMem(Self.FChildren, NewCap * SizeOf(Pointer));
  ZeroMem(Self.FChildren + OldCap * SizeOf(Pointer),
          (NewCap - OldCap) * SizeOf(Pointer));
  Self.FChildCap := NewCap
end;

procedure TComponent.AddComponent(AComp: TComponent);
var
  Slot: ^Pointer;
begin
  if Self.FChildCnt = Self.FChildCap then
    Self.GrowChildren;
  Slot  := Self.FChildren + Self.FChildCnt * SizeOf(Pointer);
  Slot^ := Pointer(AComp);
  Self.FChildCnt := Self.FChildCnt + 1
end;

procedure TComponent.RemoveComponent(AComp: TComponent);
var
  I:   Integer;
  Dst: ^Pointer;
  Src: ^Pointer;
begin
  I := 0;
  while I < Self.FChildCnt do
  begin
    Dst := Self.FChildren + I * SizeOf(Pointer);
    if Dst^ = Pointer(AComp) then
    begin
      while I < Self.FChildCnt - 1 do
      begin
        Dst  := Self.FChildren + I * SizeOf(Pointer);
        Src  := Self.FChildren + (I + 1) * SizeOf(Pointer);
        Dst^ := Src^;
        I    := I + 1
      end;
      Dst  := Self.FChildren + (Self.FChildCnt - 1) * SizeOf(Pointer);
      Dst^ := nil;
      Self.FChildCnt := Self.FChildCnt - 1;
      Exit
    end;
    I := I + 1
  end
end;

function TComponent.GetComponent(AIndex: Integer): TComponent;
var
  Slot: ^Pointer;
begin
  Slot   := Self.FChildren + AIndex * SizeOf(Pointer);
  Result := TComponent(Slot^)
end;

constructor TComponent.Create(AOwner: TComponent);
begin
  Self.FOwner    := nil;
  Self.FChildren := nil;
  Self.FChildCap := 0;
  Self.FChildCnt := 0;
  if AOwner <> nil then
  begin
    Self.FOwner := AOwner;
    AOwner.AddComponent(Self)
  end
end;

procedure TComponent.Destroy;
var
  Slot:  ^Pointer;
  Child: TComponent;
begin
  { Free children in reverse order }
  while Self.FChildCnt > 0 do
  begin
    Slot   := Self.FChildren + (Self.FChildCnt - 1) * SizeOf(Pointer);
    Child  := TComponent(Slot^);
    Slot^  := nil;
    Self.FChildCnt := Self.FChildCnt - 1;
    Child.FOwner   := nil;
    Child.Free
  end;
  FreeMem(Self.FChildren);
  Self.FChildren := nil;
  { Unregister from owner }
  if Self.FOwner <> nil then
    Self.FOwner.RemoveComponent(Self)
end;

procedure SplitIntoList(const S: string; ASep: Integer; AList: TStringList);
var
  I:     Integer;
  Start: Integer;
  SLo:   Integer;
  SHi:   Integer;
begin
  AList.Clear;
  Start := 0;
  I     := 0;
  while I < Length(S) do
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
  if Start < Length(S) then
  begin
    SLo := Start;
    SHi := Length(S) - 1;
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
begin
  Result := '';
  I := 0;
  while I < Self.FCount do
  begin
    Ptr    := Self.FStrings + I * SizeOf(string);
    Result := Result + Ptr^ + #10;
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
  WriteFile(APath, Self.GetText)
end;

function TStringList.GetEnumerator: TStringListEnumerator;
begin
  Result := TStringListEnumerator.Create(Self)
end;

procedure TStringList.CustomSort(ACompare: TStringListSortCompare);
var
  { Iterative bottom-up merge sort on the string+object arrays }
  Width:  Integer;
  Lo:     Integer;
  Mid:    Integer;
  Hi:     Integer;
  N:      Integer;
  { merge workspace }
  TmpStr: ^string;
  TmpObj: ^Pointer;
  I:      Integer;
  J:      Integer;
  K:      Integer;
  SA:     ^string;
  SB:     ^string;
  OA:     ^Pointer;
  OB:     ^Pointer;
  WS:     ^string;
  WO:     ^Pointer;
  DS:     ^string;
  DO_:    ^Pointer;
begin
  N := Self.FCount;
  if N < 2 then Exit;
  TmpStr := GetMem(N * SizeOf(string));
  TmpObj := GetMem(N * SizeOf(Pointer));
  ZeroMem(TmpStr, N * SizeOf(string));
  ZeroMem(TmpObj, N * SizeOf(Pointer));
  Width := 1;
  while Width < N do
  begin
    Lo := 0;
    while Lo < N do
    begin
      Mid := Lo + Width;
      if Mid > N then Mid := N;
      Hi  := Lo + Width * 2;
      if Hi > N then Hi := N;
      { merge [Lo..Mid) and [Mid..Hi) into TmpStr/TmpObj }
      I := Lo;
      J := Mid;
      K := Lo;
      while (I < Mid) and (J < Hi) do
      begin
        SA := Self.FStrings + I * SizeOf(string);
        SB := Self.FStrings + J * SizeOf(string);
        if ACompare(SA^, SB^) <= 0 then
        begin
          WS  := TmpStr + K * SizeOf(string);
          WO  := TmpObj + K * SizeOf(Pointer);
          OA  := Self.FObjects + I * SizeOf(Pointer);
          WS^ := SA^;
          WO^ := OA^;
          I   := I + 1
        end
        else
        begin
          WS  := TmpStr + K * SizeOf(string);
          WO  := TmpObj + K * SizeOf(Pointer);
          OB  := Self.FObjects + J * SizeOf(Pointer);
          WS^ := SB^;
          WO^ := OB^;
          J   := J + 1
        end;
        K := K + 1
      end;
      while I < Mid do
      begin
        SA  := Self.FStrings + I * SizeOf(string);
        OA  := Self.FObjects + I * SizeOf(Pointer);
        WS  := TmpStr + K * SizeOf(string);
        WO  := TmpObj + K * SizeOf(Pointer);
        WS^ := SA^;
        WO^ := OA^;
        I   := I + 1;
        K   := K + 1
      end;
      while J < Hi do
      begin
        SB  := Self.FStrings + J * SizeOf(string);
        OB  := Self.FObjects + J * SizeOf(Pointer);
        WS  := TmpStr + K * SizeOf(string);
        WO  := TmpObj + K * SizeOf(Pointer);
        WS^ := SB^;
        WO^ := OB^;
        J   := J + 1;
        K   := K + 1
      end;
      { copy merged run back }
      K := Lo;
      while K < Hi do
      begin
        WS  := TmpStr + K * SizeOf(string);
        WO  := TmpObj + K * SizeOf(Pointer);
        DS  := Self.FStrings + K * SizeOf(string);
        DO_ := Self.FObjects + K * SizeOf(Pointer);
        DS^ := WS^;
        DO_^ := WO^;
        K   := K + 1
      end;
      Lo := Lo + Width * 2
    end;
    Width := Width * 2
  end;
  { Release temp arrays — zero strings first so ARC doesn't double-release }
  I := 0;
  while I < N do
  begin
    WS  := TmpStr + I * SizeOf(string);
    WS^ := nil;
    I   := I + 1
  end;
  FreeMem(TmpStr);
  FreeMem(TmpObj)
end;

function TStringList.GetCommaText: string;
var
  I:    Integer;
  Item: string;
  Need: Boolean;
  J:    Integer;
  Ch:   Integer;
begin
  Result := '';
  I := 0;
  while I < Self.FCount do
  begin
    Item := Self.Get(I);
    { Quote if item contains comma, space, or double-quote }
    Need := False;
    J := 0;
    while J < Length(Item) do
    begin
      Ch := OrdAt(Item, J);
      if (Ch = Ord(',')) or (Ch = Ord(' ')) or (Ch = Ord('"')) then
      begin
        Need := True;
        Break
      end;
      J := J + 1
    end;
    if I > 0 then Result := Result + ',';
    if Need then
    begin
      { Wrap in double quotes; escape inner double-quotes as "" }
      Result := Result + '"';
      J := 0;
      while J < Length(Item) do
      begin
        Ch := OrdAt(Item, J);
        if Ch = Ord('"') then
          Result := Result + '""'
        else
          Result := Result + Chr(Ch);
        J := J + 1
      end;
      Result := Result + '"'
    end
    else
      Result := Result + Item;
    I := I + 1
  end
end;

procedure TStringList.SetCommaText(const S: string);
var
  I:    Integer;
  N:    Integer;
  Item: string;
  InQ:  Boolean;
  Ch:   Integer;
begin
  Self.Clear;
  N    := Length(S);
  I    := 0;
  Item := '';
  while I <= N do
  begin
    if I = N then
    begin
      Self.Add(Item);
      I := I + 1
    end
    else
    begin
      Ch := OrdAt(S, I);
      if Ch = Ord('"') then
      begin
        { quoted token }
        I    := I + 1;
        Item := '';
        InQ  := True;
        while (I < N) and InQ do
        begin
          Ch := OrdAt(S, I);
          if Ch = Ord('"') then
          begin
            if (I + 1 < N) and (OrdAt(S, I + 1) = Ord('"')) then
            begin
              { escaped double-quote }
              Item := Item + '"';
              I    := I + 2
            end
            else
            begin
              InQ := False;
              I   := I + 1
            end
          end
          else
          begin
            Item := Item + Chr(Ch);
            I    := I + 1
          end
        end;
        Self.Add(Item);
        { skip trailing comma if present }
        if (I < N) and (OrdAt(S, I) = Ord(',')) then
          I := I + 1;
        Item := ''
      end
      else if Ch = Ord(',') then
      begin
        Self.Add(Item);
        Item := '';
        I    := I + 1
      end
      else
      begin
        Item := Item + Chr(Ch);
        I    := I + 1
      end
    end
  end
end;

{ ================================================================== }
{ TStringListEnumerator                                                }
{ ================================================================== }

constructor TStringListEnumerator.Create(AList: TStringList);
begin
  Self.FList  := AList;
  Self.FIndex := -1
end;

function TStringListEnumerator.MoveNext: Boolean;
begin
  Self.FIndex := Self.FIndex + 1;
  Result := Self.FIndex < Self.FList.Count
end;

function TStringListEnumerator.GetCurrent: string;
begin
  Result := Self.FList.Get(Self.FIndex)
end;

end.
