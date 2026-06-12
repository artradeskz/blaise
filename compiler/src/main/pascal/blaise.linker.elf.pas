{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.linker.elf;

{ Internal ELF linker — section merging (Phase A of
  docs/internal-linker-design.adoc).

  TSectionMerger concatenates like-named allocatable sections from a
  set of parsed input objects, padding each contribution to its
  section's alignment, and records a placement (merged section +
  offset) for every input section.  Placements are the basis for
  symbol and relocation rebasing in Phase B: a symbol's final offset
  is its object-local value plus its section's placement offset.

  SHT_NOBITS contributions advance the merged size without adding
  bytes; mixing NOBITS and PROGBITS under one name is rejected.
  Non-allocatable bookkeeping sections (symtab, strtab, rela,
  .note.GNU-stack, .comment) are skipped — the linker rebuilds those
  itself.  Non-alloc .opdf.* debug sections ARE kept: they must ride
  through into the final executable for the OPDF debugger. }

interface

uses
  SysUtils, Generics.Collections, blaise.elfreader;

type
  ELinker = class(Exception);

  { One output section accumulating contributions from input objects. }
  TMergedSection = class
  public
    Name:   string;
    ShType: Integer;
    Flags:  Int64;
    Align:  Int64;
    Data:   string;     { concatenated bytes; empty for SHT_NOBITS }
    Size:   Int64;      { total size including NOBITS reservations }
  end;

  { Where one input section landed: merged section + byte offset. }
  TSectionPlacement = class
  public
    ObjIndex: Integer;        { caller-assigned input object index }
    SecIndex: Integer;        { ELF section index within that object }
    Merged:   TMergedSection; { destination (not owned) }
    Offset:   Int64;          { offset of the contribution }
  end;

  TSectionMerger = class
  private
    FMerged:     TList<TMergedSection>;
    FPlacements: TList<TSectionPlacement>;
    function GetOrCreate(ASec: TRdSection): TMergedSection;
    function WantSection(ASec: TRdSection): Boolean;
  public
    constructor Create;
    destructor Destroy; override;

    { Merge every wanted section of AObj.  AObjIndex tags the
      placements; callers number their inputs sequentially. }
    procedure AddObject(AObjIndex: Integer; AObj: TElfObjectFile);

    function FindMerged(const AName: string): TMergedSection;
    { Placement of input object AObjIndex's section ASecIndex, or nil
      if that section was skipped. }
    function PlacementOf(AObjIndex, ASecIndex: Integer): TSectionPlacement;

    property Merged: TList<TMergedSection> read FMerged;
    property Placements: TList<TSectionPlacement> read FPlacements;
  end;

implementation

function LkAlignUp(AVal: Int64; AAlign: Int64): Int64;
var
  Rem: Int64;
begin
  if AAlign <= 1 then
  begin
    Result := AVal;
    Exit;
  end;
  Rem := AVal mod AAlign;
  if Rem = 0 then
    Result := AVal
  else
    Result := AVal + (AAlign - Rem);
end;

function LkZeros(ACount: Int64): string;
var
  I: Int64;
begin
  Result := '';
  I := 0;
  while I < ACount do
  begin
    Result := Result + Chr(0);
    I := I + 1;
  end;
end;

constructor TSectionMerger.Create;
begin
  inherited Create();
  FMerged := TList<TMergedSection>.Create();
  FPlacements := TList<TSectionPlacement>.Create();
end;

destructor TSectionMerger.Destroy;
var
  I: Integer;
begin
  for I := 0 to FMerged.Count - 1 do
    FMerged.Get(I).Free();
  FMerged.Free();
  for I := 0 to FPlacements.Count - 1 do
    FPlacements.Get(I).Free();
  FPlacements.Free();
  inherited Destroy();
end;

function TSectionMerger.WantSection(ASec: TRdSection): Boolean;
begin
  { Bookkeeping sections are rebuilt by the linker, never merged. }
  if (ASec.ShType = SHT_NULL) or (ASec.ShType = SHT_SYMTAB) or
     (ASec.ShType = SHT_STRTAB) or (ASec.ShType = SHT_RELA) then
  begin
    Result := False;
    Exit;
  end;
  if (ASec.Name = '.note.GNU-stack') or (ASec.Name = '.comment') then
  begin
    Result := False;
    Exit;
  end;
  { Allocatable sections always merge; non-alloc only for the OPDF
    debug pass-through. }
  if (ASec.Flags and SHF_ALLOC) <> 0 then
    Result := True
  else
    Result := Pos('.opdf', ASec.Name) = 0;
end;

function TSectionMerger.GetOrCreate(ASec: TRdSection): TMergedSection;
var
  I: Integer;
  M: TMergedSection;
begin
  for I := 0 to FMerged.Count - 1 do
  begin
    M := FMerged.Get(I);
    if M.Name = ASec.Name then
    begin
      if (M.ShType = SHT_NOBITS) <> (ASec.ShType = SHT_NOBITS) then
        raise ELinker.Create('section ' + ASec.Name
          + ': NOBITS and PROGBITS contributions cannot be merged');
      Result := M;
      Exit;
    end;
  end;
  M := TMergedSection.Create();
  M.Name := ASec.Name;
  M.ShType := ASec.ShType;
  M.Flags := ASec.Flags;
  M.Align := 1;
  M.Data := '';
  M.Size := 0;
  FMerged.Add(M);
  Result := M;
end;

procedure TSectionMerger.AddObject(AObjIndex: Integer; AObj: TElfObjectFile);
var
  I: Integer;
  Sec: TRdSection;
  M: TMergedSection;
  P: TSectionPlacement;
  Aligned: Int64;
  SecAlign: Int64;
begin
  for I := 0 to AObj.Sections.Count - 1 do
  begin
    Sec := AObj.Sections.Get(I);
    if not Self.WantSection(Sec) then Continue;

    M := Self.GetOrCreate(Sec);
    SecAlign := Sec.AddrAlign;
    if SecAlign < 1 then SecAlign := 1;
    if SecAlign > M.Align then M.Align := SecAlign;

    Aligned := LkAlignUp(M.Size, SecAlign);
    if M.ShType <> SHT_NOBITS then
    begin
      if Aligned > M.Size then
        M.Data := M.Data + LkZeros(Aligned - M.Size);
      M.Data := M.Data + Sec.Data;
    end;
    P := TSectionPlacement.Create();
    P.ObjIndex := AObjIndex;
    P.SecIndex := I;
    P.Merged := M;
    P.Offset := Aligned;
    FPlacements.Add(P);
    M.Size := Aligned + Sec.Size;
  end;
end;

function TSectionMerger.FindMerged(const AName: string): TMergedSection;
var
  I: Integer;
begin
  for I := 0 to FMerged.Count - 1 do
    if FMerged.Get(I).Name = AName then
    begin
      Result := FMerged.Get(I);
      Exit;
    end;
  Result := nil;
end;

function TSectionMerger.PlacementOf(AObjIndex,
  ASecIndex: Integer): TSectionPlacement;
var
  I: Integer;
  P: TSectionPlacement;
begin
  for I := 0 to FPlacements.Count - 1 do
  begin
    P := FPlacements.Get(I);
    if (P.ObjIndex = AObjIndex) and (P.SecIndex = ASecIndex) then
    begin
      Result := P;
      Exit;
    end;
  end;
  Result := nil;
end;

end.
