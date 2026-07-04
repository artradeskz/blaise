{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  blaise_mem — Pascal memory allocator for the Blaise runtime.

  Replaces libc malloc/free/realloc with an allocator backed by POSIX
  mmap/munmap.  Self-contained: no dependency on strings, ARC, or
  any stdlib unit.

  Design:

  Small allocations (up to LARGE_THRESHOLD bytes):
    Served from 64 KB arenas obtained via mmap.  Each allocation has
    an 8-byte header storing the usable size.  Freed blocks go onto a
    per-size-class freelist for O(1) reuse.  Size classes are powers
    of two: 16, 32, 64, 128, 256, 512, 1024, 2048.

    Only the head arena is used for bump allocation.  When it fills,
    a new arena is allocated and becomes the head.  No arena-list walk.

  Large allocations (above LARGE_THRESHOLD):
    Each gets its own mmap region with a 16-byte header.  Freed large
    blocks are cached on a LIFO freelist for O(1) reuse.  The cache
    holds up to LARGE_CACHE_MAX entries; excess blocks are munmap-ed
    immediately.  Large reallocs use Linux mremap to resize in-place
    without copying.  All mmap sizes are rounded up to page granularity
    (4 KB) for better cache hit rates.

  All returned pointers are 8-byte aligned.

  Thread safety:
    All allocator state (arenas, freelists, large-block cache) is
    declared as threadvar, giving each thread its own independent
    allocator instance with zero contention and no locks.  Spawned
    threads start with nil arenas and empty freelists; their first
    allocation creates a fresh arena via mmap.  Memory allocated on
    one thread must not be freed on another (the freelist push would
    go to the wrong thread's list).
}

unit blaise_mem;

interface

function  _BlaiseGetMem(Size: Integer): Pointer;
procedure _BlaiseFreeMem(Ptr: Pointer);
function  _BlaiseReallocMem(Ptr: Pointer; NewSize: Integer): Pointer;

implementation

function  _libc_mmap(Addr: Pointer; Length: Int64; Prot, Flags, Fd: Integer;
            Offset: Int64): Pointer; external name 'mmap';
function  _libc_munmap(Addr: Pointer; Length: Int64): Integer;
            external name 'munmap';
function  _libc_mremap(OldAddr: Pointer; OldSize, NewSize: Int64;
            Flags: Integer): Pointer; external name 'mremap';
procedure _libc_memcpy(Dst, Src: Pointer; N: Int64); external name 'memcpy';

const
  PROT_READ       = 1;
  PROT_WRITE      = 2;
  MAP_PRIVATE     = 2;
  MAP_ANONYMOUS   = 32;
  MAP_FAILED_VAL  = -1;
  MREMAP_MAYMOVE  = 1;

  PAGE_SIZE       = 4096;
  ARENA_SIZE      = 65536;
  LARGE_THRESHOLD = 2048;
  HEADER_SIZE     = 8;
  LARGE_HEADER    = 16;
  LARGE_CACHE_MAX = 32;

type
  PBlockHeader = ^TBlockHeader;
  TBlockHeader = record
    AllocSize: Integer;
    Flags:     Integer;
  end;

  PLargeHeader = ^TLargeHeader;
  TLargeHeader = record
    TotalMapped: Int64;
    AllocSize:   Integer;
    Flags:       Integer;
  end;

  PFreeNode = ^TFreeNode;
  TFreeNode = record
    Next: PFreeNode;
  end;

  PLargeFreeNode = ^TLargeFreeNode;
  TLargeFreeNode = record
    Next:        PLargeFreeNode;
    TotalMapped: Int64;
  end;

  PArena = ^TArena;
  TArena = record
    Base:     Pointer;
    Offset:   Integer;
    Capacity: Integer;
    Next:     PArena;
  end;

const
  FLAG_LARGE = 1;
  FLAG_SMALL = 0;

threadvar
  FreeLists: array[0..7] of PFreeNode;
  ArenaHead: PArena;
  LargeFreeHead: PLargeFreeNode;
  LargeFreeCount: Integer;

function MapFailed(P: Pointer): Boolean;
begin
  Result := (P = nil) or (PtrUInt(P) = PtrUInt(MAP_FAILED_VAL));
end;

function PageRound(Size: Int64): Int64;
begin
  Result := (Size + Int64(PAGE_SIZE - 1)) and Int64($FFFFFFFFFFFFF000);
end;

function MmapAlloc(Size: Int64): Pointer;
begin
  Size := PageRound(Size);
  Result := _libc_mmap(nil, Size,
    PROT_READ or PROT_WRITE,
    MAP_PRIVATE or MAP_ANONYMOUS,
    -1, 0);
  if MapFailed(Result) then
    Result := nil;
end;

function SizeClassIndex(Size: Integer): Integer;
begin
  if Size <= 16 then begin Result := 0; Exit end;
  if Size <= 32 then begin Result := 1; Exit end;
  if Size <= 64 then begin Result := 2; Exit end;
  if Size <= 128 then begin Result := 3; Exit end;
  if Size <= 256 then begin Result := 4; Exit end;
  if Size <= 512 then begin Result := 5; Exit end;
  if Size <= 1024 then begin Result := 6; Exit end;
  Result := 7;
end;

function SizeClassBytes(Index: Integer): Integer;
begin
  case Index of
    0: Result := 16;
    1: Result := 32;
    2: Result := 64;
    3: Result := 128;
    4: Result := 256;
    5: Result := 512;
    6: Result := 1024;
  else
    Result := 2048;
  end;
end;

function RoundUpToClass(Size: Integer): Integer;
begin
  Result := SizeClassBytes(SizeClassIndex(Size));
end;

function AllocArena: PArena;
var
  Base: Pointer;
  A: PArena;
begin
  Base := MmapAlloc(Int64(ARENA_SIZE));
  if Base = nil then
  begin
    Exit(nil);
  end;
  A := PArena(Base);
  A^.Base := Base;
  A^.Offset := SizeOf(TArena);
  A^.Capacity := ARENA_SIZE;
  A^.Next := ArenaHead;
  ArenaHead := A;
  Result := A;
end;

function ArenaAlloc(Size: Integer): Pointer;
var
  A: PArena;
  BlockSize, Needed: Integer;
  Hdr: PBlockHeader;
begin
  BlockSize := RoundUpToClass(Size);
  Needed := HEADER_SIZE + BlockSize;

  A := ArenaHead;
  if (A <> nil) and (A^.Offset + Needed <= A^.Capacity) then
  begin
    Hdr := Pointer(PtrUInt(A^.Base) + PtrUInt(A^.Offset));
    Hdr^.AllocSize := Size;
    Hdr^.Flags := FLAG_SMALL;
    A^.Offset := A^.Offset + Needed;
    Exit(Pointer(PtrUInt(Hdr) + HEADER_SIZE));
  end;

  A := AllocArena();
  if A = nil then
  begin
    Exit(nil);
  end;
  Hdr := Pointer(PtrUInt(A^.Base) + PtrUInt(A^.Offset));
  Hdr^.AllocSize := Size;
  Hdr^.Flags := FLAG_SMALL;
  A^.Offset := A^.Offset + Needed;
  Result := Pointer(PtrUInt(Hdr) + HEADER_SIZE);
end;

function SmallGetMem(Size: Integer): Pointer;
var
  Idx: Integer;
  Node: PFreeNode;
  Hdr: PBlockHeader;
begin
  Idx := SizeClassIndex(Size);

  Node := FreeLists[Idx];
  if Node <> nil then
  begin
    FreeLists[Idx] := Node^.Next;
    Hdr := PBlockHeader(Pointer(PtrUInt(Node) - HEADER_SIZE));
    Hdr^.AllocSize := Size;
    Exit(Pointer(Node));
  end;

  Result := ArenaAlloc(Size);
end;

procedure SmallFreeMem(Ptr: Pointer);
var
  Hdr: PBlockHeader;
  Idx: Integer;
  Node: PFreeNode;
begin
  Hdr := PBlockHeader(Pointer(PtrUInt(Ptr) - HEADER_SIZE));
  Idx := SizeClassIndex(Hdr^.AllocSize);
  Node := PFreeNode(Ptr);
  Node^.Next := FreeLists[Idx];
  FreeLists[Idx] := Node;
end;

function LargeGetMem(Size: Integer): Pointer;
var
  Total: Int64;
  Base: Pointer;
  Hdr: PLargeHeader;
  Node: PLargeFreeNode;
  Needed, CachedSize: Int64;
begin
  Needed := PageRound(Int64(LARGE_HEADER) + Int64(Size));

  Node := LargeFreeHead;
  if Node <> nil then
  begin
    CachedSize := Node^.TotalMapped;
    LargeFreeHead := Node^.Next;
    Dec(LargeFreeCount);
    if CachedSize >= Needed then
    begin
      Hdr := PLargeHeader(Pointer(Node));
      Hdr^.TotalMapped := CachedSize;
      Hdr^.AllocSize := Size;
      Hdr^.Flags := FLAG_LARGE;
      Exit(Pointer(PtrUInt(Hdr) + LARGE_HEADER));
    end;
    Base := _libc_mremap(Pointer(Node), CachedSize, Needed, MREMAP_MAYMOVE);
    if not MapFailed(Base) then
    begin
      Hdr := PLargeHeader(Base);
      Hdr^.TotalMapped := Needed;
      Hdr^.AllocSize := Size;
      Hdr^.Flags := FLAG_LARGE;
      Exit(Pointer(PtrUInt(Base) + LARGE_HEADER));
    end;
    _libc_munmap(Pointer(Node), CachedSize);
  end;

  Total := Needed;
  Base := MmapAlloc(Total);
  if Base = nil then
  begin
    Exit(nil);
  end;
  Hdr := PLargeHeader(Base);
  Hdr^.TotalMapped := Total;
  Hdr^.AllocSize := Size;
  Hdr^.Flags := FLAG_LARGE;
  Result := Pointer(PtrUInt(Base) + LARGE_HEADER);
end;

procedure LargeFreeMem(Ptr: Pointer);
var
  Hdr: PLargeHeader;
  Node: PLargeFreeNode;
begin
  Hdr := PLargeHeader(Pointer(PtrUInt(Ptr) - LARGE_HEADER));
  if LargeFreeCount < LARGE_CACHE_MAX then
  begin
    Node := PLargeFreeNode(Pointer(Hdr));
    Node^.TotalMapped := Hdr^.TotalMapped;
    Node^.Next := LargeFreeHead;
    LargeFreeHead := Node;
    Inc(LargeFreeCount);
  end
  else
    _libc_munmap(Pointer(Hdr), Hdr^.TotalMapped);
end;

function IsLarge(Ptr: Pointer): Boolean;
var
  Hdr: PBlockHeader;
begin
  Hdr := PBlockHeader(Pointer(PtrUInt(Ptr) - HEADER_SIZE));
  Result := Hdr^.Flags = FLAG_LARGE;
end;

function GetAllocSize(Ptr: Pointer): Integer;
var
  SmallHdr: PBlockHeader;
  LargeHdr: PLargeHeader;
begin
  SmallHdr := PBlockHeader(Pointer(PtrUInt(Ptr) - HEADER_SIZE));
  if SmallHdr^.Flags = FLAG_LARGE then
  begin
    LargeHdr := PLargeHeader(Pointer(PtrUInt(Ptr) - LARGE_HEADER));
    Result := LargeHdr^.AllocSize;
  end
  else
    Result := SmallHdr^.AllocSize;
end;

{ ------------------------------------------------------------------ }
{ Public API                                                           }
{ ------------------------------------------------------------------ }

function _BlaiseGetMem(Size: Integer): Pointer;
begin
  if Size <= 0 then
  begin
    Exit(nil);
  end;
  if Size > LARGE_THRESHOLD then
    Result := LargeGetMem(Size)
  else
    Result := SmallGetMem(Size);
end;

procedure _BlaiseFreeMem(Ptr: Pointer);
begin
  if Ptr = nil then Exit;
  if IsLarge(Ptr) then
    LargeFreeMem(Ptr)
  else
    SmallFreeMem(Ptr);
end;

function _BlaiseReallocMem(Ptr: Pointer; NewSize: Integer): Pointer;
var
  OldSize, CopySize: Integer;
  Hdr: PBlockHeader;
  LHdr: PLargeHeader;
  Base, NewBase: Pointer;
  OldMapped, NewMapped: Int64;
begin
  if Ptr = nil then
  begin
    Exit(_BlaiseGetMem(NewSize));
  end;
  if NewSize <= 0 then
  begin
    _BlaiseFreeMem(Ptr);
    Exit(nil);
  end;
  OldSize := GetAllocSize(Ptr);
  if (not IsLarge(Ptr)) and (NewSize <= LARGE_THRESHOLD) then
  begin
    if RoundUpToClass(NewSize) = RoundUpToClass(OldSize) then
    begin
      Hdr := PBlockHeader(Pointer(PtrUInt(Ptr) - HEADER_SIZE));
      Hdr^.AllocSize := NewSize;
      Exit(Ptr);
    end;
  end;
  if IsLarge(Ptr) and (NewSize > LARGE_THRESHOLD) then
  begin
    LHdr := PLargeHeader(Pointer(PtrUInt(Ptr) - LARGE_HEADER));
    OldMapped := LHdr^.TotalMapped;
    NewMapped := PageRound(Int64(LARGE_HEADER) + Int64(NewSize));
    if NewMapped = OldMapped then
    begin
      LHdr^.AllocSize := NewSize;
      Exit(Ptr);
    end;
    Base := Pointer(LHdr);
    NewBase := _libc_mremap(Base, OldMapped, NewMapped, MREMAP_MAYMOVE);
    if not MapFailed(NewBase) then
    begin
      LHdr := PLargeHeader(NewBase);
      LHdr^.TotalMapped := NewMapped;
      LHdr^.AllocSize := NewSize;
      LHdr^.Flags := FLAG_LARGE;
      Exit(Pointer(PtrUInt(NewBase) + LARGE_HEADER));
    end;
  end;
  Result := _BlaiseGetMem(NewSize);
  if Result = nil then Exit;
  if OldSize < NewSize then
    CopySize := OldSize
  else
    CopySize := NewSize;
  _libc_memcpy(Result, Ptr, Int64(CopySize));
  _BlaiseFreeMem(Ptr);
end;

end.
