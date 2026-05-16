{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  Blaise RTL — ARC management (Pascal port of blaise_arc.c)

  String layout — data-pointer convention (shared with blaise_str.pas):
    data_ptr − 12  RefCount  (Integer, 4 bytes)
    data_ptr −  8  Length    (Integer, 4 bytes)
    data_ptr −  4  Capacity  (Integer, 4 bytes)
    data_ptr +  0  UTF-8 char data + NUL terminator
    ↑ the DATA POINTER is what the variable slot holds

  Class instance layout — same offset convention for ARC header:
    +--[4 bytes]--+--[4 bytes]--+--[8 bytes]--+--[user fields...]--+
    | RefCount    | (padding)   | cleanup ptr | ...                |
    +-------------+-------------+-------------+--------------------+
                                               ^--- user pointer (what Pascal code sees)

  nil = unassigned.  RefCount = -1 = immortal (string literals).

  _ClassAlloc and _ClassRelease remain in blaise_arc.c because they
  store and call a function pointer — not yet expressible in Blaise.
}

unit blaise_arc;

{$mode objfpc}{$H+}

interface

procedure _StringAddRef(Ptr: Pointer);
procedure _StringRelease(Ptr: Pointer);
function  _StringEquals(S1, S2: Pointer): Integer;
function  _StringConcat(S1, S2: Pointer): Pointer;
procedure TObject_Destroy(Self: Pointer);
function  TObject_ToString(Self: Pointer): Pointer;
function  _MethodAddress(Self, Name: Pointer): Pointer;
function  _InheritsFrom(AChild, AParent: Pointer): Boolean;
function  _ClassCreate(TInfo: Pointer): Pointer;
procedure _ClassAddRef(UserPtr: Pointer);
procedure _ClassFree(UserPtr: Pointer);
{ _ClassRelease and _ClassAlloc are implemented in blaise_arc_class.c
  because they store and call a cleanup function pointer in the object
  header — a pattern not yet expressible in Blaise's Pascal RTL.
  We call _ClassAlloc from _ClassCreate via an external declaration. }
procedure _ClassRelease(UserPtr: Pointer); external name '_ClassRelease';
function  _ClassAlloc(Size: Int64; Cleanup: Pointer): Pointer; external name '_ClassAlloc';

implementation

const
  IMMORTAL  = -1;
  HDR_SIZE  = 12;   { string header: RefCount + Length + Capacity }
  CLASS_HDR = 16;   { class header:  RefCount + pad + cleanup ptr }

function  _libc_malloc(Size: Int64): Pointer;              external name 'malloc';
procedure _libc_free(Ptr: Pointer);                        external name 'free';
procedure _libc_memcpy(Dst, Src: Pointer; N: Int64);       external name 'memcpy';
function  _libc_memcmp(P1, P2: Pointer; N: Int64): Integer; external name 'memcmp';

{ Diagnostic check: verifies the string header looks sane before
  we treat refcount==0 as a free signal.  Aborts with stderr message
  on corruption. }
procedure _StringReleaseCheck(DataPtr: Pointer; RefCount, Length, Capacity: Integer);
  external name '_StringReleaseCheck';

procedure MemCopy(Dst, Src: Pointer; N: Integer);
begin
  if N > 0 then
    _libc_memcpy(Dst, Src, N);
end;

function MemCompare(P1, P2: Pointer; N: Integer): Integer;
begin
  if N = 0 then
    Result := 0
  else
    Result := _libc_memcmp(P1, P2, N);
end;

{ ------------------------------------------------------------------ }
{ String ARC                                                           }
{ ------------------------------------------------------------------ }

procedure _StringAddRef(Ptr: Pointer);
var
  RC: ^Integer;
begin
  if Ptr = nil then Exit;
  RC := Ptr - HDR_SIZE;   { RefCount at data_ptr − 12 }
  if RC^ = IMMORTAL then Exit;
  RC^ := RC^ + 1;
end;

procedure _StringRelease(Ptr: Pointer);
var
  Base: Pointer;
  RC, LN, CP: ^Integer;
begin
  if Ptr = nil then Exit;
  Base := Ptr - HDR_SIZE;  { header base = data_ptr − 12 }
  RC   := Base;
  if RC^ = IMMORTAL then Exit;
  { Sanity-check the header before decrement.  Catches double-free,
    use-after-free, and write-past-end corruption with a clear message
    instead of a wild segfault later. }
  LN := Base + 4;
  CP := Base + 8;
  _StringReleaseCheck(Ptr, RC^, LN^, CP^);
  RC^ := RC^ - 1;
  if RC^ = 0 then _libc_free(Base);
end;

function _StringEquals(S1, S2: Pointer): Integer;
var
  Len1, Len2: Integer;
  LN:         ^Integer;
  C1, C2:     PChar;
begin
  if S1 = S2 then
  begin
    Result := 1;
    Exit;
  end;
  if S1 = nil then
    Len1 := 0
  else
  begin
    LN   := S1 - 8;   { Length at data_ptr − 8 }
    Len1 := LN^;
  end;
  if S2 = nil then
    Len2 := 0
  else
  begin
    LN   := S2 - 8;
    Len2 := LN^;
  end;
  if Len1 <> Len2 then
  begin
    Result := 0;
    Exit;
  end;
  if Len1 = 0 then
  begin
    Result := 1;
    Exit;
  end;
  C1 := PChar(S1);    { data IS the pointer }
  C2 := PChar(S2);
  if MemCompare(C1, C2, Len1) = 0 then
    Result := 1
  else
    Result := 0;
end;

function _StringConcat(S1, S2: Pointer): Pointer;
var
  Len1, Len2, Total: Integer;
  LN:                ^Integer;
  Base:              Pointer;
  RC, LenF, CapF:    ^Integer;
  Dst:               PChar;
begin
  if S1 = nil then
    Len1 := 0
  else
  begin
    LN   := S1 - 8;   { Length at data_ptr − 8 }
    Len1 := LN^;
  end;
  if S2 = nil then
    Len2 := 0
  else
  begin
    LN   := S2 - 8;
    Len2 := LN^;
  end;
  Total  := Len1 + Len2;
  Base   := _libc_malloc(Int64(HDR_SIZE + Total + 1));
  if Base = nil then Exit;
  RC    := Base;             { RefCount at base+0 }
  RC^   := 0;
  LenF  := Base + 4;
  LenF^ := Total;
  CapF  := Base + 8;
  CapF^ := Total;
  Result := Base + HDR_SIZE; { DATA POINTER }
  Dst    := PChar(Result);
  if Len1 > 0 then
    MemCopy(Dst, PChar(S1), Len1);
  if Len2 > 0 then
    MemCopy(Dst + Len1, PChar(S2), Len2);
  Dst[Total] := 0;
end;

{ ------------------------------------------------------------------ }
{ Class ARC (no function pointers needed here)                         }
{ ------------------------------------------------------------------ }

procedure TObject_Destroy(Self: Pointer);
begin
end;

{ TObject_ToString: returns the class name as an immortal string.
  Instance layout: Self[0] = vptr -> vtable.
  Vtable layout:   vtable[0] = typeinfo, vtable[1] = Destroy, vtable[2] = ToString.
  Typeinfo layout: typeinfo[0]=parent, typeinfo[1]=impllist, typeinfo[2]=classname ptr. }
function TObject_ToString(Self: Pointer): Pointer;
var
  Slot:   ^Pointer;
  VTable: Pointer;
  TInfo:  Pointer;
begin
  if Self = nil then
    begin
    Result := nil;
    Exit;
    end;
  Slot   := Self;         { instance: first 8 bytes = vptr }
  VTable := Slot^;        { VTable points to vtable data }
  Slot   := VTable;       { vtable[0] = typeinfo ptr }
  TInfo  := Slot^;        { TInfo points to typeinfo data }
  Slot   := TInfo + 16;   { typeinfo[2] = classname, at byte offset 16 }
  Result := Slot^;
end;

{ _MethodAddress: walk the typeinfo chain for an instance, looking up
  Name in each class's published-method table.  Layout:
    instance[0]  = vptr -> vtable
    vtable[0]    = typeinfo
    typeinfo[3]  = published-methods table (or 0)
    methods[0]   = count (Int64)
    methods[1+]  = pairs of (name-string-data-ptr, code-ptr)
  Returns nil when no match is found.  Equality on names uses
  _StringEquals so the caller passes a Blaise string. }
function _MethodAddress(Self, Name: Pointer): Pointer;
var
  Slot:    ^Pointer;
  VTable:  Pointer;
  TInfo:   Pointer;
  Methods: Pointer;
  Count:   ^Int64;
  Entry:   ^Pointer;
  EntName: Pointer;
  EntAddr: Pointer;
  I:       Integer;
begin
  Result := nil;
  if (Self = nil) or (Name = nil) then Exit;
  Slot   := Self;
  VTable := Slot^;
  if VTable = nil then Exit;
  Slot  := VTable;
  TInfo := Slot^;
  while TInfo <> nil do
  begin
    Slot    := TInfo + 24;   { typeinfo[3] = methods table ptr }
    Methods := Slot^;
    if Methods <> nil then
    begin
      Count := Methods;
      Entry := Methods + 8;  { skip 8-byte count }
      for I := 0 to Integer(Count^) - 1 do
      begin
        EntName := Entry^;
        Entry   := Pointer(Entry) + 8;
        EntAddr := Entry^;
        Entry   := Pointer(Entry) + 8;
        if _StringEquals(EntName, Name) <> 0 then
        begin
          Result := EntAddr;
          Exit;
        end;
      end;
    end;
    Slot  := TInfo;          { typeinfo[0] = parent }
    TInfo := Slot^;
  end;
end;

{ _InheritsFrom: class-identity walk for TObject.InheritsFrom.
  AChild and AParent are both typeinfo pointers (the values returned by
  Obj.ClassType or a bare class-identifier reference).
  Returns True when AChild equals AParent or is a descendant of AParent.
  A nil AParent always returns False; a nil AChild always returns False. }
function _InheritsFrom(AChild, AParent: Pointer): Boolean;
var
  TI: ^Pointer;
  Current: Pointer;
begin
  Result := False;
  if (AChild = nil) or (AParent = nil) then Exit;
  Current := AChild;
  while Current <> nil do
  begin
    if Current = AParent then
    begin
      Result := True;
      Exit;
    end;
    TI      := Current;   { typeinfo[0] = parent pointer }
    Current := TI^;
  end;
end;

{ _ClassCreate: runtime equivalent of the inline EmitConstructorCall
  lowering the codegen produces for the static 'TFoo.Create' form.
  Reads totalsize, fieldcleanup pointer, and vtable pointer from the
  expanded class typeinfo (see typeinfo layout in uCodeGenQBE.pas's
  EmitTypeInfoDefs).  Allocates an instance, installs the vtable
  pointer at slot 0, and bumps the refcount once.

  Typeinfo offsets read here:
    typeinfo[ 4]  +32  -> totalsize  (Int64)
    typeinfo[ 5]  +40  -> $_FieldCleanup_<T>
    typeinfo[ 6]  +48  -> $vtable_<T> }
function _ClassCreate(TInfo: Pointer): Pointer;
var
  SizeSlot:    ^Int64;
  PtrSlot:     ^Pointer;
  Size:        Int64;
  Cleanup:     Pointer;
  VTable:      Pointer;
  UserPtr:     Pointer;
  VTableSlot:  ^Pointer;
begin
  Result := nil;
  if TInfo = nil then Exit;

  SizeSlot := TInfo + 32;
  Size     := SizeSlot^;

  PtrSlot  := TInfo + 40;
  Cleanup  := PtrSlot^;

  PtrSlot  := TInfo + 48;
  VTable   := PtrSlot^;

  UserPtr  := _ClassAlloc(Size, Cleanup);
  if UserPtr = nil then Exit;

  { Install the vtable pointer at instance[0] — the codegen emits
    'storel $vtable_T, %self' immediately after _ClassAlloc; mirror
    that here. }
  VTableSlot  := UserPtr;
  VTableSlot^ := VTable;

  _ClassAddRef(UserPtr);
  Result := UserPtr;
end;

procedure _ClassAddRef(UserPtr: Pointer);
var
  Hdr: Pointer;
  RC:  ^Integer;
begin
  if UserPtr = nil then Exit;
  Hdr := UserPtr - CLASS_HDR;
  RC  := Hdr;
  RC^ := RC^ + 1;
end;

procedure _ClassFree(UserPtr: Pointer);
begin
  if UserPtr = nil then Exit;
  _libc_free(UserPtr - CLASS_HDR);
end;

end.
