{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

{
  Blaise RTL — ARC management (Pascal port of blaise_arc.c)

  String layout (shared with blaise_str.pas):
    +--[4 bytes]--+--[4 bytes]--+--[4 bytes]--+--[N bytes]--+--[1 byte]--+
    | RefCount    | Length      | Capacity    | UTF-8 data  | NUL        |
    +-------------+-------------+-------------+-------------+------------+
    ^--- string pointer

  Class instance layout:
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
procedure _ClassAddRef(UserPtr: Pointer);
procedure _ClassFree(UserPtr: Pointer);

implementation

const
  IMMORTAL  = -1;
  HDR_SIZE  = 12;   { string header: RefCount + Length + Capacity }
  CLASS_HDR = 16;   { class header:  RefCount + pad + cleanup ptr }

function  _libc_malloc(Size: Int64): Pointer;               external name 'malloc';
procedure _libc_free(Ptr: Pointer);                         external name 'free';
function  _libc_memcpy(Dst, Src: Pointer; N: Int64): Pointer; external name 'memcpy';
function  _libc_memcmp(S1, S2: Pointer; N: Int64): Integer; external name 'memcmp';

{ ------------------------------------------------------------------ }
{ String ARC                                                           }
{ ------------------------------------------------------------------ }

procedure _StringAddRef(Ptr: Pointer);
var
  RC: ^Integer;
begin
  if Ptr = nil then Exit;
  RC := Ptr;
  if RC^ = IMMORTAL then Exit;
  RC^ := RC^ + 1;
end;

procedure _StringRelease(Ptr: Pointer);
var
  RC: ^Integer;
begin
  if Ptr = nil then Exit;
  RC := Ptr;
  if RC^ = IMMORTAL then Exit;
  RC^ := RC^ - 1;
  if RC^ = 0 then _libc_free(Ptr);
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
    LN   := S1 + 4;
    Len1 := LN^;
  end;
  if S2 = nil then
    Len2 := 0
  else
  begin
    LN   := S2 + 4;
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
  C1 := PChar(S1 + HDR_SIZE);
  C2 := PChar(S2 + HDR_SIZE);
  if _libc_memcmp(C1, C2, Int64(Len1)) = 0 then
    Result := 1
  else
    Result := 0;
end;

function _StringConcat(S1, S2: Pointer): Pointer;
var
  Len1, Len2, Total: Integer;
  LN:                ^Integer;
  RC, LenF, CapF:    ^Integer;
  Dst:               PChar;
begin
  if S1 = nil then
    Len1 := 0
  else
  begin
    LN   := S1 + 4;
    Len1 := LN^;
  end;
  if S2 = nil then
    Len2 := 0
  else
  begin
    LN   := S2 + 4;
    Len2 := LN^;
  end;
  Total  := Len1 + Len2;
  Result := _libc_malloc(Int64(HDR_SIZE + Total + 1));
  if Result = nil then Exit;
  RC    := Result;
  RC^   := 0;
  LenF  := Result + 4;
  LenF^ := Total;
  CapF  := Result + 8;
  CapF^ := Total;
  Dst   := PChar(Result + HDR_SIZE);
  if Len1 > 0 then
    _libc_memcpy(Dst, S1 + HDR_SIZE, Int64(Len1));
  if Len2 > 0 then
    _libc_memcpy(Dst + Len1, S2 + HDR_SIZE, Int64(Len2));
  Dst[Total] := 0;
end;

{ ------------------------------------------------------------------ }
{ Class ARC (no function pointers needed here)                         }
{ ------------------------------------------------------------------ }

procedure TObject_Destroy(Self: Pointer);
begin
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
