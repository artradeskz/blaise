{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
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
procedure _ClassAddRef(UserPtr: Pointer);
procedure _ClassFree(UserPtr: Pointer);

implementation

const
  IMMORTAL  = -1;
  HDR_SIZE  = 12;   { string header: RefCount + Length + Capacity }
  CLASS_HDR = 16;   { class header:  RefCount + pad + cleanup ptr }

function  _libc_malloc(Size: Int64): Pointer; external name 'malloc';
procedure _libc_free(Ptr: Pointer);           external name 'free';

procedure MemCopy(Dst, Src: Pointer; N: Integer);
var
  D, S: PChar;
  I:    Integer;
begin
  D := PChar(Dst);
  S := PChar(Src);
  for I := 0 to N - 1 do
    D[I] := S[I];
end;

function MemCompare(P1, P2: Pointer; N: Integer): Integer;
var
  A, B: PChar;
  I:    Integer;
begin
  A := PChar(P1);
  B := PChar(P2);
  for I := 0 to N - 1 do
    if A[I] <> B[I] then
    begin
      Result := A[I] - B[I];
      Exit;
    end;
  Result := 0;
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
  RC:   ^Integer;
begin
  if Ptr = nil then Exit;
  Base := Ptr - HDR_SIZE;  { header base = data_ptr − 12 }
  RC   := Base;
  if RC^ = IMMORTAL then Exit;
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
