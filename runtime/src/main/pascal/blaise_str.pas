{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  Blaise RTL — string operation functions (Pascal port of blaise_str.c)

  String memory layout — data-pointer convention:

    Allocation:
      +--[4 bytes]--+--[4 bytes]--+--[4 bytes]--+--[N bytes]--+--[1 byte]--+
      | RefCount    | Length      | Capacity    | UTF-8 data  | NUL        |
      +-------------+-------------+-------------+-------------+------------+
      ^--- base (raw malloc result)             ^--- DATA POINTER (stored in var)

  The variable slot holds the DATA POINTER (pointing at the first character
  byte).  The 12-byte header lives immediately before it at negative offsets:

      data_ptr − 12  RefCount  (Integer, 4 bytes)
      data_ptr −  8  Length    (Integer, 4 bytes)
      data_ptr −  4  Capacity  (Integer, 4 bytes)
      data_ptr +  0  char data (Length bytes + NUL terminator)

  nil represents an empty / unassigned string.
  RefCount = -1 marks immortal (statically-allocated string literals).
}

unit blaise_str;

{$mode objfpc}{$H+}

interface

{ ------------------------------------------------------------------ }
{ Libc bindings                                                        }
{ ------------------------------------------------------------------ }
procedure _libc_memcpy(Dst, Src: Pointer; N: Int64);                   external name 'memcpy';

{ blaise_mem bindings — link directly by symbol name.  We avoid
  'uses blaise_mem' because that would pull blaise_mem's implementation-
  section _libc_memcpy declaration into our namespace and conflict with
  the one above. }
function  _BlaiseGetMem(Size: Integer): Pointer; external name '_BlaiseGetMem';
procedure _BlaiseFreeMem(Ptr: Pointer);          external name '_BlaiseFreeMem';

{ ------------------------------------------------------------------ }
{ String RTL public interface                                          }
{ ------------------------------------------------------------------ }
function  _StringLength(S: Pointer): Integer;
function  _StringPos(Sub, S: Pointer): Integer;
function  _StringPosEx(Sub, S: Pointer; StartPos: Integer): Integer;
function  _StringCopy(S: Pointer; From, Count: Integer): Pointer;
function  _StringDelete(S: Pointer; Idx, Count: Integer): Pointer;
function  _StringSetLength(S: Pointer; N: Integer): Pointer;
function  _StringUpperCase(S: Pointer): Pointer;
function  _StringLowerCase(S: Pointer): Pointer;
function  _StringTrim(S: Pointer): Pointer;
function  _StringSameText(S1, S2: Pointer): Integer;
function  _IntToStr(N: Integer): Pointer;
function  _Int64ToStr(N: Int64): Pointer;
function  _StrToInt(S: Pointer): Integer;
function  _StrToInt64(S: Pointer): Int64;
function  _OrdAt(S: Pointer; I: Integer): Integer;
function  _Chr(N: Integer): Pointer;
function  _UpCase(N: Integer): Pointer;
function  _StringCompare(S1, S2: Pointer): Integer;
function  _StringCompareText(S1, S2: Pointer): Integer;
function  _StringFromPChar(P: PChar): Pointer;

{ ------------------------------------------------------------------ }
{ Dynamic array RTL                                                    }
{ ------------------------------------------------------------------ }

{ Dynamic array memory layout — data-pointer convention:
    [refcount:4][length:4][element 0][element 1]...
  The variable slot holds the DATA POINTER (element 0 address).
  nil represents an empty / unassigned array.
  Refcount = -1 marks immortal (statically-allocated).

  _DynArraySetLength(OldPtr, NewLen, ElemSize) → new data pointer.
  _DynArrayLength(Ptr) → length (0 for nil). }
function _DynArraySetLength(Ptr: Pointer; NewLen, ElemSize: Integer): Pointer;
function _DynArrayLength(Ptr: Pointer): Integer;

{ File-path manipulation — pure string operations, no OS calls }
function _ChangeFileExt(Path, Ext: Pointer): Pointer;
function _ExtractFileName(Path: Pointer): Pointer;
function _ExtractFilePath(Path: Pointer): Pointer;
function _ExtractFileDir(Path: Pointer): Pointer;
function _ExtractFileExt(Path: Pointer): Pointer;
function _IncludeTrailingPathDelimiter(Path: Pointer): Pointer;
function _ExcludeTrailingPathDelimiter(Path: Pointer): Pointer;

{ _StringFormatN — pure Pascal Format implementation.
  Args points to an array of 16-byte records: [Tag:Int64, Value:Int64].
  Tag=0 → integer (Value is the int), Tag=1 → string (Value is the pointer).
  Supported specifiers: %d (integer), %s (string), %% (literal %). }
function _StringFormatN(Fmt: Pointer; Args: Pointer; Count: Integer): Pointer;

implementation

const
  HDR_SIZE = 12;  { 3 x 4-byte integers: RefCount, Length, Capacity }

{ ------------------------------------------------------------------ }
{ Memory helpers                                                        }
{ ------------------------------------------------------------------ }

procedure MemCopy(Dst, Src: Pointer; N: Integer);
begin
  if N > 0 then
    _libc_memcpy(Dst, Src, N);
end;

{ ------------------------------------------------------------------ }
{ Internal helpers                                                     }
{ ------------------------------------------------------------------ }

{ StrLen: Ptr is the DATA pointer; length lives at Ptr-8 }
function StrLen(Ptr: Pointer): Integer;
var
  P: ^Integer;
begin
  if Ptr = nil then
    Result := 0
  else
  begin
    P := Ptr - 8;   { Length field at data_ptr − 8 }
    Result := P^;
  end;
end;

{ StrData: data IS the pointer — identity for data-pointer convention }
function StrData(Ptr: Pointer): PChar;
begin
  Result := PChar(Ptr);
end;

{ Allocate a new Blaise string of exactly Len bytes plus NUL.
  RefCount = 0 (unowned); caller must call _StringAddRef.
  Returns DATA POINTER (= base + HDR_SIZE). }
function StrAlloc(Len: Integer): Pointer;
var
  TotalL: Int64;
  Base:   Pointer;
  RC, LN, CP: ^Integer;
  NulPtr: PChar;
begin
  TotalL := Int64(HDR_SIZE) + Int64(Len) + 1;
  Base   := _BlaiseGetMem(Integer(TotalL));
  if Base = nil then
  begin
    Result := nil;
    Exit;
  end;
  RC  := Base;        { RefCount at base+0 }
  RC^ := 0;
  LN  := Base + 4;    { Length at base+4 }
  LN^ := Len;
  CP  := Base + 8;    { Capacity at base+8 }
  CP^ := Len;
  Result := Base + HDR_SIZE;   { DATA POINTER }
  NulPtr        := PChar(Result);
  NulPtr[Len]   := 0;          { NUL terminator at data+Len }
end;

{ ------------------------------------------------------------------ }
{ _StringLength                                                        }
{ ------------------------------------------------------------------ }

function _StringLength(S: Pointer): Integer;
begin
  Result := StrLen(S);
end;

{ ------------------------------------------------------------------ }
{ _StringPos(Sub, S) : Integer  — 0-based; -1 if not found           }
{ ------------------------------------------------------------------ }

function _StringPos(Sub, S: Pointer): Integer;
var
  SLen, SubLen: Integer;
  SData, SubData: PChar;
  I, J: Integer;
  Match: Boolean;
begin
  SLen   := StrLen(S);
  SubLen := StrLen(Sub);
  if SubLen = 0 then
  begin
    Result := 0;
    Exit;
  end;
  if SubLen > SLen then
  begin
    Result := -1;
    Exit;
  end;
  SData   := StrData(S);
  SubData := StrData(Sub);
  I := 0;
  while I <= SLen - SubLen do
  begin
    Match := True;
    J := 0;
    while J < SubLen do
    begin
      if SData[I + J] <> SubData[J] then
      begin
        Match := False;
        Break;
      end;
      Inc(J);
    end;
    if Match then
    begin
      Result := I;
      Exit;
    end;
    Inc(I);
  end;
  Result := -1;
end;

{ ------------------------------------------------------------------ }
{ _StringPosEx(Sub, S, StartPos) — like _StringPos but starts from   }
{ the given 0-based position.  Returns -1 if not found.              }
{ ------------------------------------------------------------------ }

function _StringPosEx(Sub, S: Pointer; StartPos: Integer): Integer;
var
  SLen, SubLen: Integer;
  SData, SubData: PChar;
  I, J: Integer;
  Match: Boolean;
begin
  SLen   := StrLen(S);
  SubLen := StrLen(Sub);
  if SubLen = 0 then
  begin
    Result := 0;
    Exit;
  end;
  if (SubLen > SLen) or (StartPos >= SLen) then
  begin
    Result := -1;
    Exit;
  end;
  SData   := StrData(S);
  SubData := StrData(Sub);
  if StartPos < 0 then StartPos := 0;
  I := StartPos;
  while I <= SLen - SubLen do
  begin
    Match := True;
    J := 0;
    while J < SubLen do
    begin
      if SData[I + J] <> SubData[J] then
      begin
        Match := False;
        Break;
      end;
      Inc(J);
    end;
    if Match then
    begin
      Result := I;
      Exit;
    end;
    Inc(I);
  end;
  Result := -1;
end;

{ ------------------------------------------------------------------ }
{ _StringCopy(S, From, Count) : string  — 0-based From               }
{ ------------------------------------------------------------------ }

function _StringCopy(S: Pointer; From, Count: Integer): Pointer;
var
  SLen:  Integer;
  Data:  PChar;
begin
  SLen := StrLen(S);
  if From < 0 then From := 0;
  if From >= SLen then
  begin
    Result := StrAlloc(0);
    Exit;
  end;
  { Avoid signed overflow when Count is large (Copy(S, N, MaxInt) idiom) —
    compare Count against (SLen - From) instead of (From + Count) > SLen. }
  if (Count < 0) or (Count > SLen - From) then
    Count := SLen - From;
  Result := StrAlloc(Count);
  if (Result <> nil) and (Count > 0) then
  begin
    Data := StrData(S);
    MemCopy(StrData(Result), Data + From, Count);
  end;
end;

{ ------------------------------------------------------------------ }
{ _StringDelete(S, Idx, Count) : string                                }
{                                                                      }
{ Returns a new string with Count characters removed starting at Idx   }
{ (0-based).  Out-of-range Idx or non-positive Count returns a copy of }
{ the input.  Caller owns the returned string (RefCount = 0); callers  }
{ that overwrite a var-string slot must release the old value first    }
{ and addref the result, exactly as for _StringCopy.                   }
{ ------------------------------------------------------------------ }

function _StringDelete(S: Pointer; Idx, Count: Integer): Pointer;
var
  SLen, RemoveCount, NewLen: Integer;
  Data, ResData: PChar;
begin
  SLen := StrLen(S);
  if (Idx < 0) or (Idx >= SLen) or (Count <= 0) then
  begin
    Result := StrAlloc(SLen);
    if (Result <> nil) and (SLen > 0) then
      MemCopy(StrData(Result), StrData(S), SLen);
    Exit;
  end;
  RemoveCount := Count;
  if Idx + RemoveCount > SLen then
    RemoveCount := SLen - Idx;
  NewLen := SLen - RemoveCount;
  Result := StrAlloc(NewLen);
  if Result = nil then Exit;
  Data    := StrData(S);
  ResData := StrData(Result);
  if Idx > 0 then
    MemCopy(ResData, Data, Idx);
  if NewLen - Idx > 0 then
    MemCopy(ResData + Idx, Data + Idx + RemoveCount, NewLen - Idx);
end;

{ ------------------------------------------------------------------ }
{ _StringSetLength(S, N) : string                                      }
{                                                                      }
{ Returns a new string of length N.  Truncates if N <= old length;     }
{ pads with NUL bytes if N is larger.  Caller owns the result.         }
{ ------------------------------------------------------------------ }

function _StringSetLength(S: Pointer; N: Integer): Pointer;
var
  OldLen, CopyLen, I: Integer;
  Data, ResData:      PChar;
begin
  if N < 0 then N := 0;
  Result := StrAlloc(N);
  if (Result = nil) or (N = 0) then Exit;
  if S = nil then OldLen := 0 else OldLen := StrLen(S);
  if OldLen < N then CopyLen := OldLen else CopyLen := N;
  ResData := StrData(Result);
  if CopyLen > 0 then
  begin
    Data := StrData(S);
    MemCopy(ResData, Data, CopyLen);
  end;
  for I := CopyLen to N - 1 do
    ResData[I] := #0;
end;

{ ------------------------------------------------------------------ }
{ _StringUpperCase                                                     }
{ ------------------------------------------------------------------ }

function _StringUpperCase(S: Pointer): Pointer;
var
  Len:     Integer;
  SrcData: PChar;
  DstData: PChar;
  I, C:    Integer;
begin
  Len    := StrLen(S);
  Result := StrAlloc(Len);
  if Result = nil then Exit;
  SrcData := StrData(S);
  DstData := StrData(Result);
  for I := 0 to Len - 1 do
  begin
    C := SrcData[I];
    if (C >= 97) and (C <= 122) then
      DstData[I] := C - 32
    else
      DstData[I] := C;
  end;
end;

{ ------------------------------------------------------------------ }
{ _StringLowerCase                                                     }
{ ------------------------------------------------------------------ }

function _StringLowerCase(S: Pointer): Pointer;
var
  Len:     Integer;
  SrcData: PChar;
  DstData: PChar;
  I, C:    Integer;
begin
  Len    := StrLen(S);
  Result := StrAlloc(Len);
  if Result = nil then Exit;
  SrcData := StrData(S);
  DstData := StrData(Result);
  for I := 0 to Len - 1 do
  begin
    C := SrcData[I];
    if (C >= 65) and (C <= 90) then
      DstData[I] := C + 32
    else
      DstData[I] := C;
  end;
end;

{ ------------------------------------------------------------------ }
{ _StringTrim                                                          }
{ ------------------------------------------------------------------ }

function _StringTrim(S: Pointer): Pointer;
var
  Len:    Integer;
  Data:   PChar;
  Lo, Hi: Integer;
  NewLen: Integer;
begin
  Len  := StrLen(S);
  Data := StrData(S);
  Lo := 0;
  while Lo < Len do
  begin
    if Data[Lo] > 32 then Break;
    Inc(Lo);
  end;
  Hi := Len - 1;
  while Hi >= Lo do
  begin
    if Data[Hi] > 32 then Break;
    Dec(Hi);
  end;
  if Hi >= Lo then
    NewLen := Hi - Lo + 1
  else
    NewLen := 0;
  Result := StrAlloc(NewLen);
  if (Result = nil) or (NewLen = 0) then Exit;
  MemCopy(StrData(Result), Data + Lo, NewLen);
end;

{ ------------------------------------------------------------------ }
{ _StringSameText                                                      }
{ ------------------------------------------------------------------ }

function _StringSameText(S1, S2: Pointer): Integer;
var
  Len1, Len2, I: Integer;
  D1, D2:        PChar;
  C1, C2:        Integer;
begin
  Len1 := StrLen(S1);
  Len2 := StrLen(S2);
  if Len1 <> Len2 then
  begin
    Result := 0;
    Exit;
  end;
  D1 := StrData(S1);
  D2 := StrData(S2);
  for I := 0 to Len1 - 1 do
  begin
    C1 := D1[I];
    C2 := D2[I];
    if (C1 >= 65) and (C1 <= 90) then C1 := C1 + 32;
    if (C2 >= 65) and (C2 <= 90) then C2 := C2 + 32;
    if C1 <> C2 then
    begin
      Result := 0;
      Exit;
    end;
  end;
  Result := 1;
end;

{ ------------------------------------------------------------------ }
{ WriteDecimal — write N as decimal digits into Buf (no NUL).        }
{ Buf must have at least 21 bytes.  Returns character count.         }
{ ------------------------------------------------------------------ }

function WriteDecimal(N: Int64; Buf: PChar): Integer;
var
  IsNeg: Boolean;
  AbsN:  Int64;
  Pos:   Integer;
  Tmp:   Pointer;
  TP:    PChar;
  I, J:  Integer;
  Digit: Integer;
begin
  Tmp := _BlaiseGetMem(22);
  TP  := PChar(Tmp);
  IsNeg := N < 0;
  if IsNeg then
    AbsN := -N
  else
    AbsN := N;
  if AbsN = 0 then
  begin
    TP[0] := 48;  { '0' }
    Pos   := 1;
  end
  else
  begin
    Pos := 0;
    while AbsN > 0 do
    begin
      Digit  := Integer(AbsN mod 10);
      TP[Pos] := 48 + Digit;
      AbsN   := AbsN div 10;
      Inc(Pos);
    end;
  end;
  I := 0;
  if IsNeg then
  begin
    Buf[0] := 45;  { '-' }
    I := 1;
  end;
  J := Pos - 1;
  while J >= 0 do
  begin
    Buf[I] := TP[J];
    Inc(I);
    Dec(J);
  end;
  _BlaiseFreeMem(Tmp);
  Result := I;
end;

{ ------------------------------------------------------------------ }
{ _IntToStr                                                            }
{ ------------------------------------------------------------------ }

function _IntToStr(N: Integer): Pointer;
var
  Buf:     Pointer;
  BP:      PChar;
  Written: Integer;
begin
  Buf     := _BlaiseGetMem(22);
  BP      := PChar(Buf);
  Written := WriteDecimal(Int64(N), BP);
  Result  := StrAlloc(Written);
  if (Result <> nil) and (Written > 0) then
    MemCopy(StrData(Result), Buf, Written);
  _BlaiseFreeMem(Buf);
end;

{ ------------------------------------------------------------------ }
{ _Int64ToStr                                                          }
{ ------------------------------------------------------------------ }

function _Int64ToStr(N: Int64): Pointer;
var
  Buf:     Pointer;
  BP:      PChar;
  Written: Integer;
begin
  Buf     := _BlaiseGetMem(22);
  BP      := PChar(Buf);
  Written := WriteDecimal(N, BP);
  Result  := StrAlloc(Written);
  if (Result <> nil) and (Written > 0) then
    MemCopy(StrData(Result), Buf, Written);
  _BlaiseFreeMem(Buf);
end;

{ ------------------------------------------------------------------ }
{ _StrToInt / _StrToInt64                                             }
{ ------------------------------------------------------------------ }

function _StrToInt(S: Pointer): Integer;
var
  Data:  PChar;
  Neg:   Boolean;
  I, C:  Integer;
  Value: Int64;
begin
  Data  := StrData(S);
  I     := 0;
  Neg   := False;
  if Data[0] = 45 then  { '-' }
  begin
    Neg := True;
    I   := 1;
  end
  else if Data[0] = 43 then  { '+' }
    I := 1;
  Value := 0;
  if Data[I] = 36 then  { '$' — hexadecimal }
  begin
    Inc(I);
    C := Data[I];
    while ((C >= 48) and (C <= 57))
       or ((C >= 65) and (C <= 70))
       or ((C >= 97) and (C <= 102)) do
    begin
      if C >= 97 then
        Value := Value * 16 + Int64(C - 87)   { 'a'..'f' → 10..15 }
      else if C >= 65 then
        Value := Value * 16 + Int64(C - 55)   { 'A'..'F' → 10..15 }
      else
        Value := Value * 16 + Int64(C - 48);  { '0'..'9' }
      Inc(I);
      C := Data[I];
    end;
  end
  else
  begin
    C := Data[I];
    while (C >= 48) and (C <= 57) do
    begin
      Value := Value * 10 + Int64(C - 48);
      Inc(I);
      C := Data[I];
    end;
  end;
  if Neg then
    Result := Integer(-Value)
  else
    Result := Integer(Value);
end;

function _StrToInt64(S: Pointer): Int64;
var
  Data:  PChar;
  Neg:   Boolean;
  I, C:  Integer;
begin
  Data  := StrData(S);
  I     := 0;
  Neg   := False;
  if Data[0] = 45 then
  begin
    Neg := True;
    I   := 1;
  end
  else if Data[0] = 43 then
    I := 1;
  Result := 0;
  if Data[I] = 36 then  { '$' — hexadecimal }
  begin
    Inc(I);
    C := Data[I];
    while ((C >= 48) and (C <= 57))
       or ((C >= 65) and (C <= 70))
       or ((C >= 97) and (C <= 102)) do
    begin
      if C >= 97 then
        Result := Result * 16 + Int64(C - 87)
      else if C >= 65 then
        Result := Result * 16 + Int64(C - 55)
      else
        Result := Result * 16 + Int64(C - 48);
      Inc(I);
      C := Data[I];
    end;
  end
  else
  begin
    C := Data[I];
    while (C >= 48) and (C <= 57) do
    begin
      Result := Result * 10 + Int64(C - 48);
      Inc(I);
      C := Data[I];
    end;
  end;
  if Neg then
    Result := -Result;
end;

{ ------------------------------------------------------------------ }
{ _OrdAt                                                               }
{ ------------------------------------------------------------------ }

function _OrdAt(S: Pointer; I: Integer): Integer;
var
  Len:  Integer;
  Data: PChar;
begin
  Len  := StrLen(S);
  if (I < 0) or (I >= Len) then
  begin
    Result := 0;
    Exit;
  end;
  Data   := StrData(S);
  Result := Data[I];
end;

{ ------------------------------------------------------------------ }
{ _Chr                                                                 }
{ ------------------------------------------------------------------ }

function _Chr(N: Integer): Pointer;
var
  DP: PChar;
begin
  Result := StrAlloc(1);
  if Result = nil then Exit;
  DP    := StrData(Result);
  DP[0] := N;
end;

{ ------------------------------------------------------------------ }
{ _UpCase                                                              }
{ ------------------------------------------------------------------ }

function _UpCase(N: Integer): Pointer;
var
  C: Integer;
begin
  C := N;
  if (C >= 97) and (C <= 122) then
    C := C - 32;
  Result := _Chr(C);
end;

{ ------------------------------------------------------------------ }
{ _StringCompare                                                       }
{ ------------------------------------------------------------------ }

function _StringCompare(S1, S2: Pointer): Integer;
var
  Len1, Len2, Len: Integer;
  D1, D2:          PChar;
  I, C1, C2:       Integer;
begin
  Len1 := StrLen(S1);
  Len2 := StrLen(S2);
  if Len1 < Len2 then Len := Len1 else Len := Len2;
  D1 := StrData(S1);
  D2 := StrData(S2);
  for I := 0 to Len - 1 do
  begin
    C1 := D1[I];
    C2 := D2[I];
    if C1 <> C2 then
    begin
      Result := C1 - C2;
      Exit;
    end;
  end;
  Result := Len1 - Len2;
end;

{ ------------------------------------------------------------------ }
{ _StringCompareText                                                   }
{ ------------------------------------------------------------------ }

function _StringCompareText(S1, S2: Pointer): Integer;
var
  Len1, Len2, Len: Integer;
  D1, D2:          PChar;
  I, C1, C2:       Integer;
begin
  Len1 := StrLen(S1);
  Len2 := StrLen(S2);
  if Len1 < Len2 then Len := Len1 else Len := Len2;
  D1 := StrData(S1);
  D2 := StrData(S2);
  for I := 0 to Len - 1 do
  begin
    C1 := D1[I];
    C2 := D2[I];
    if (C1 >= 65) and (C1 <= 90) then C1 := C1 + 32;
    if (C2 >= 65) and (C2 <= 90) then C2 := C2 + 32;
    if C1 <> C2 then
    begin
      Result := C1 - C2;
      Exit;
    end;
  end;
  Result := Len1 - Len2;
end;

{ ------------------------------------------------------------------ }
{ _StringFromPChar                                                     }
{ ------------------------------------------------------------------ }

function _StringFromPChar(P: PChar): Pointer;
var
  Len: Integer;
begin
  if P = nil then
  begin
    Result := StrAlloc(0);
    Exit;
  end;
  Len := 0;
  while P[Len] <> 0 do
    Inc(Len);
  Result := StrAlloc(Len);
  if (Result <> nil) and (Len > 0) then
    MemCopy(StrData(Result), P, Len);
end;

{ ------------------------------------------------------------------ }
{ _StringFormat                                                        }
{ ------------------------------------------------------------------ }

function _StringFormatN(Fmt: Pointer; Args: Pointer; Count: Integer): Pointer;
var
  F, Dst: PChar;
  FLen, OutLen, I, ArgIdx, Tag, SLen, Written: Integer;
  Val: Int64;
  AP: Pointer;
  TagPtr, ValPtr: ^Int64;
  IntBuf: Pointer;
  IBP: PChar;
begin
  F := StrData(Fmt);
  FLen := StrLen(Fmt);
  ArgIdx := 0;

  { Pass 1: compute output length }
  OutLen := 0;
  I := 0;
  while I < FLen do
  begin
    if (F[I] = 37) and (I + 1 < FLen) then  { '%' }
    begin
      Inc(I);
      if F[I] = 100 then  { 'd' }
      begin
        if ArgIdx < Count then
        begin
          AP := Args + ArgIdx * 16;
          TagPtr := AP;
          ValPtr := AP + 8;
          Tag := Integer(TagPtr^);
          Val := ValPtr^;
          if Tag = 0 then
          begin
            IntBuf := _BlaiseGetMem(22);
            IBP := PChar(IntBuf);
            Written := WriteDecimal(Val, IBP);
            OutLen := OutLen + Written;
            _BlaiseFreeMem(IntBuf);
          end
          else
          begin
            SLen := StrLen(Pointer(Val));
            OutLen := OutLen + SLen;
          end;
        end;
        Inc(ArgIdx);
        Inc(I);
      end
      else if F[I] = 115 then  { 's' }
      begin
        if ArgIdx < Count then
        begin
          AP := Args + ArgIdx * 16;
          TagPtr := AP;
          ValPtr := AP + 8;
          Tag := Integer(TagPtr^);
          Val := ValPtr^;
          if Tag = 1 then
          begin
            SLen := StrLen(Pointer(Val));
            OutLen := OutLen + SLen;
          end
          else
          begin
            IntBuf := _BlaiseGetMem(22);
            IBP := PChar(IntBuf);
            Written := WriteDecimal(Val, IBP);
            OutLen := OutLen + Written;
            _BlaiseFreeMem(IntBuf);
          end;
        end;
        Inc(ArgIdx);
        Inc(I);
      end
      else if F[I] = 37 then  { '%%' → literal % }
      begin
        Inc(OutLen);
        Inc(I);
      end
      else
      begin
        OutLen := OutLen + 2;
        Inc(I);
      end;
    end
    else
    begin
      Inc(OutLen);
      Inc(I);
    end;
  end;

  Result := StrAlloc(OutLen);
  if Result = nil then Exit;
  Dst := PChar(Result);

  { Pass 2: fill buffer }
  I := 0;
  ArgIdx := 0;
  while I < FLen do
  begin
    if (F[I] = 37) and (I + 1 < FLen) then
    begin
      Inc(I);
      if F[I] = 100 then  { 'd' }
      begin
        if ArgIdx < Count then
        begin
          AP := Args + ArgIdx * 16;
          TagPtr := AP;
          ValPtr := AP + 8;
          Tag := Integer(TagPtr^);
          Val := ValPtr^;
          if Tag = 0 then
          begin
            IntBuf := _BlaiseGetMem(22);
            IBP := PChar(IntBuf);
            Written := WriteDecimal(Val, IBP);
            MemCopy(Dst, IBP, Written);
            Dst := Dst + Written;
            _BlaiseFreeMem(IntBuf);
          end
          else
          begin
            SLen := StrLen(Pointer(Val));
            if SLen > 0 then
              MemCopy(Dst, PChar(Pointer(Val)), SLen);
            Dst := Dst + SLen;
          end;
        end;
        Inc(ArgIdx);
        Inc(I);
      end
      else if F[I] = 115 then  { 's' }
      begin
        if ArgIdx < Count then
        begin
          AP := Args + ArgIdx * 16;
          TagPtr := AP;
          ValPtr := AP + 8;
          Tag := Integer(TagPtr^);
          Val := ValPtr^;
          if Tag = 1 then
          begin
            SLen := StrLen(Pointer(Val));
            if SLen > 0 then
              MemCopy(Dst, PChar(Pointer(Val)), SLen);
            Dst := Dst + SLen;
          end
          else
          begin
            IntBuf := _BlaiseGetMem(22);
            IBP := PChar(IntBuf);
            Written := WriteDecimal(Val, IBP);
            MemCopy(Dst, IBP, Written);
            Dst := Dst + Written;
            _BlaiseFreeMem(IntBuf);
          end;
        end;
        Inc(ArgIdx);
        Inc(I);
      end
      else if F[I] = 37 then
      begin
        Dst[0] := 37;
        Dst := Dst + 1;
        Inc(I);
      end
      else
      begin
        Dst[0] := 37;
        Dst := Dst + 1;
        Dst[0] := F[I];
        Dst := Dst + 1;
        Inc(I);
      end;
    end
    else
    begin
      Dst[0] := F[I];
      Dst := Dst + 1;
      Inc(I);
    end;
  end;
  Dst[0] := 0;
end;

{ ------------------------------------------------------------------ }
{ File-path manipulation                                               }
{ ------------------------------------------------------------------ }

function _ChangeFileExt(Path, Ext: Pointer): Pointer;
var
  P, E: PChar;
  PLen, ELen, I, DotPos, StemLen: Integer;
begin
  P := StrData(Path);
  E := StrData(Ext);
  PLen := StrLen(Path);
  ELen := StrLen(Ext);
  DotPos := -1;
  I := PLen - 1;
  while I >= 0 do
  begin
    if P[I] = 47 then Break;
    if P[I] = 46 then begin DotPos := I; Break end;
    Dec(I);
  end;
  if DotPos >= 0 then StemLen := DotPos else StemLen := PLen;
  Result := StrAlloc(StemLen + ELen);
  if Result = nil then Exit;
  if StemLen > 0 then MemCopy(Result, P, StemLen);
  if ELen > 0 then MemCopy(Result + StemLen, E, ELen);
end;

function _ExtractFileName(Path: Pointer): Pointer;
var
  P: PChar;
  PLen, I, Start: Integer;
begin
  P := StrData(Path);
  PLen := StrLen(Path);
  Start := 0;
  for I := 0 to PLen - 1 do
    if P[I] = 47 then Start := I + 1;
  Result := StrAlloc(PLen - Start);
  if (Result <> nil) and (PLen - Start > 0) then
    MemCopy(Result, P + Start, PLen - Start);
end;

function _ExtractFilePath(Path: Pointer): Pointer;
var
  P: PChar;
  PLen, I, SlashPos: Integer;
begin
  P := StrData(Path);
  PLen := StrLen(Path);
  SlashPos := -1;
  for I := 0 to PLen - 1 do
    if P[I] = 47 then SlashPos := I;
  if SlashPos < 0 then
  begin
    Result := StrAlloc(0);
    Exit;
  end;
  Result := StrAlloc(SlashPos + 1);
  if Result <> nil then MemCopy(Result, P, SlashPos + 1);
end;

function _ExtractFileDir(Path: Pointer): Pointer;
var
  P: PChar;
  PLen, I, SlashPos: Integer;
begin
  P := StrData(Path);
  PLen := StrLen(Path);
  SlashPos := -1;
  for I := 0 to PLen - 1 do
    if P[I] = 47 then SlashPos := I;
  if (SlashPos < 0) or (SlashPos = 0) then
  begin
    Result := StrAlloc(0);
    Exit;
  end;
  Result := StrAlloc(SlashPos);
  if Result <> nil then MemCopy(Result, P, SlashPos);
end;

function _ExtractFileExt(Path: Pointer): Pointer;
var
  P: PChar;
  PLen, I, LastDot, LastSep: Integer;
  ExtLen: Integer;
begin
  P := StrData(Path);
  PLen := StrLen(Path);
  LastDot := -1;
  LastSep := -1;
  for I := 0 to PLen - 1 do
  begin
    if P[I] = 47 then LastSep := I;
    if P[I] = 46 then LastDot := I;
  end;
  if (LastDot < 0) or ((LastSep >= 0) and (LastDot < LastSep)) then
  begin
    Result := StrAlloc(0);
    Exit;
  end;
  ExtLen := PLen - LastDot;
  Result := StrAlloc(ExtLen);
  if (Result <> nil) and (ExtLen > 0) then
    MemCopy(Result, P + LastDot, ExtLen);
end;

function _IncludeTrailingPathDelimiter(Path: Pointer): Pointer;
var
  P, DP: PChar;
  PLen: Integer;
begin
  P := StrData(Path);
  PLen := StrLen(Path);
  if (PLen > 0) and (P[PLen - 1] = 47) then
  begin
    Result := StrAlloc(PLen);
    if Result <> nil then MemCopy(Result, P, PLen);
    Exit;
  end;
  Result := StrAlloc(PLen + 1);
  if Result = nil then Exit;
  if PLen > 0 then MemCopy(Result, P, PLen);
  DP := StrData(Result);
  DP[PLen] := 47;
end;

function _ExcludeTrailingPathDelimiter(Path: Pointer): Pointer;
var
  P: PChar;
  PLen: Integer;
begin
  P := StrData(Path);
  PLen := StrLen(Path);
  if (PLen > 0) and (P[PLen - 1] = 47) then Dec(PLen);
  Result := StrAlloc(PLen);
  if (Result <> nil) and (PLen > 0) then
    MemCopy(Result, P, PLen);
end;

{ ------------------------------------------------------------------ }
{ Dynamic array RTL                                                    }
{ ------------------------------------------------------------------ }

const
  DA_HDR = 8;  { [refcount:4][length:4] before element 0 }

function _DynArrayLength(Ptr: Pointer): Integer;
var
  LenPtr: ^Integer;
begin
  if Ptr = nil then
  begin
    Result := 0;
    Exit;
  end;
  { length is stored at offset −4 from data pointer }
  LenPtr := Ptr - 4;
  Result := LenPtr^;
end;

procedure DaWriteInt32(P: ^Integer; V: Integer);
begin
  P^ := V;
end;

function _DynArraySetLength(Ptr: Pointer; NewLen, ElemSize: Integer): Pointer;
var
  NewBase:  Pointer;
  DataSz:   Integer;
  OldLen:   Integer;
  CopyLen:  Integer;
  ZP:       PChar;
  ZI:       Integer;
  HdrPtr:   ^Integer;
begin
  if NewLen <= 0 then
  begin
    if Ptr <> nil then
      _BlaiseFreeMem(Ptr - DA_HDR);
    Result := nil;
    Exit;
  end;
  DataSz  := DA_HDR + NewLen * ElemSize;
  NewBase := _BlaiseGetMem(DataSz);
  { write header: refcount = 1, length = NewLen }
  HdrPtr    := NewBase;
  DaWriteInt32(HdrPtr, 1);           { refcount }
  HdrPtr    := NewBase + 4;
  DaWriteInt32(HdrPtr, NewLen);      { length }
  { zero element area }
  ZP := PChar(NewBase) + DA_HDR;
  ZI := 0;
  while ZI < NewLen * ElemSize do
  begin
    ZP[ZI] := 0;
    ZI := ZI + 1;
  end;
  { copy existing elements }
  if Ptr <> nil then
  begin
    OldLen  := _DynArrayLength(Ptr);
    if OldLen < NewLen then CopyLen := OldLen else CopyLen := NewLen;
    if CopyLen > 0 then
      MemCopy(PChar(NewBase) + DA_HDR, PChar(Ptr), CopyLen * ElemSize);
    _BlaiseFreeMem(Ptr - DA_HDR);
  end;
  Result := PChar(NewBase) + DA_HDR;
end;

end.
