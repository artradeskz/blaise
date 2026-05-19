{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  Blaise RTL — output primitives (replaces printf/fprintf)

  _SysWriteStr, _SysWriteInt, _SysWriteInt64 write to any file
  descriptor using the POSIX write(2) syscall directly — no C shim.
  No format strings, no libc I/O buffering.
}

unit blaise_sys;

{$mode objfpc}{$H+}

interface

procedure _SysWriteStr(Fd: Integer; S: Pointer);
procedure _SysWriteInt(Fd: Integer; N: Integer);
procedure _SysWriteInt64(Fd: Integer; N: Int64);
procedure _SysWriteNewline(Fd: Integer);

implementation

{ POSIX write(2) — declared directly; no C shim needed. }
function posix_write(Fd: Integer; Buf: PChar; Count: Int64): Int64; external name 'write';

{ RTL symbols resolved at link time from blaise_str.o / blaise_arc.o }
function  _IntToStr(N: Integer): Pointer;   external name '_IntToStr';
function  _Int64ToStr(N: Int64): Pointer;   external name '_Int64ToStr';
procedure _StringAddRef(Ptr: Pointer);      external name '_StringAddRef';
procedure _StringRelease(Ptr: Pointer);     external name '_StringRelease';

{ Data-pointer convention: variable holds pointer to char data;
  length lives at data_ptr − 8; no HDR_SIZE offset needed for data access. }

procedure SysWriteRaw(Fd: Integer; Buf: PChar; Len: Integer);
var
  P: PChar;
  Remaining: Int64;
  Written: Int64;
begin
  P := Buf;
  Remaining := Int64(Len);
  while Remaining > 0 do
  begin
    Written := posix_write(Fd, P, Remaining);
    if Written <= 0 then Break;
    P := P + Written;
    Remaining := Remaining - Written;
  end;
end;

procedure _SysWriteStr(Fd: Integer; S: Pointer);
var
  LPtr: ^Integer;
  Len: Integer;
begin
  if S = nil then Exit;
  LPtr := S - 8;
  Len := LPtr^;
  if Len = 0 then Exit;
  SysWriteRaw(Fd, PChar(S), Len);
end;

procedure _SysWriteNewline(Fd: Integer);
var
  NL: array[0..0] of Byte;
begin
  NL[0] := 10;
  SysWriteRaw(Fd, PChar(@NL[0]), 1);
end;

procedure _SysWriteInt(Fd: Integer; N: Integer);
var
  S: Pointer;
  LPtr: ^Integer;
  Len: Integer;
begin
  S := _IntToStr(N);
  _StringAddRef(S);
  LPtr := S - 8;
  Len := LPtr^;
  SysWriteRaw(Fd, PChar(S), Len);
  _StringRelease(S);
end;

procedure _SysWriteInt64(Fd: Integer; N: Int64);
var
  S: Pointer;
  LPtr: ^Integer;
  Len: Integer;
begin
  S := _Int64ToStr(N);
  _StringAddRef(S);
  LPtr := S - 8;
  Len := LPtr^;
  SysWriteRaw(Fd, PChar(S), Len);
  _StringRelease(S);
end;

end.
