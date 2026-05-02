{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

{
  Blaise RTL — output primitives (replaces printf/fprintf)

  _SysWriteStr, _SysWriteInt, _SysWriteInt64 write to any file
  descriptor using the POSIX write(2) syscall (via blaise_sys.c).
  No format strings, no libc I/O buffering.

  _SysWriteNewline is implemented in blaise_sys.c and declared here
  as external so callers can use it without a C dependency.
}

unit blaise_sys;

{$mode objfpc}{$H+}

interface

procedure _SysWriteStr(Fd: Integer; S: Pointer);
procedure _SysWriteInt(Fd: Integer; N: Integer);
procedure _SysWriteInt64(Fd: Integer; N: Int64);
procedure _SysWriteNewline(Fd: Integer); external name '_SysWriteNewline';

implementation

{ C syscall shim (blaise_sys.c) }
procedure _SysWrite(Fd: Integer; Buf: PChar; Len: Int64); external name '_SysWrite';

{ RTL symbols resolved at link time from blaise_str.o / blaise_arc.o }
function  _IntToStr(N: Integer): Pointer;   external name '_IntToStr';
function  _Int64ToStr(N: Int64): Pointer;   external name '_Int64ToStr';
procedure _StringAddRef(Ptr: Pointer);      external name '_StringAddRef';
procedure _StringRelease(Ptr: Pointer);     external name '_StringRelease';

{ Data-pointer convention: variable holds pointer to char data;
  length lives at data_ptr − 8; no HDR_SIZE offset needed for data access. }

procedure _SysWriteStr(Fd: Integer; S: Pointer);
var
  LPtr: ^Integer;
  Len:  Integer;
begin
  if S = nil then Exit;
  LPtr := S - 8;   { Length at data_ptr − 8 }
  Len  := LPtr^;
  if Len = 0 then Exit;
  _SysWrite(Fd, PChar(S), Int64(Len));  { data IS S }
end;

procedure _SysWriteInt(Fd: Integer; N: Integer);
var
  S:    Pointer;
  LPtr: ^Integer;
  Len:  Integer;
begin
  S := _IntToStr(N);
  _StringAddRef(S);
  LPtr := S - 8;
  Len  := LPtr^;
  _SysWrite(Fd, PChar(S), Int64(Len));
  _StringRelease(S);
end;

procedure _SysWriteInt64(Fd: Integer; N: Int64);
var
  S:    Pointer;
  LPtr: ^Integer;
  Len:  Integer;
begin
  S := _Int64ToStr(N);
  _StringAddRef(S);
  LPtr := S - 8;
  Len  := LPtr^;
  _SysWrite(Fd, PChar(S), Int64(Len));
  _StringRelease(S);
end;

end.
