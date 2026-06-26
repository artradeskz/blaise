{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit rtl.platform.layout.freebsd;

// FreeBSD x86_64 struct layouts and OS constants — the concrete TPlatformLayout
// adapter for FreeBSD (docs/native-target-architecture.adoc, Step 0b;
// docs/freebsd-x86_64-backend-design.adoc, Step 2).
//
// This is the FreeBSD sibling of rtl.platform.layout.linux.  The POSIX method
// bodies in rtl.platform.posix are shared between Linux and FreeBSD; the only
// per-target divergence is the struct stat layout and a handful of OS constant
// values, both of which live here.  No conditional compilation: the FreeBSD RTL
// archive composes this unit in place of the Linux one.
//
// Layout pinned to FreeBSD 14.x amd64 (sys/sys/stat.h).  It is identical on
// FreeBSD 13.x: the ino_t/dev_t widening that changed struct stat landed in
// FreeBSD 12 and has been stable since, so 13.x and 14.x share these offsets.
//
// struct stat offsets (FreeBSD amd64): st_mode at byte 24, st_size at byte 112,
// st_mtim.tv_sec at byte 64.  The buffer is sized at 224 bytes
// (sizeof(struct stat)).  These differ from Linux (48/88/144) — reusing the
// Linux offsets here would read garbage file sizes and dates, the single most
// error-prone item in the FreeBSD port.
//
// The O_CREAT / O_TRUNC / O_APPEND flag bits also differ from Linux; the rest
// (S_*, SEEK_*, CLOCK_REALTIME, WNOHANG) happen to share Linux's values.

interface

uses
  rtl.platform;

type
  TPlatformLayoutFreeBSDX86_64 = class(TPlatformLayout)
  public
    function O_RDONLY: Integer; override;
    function O_WRONLY: Integer; override;
    function O_RDWR:   Integer; override;
    function O_CREAT:  Integer; override;
    function O_TRUNC:  Integer; override;
    function O_APPEND: Integer; override;

    function S_IFMT:  Integer; override;
    function S_IFDIR: Integer; override;

    function SEEK_SET: Integer; override;
    function SEEK_CUR: Integer; override;
    function SEEK_END: Integer; override;

    function CLOCK_REALTIME: Integer; override;
    function WNOHANG:        Integer; override;

    function StatBufSize: Integer; override;
    function StatSize(Buf: Pointer):  Int64; override;
    function StatMtime(Buf: Pointer): Int64; override;
    function StatMode(Buf: Pointer):  Integer; override;
  end;

implementation

const
  { FreeBSD 14.x amd64 struct stat field offsets (bytes). }
  STAT_OFF_MODE  = 24;   { st_mode  (mode_t, u16) }
  STAT_OFF_MTIME = 64;   { st_mtim.tv_sec (Int64) }
  STAT_OFF_SIZE  = 112;  { st_size  (off_t, Int64) }
  STAT_SIZE      = 224;  { sizeof(struct stat) }

function TPlatformLayoutFreeBSDX86_64.O_RDONLY: Integer; begin Result := 0;      end;
function TPlatformLayoutFreeBSDX86_64.O_WRONLY: Integer; begin Result := 1;      end;
function TPlatformLayoutFreeBSDX86_64.O_RDWR:   Integer; begin Result := 2;      end;
function TPlatformLayoutFreeBSDX86_64.O_CREAT:  Integer; begin Result := $0200;  end;
function TPlatformLayoutFreeBSDX86_64.O_TRUNC:  Integer; begin Result := $0400;  end;
function TPlatformLayoutFreeBSDX86_64.O_APPEND: Integer; begin Result := $0008;  end;

function TPlatformLayoutFreeBSDX86_64.S_IFMT:  Integer; begin Result := $F000; end;
function TPlatformLayoutFreeBSDX86_64.S_IFDIR: Integer; begin Result := $4000; end;

function TPlatformLayoutFreeBSDX86_64.SEEK_SET: Integer; begin Result := 0; end;
function TPlatformLayoutFreeBSDX86_64.SEEK_CUR: Integer; begin Result := 1; end;
function TPlatformLayoutFreeBSDX86_64.SEEK_END: Integer; begin Result := 2; end;

function TPlatformLayoutFreeBSDX86_64.CLOCK_REALTIME: Integer; begin Result := 0; end;
function TPlatformLayoutFreeBSDX86_64.WNOHANG:        Integer; begin Result := 1; end;

function TPlatformLayoutFreeBSDX86_64.StatBufSize: Integer;
begin
  Result := STAT_SIZE;
end;

function TPlatformLayoutFreeBSDX86_64.StatSize(Buf: Pointer): Int64;
var
  P: ^Int64;
begin
  P := Pointer(PChar(Buf) + STAT_OFF_SIZE);
  Result := P^;
end;

function TPlatformLayoutFreeBSDX86_64.StatMtime(Buf: Pointer): Int64;
var
  P: ^Int64;
begin
  P := Pointer(PChar(Buf) + STAT_OFF_MTIME);
  Result := P^;
end;

function TPlatformLayoutFreeBSDX86_64.StatMode(Buf: Pointer): Integer;
var
  P: ^Integer;
begin
  P := Pointer(PChar(Buf) + STAT_OFF_MODE);
  Result := P^;
end;

initialization
  if GPlatformLayout = nil then
    GPlatformLayout := TPlatformLayoutFreeBSDX86_64.Create();

end.
