{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  Blaise RTL — file I/O, CLI, and directory primitives.

  Replaces blaise_io.c with direct POSIX libc bindings.  All string
  arguments follow the Blaise data-pointer convention: the variable holds
  a pointer to char data; the 12-byte header (refcount/length/capacity)
  lives immediately before it.

  String memory is allocated via _BlaiseGetMem / _BlaiseFreeMem so that
  _StringRelease can free all strings through the same allocator.
}

unit blaise_io;

{$mode objfpc}{$H+}

interface

{ argc/argv — set by the QBE-emitted $main before user code runs. }
procedure _SetArgs(Argc: Integer; Argv: Pointer);
function  _ParamCount: Integer;
function  _ParamStr(Index: Integer): Pointer;

{ File operations }
function  _FileExists(Path: Pointer): Integer;
procedure _DeleteFile(Path: Pointer);
function  _RenameFile(OldPath, NewPath: Pointer): Integer;
function  _ReadFile(Path: Pointer): Pointer;
procedure _WriteFile(Path, Content: Pointer);
procedure _AppendFile(Path, Content: Pointer);

{ Directory operations }
function  _DirectoryExists(Path: Pointer): Integer;
function  _ForceDirectories(Path: Pointer): Integer;
procedure _RemoveDir(Path: Pointer);
function  _GetCurrentDir: Pointer;
function  _SetCurrentDir(Path: Pointer): Integer;

{ OS utilities }
function  _GetTempDir: Pointer;
function  _GetTempFileName(Dir, Prefix: Pointer): Pointer;
function  _GetProcessID: Integer;
function  _GetEnvVar(Name: Pointer): Pointer;
procedure _Sleep(Ms: Integer);
procedure _Halt(Code: Integer);
function  _Exec(Cmd: Pointer): Integer;

{ File-descriptor primitives (used by streams.pas) }
function  _FdOpenRead(Path: Pointer): Integer;
function  _FdOpenWrite(Path: Pointer): Integer;
function  _FdOpenAppend(Path: Pointer): Integer;
function  _FdRead(Fd: Integer; Buf: Pointer; Count: Integer): Integer;
function  _FdWrite(Fd: Integer; Buf: Pointer; Count: Integer): Integer;
function  _FdSeek(Fd: Integer; Offset: Int64; Origin: Integer): Int64;
function  _FdSize(Fd: Integer): Int64;
procedure _FdClose(Fd: Integer);

{ All libc/POSIX bindings in the interface section (Blaise requirement:
  external declarations with nil body must not appear in implementation). }

{ Memory }
function  _BlaiseGetMem(Size: Integer): Pointer; external name '_BlaiseGetMem';
procedure _BlaiseFreeMem(Ptr: Pointer);          external name '_BlaiseFreeMem';

{ String ARC (resolved from blaise_str.o / blaise_arc.o) }
procedure _StringAddRef(Ptr: Pointer);  external name '_StringAddRef';
procedure _StringRelease(Ptr: Pointer); external name '_StringRelease';

{ POSIX libc — file I/O }
type
  TStatBuf = record
    Dev:     Int64;
    Ino:     Int64;
    Nlink:   Int64;
    Mode:    Integer;
    Uid:     Integer;
    Gid:     Integer;
    Pad0:    Integer;
    Rdev:    Int64;
    Size:    Int64;
    Blksize: Int64;
    Blocks:  Int64;
    Atime:   Int64;
    AtimeNs: Int64;
    Mtime:   Int64;
    MtimeNs: Int64;
    Ctime:   Int64;
    CtimeNs: Int64;
    Unused:  array[0..2] of Int64;
  end;
  PStatBuf = ^TStatBuf;

  TTimeSpec = record
    Sec:  Int64;
    NSec: Int64;
  end;

function  libc_open(Path: PChar; Flags: Integer; Mode: Integer): Integer;   external name 'open';
function  libc_open2(Path: PChar; Flags: Integer): Integer;                 external name 'open';
function  libc_read(Fd: Integer; Buf: Pointer; Count: Int64): Int64;        external name 'read';
function  libc_write(Fd: Integer; Buf: Pointer; Count: Int64): Int64;       external name 'write';
function  libc_lseek(Fd: Integer; Offset: Int64; Whence: Integer): Int64;   external name 'lseek';
function  libc_close(Fd: Integer): Integer;                                  external name 'close';
function  libc_fstat(Fd: Integer; Buf: PStatBuf): Integer;                  external name 'fstat';
function  libc_stat(Path: PChar; Buf: PStatBuf): Integer;                   external name 'stat';
function  libc_mkdir(Path: PChar; Mode: Integer): Integer;                   external name 'mkdir';
function  libc_rmdir(Path: PChar): Integer;                                  external name 'rmdir';
function  libc_unlink(Path: PChar): Integer;                                 external name 'unlink';
function  libc_rename(OldPath, NewPath: PChar): Integer;                     external name 'rename';
function  libc_getcwd(Buf: PChar; Size: Int64): PChar;                       external name 'getcwd';
function  libc_chdir(Path: PChar): Integer;                                  external name 'chdir';
function  libc_getenv(Name: PChar): PChar;                                   external name 'getenv';
function  libc_mkstemp(Template: PChar): Integer;                            external name 'mkstemp';
function  libc_nanosleep(Req: Pointer; Rem: Pointer): Integer;               external name 'nanosleep';
function  libc_getpid: Integer;                                               external name 'getpid';
function  libc_system(Cmd: PChar): Integer;                                  external name 'system';
procedure libc_exit(Code: Integer);                                          external name 'exit';

{ strlen — needed to measure C strings returned by libc (e.g. getenv, getcwd) }
function  libc_strlen(S: PChar): Int64; external name 'strlen';

implementation

const
  BLAISE_STR_HDR = 12;  { refcount(4) + length(4) + capacity(4) }

  { open(2) flags }
  O_RDONLY = 0;
  O_WRONLY = 1;
  O_RDWR   = 2;
  O_CREAT  = $40;
  O_TRUNC  = $200;
  O_APPEND = $400;

  { stat mode bits }
  S_IFMT  = $F000;
  S_IFDIR = $4000;

  { lseek origins }
  SEEK_SET = 0;
  SEEK_CUR = 1;
  SEEK_END = 2;

{ --- Global argc/argv ------------------------------------------------- }

type
  TPCharArray = ^PChar;

var
  GArgC: Integer;
  GArgV: TPCharArray;

procedure _SetArgs(Argc: Integer; Argv: Pointer);
begin
  GArgC := Argc;
  GArgV := TPCharArray(Argv);
end;

function _ParamCount: Integer;
begin
  if GArgC > 0 then
    Result := GArgC - 1
  else
    Result := 0;
end;

{ --- Internal string helpers ------------------------------------------ }

{ Allocate a fresh Blaise string of Len bytes (refcount = 0).
  Returns the DATA POINTER (char data starts at result). }
function StrAlloc(Len: Integer): Pointer;
var
  Base:    PChar;
  RC, LN, CP: ^Integer;
  NulPtr:  PChar;
begin
  Base := _BlaiseGetMem(BLAISE_STR_HDR + Len + 1);
  if Base = nil then begin Result := nil; Exit end;
  RC  := Pointer(Base);      RC^ := 0;    { refcount  }
  LN  := Pointer(Base + 4);  LN^ := Len;  { length    }
  CP  := Pointer(Base + 8);  CP^ := Len;  { capacity  }
  NulPtr := PChar(Base + BLAISE_STR_HDR);
  NulPtr[Len] := #0;
  Result := Base + BLAISE_STR_HDR;  { DATA POINTER }
end;

{ Build a Blaise string from a C NUL-terminated string. }
function StrFromCStr(S: PChar): Pointer;
var
  Len: Integer;
  R:   PChar;
  I:   Integer;
begin
  if S = nil then begin Result := StrAlloc(0); Exit end;
  Len := Integer(libc_strlen(S));
  R := StrAlloc(Len);
  if (R <> nil) and (Len > 0) then
    for I := 0 to Len - 1 do
      R[I] := S[I];
  Result := R;
end;

{ Length of a Blaise string (data_ptr - 8). }
function StrLen(DataPtr: Pointer): Integer;
var
  LPtr: ^Integer;
begin
  if DataPtr = nil then begin Result := 0; Exit end;
  LPtr := Pointer(PChar(DataPtr) - 8);
  Result := LPtr^;
end;

{ NUL-terminated C string pointer of a Blaise string (data IS the pointer). }
function StrData(DataPtr: Pointer): PChar;
begin
  if DataPtr = nil then
    Result := nil
  else
    Result := PChar(DataPtr);
end;

{ --- argc/argv --------------------------------------------------------- }

function _ParamStr(Index: Integer): Pointer;
var
  Slot: TPCharArray;
begin
  if (GArgV = nil) or (Index < 0) or (Index >= GArgC) then
    begin Result := StrAlloc(0); Exit end;
  Slot := GArgV + (Index * SizeOf(Pointer));
  Result := StrFromCStr(Slot^);
end;

{ --- File operations --------------------------------------------------- }

function _FileExists(Path: Pointer): Integer;
var
  Fd: Integer;
begin
  Fd := libc_open2(StrData(Path), O_RDONLY);
  if Fd < 0 then begin Result := 0; Exit end;
  libc_close(Fd);
  Result := 1;
end;

procedure _DeleteFile(Path: Pointer);
begin
  libc_unlink(StrData(Path));
end;

function _RenameFile(OldPath, NewPath: Pointer): Integer;
begin
  if libc_rename(StrData(OldPath), StrData(NewPath)) = 0 then
    Result := 1
  else
    Result := 0;
end;

function _ReadFile(Path: Pointer): Pointer;
var
  Fd:   Integer;
  St:   TStatBuf;
  Sz:   Int64;
  R:    PChar;
  Got:  Int64;
  LPtr: ^Integer;
begin
  Fd := libc_open2(StrData(Path), O_RDONLY);
  if Fd < 0 then begin Result := StrAlloc(0); Exit end;
  if libc_fstat(Fd, @St) < 0 then begin libc_close(Fd); Result := StrAlloc(0); Exit end;
  Sz := St.Size;
  if Sz < 0 then begin libc_close(Fd); Result := StrAlloc(0); Exit end;
  R := StrAlloc(Integer(Sz));
  if R = nil then begin libc_close(Fd); Result := nil; Exit end;
  Got := libc_read(Fd, R, Sz);
  libc_close(Fd);
  { patch actual length read }
  LPtr  := Pointer(PChar(R) - 8);  LPtr^ := Integer(Got);  { length   }
  LPtr  := Pointer(PChar(R) - 4);  LPtr^ := Integer(Got);  { capacity }
  R[Integer(Got)] := #0;
  Result := R;
end;

procedure WriteAllToFd(Fd: Integer; Data: PChar; Len: Integer);
var
  P: PChar;
  Rem: Int64;
  Written: Int64;
begin
  P := Data;
  Rem := Int64(Len);
  while Rem > 0 do
  begin
    Written := libc_write(Fd, P, Rem);
    if Written <= 0 then Break;
    P := P + Written;
    Rem := Rem - Written;
  end;
end;

procedure _WriteFile(Path, Content: Pointer);
var
  Fd:  Integer;
  Len: Integer;
begin
  Fd := libc_open(StrData(Path), O_WRONLY or O_CREAT or O_TRUNC, 420 { 0644 });
  if Fd < 0 then Exit;
  Len := StrLen(Content);
  if Len > 0 then
    WriteAllToFd(Fd, StrData(Content), Len);
  libc_close(Fd);
end;

procedure _AppendFile(Path, Content: Pointer);
var
  Fd:  Integer;
  Len: Integer;
begin
  Fd := libc_open(StrData(Path), O_WRONLY or O_CREAT or O_APPEND, 420 { 0644 });
  if Fd < 0 then Exit;
  Len := StrLen(Content);
  if Len > 0 then
    WriteAllToFd(Fd, StrData(Content), Len);
  libc_close(Fd);
end;

{ --- Directory operations ---------------------------------------------- }

function _DirectoryExists(Path: Pointer): Integer;
var
  St: TStatBuf;
begin
  if libc_stat(StrData(Path), @St) <> 0 then begin Result := 0; Exit end;
  if (St.Mode and S_IFMT) = S_IFDIR then Result := 1 else Result := 0;
end;

function _ForceDirectories(Path: Pointer): Integer;
var
  P:     PChar;
  Buf:   array[0..4095] of Byte;
  BufP:  PChar;
  Len:   Integer;
  I:     Integer;
  Saved: Byte;
  St:    TStatBuf;
begin
  P := StrData(Path);
  if (P = nil) or (P[0] = #0) then begin Result := 0; Exit end;
  Len := Integer(libc_strlen(P));
  if Len >= 4096 then begin Result := 0; Exit end;
  BufP := PChar(@Buf[0]);
  for I := 0 to Len do BufP[I] := P[I];
  I := 1;
  while I <= Len do
  begin
    if (BufP[I] = '/') or (BufP[I] = #0) then
    begin
      Saved := Byte(BufP[I]);
      BufP[I] := #0;
      if libc_stat(BufP, @St) <> 0 then
      begin
        if libc_mkdir(BufP, 493 { 0755 }) <> 0 then
        begin
          Result := 0; Exit;
        end;
      end else if (St.Mode and S_IFMT) <> S_IFDIR then
      begin
        Result := 0; Exit;
      end;
      BufP[I] := Chr(Saved);
    end;
    Inc(I);
  end;
  Result := 1;
end;

procedure _RemoveDir(Path: Pointer);
begin
  libc_rmdir(StrData(Path));
end;

function _GetCurrentDir: Pointer;
var
  Buf:       array[0..4095] of Byte;
  CWD:       PChar;
  Len:       Integer;
  NeedSlash: Integer;
  R:         PChar;
  I:         Integer;
begin
  CWD := libc_getcwd(PChar(@Buf[0]), 4096);
  if CWD = nil then begin Result := StrAlloc(0); Exit end;
  Len := Integer(libc_strlen(CWD));
  if (Len > 0) and (CWD[Len - 1] <> '/') then NeedSlash := 1 else NeedSlash := 0;
  R := StrAlloc(Len + NeedSlash);
  if R = nil then begin Result := nil; Exit end;
  for I := 0 to Len - 1 do R[I] := CWD[I];
  if NeedSlash = 1 then R[Len] := '/';
  Result := R;
end;

function _SetCurrentDir(Path: Pointer): Integer;
begin
  if libc_chdir(StrData(Path)) = 0 then Result := 1 else Result := 0;
end;

{ --- OS utilities ------------------------------------------------------ }

function _GetTempDir: Pointer;
var
  Tmp:       PChar;
  Len:       Integer;
  NeedSlash: Integer;
  R:         PChar;
  I:         Integer;
begin
  Tmp := libc_getenv(StrData('TMPDIR'));
  if (Tmp = nil) or (Tmp[0] = #0) then Tmp := StrData('/tmp');
  Len := Integer(libc_strlen(Tmp));
  if (Len > 0) and (Tmp[Len - 1] <> '/') then NeedSlash := 1 else NeedSlash := 0;
  R := StrAlloc(Len + NeedSlash);
  if R = nil then begin Result := nil; Exit end;
  for I := 0 to Len - 1 do R[I] := Tmp[I];
  if NeedSlash = 1 then R[Len] := '/';
  Result := R;
end;

function _GetTempFileName(Dir, Prefix: Pointer): Pointer;
var
  DStr:      PChar;
  PStr:      PChar;
  DLen:      Integer;
  PLen:      Integer;
  NeedSlash: Integer;
  TmplLen:   Integer;
  Tmpl:      PChar;
  Tmp:       PChar;
  TmpLen:    Integer;
  Fd:        Integer;
  I:         Integer;
begin
  DStr := StrData(Dir);
  PStr := StrData(Prefix);
  if DStr = nil then DLen := 0 else DLen := Integer(libc_strlen(DStr));
  if PStr = nil then PLen := 0 else PLen := Integer(libc_strlen(PStr));

  if DLen = 0 then
  begin
    Tmp := libc_getenv(StrData('TMPDIR'));
    if (Tmp = nil) or (Tmp[0] = #0) then Tmp := StrData('/tmp');
    TmpLen := Integer(libc_strlen(Tmp));
    NeedSlash := 0;
    if (TmpLen > 0) and (Tmp[TmpLen - 1] <> '/') then NeedSlash := 1;
    TmplLen := TmpLen + NeedSlash + PLen + 6;
    Tmpl := _BlaiseGetMem(TmplLen + 1);
    if Tmpl = nil then begin Result := StrFromCStr(StrData('/tmp/blaise_XXXXXX')); Exit end;
    for I := 0 to TmpLen - 1 do Tmpl[I] := Tmp[I];
    if NeedSlash = 1 then Tmpl[TmpLen] := '/';
    for I := 0 to PLen - 1 do Tmpl[TmpLen + NeedSlash + I] := PStr[I];
    for I := 0 to 5 do Tmpl[TmpLen + NeedSlash + PLen + I] := 'X';
    Tmpl[TmplLen] := #0;
  end else
  begin
    NeedSlash := 0;
    if DStr[DLen - 1] <> '/' then NeedSlash := 1;
    TmplLen := DLen + NeedSlash + PLen + 6;
    Tmpl := _BlaiseGetMem(TmplLen + 1);
    if Tmpl = nil then begin Result := StrFromCStr(StrData('/tmp/blaise_XXXXXX')); Exit end;
    for I := 0 to DLen - 1 do Tmpl[I] := DStr[I];
    if NeedSlash = 1 then Tmpl[DLen] := '/';
    for I := 0 to PLen - 1 do Tmpl[DLen + NeedSlash + I] := PStr[I];
    for I := 0 to 5 do Tmpl[DLen + NeedSlash + PLen + I] := 'X';
    Tmpl[TmplLen] := #0;
  end;

  Fd := libc_mkstemp(Tmpl);
  if Fd >= 0 then libc_close(Fd);
  Result := StrFromCStr(Tmpl);
  _BlaiseFreeMem(Tmpl);
end;

function _GetProcessID: Integer;
begin
  Result := libc_getpid;
end;

function _GetEnvVar(Name: Pointer): Pointer;
var
  Val: PChar;
begin
  Val := libc_getenv(StrData(Name));
  if Val = nil then begin Result := StrAlloc(0); Exit end;
  Result := StrFromCStr(Val);
end;

procedure _Sleep(Ms: Integer);
var
  Ts: TTimeSpec;
begin
  Ts.Sec  := Ms div 1000;
  Ts.NSec := Int64(Ms mod 1000) * 1000000;
  libc_nanosleep(@Ts, nil);
end;

procedure _Halt(Code: Integer);
begin
  libc_exit(Code);
end;

function _Exec(Cmd: Pointer): Integer;
begin
  Result := libc_system(StrData(Cmd));
end;

{ --- File-descriptor primitives ---------------------------------------- }

function _FdOpenRead(Path: Pointer): Integer;
begin
  Result := libc_open2(StrData(Path), O_RDONLY);
end;

function _FdOpenWrite(Path: Pointer): Integer;
begin
  Result := libc_open(StrData(Path), O_WRONLY or O_CREAT or O_TRUNC, 420 { 0644 });
end;

function _FdOpenAppend(Path: Pointer): Integer;
begin
  Result := libc_open(StrData(Path), O_WRONLY or O_CREAT or O_APPEND, 420 { 0644 });
end;

function _FdRead(Fd: Integer; Buf: Pointer; Count: Integer): Integer;
begin
  if (Fd < 0) or (Count <= 0) then begin Result := 0; Exit end;
  Result := Integer(libc_read(Fd, Buf, Int64(Count)));
end;

function _FdWrite(Fd: Integer; Buf: Pointer; Count: Integer): Integer;
begin
  if (Fd < 0) or (Count <= 0) then begin Result := 0; Exit end;
  Result := Integer(libc_write(Fd, Buf, Int64(Count)));
end;

function _FdSeek(Fd: Integer; Offset: Int64; Origin: Integer): Int64;
var
  Whence: Integer;
begin
  case Origin of
    1: Whence := SEEK_CUR;
    2: Whence := SEEK_END;
  else
    Whence := SEEK_SET;
  end;
  Result := libc_lseek(Fd, Offset, Whence);
end;

function _FdSize(Fd: Integer): Int64;
var
  St: TStatBuf;
begin
  if libc_fstat(Fd, @St) <> 0 then begin Result := -1; Exit end;
  Result := St.Size;
end;

procedure _FdClose(Fd: Integer);
begin
  if Fd >= 0 then libc_close(Fd);
end;

end.
