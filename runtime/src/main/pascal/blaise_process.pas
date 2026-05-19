{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  Blaise RTL — process management.

  Replaces blaise_process.c with direct POSIX libc bindings.
  BlaiseProcess is a Pascal record allocated via _BlaiseGetMem.

  API mirrors the C version exactly so the Pascal-side process.pas
  (stdlib) needs no changes.
}

unit blaise_process;

{$mode objfpc}{$H+}

interface

function  _ProcessCreate: Pointer;
procedure _ProcessSetExe(Proc: Pointer; ExeStr: Pointer);
procedure _ProcessAddArg(Proc: Pointer; ArgStr: Pointer);
procedure _ProcessExecute(Proc: Pointer);
function  _ProcessRunning(Proc: Pointer): Integer;
function  _ProcessReadOutput(Proc: Pointer): Pointer;
procedure _ProcessWaitOnExit(Proc: Pointer);
function  _ProcessExitCode(Proc: Pointer): Integer;
procedure _ProcessFree(Proc: Pointer);

{ All external POSIX bindings in the interface section (Blaise requirement). }

function  _BlaiseGetMem(Size: Integer): Pointer; external name '_BlaiseGetMem';
procedure _BlaiseFreeMem(Ptr: Pointer);          external name '_BlaiseFreeMem';
procedure _StringAddRef(Ptr: Pointer);           external name '_StringAddRef';
procedure _StringRelease(Ptr: Pointer);          external name '_StringRelease';

{ POSIX process primitives }
function  libc_fork: Integer;                              external name 'fork';
function  libc_execvp(File_: PChar; Argv: Pointer): Integer; external name 'execvp';
procedure libc_exit(Code: Integer);                        external name '_exit';
function  libc_waitpid(Pid: Integer; Status: Pointer; Options: Integer): Integer; external name 'waitpid';
function  libc_pipe(Fds: Pointer): Integer;                external name 'pipe';
function  libc_dup2(OldFd, NewFd: Integer): Integer;       external name 'dup2';
function  libc_read(Fd: Integer; Buf: Pointer; Count: Int64): Int64; external name 'read';
function  libc_close(Fd: Integer): Integer;                external name 'close';
function  libc_strlen(S: PChar): Int64;                    external name 'strlen';

implementation

const
  BLAISE_STR_HDR = 12;
  WNOHANG        = 1;

{ TPCharArray: pointer-to-pointer used for argv arrays. }
type
  TPCharArray = ^PChar;

{ BlaiseProcess record — mirrors the C struct layout in blaise_process.c. }
type
  TBlaiseProcess = record
    Exe:      PChar;        { heap copy of the executable path }
    Argv:     TPCharArray;  { NULL-terminated argv array, argv[0] = exe }
    ArgC:     Integer;      { number of user args (not counting exe slot) }
    ArgVCap:  Integer;      { allocated capacity of Argv }
    Pid:      Integer;      { child PID, 0 before Execute }
    PipeFd:   Integer;      { read end of stdout+stderr pipe, -1 when closed }
    ExitCode: Integer;
    Waited:   Integer;      { 1 after waitpid reaped the child }
  end;
  PBlaiseProcess = ^TBlaiseProcess;

{ --- Internal string helpers ------------------------------------------ }

function StrAlloc(Len: Integer): Pointer;
var
  Base:       PChar;
  RC, LN, CP: ^Integer;
  NulPtr:     PChar;
begin
  Base := _BlaiseGetMem(BLAISE_STR_HDR + Len + 1);
  if Base = nil then begin Result := nil; Exit end;
  RC  := Pointer(Base);      RC^ := 0;
  LN  := Pointer(Base + 4);  LN^ := Len;
  CP  := Pointer(Base + 8);  CP^ := Len;
  NulPtr := PChar(Base + BLAISE_STR_HDR);
  NulPtr[Len] := #0;
  Result := Base + BLAISE_STR_HDR;
end;

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
    for I := 0 to Len - 1 do R[I] := S[I];
  Result := R;
end;

function StrData(DataPtr: Pointer): PChar;
begin
  if DataPtr = nil then Result := nil else Result := PChar(DataPtr);
end;

{ Duplicate a C string onto the Blaise heap. }
function StrDup(S: PChar): PChar;
var
  Len: Integer;
  Buf: PChar;
  I:   Integer;
begin
  if S = nil then begin Result := nil; Exit end;
  Len := Integer(libc_strlen(S));
  Buf := _BlaiseGetMem(Len + 1);
  if Buf = nil then begin Result := nil; Exit end;
  for I := 0 to Len do Buf[I] := S[I];
  Result := Buf;
end;

{ Read a pointer from a TPCharArray slot at offset Index.
  Pointer arithmetic is byte-level, so scale by SizeOf(Pointer) = 8. }
function ArgvGet(Arr: TPCharArray; Index: Integer): PChar;
var
  Slot: TPCharArray;
begin
  Slot := Arr + (Index * SizeOf(Pointer));
  Result := Slot^;
end;

{ Write a pointer into a TPCharArray slot at offset Index. }
procedure ArgvSet(Arr: TPCharArray; Index: Integer; Val: Pointer);
var
  Slot: TPCharArray;
begin
  Slot := Arr + (Index * SizeOf(Pointer));
  Slot^ := PChar(Val);
end;

{ --- Process API ------------------------------------------------------- }

function _ProcessCreate: Pointer;
var
  P:    PBlaiseProcess;
  PB:   PChar;
  I:    Integer;
begin
  P := _BlaiseGetMem(SizeOf(TBlaiseProcess));
  if P = nil then begin Result := nil; Exit end;
  { zero-initialise }
  PB := PChar(P);
  for I := 0 to SizeOf(TBlaiseProcess) - 1 do
    PB[I] := #0;
  P^.PipeFd := -1;
  Result := P;
end;

procedure _ProcessSetExe(Proc: Pointer; ExeStr: Pointer);
var
  P: PBlaiseProcess;
begin
  P := Proc;
  if P^.Exe <> nil then _BlaiseFreeMem(P^.Exe);
  P^.Exe := StrDup(StrData(ExeStr));
end;

procedure _ProcessAddArg(Proc: Pointer; ArgStr: Pointer);
var
  P:       PBlaiseProcess;
  NewCap:  Integer;
  NewArgv: TPCharArray;
  I:       Integer;
begin
  P := Proc;
  { grow argv array if needed — leave room for exe slot + NULL }
  if P^.ArgC + 2 >= P^.ArgVCap then
  begin
    if P^.ArgVCap = 0 then NewCap := 8 else NewCap := P^.ArgVCap * 2;
    NewArgv := _BlaiseGetMem(NewCap * SizeOf(Pointer));
    if NewArgv = nil then Exit;
    for I := 0 to P^.ArgC - 1 do
      ArgvSet(NewArgv, I, ArgvGet(P^.Argv, I));
    if P^.Argv <> nil then _BlaiseFreeMem(P^.Argv);
    P^.Argv    := NewArgv;
    P^.ArgVCap := NewCap;
  end;
  ArgvSet(P^.Argv, P^.ArgC, StrDup(StrData(ArgStr)));
  Inc(P^.ArgC);
end;

procedure _ProcessExecute(Proc: Pointer);
var
  P:     PBlaiseProcess;
  Fds:   array[0..1] of Integer;
  Total: Integer;
  Argv:  TPCharArray;
  I:     Integer;
  Pid:   Integer;
begin
  P := Proc;
  Fds[0] := -1;
  Fds[1] := -1;
  if libc_pipe(@Fds[0]) < 0 then Exit;

  { Build argv: [exe, arg1, ..., argN, NULL] }
  Total := P^.ArgC + 2;
  Argv  := _BlaiseGetMem(Total * SizeOf(Pointer));
  if Argv = nil then begin libc_close(Fds[0]); libc_close(Fds[1]); Exit end;
  if P^.Exe <> nil then ArgvSet(Argv, 0, P^.Exe)
  else ArgvSet(Argv, 0, nil);
  for I := 0 to P^.ArgC - 1 do
    ArgvSet(Argv, I + 1, ArgvGet(P^.Argv, I));
  ArgvSet(Argv, Total - 1, nil);

  Pid := libc_fork;
  if Pid < 0 then
  begin
    _BlaiseFreeMem(Argv);
    libc_close(Fds[0]);
    libc_close(Fds[1]);
    Exit;
  end;

  if Pid = 0 then
  begin
    { child: redirect stdout+stderr to write end of pipe }
    libc_close(Fds[0]);
    libc_dup2(Fds[1], 1);  { STDOUT_FILENO }
    libc_dup2(Fds[1], 2);  { STDERR_FILENO }
    libc_close(Fds[1]);
    libc_execvp(ArgvGet(Argv, 0), Argv);
    libc_exit(127);
  end;

  { parent }
  _BlaiseFreeMem(Argv);
  libc_close(Fds[1]);
  P^.Pid    := Pid;
  P^.PipeFd := Fds[0];
  P^.Waited := 0;
end;

function _ProcessRunning(Proc: Pointer): Integer;
var
  P:      PBlaiseProcess;
  Status: Integer;
  R:      Integer;
begin
  P := Proc;
  if (P^.Waited <> 0) or (P^.Pid = 0) then begin Result := 0; Exit end;
  Status := 0;
  R := libc_waitpid(P^.Pid, @Status, WNOHANG);
  if R = P^.Pid then
  begin
    { WIFEXITED: status & $7F = 0 }
    if (Status and $7F) = 0 then
      P^.ExitCode := (Status shr 8) and $FF
    else
      P^.ExitCode := 1;
    P^.Waited := 1;
    Result := 0;
  end else if R = 0 then
    Result := 1
  else
    Result := 0;
end;

function _ProcessReadOutput(Proc: Pointer): Pointer;
var
  P:   PBlaiseProcess;
  Buf: array[0..4095] of Byte;
  N:   Int64;
  R:   PChar;
  I:   Integer;
begin
  P := Proc;
  if P^.PipeFd < 0 then begin Result := StrAlloc(0); Exit end;
  N := libc_read(P^.PipeFd, @Buf[0], 4096);
  if N <= 0 then
  begin
    libc_close(P^.PipeFd);
    P^.PipeFd := -1;
    Result := StrAlloc(0);
    Exit;
  end;
  R := StrAlloc(Integer(N));
  if R <> nil then
    for I := 0 to Integer(N) - 1 do R[I] := Chr(Buf[I]);
  Result := R;
end;

procedure _ProcessWaitOnExit(Proc: Pointer);
var
  P:      PBlaiseProcess;
  Status: Integer;
begin
  P := Proc;
  if (P^.Waited <> 0) or (P^.Pid = 0) then Exit;
  Status := 0;
  libc_waitpid(P^.Pid, @Status, 0);
  if (Status and $7F) = 0 then
    P^.ExitCode := (Status shr 8) and $FF
  else
    P^.ExitCode := 1;
  P^.Waited := 1;
end;

function _ProcessExitCode(Proc: Pointer): Integer;
begin
  Result := PBlaiseProcess(Proc)^.ExitCode;
end;

procedure _ProcessFree(Proc: Pointer);
var
  P:    PBlaiseProcess;
  I:    Integer;
  Slot: PChar;
begin
  P := Proc;
  if P = nil then Exit;
  if P^.PipeFd >= 0 then libc_close(P^.PipeFd);
  if P^.Exe <> nil then _BlaiseFreeMem(P^.Exe);
  if P^.Argv <> nil then
  begin
    for I := 0 to P^.ArgC - 1 do
    begin
      Slot := ArgvGet(P^.Argv, I);
      if Slot <> nil then _BlaiseFreeMem(Slot);
    end;
    _BlaiseFreeMem(P^.Argv);
  end;
  _BlaiseFreeMem(P);
end;

end.
