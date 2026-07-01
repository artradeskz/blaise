{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit runtime.syscall.freebsd;

// FreeBSD x86_64 direct-syscall kernel leaf — the libc replacement for a static,
// libc-free FreeBSD ET_EXEC (docs/freebsd-x86_64-backend-design.adoc, Step 3/4).
//
// This is the FreeBSD sibling of runtime.syscall.linux.  It DEFINES the bare
// POSIX names that rtl.platform.posix references via `external name 'write'`
// etc.; the FreeBSD RTL composition links it (the link-time swap) in place of
// the Linux leaf, so the resulting binary reaches the kernel with raw
// `syscall`s and needs no libc, no PT_INTERP.
//
// Step 4a scope: the file/process syscall leaves (open/close/read/write/lseek,
// stat/fstat/mkdir/rmdir/unlink/rename/chdir/chmod, getpid/dup2/pipe/fork/
// execve/wait4/kill/getcwd, mmap/munmap/nanosleep/clock_gettime), plus the
// pre-existing `_exit`, `_sys_write` and `environ`.  The harder leaves
// (memcpy/memset, date math, the mmap allocator, threads) grow here in Steps
// 4b/4c.
//
// System V AMD64 -> FreeBSD syscall ABI:
//   * syscall number in %rax; args in %rdi,%rsi,%rdx,%r10,%r8,%r9 (the 4th C
//     arg %rcx must be moved to %r10 — the `syscall` instruction clobbers %rcx).
//   * The syscall NUMBERS differ from Linux (exit=1, write=4, read=3, open=5,
//     close=6 — see sys/syscall.h); they are NOT Linux's.  FreeBSD 12 renumbered
//     stat/fstat/lseek/mmap for the 64-bit-inode ("ino64") ABI; this leaf uses
//     the ino64 numbers to match the FreeBSD 14 224-byte `struct stat` that the
//     rtl.platform.layout.freebsd adapter expects.
//   * ERROR CONVENTION — the key FreeBSD difference from Linux.  FreeBSD reports
//     errors via the CARRY FLAG: on error CF is set and %rax holds a POSITIVE
//     errno; on success CF is clear and %rax is the result.  The Pascal call
//     sites in rtl.platform.posix expect the Linux -errno convention (they test
//     `if Fd < 0`, `< 0`, `<> 0`).  So every leaf that can fail translates:
//     after `syscall`, `jae` past a `negq %rax` when CF is clear (success —
//     leave %rax untouched); when CF is set, `negq %rax` turns the positive
//     errno into -errno.  Each body uses a UNIQUE local label (.Lok_xxx) so the
//     forward-local jumps do not collide when the unit assembles to one object.
//
// `nostackframe` lets each asm body own the frame so the registers hold the raw
// incoming arguments unmodified.

interface

{ File descriptors. }
function open(Path: PChar; Flags: Integer; Mode: Integer): Integer;
function close(Fd: Integer): Integer;
function read(Fd: Integer; Buf: Pointer; Count: Int64): Int64;
{ `write` collides with the Write/WriteLn builtin as a Pascal identifier, so the
  Pascal name is _sys_write; the asm body additionally emits a bare `write`
  label (.globl) so the linker symbol matches rtl.platform.posix's
  `external name 'write'`.  Every other leaf's name is a valid Pascal identifier
  and needs no alias. }
function _sys_write(Fd: Integer; Buf: Pointer; Count: Int64): Int64;
function lseek(Fd: Integer; Offset: Int64; Whence: Integer): Int64;

{ Filesystem. }
function fstat(Fd: Integer; Buf: Pointer): Integer;
{ FreeBSD's ino64 ABI has NO plain `stat` syscall — it is expressed as
  fstatat(AT_FDCWD, path, buf, 0).  This wrapper sets up that call so the bare
  `stat` symbol posix imports still resolves. }
function stat(Path: PChar; Buf: Pointer): Integer;
function mkdir(Path: PChar; Mode: Integer): Integer;
function rmdir(Path: PChar): Integer;
function unlink(Path: PChar): Integer;
function rename(OldPath, NewPath: PChar): Integer;
function chdir(Path: PChar): Integer;
function chmod(Path: PChar; Mode: Integer): Integer;

{ Process. }
function getpid: Integer;
function dup2(OldFd, NewFd: Integer): Integer;
{ FreeBSD deprecated the 2-arg pipe(2) (legacy 42); this calls pipe2(fds, 0). }
function pipe(Fds: Pointer): Integer;

{ Memory. }
function mmap(Addr: Pointer; Length: Int64; Prot, Flags, Fd: Integer;
             Offset: Int64): Pointer;
function munmap(Addr: Pointer; Length: Int64): Integer;

{ Time. }
function nanosleep(Req, Rem: Pointer): Integer;
function clock_gettime(ClockId: Integer; Ts: Pointer): Integer;

{ Process control + raw primitives the higher-level wrappers build on. }
function fork: Integer;
function execve(Path: PChar; Argv, Envp: Pointer): Integer;
function wait4(Pid: Integer; Status: Pointer; Options: Integer;
               Rusage: Pointer): Integer;
function kill(Pid, Sig: Integer): Integer;
{ Raw __getcwd(2): fills Buf (up to Size); returns 0 on success or -errno.  The
  wrapper in the posix layer adapts that to libc's buffer-pointer contract. }
function sys_getcwd(Buf: PChar; Size: Int64): Int64;

{ _exit(2) — SYS_exit = 1.  Terminates the process; never returns.  The
  unit-level routine name `_exit` already emits the unmangled `_exit` symbol that
  satisfies posix's `external name '_exit'`. }
procedure _exit(Code: Integer);

{ The current process environment (envp), captured by _start.  rtl.platform.posix
  / getenv walk this NULL-terminated array.  Defined here (as on Linux) so the
  kernel leaf owns it. }
var
  environ: Pointer;

implementation

{ ---- FreeBSD x86_64 syscall numbers (FreeBSD 14 sys/sys/syscall.h). ----
  Verified against
  https://raw.githubusercontent.com/freebsd/freebsd-src/release/14.0.0/sys/sys/syscall.h
  ino64 variants used where FreeBSD 12 renumbered (fstat=551, lseek=478,
  mmap=477; stat has no ino64 syscall — expressed via fstatat=552). }
const
  SYS_exit          = 1;
  SYS_fork          = 2;
  SYS_read          = 3;
  SYS_write         = 4;
  SYS_open          = 5;
  SYS_close         = 6;
  SYS_wait4         = 7;
  SYS_unlink        = 10;
  SYS_chdir         = 12;
  SYS_chmod         = 15;
  SYS_getpid        = 20;
  SYS_kill          = 37;
  SYS_munmap        = 73;
  SYS_dup2          = 90;
  SYS_rename        = 128;
  SYS_mkdir         = 136;
  SYS_rmdir         = 137;
  SYS_getcwd        = 326;   { __getcwd }
  SYS_clock_gettime = 232;
  SYS_nanosleep     = 240;
  SYS_mmap          = 477;   { ino64 (legacy freebsd6 mmap = 197) }
  SYS_lseek         = 478;   { ino64 (legacy lseek = 199) }
  SYS_fstat         = 551;   { ino64 (legacy freebsd11_fstat = 189) }
  SYS_fstatat       = 552;   { ino64 (legacy freebsd11_fstatat = 493) }
  SYS_pipe2         = 542;   { pipe(2) legacy 42 deprecated }
  SYS_execve        = 59;
  AT_FDCWD          = -100;  { dirfd for path-relative *at() syscalls at cwd }
{ The asm bodies use literal immediates (the assembler needs a literal, not a
  symbol); the const block above documents the number-to-name mapping. }

function open(Path: PChar; Flags: Integer; Mode: Integer): Integer;
  assembler; nostackframe;
asm
    movq $5, %rax            { SYS_open }
    syscall
    jae  .Lok_open           { CF clear = success }
    negq %rax                { CF set = error: errno -> -errno }
.Lok_open:
    ret
end;

function close(Fd: Integer): Integer;
  assembler; nostackframe;
asm
    movq $6, %rax            { SYS_close }
    syscall
    jae  .Lok_close
    negq %rax
.Lok_close:
    ret
end;

function read(Fd: Integer; Buf: Pointer; Count: Int64): Int64;
  assembler; nostackframe;
asm
    movq $3, %rax            { SYS_read }
    syscall
    jae  .Lok_read
    negq %rax
.Lok_read:
    ret
end;

{ write CAN fail; posix's write-loop expects a negative return on error, so it
  gets CF-translation too. }
function _sys_write(Fd: Integer; Buf: Pointer; Count: Int64): Int64;
  assembler; nostackframe;
asm
.globl write
write:
    movq $4, %rax            { SYS_write }
    syscall
    jae  .Lok_write
    negq %rax
.Lok_write:
    ret
end;

function lseek(Fd: Integer; Offset: Int64; Whence: Integer): Int64;
  assembler; nostackframe;
asm
    movq $478, %rax          { SYS_lseek (ino64) }
    syscall
    jae  .Lok_lseek
    negq %rax
.Lok_lseek:
    ret
end;

function fstat(Fd: Integer; Buf: Pointer): Integer;
  assembler; nostackframe;
asm
    movq $551, %rax          { SYS_fstat (ino64) }
    syscall
    jae  .Lok_fstat
    negq %rax
.Lok_fstat:
    ret
end;

{ stat(path, buf) -> fstatat(AT_FDCWD, path, buf, 0).  Incoming: %rdi=Path,
  %rsi=Buf.  Shift to the fstatat argument layout: dirfd(%rdi)=AT_FDCWD,
  path(%rsi)=Path, buf(%rdx)=Buf, flag(%r10)=0.  arg4 goes straight to %r10
  (the syscall's 4th kernel register); no %rcx move is needed since we build
  the arguments here rather than receive four C args. }
function stat(Path: PChar; Buf: Pointer): Integer;
  assembler; nostackframe;
asm
    movq %rsi, %rdx          { buf   -> arg3 }
    movq %rdi, %rsi          { path  -> arg2 }
    movq $-100, %rdi         { AT_FDCWD -> arg1 (dirfd) }
    xorq %r10, %r10          { flag = 0 -> arg4 }
    movq $552, %rax          { SYS_fstatat (ino64) }
    syscall
    jae  .Lok_stat
    negq %rax
.Lok_stat:
    ret
end;

function mkdir(Path: PChar; Mode: Integer): Integer;
  assembler; nostackframe;
asm
    movq $136, %rax          { SYS_mkdir }
    syscall
    jae  .Lok_mkdir
    negq %rax
.Lok_mkdir:
    ret
end;

function chmod(Path: PChar; Mode: Integer): Integer;
  assembler; nostackframe;
asm
    movq $15, %rax           { SYS_chmod }
    syscall
    jae  .Lok_chmod
    negq %rax
.Lok_chmod:
    ret
end;

function rmdir(Path: PChar): Integer;
  assembler; nostackframe;
asm
    movq $137, %rax          { SYS_rmdir }
    syscall
    jae  .Lok_rmdir
    negq %rax
.Lok_rmdir:
    ret
end;

function unlink(Path: PChar): Integer;
  assembler; nostackframe;
asm
    movq $10, %rax           { SYS_unlink }
    syscall
    jae  .Lok_unlink
    negq %rax
.Lok_unlink:
    ret
end;

function rename(OldPath, NewPath: PChar): Integer;
  assembler; nostackframe;
asm
    movq $128, %rax          { SYS_rename }
    syscall
    jae  .Lok_rename
    negq %rax
.Lok_rename:
    ret
end;

function chdir(Path: PChar): Integer;
  assembler; nostackframe;
asm
    movq $12, %rax           { SYS_chdir }
    syscall
    jae  .Lok_chdir
    negq %rax
.Lok_chdir:
    ret
end;

function getpid: Integer;
  assembler; nostackframe;
asm
    movq $20, %rax           { SYS_getpid }
    syscall
    ret                      { getpid never fails; no CF translation }
end;

function dup2(OldFd, NewFd: Integer): Integer;
  assembler; nostackframe;
asm
    movq $90, %rax           { SYS_dup2 }
    syscall
    jae  .Lok_dup2
    negq %rax
.Lok_dup2:
    ret
end;

{ pipe(fds) -> pipe2(fds, 0).  Incoming: %rdi=Fds; add flags=0 in %rsi. }
function pipe(Fds: Pointer): Integer;
  assembler; nostackframe;
asm
    xorq %rsi, %rsi          { flags = 0 }
    movq $542, %rax          { SYS_pipe2 }
    syscall
    jae  .Lok_pipe
    negq %rax
.Lok_pipe:
    ret
end;

{ mmap has 6 args; arg4 (Flags) arrives in %rcx (C ABI) but the kernel wants it
  in %r10.  Move it before the syscall. }
function mmap(Addr: Pointer; Length: Int64; Prot, Flags, Fd: Integer;
             Offset: Int64): Pointer;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $477, %rax          { SYS_mmap (ino64) }
    syscall
    jae  .Lok_mmap
    negq %rax
.Lok_mmap:
    ret
end;

function munmap(Addr: Pointer; Length: Int64): Integer;
  assembler; nostackframe;
asm
    movq $73, %rax           { SYS_munmap }
    syscall
    jae  .Lok_munmap
    negq %rax
.Lok_munmap:
    ret
end;

function nanosleep(Req, Rem: Pointer): Integer;
  assembler; nostackframe;
asm
    movq $240, %rax          { SYS_nanosleep }
    syscall
    jae  .Lok_nanosleep
    negq %rax
.Lok_nanosleep:
    ret
end;

function clock_gettime(ClockId: Integer; Ts: Pointer): Integer;
  assembler; nostackframe;
asm
    movq $232, %rax          { SYS_clock_gettime }
    syscall
    jae  .Lok_clock_gettime
    negq %rax
.Lok_clock_gettime:
    ret
end;

function fork: Integer;
  assembler; nostackframe;
asm
    movq $2, %rax            { SYS_fork }
    syscall
    jae  .Lok_fork
    negq %rax
.Lok_fork:
    ret
end;

function execve(Path: PChar; Argv, Envp: Pointer): Integer;
  assembler; nostackframe;
asm
    movq $59, %rax           { SYS_execve }
    syscall
    jae  .Lok_execve
    negq %rax
.Lok_execve:
    ret
end;

{ wait4 has 4 args; arg4 (Rusage) arrives in %rcx -> move to %r10. }
function wait4(Pid: Integer; Status: Pointer; Options: Integer;
               Rusage: Pointer): Integer;
  assembler; nostackframe;
asm
    movq %rcx, %r10
    movq $7, %rax            { SYS_wait4 }
    syscall
    jae  .Lok_wait4
    negq %rax
.Lok_wait4:
    ret
end;

function kill(Pid, Sig: Integer): Integer;
  assembler; nostackframe;
asm
    movq $37, %rax           { SYS_kill }
    syscall
    jae  .Lok_kill
    negq %rax
.Lok_kill:
    ret
end;

function sys_getcwd(Buf: PChar; Size: Int64): Int64;
  assembler; nostackframe;
asm
    movq $326, %rax          { SYS___getcwd }
    syscall
    jae  .Lok_getcwd
    negq %rax
.Lok_getcwd:
    ret
end;

{ _exit(code) — SYS_exit = 1.  Terminates the process; never returns, so no
  CF translation is needed. }
procedure _exit(Code: Integer); assembler; nostackframe;
asm
    movq $1, %rax            { SYS_exit }
    syscall
    ret
end;

end.
