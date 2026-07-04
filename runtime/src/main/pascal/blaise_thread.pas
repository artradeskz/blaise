{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise_thread;

{ POSIX thread primitives — direct bindings to pthread and sysconf.
  No C shim required; all functions use the standard C ABI which QBE
  already emits. }

interface

{ Thread creation / join }
function pthread_create(Thread: Pointer; Attr: Pointer;
  StartRoutine: Pointer; Arg: Pointer): Integer;
  external name 'pthread_create';
function pthread_join(Thread: Int64; RetVal: Pointer): Integer;
  external name 'pthread_join';

{ Mutex — callers allocate a 48-byte buffer (array[0..5] of Int64)
  and pass its address.  48 bytes covers pthread_mutex_t on all
  current Linux x86_64 and aarch64 targets (actual size is 40). }
function pthread_mutex_init(Mutex: Pointer; Attr: Pointer): Integer;
  external name 'pthread_mutex_init';
function pthread_mutex_lock(Mutex: Pointer): Integer;
  external name 'pthread_mutex_lock';
function pthread_mutex_unlock(Mutex: Pointer): Integer;
  external name 'pthread_mutex_unlock';
function pthread_mutex_destroy(Mutex: Pointer): Integer;
  external name 'pthread_mutex_destroy';

{ sysconf(_SC_NPROCESSORS_ONLN) — returns number of online CPUs. }
function sysconf(Name: Integer): Int64; external name 'sysconf';

const
  _SC_NPROCESSORS_ONLN = 84;

function GetCPUCount: Integer;

implementation

function GetCPUCount: Integer;
var N: Int64;
begin
  N := sysconf(_SC_NPROCESSORS_ONLN);
  if N > 0 then
    Result := Integer(N)
  else
    Result := 1
end;

end.
