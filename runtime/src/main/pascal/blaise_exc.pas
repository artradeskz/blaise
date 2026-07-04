{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  Blaise RTL — Exception frame management and type identity (pure Pascal)

  Replaces the former blaise_exc.c.  setjmp/longjmp are provided by a
  platform-specific assembly stub (blaise_setjmp_x86_64.s for x86_64)
  so the exception subsystem has zero C dependencies.

  Exception frame layout (BlaiseExcFrame):
    offset  0: jmp_buf  (64 bytes on x86_64 — 8 callee-saved registers)
    offset 64: exception  (Pointer — live exception object, nil on normal path)
    offset 72: prev       (Pointer — previous frame in thread-local chain)

  Frame size contract: the compiler allocates 512 bytes via QBE alloc16 for
  each try block.  This must be >= 80 bytes (64 jmp_buf + 2 pointers) on
  all supported targets.  The generous allocation leaves room for future
  ARM64 jmp_buf growth without a compiler change.

  Thread safety: g_exc_top and g_current_exception are declared as
  threadvar, giving each thread its own exception chain.
}

unit blaise_exc;

interface

procedure _PushExcFrame(Frame: Pointer);
procedure _PopExcFrame;
procedure _Raise(Obj: Pointer);
procedure _Reraise(Exc: Pointer);
function  _CurrentException: Pointer;
function  _CurrentExceptionMessage: Pointer;
function  _IsInstance(Obj: Pointer; Target: Pointer): Integer;
function  _ImplementsInterface(Obj: Pointer; IntfTI: Pointer): Integer;
function  _GetItab(Obj: Pointer; IntfTI: Pointer): Pointer;
procedure _Raise_InvalidCast;
procedure _CheckNil(Obj: Pointer);

implementation

const
  OFS_EXCEPTION = 64;
  OFS_PREV = 72;

type
  PPointer = ^Pointer;

procedure _blaise_longjmp(Buf: Pointer; Val: Integer); external name '_blaise_longjmp';

function  _BlaiseGetMem(Size: Integer): Pointer; external name '_BlaiseGetMem';
function  _libc_write(Fd: Integer; Buf: Pointer; Count: Int64): Int64; external name 'write';
procedure _libc_abort; external name 'abort';

threadvar
  g_exc_top: Pointer;
  g_current_exception: Pointer;

function ExcStrEmpty: Pointer;
var
  Base: Pointer;
  RC, LN, CP: ^Integer;
  Data: PChar;
begin
  Base := _BlaiseGetMem(13);
  if Base = nil then
  begin
    Exit(nil);
  end;
  RC := Base;
  RC^ := 0;
  LN := Base + 4;
  LN^ := 0;
  CP := Base + 8;
  CP^ := 0;
  Data := PChar(Base + 12);
  Data[0] := #0;
  Result := Base + 12;
end;

procedure _PushExcFrame(Frame: Pointer);
var
  ExcSlot: PPointer;
  PrevSlot: PPointer;
begin
  ExcSlot := Frame + OFS_EXCEPTION;
  ExcSlot^ := nil;
  PrevSlot := Frame + OFS_PREV;
  PrevSlot^ := g_exc_top;
  g_exc_top := Frame;
end;

procedure _PopExcFrame;
var
  PrevSlot: PPointer;
begin
  if g_exc_top <> nil then
  begin
    PrevSlot := g_exc_top + OFS_PREV;
    g_exc_top := PrevSlot^;
  end;
end;

procedure _Raise(Obj: Pointer);
var
  ExcSlot: PPointer;
begin
  if g_exc_top = nil then
    _libc_abort;
  g_current_exception := Obj;
  ExcSlot := g_exc_top + OFS_EXCEPTION;
  ExcSlot^ := Obj;
  _blaise_longjmp(g_exc_top, 1);
end;

procedure _Reraise(Exc: Pointer);
begin
  _Raise(Exc);
end;

function _CurrentException: Pointer;
begin
  Result := g_current_exception;
end;

function _CurrentExceptionMessage: Pointer;
var
  Exc: Pointer;
  MsgSlot: PPointer;
  Msg: Pointer;
begin
  Exc := g_current_exception;
  if Exc = nil then
  begin
    Exit(ExcStrEmpty());
  end;
  MsgSlot := Exc + 8;
  Msg := MsgSlot^;
  if Msg = nil then
    Result := ExcStrEmpty()
  else
    Result := Msg;
end;

{ ------------------------------------------------------------------
  Type identity — is / as operators
  ------------------------------------------------------------------

  BlaiseTypeInfo layout (matches the codegen-emitted typeinfo_ data):
    offset 0: parent    (Pointer — parent class TypeInfo, or nil for root)
    offset 8: impllist  (Pointer — nil-terminated array of (typeinfo*, itab*) pairs)
  ------------------------------------------------------------------ }

function _IsInstance(Obj: Pointer; Target: Pointer): Integer;
var
  VTable: PPointer;
  TI: Pointer;
  ParentSlot: PPointer;
begin
  Result := 0;
  if (Obj = nil) or (Target = nil) then Exit;
  VTable := PPointer(Obj)^;
  TI := VTable^;
  while TI <> nil do
  begin
    if TI = Target then
    begin
      Exit(1);
    end;
    ParentSlot := TI;
    TI := ParentSlot^;
  end;
end;

function _ImplementsInterface(Obj: Pointer; IntfTI: Pointer): Integer;
var
  VTable: PPointer;
  TI: Pointer;
  ParentSlot: PPointer;
  ImplSlot: PPointer;
  Impl: PPointer;
begin
  Result := 0;
  if (Obj = nil) or (IntfTI = nil) then Exit;
  VTable := PPointer(Obj)^;
  TI := VTable^;
  while TI <> nil do
  begin
    ImplSlot := TI + 8;
    Impl := ImplSlot^;
    while (Impl <> nil) and (Impl^ <> nil) do
    begin
      if Impl^ = IntfTI then
      begin
        Exit(1);
      end;
      Impl := Pointer(Impl) + 16;
    end;
    ParentSlot := TI;
    TI := ParentSlot^;
  end;
end;

function _GetItab(Obj: Pointer; IntfTI: Pointer): Pointer;
var
  VTable: PPointer;
  TI: Pointer;
  ParentSlot: PPointer;
  ImplSlot: PPointer;
  Impl: PPointer;
  ItabSlot: PPointer;
begin
  Result := nil;
  if (Obj = nil) or (IntfTI = nil) then Exit;
  VTable := PPointer(Obj)^;
  TI := VTable^;
  while TI <> nil do
  begin
    ImplSlot := TI + 8;
    Impl := ImplSlot^;
    while (Impl <> nil) and (Impl^ <> nil) do
    begin
      if Impl^ = IntfTI then
      begin
        ItabSlot := Pointer(Impl) + 8;
        Exit(ItabSlot^);
      end;
      Impl := Pointer(Impl) + 16;
    end;
    ParentSlot := TI;
    TI := ParentSlot^;
  end;
end;

procedure DiagAbort(Msg: Pointer; Len: Integer);
var
  NL: Byte;
begin
  _libc_write(2, Msg, Int64(Len));
  NL := 10;
  _libc_write(2, @NL, 1);
  _libc_abort;
end;

procedure _Raise_InvalidCast;
begin
  DiagAbort('Runtime error: invalid typecast', 31);
end;

procedure _CheckNil(Obj: Pointer);
begin
  if Obj = nil then
    DiagAbort('Runtime error: method call on nil object', 41);
end;

end.
