{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.native.x86_64;

{ x86_64 (System V AMD64 ABI) backend for the native code generator.

  Emits AT&T-syntax assembly text (fed to `as`/`cc`, like QBE's .s output).

  Expression evaluation strategy (naive, correctness-first): every integer
  expression is evaluated into %eax.  Binary operators evaluate the left
  operand into %eax, push it, evaluate the right operand into %eax, pop the
  left into %ecx, then combine.  This needs no register allocator and is
  correct for arbitrary nesting; the push/pop pairs are always balanced within
  one expression, so %rsp is back to its frame-aligned position at every call
  site (SysV requires 16-byte alignment at calls).

  Milestone M2: integer literals, + - * div mod, and Write/WriteLn of integers
  (mapped to the _SysWriteInt / _SysWriteNewline runtime calls). }

interface

uses
  SysUtils, Classes, contnrs, Generics.Collections, uAST, uSymbolTable, uStrCompat,
  blaise.codegen.native.backend, blaise.codegen.target;

type
  TX86_64Backend = class(TNativeBackend)
  protected
    FLabelCount: Integer;       { monotonic source of unique local labels }
    { Global slots to define in the .data section: program-level variables plus
      hidden for-loop end-value slots.  Insertion-ordered so EmitDataSection
      emits them in declaration order; ContainsKey gives O(1) dedup.  The value
      is the slot's static type so loads, stores, and the .data directive all
      pick the right width and signedness. }
    FDataGlobals: TOrderedDictionary<string, TTypeDesc>;
    { Class-name string blobs already emitted to avoid duplicate label errors.
      Keyed by mangled name. }
    FClassNameEmitted: TDictionary<string, Boolean>;
    { String literal pool: unique string values in encounter order.  Each gets
      a __sN label in .rodata (12-byte ARC header + data + NUL).  The data
      pointer (str_ptr convention) is header+12. }
    FStrLits: TStringList;

    { Current function's stack frame: maps a local name (param, var, or Result)
      to its negative %rbp-relative byte offset.  nil while emitting program
      $main (whose top-level vars are globals, not frame slots).  Built once per
      function then looked up by name on every ident read and assignment — a
      key->value map, so TDictionary is the right container for the access
      pattern. }
    FFrame:     TDictionary<string, Integer>;
    { Parallel to FFrame: the static type of each frame slot, so loads and
      stores pick the right width and signedness. }
    FFrameTypes: TDictionary<string, TTypeDesc>;
    FFrameSize:  Integer;       { bytes to reserve for locals (16-aligned) }

    { Loop label stacks for break/continue: the top entry is the innermost
      loop's end-label (break) or condition-label (continue).
      Parallel FBreakExcDepths / FContinueExcDepths record FExcDepth at the
      point where the loop was entered so EmitExcUnwind knows how many frames
      to pop on a non-local exit. }
    FBreakLabels:       TStack<string>;
    FContinueLabels:    TStack<string>;
    FBreakExcDepths:    TStack<Integer>;
    FContinueExcDepths: TStack<Integer>;
    { Exit label: when non-empty, Exit jumps here (function epilogue).  Empty
      in program $main where Exit maps to a bare return. }
    FExitLabel: string;
    { True when the current function returns a record via the sret convention:
      the hidden first param (%rdi) is the caller's result buffer; Result maps
      to the pointer stored in the Result frame slot; field writes dereference
      through it; the epilogue emits a plain ret. }
    FSretFunc: Boolean;

    { Exception-frame accounting (per-function, reset in ClearFrame):
      FExcDepth    — number of exc frames currently live (pushed − popped).
      FExcFrameNext — index of the next pre-allocated frame slot to consume.
      FFinallyStack — parallel to FExcDepth: the finally body for each live
                      try/finally frame, or nil for a try/except frame.
                      Used by EmitExcUnwind to run finally bodies on Exit/Break/Continue.
                      Uses TList<TCompoundStmt> so nil entries are safe (no ARC release). }
    FExcDepth:     Integer;
    FExcFrameNext: Integer;
    FFinallyStack: TList<TCompoundStmt>;
    { Number of exc frame global slots to emit for the program main body.
      Zero when no try stmts appear in the top-level program statements. }
    FProgExcFrameCount: Integer;

    { Allocate a fresh local assembly label (".L<prefix><N>"). }
    function NewLabel(const APrefix: string): string;
    { Register a global integer slot of the given type (idempotent; the first
      registration's type wins).  The width and signedness drive both the
      .data directive and every load/store of the slot. }
    procedure AddGlobal(const AName: string; AType: TTypeDesc);
    { The static type of a frame-local slot, or nil if AName is not a local. }
    function LocalType(const AName: string): TTypeDesc;
    { The static type of a program global, or nil if AName is not registered. }
    function GlobalType(const AName: string): TTypeDesc;
    { Emit the accumulated .data section (one slot per registered global). }
    procedure EmitDataSection;
    { Emit all class-related data: class-name strings, published-method tables,
      typeinfo blocks, vtables, itab/impllist blocks.  Mirrors QBE backend's
      EmitTypeInfoDefs + EmitVTableDefs.  Called from EmitProgram. }
    procedure EmitClassSection(AProg: TProgram);
    { Escape a Pascal string for use inside an AS .ascii directive. }
    function AsmEscapeString(const AStr: string): string;
    { Emit a leaq __sN+12(%rip), %rax for the string literal AValue,
      registering a new .rodata blob if not yet seen. }
    procedure EmitStrLitAddr(const AValue: string);
    { Emit string literal blobs in .rodata. Called from EmitDataSection. }
    procedure EmitStrLitSection;
    { Emit an immortal class-name string blob in the data section and return
      the label+12 expression that points to the character data. }
    function EmitClassNameString(const AClassName: string): string;
    { Emit the body of one $_FieldCleanup_<T> function.  For classes with
      no managed fields this is just a ret; with ARC string/class fields it
      would call release helpers (deferred — today all user classes have only
      integer fields). }
    procedure EmitFieldCleanupFn(const AMangledName: string;
                                 ART: TRecordTypeDesc);
    { Emit all class method definitions (OwnerTypeName <> ''). }
    procedure EmitClassMethods(AProg: TProgram);

    { True when AName is a slot in the current function frame. }
    function IsLocal(const AName: string): Boolean;
    { The AT&T operand addressing AName: "-N(%rbp)" for a frame local,
      "name(%rip)" for a global. }
    function VarOperand(const AName: string): string;
    { Operands for the two halves of an interface fat pointer.  Locals occupy
      a contiguous 16-byte slot (obj at the slot base, itab 8 bytes above);
      globals are two separate .data labels, AName + '_obj'/'_itab'. }
    function IntfObjOperand(const AName: string; AIsGlobal: Boolean): string;
    function IntfItabOperand(const AName: string; AIsGlobal: Boolean): string;
    { Lower one interface method call (TFieldAccessExpr.IsInterfaceCall or a
      TMethodCallExpr/Stmt whose ResolvedClassType is tyInterface): load obj +
      itab, index the itab by method slot, call the loaded pointer with obj as
      Self and AArgs after it.  Result (if any) left in %rax/%xmm0. }
    procedure EmitInterfaceCall(const AObjName: string; AIsGlobal: Boolean;
                                AIntf: TInterfaceTypeDesc;
                                const AMethName: string; AArgs: TObjectList);
    procedure EmitInterfaceFieldCall(AFld: TFieldInfo; AIntf: TInterfaceTypeDesc;
                                const AMethName: string; AArgs: TObjectList);
    { Emit typeinfo / itab / impllist blocks for interfaces and the classes
      that implement them.  Mirrors the QBE backend's EmitInterfaceDefs. }
    procedure EmitInterfaceDefs(AProg: TProgram);
    { Lower an assignment whose LHS is interface-typed.  Handles the four RHS
      forms: as-cast (T as IFoo via _GetItab), direct class->interface (static
      itab), interface->interface copy, and := nil.  Strong references only;
      weak interface refs are deferred. }
    procedure EmitInterfaceAssign(AAsgn: TAssignment);
    { True when AMethName resolves to an abstract slot on ARec (the itab entry
      must then point at _AbstractMethodError). }
    function IsAbstractClassMethod(ARec: TRecordTypeDesc;
                                   const AMethName: string): Boolean;
    { Load an integer-family value from AOperand into %rax, extended to 64
      bits per AType (sign/zero-extend by width and signedness). }
    procedure EmitLoadVar(const AOperand: string; AType: TTypeDesc);
    { Store the integer-family value currently in %rax into AOperand, using
      the right-width register sub-view for AType. }
    procedure EmitStoreVar(const AOperand: string; AType: TTypeDesc);
    { Reserve an 8-byte-aligned frame slot for AName:AType, advancing AOffset. }
    procedure AddSlot(const AName: string; AType: TTypeDesc;
                      var AOffset: Integer);
    { Build FFrame for a function: assign offsets to params, Result, locals. }
    procedure BuildFrame(ADecl: TMethodDecl);
    { Tear down the current frame. }
    procedure ClearFrame;

    procedure EmitProgram(AProg: TProgram); override;
    { Emit a standalone procedure/function definition. }
    procedure EmitFunctionDef(ADecl: TMethodDecl);
    { Spill incoming arg register AIdx into a param slot at AType's width. }
    procedure EmitSpillArg(AIdx: Integer; const AOperand: string;
                           AType: TTypeDesc);
    { Lower one statement. }
    procedure EmitStmt(AStmt: TASTStmt);
    { Lower a Write/WriteLn call (ANewline = WriteLn). }
    procedure EmitWrite(ACall: TProcCall; ANewline: Boolean);
    { Lower a for loop. }
    procedure EmitForStmt(AFor: TForStmt);
    { Count all try/finally and try/except statements nested inside AStmt
      (recursively) to pre-allocate exc frame slots in BuildFrame. }
    function CountTryStmts(AStmt: TASTStmt): Integer;
    { Unwind exception frames from FExcDepth down to ATargetDepth+1.
      For try/finally frames, emits the finally body inline.
      For try/except frames, only calls _PopExcFrame. }
    procedure EmitExcUnwind(ATargetDepth: Integer);
    { Lower try/finally. }
    procedure EmitTryFinallyStmt(AStmt: TTryFinallyStmt);
    { Lower try/except. }
    procedure EmitTryExceptStmt(AStmt: TTryExceptStmt);
    { Lower raise / bare raise. }
    procedure EmitRaiseStmt(AStmt: TRaiseStmt);
    { Allocate stack storage for an inline array literal [a,b,...], fill each
      element, and leave the base pointer in %rax.  Returns the number of bytes
      allocated on the stack (caller must addq that amount after the call). }
    function EmitOpenArrayLiteral(ALit: TArrayLiteralExpr): Integer;
    { Emit a direct call to a user procedure/function; result (if any) in %eax.
      ADecl is the callee's declaration (needed for var/out param handling);
      nil for type-cast calls. }
    procedure EmitCall(const AFuncSym: string; ADecl: TMethodDecl;
                       AArgs: TObjectList);
    { Emit a call to a record-returning function using the sret convention:
      ASretAddr is the AT&T operand for the destination buffer (already allocated
      by the caller), passed as the hidden first integer argument in %rdi. }
    procedure EmitSretCall(const AFuncSym: string; ADecl: TMethodDecl;
                           AArgs: TObjectList; const ASretAddr: string);
    { Indirect call: load a bare function pointer from APtrOperand (an AT&T
      memory operand, e.g. "-8(%rbp)"), set up args as for EmitCall, then
      dispatch via callq *%r10.  AProcType supplies the param list for
      var-param detection; result (if any) is left in %rax. }
    procedure EmitCallIndirect(const APtrOperand: string;
                               AProcType: TProceduralTypeDesc;
                               AArgs: TObjectList);
    { Evaluate an integer expression; result left in %rax (64-bit-extended). }
    procedure EmitExprToEax(AExpr: TASTExpr);
    { Evaluate a float expression (tyDouble or tySingle); result left in %xmm0.
      Binary ops: left → push onto int stack via subq/movsd, right → %xmm0,
      pop left → %xmm1, then addsd/subsd/mulsd/divsd. }
    procedure EmitExprToXmm0(AExpr: TASTExpr);
    { Load a float (Double or Single) from AOperand into %xmm0. }
    procedure EmitLoadFloat(const AOperand: string; AType: TTypeDesc);
    { Store %xmm0 into AOperand at the float type's width. }
    procedure EmitStoreFloat(const AOperand: string; AType: TTypeDesc);
    { The integer-family type to use when loading the value of AExpr: the
      recorded slot type for a known local/global (authoritative), otherwise
      the node's ResolvedType. }
    function IntExprType(AExpr: TASTExpr): TTypeDesc;
    { Re-truncate and re-extend the value in %rax to AType's width and
      signedness — used after a call (whose ABI return is 32-bit) and to
      implement an explicit narrowing/widening type cast. }
    procedure EmitNarrowToType(AType: TTypeDesc);
    { Evaluate a boolean condition and branch: if true jump ATrueLabel, else
      fall through to AFalseLabel (a jmp is emitted to it). }
    procedure EmitCondBranch(AExpr: TASTExpr;
                             const ATrueLabel, AFalseLabel: string);
    { Emit a TMethodCallExpr (class method call, with explicit receiver).
      Loads Self into %rdi and evaluates scalar args; result in %rax/%xmm0. }
    procedure EmitMethodCallExpr(ACall: TMethodCallExpr);
    { Emit a TMethodCallStmt (class method call in statement position). }
    procedure EmitMethodCallStmt(ACall: TMethodCallStmt);
    { Emit a TInheritedCallStmt (`inherited Method[(args)]`).  Direct static
      dispatch to the parent method (no vtable); Self is the current method's
      Self; a value-returning parent stores its result into the Result slot. }
    procedure EmitInheritedCall(ACall: TInheritedCallStmt);
    { Evaluate one method-call argument and push it onto the stack.  Scalar and
      var/out params push one value; interface params push two (itab first, then
      obj — reversed so the pop loop restores them in the correct register order). }
    procedure EmitMethodArgPush(APar: TMethodParam; AArg: TASTExpr);
    { Return the total number of integer register slots consumed by AParams.
      Most params = 1 slot; interface params = 2 slots (obj + itab); open-array
      params = 2 slots (ptr + high).  Used by pop loops so they count slots, not
      logical argument positions. }
    function CountArgSlots(AParams: TObjectList): Integer;
    { Emit a method-pointer (of-object) call: load Code from offset 0 and Data
      from offset 8 of the TMethod block at APtrOperand; call Code with Data as
      Self (%rdi) and the remaining args shifted. }
    procedure EmitMethodPtrCall(const APtrOperand: string;
                                AProcType: TProceduralTypeDesc;
                                AArgs: TObjectList);
    { Emit a Format(Fmt, arg1, ...) built-in call via _StringFormatN.
      Builds a temporary args array on the stack: each slot is 16 bytes
      (type tag at [0], value at [8]), matching the QBE backend's layout. }
    procedure EmitFormatCall(AArgs: TObjectList);
  public
    constructor Create(const ATarget: TTargetDesc); override;
    destructor Destroy; override;
  end;

implementation

const
  { SysV AMD64 integer argument registers (32-bit views), in order. }
  SysVArgRegs: array[0..5] of string =
    ('%edi', '%esi', '%edx', '%ecx', '%r8d', '%r9d');
  { Same registers, 64-bit views — used for Int64/UInt64 arguments. }
  SysVArgRegs64: array[0..5] of string =
    ('%rdi', '%rsi', '%rdx', '%rcx', '%r8', '%r9');
  { 8-bit and 16-bit views, for spilling a narrow incoming argument into its
    same-width param slot. }
  SysVArgRegs8: array[0..5] of string =
    ('%dil', '%sil', '%dl', '%cl', '%r8b', '%r9b');
  SysVArgRegs16: array[0..5] of string =
    ('%di', '%si', '%dx', '%cx', '%r8w', '%r9w');

{ ------------------------------------------------------------------ }
{ Integer-family width / signedness helpers                            }
{ ------------------------------------------------------------------ }

{ Byte width (1/2/4/8) of an integer-family type. Defaults to 4. }
function IntByteSize(AType: TTypeDesc): Integer;
begin
  if AType = nil then
  begin
    Exit(4);
  end;
  case AType.Kind of
    tyByte, tyBoolean:                          Result := 1;
    tySmallInt, tyWord:                         Result := 2;
    tyInteger, tyUInt32, tyEnum:                Result := 4;
    tyInt64, tyUInt64,
    tyProcedural, tyPointer, tyPChar, tyClass,
    tyString, tyMetaClass, tyDynArray:          Result := 8;
    tyDouble:                                   Result := 8;
    tySingle:                                   Result := 4;
  else
    Result := 4;
  end;
end;

{ True for floating-point types supported in %xmm registers. }
function IsFloatFamily(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and (AType.Kind in [tyDouble, tySingle]);
end;

{ SysV AMD64 XMM argument registers, in order. }
const
  SysVXmmArgRegs: array[0..5] of string =
    ('%xmm0', '%xmm1', '%xmm2', '%xmm3', '%xmm4', '%xmm5');

{ True for unsigned integer-family types. Byte/Word/UInt32/UInt64 are
  unsigned; Boolean and Enum hold non-negative ordinals and so are read
  zero-extended. SmallInt/Integer/Int64 are signed. }
function IsUnsignedInt(AType: TTypeDesc): Boolean;
begin
  if AType = nil then
  begin
    Exit(False);
  end;
  Result := AType.Kind in [tyByte, tyBoolean, tyWord, tyUInt32, tyUInt64, tyEnum];
end;


{ The assembly symbol for a procedure/function: the semantic pass sets
  ResolvedQbeName for overloaded/mangled names; otherwise use the source name
  verbatim (matching the QBE backend's $name vs $ResolvedQbeName choice). }
function FuncSymbolFromDecl(ADecl: TMethodDecl): string;
begin
  if (ADecl <> nil) and (ADecl.ResolvedQbeName <> '') then
    Result := NativeMangle(ADecl.ResolvedQbeName)
  else if ADecl <> nil then
    Result := NativeMangle(ADecl.Name)
  else
    Result := '';
end;

function FuncSymbolOf(ACall: TFuncCallExpr): string;
begin
  Result := FuncSymbolFromDecl(TMethodDecl(ACall.ResolvedDecl));
  if Result = '' then
    Result := NativeMangle(ACall.Name);
end;

constructor TX86_64Backend.Create(const ATarget: TTargetDesc);
begin
  inherited Create(ATarget);
  FLabelCount          := 0;
  FDataGlobals         := TOrderedDictionary<>.Create;
  FClassNameEmitted    := TDictionary<>.Create;
  FStrLits             := TStringList.Create;
  FBreakLabels        := TStack<>.Create;
  FContinueLabels     := TStack<>.Create;
  FBreakExcDepths     := TStack<>.Create;
  FContinueExcDepths  := TStack<>.Create;
  FFinallyStack       := TList<TCompoundStmt>.Create;
  FFrame          := nil;
  FFrameTypes     := nil;
  FFrameSize      := 0;
  FExitLabel      := '';
  FSretFunc       := False;
  FExcDepth           := 0;
  FExcFrameNext       := 0;
  FProgExcFrameCount  := 0;
end;

destructor TX86_64Backend.Destroy;
begin
  Self.ClearFrame;
  FFinallyStack.Free;
  FContinueExcDepths.Free;
  FBreakExcDepths.Free;
  FContinueLabels.Free;
  FBreakLabels.Free;
  FClassNameEmitted.Free;
  FStrLits.Free;
  FDataGlobals.Free;
  inherited Destroy;
end;

function TX86_64Backend.NewLabel(const APrefix: string): string;
begin
  Result := '.L' + APrefix + IntToStr(FLabelCount);
  Inc(FLabelCount);
end;

procedure TX86_64Backend.AddGlobal(const AName: string; AType: TTypeDesc);
begin
  if not FDataGlobals.ContainsKey(AName) then
    FDataGlobals.Add(AName, AType);
end;

function TX86_64Backend.GlobalType(const AName: string): TTypeDesc;
begin
  if not FDataGlobals.TryGetValue(AName, Result) then
    Result := nil;
end;

procedure TX86_64Backend.EmitDataSection;
var
  I, Sz:    Integer;
  Name:     string;
  Directive: string;
begin
  if (FDataGlobals.Count = 0) and (FProgExcFrameCount = 0) then
  begin
    Self.EmitStrLitSection;
    Exit;
  end;
  Self.Emit('.data');
  for I := 0 to FDataGlobals.Count - 1 do
  begin
    Name := FDataGlobals.Keys[I];
    { Method pointers (of-object): 16-byte Code+Data block, zero-initialised. }
    if (Self.GlobalType(Name) <> nil) and
       (Self.GlobalType(Name).Kind = tyProcedural) and
       TProceduralTypeDesc(Self.GlobalType(Name)).IsMethodPtr then
    begin
      Self.Emit('.balign 8');
      if Copy(Name, 1, 2) <> '.L' then
        Self.Emit('.globl ' + Name);
      Self.Emit(Name + ':');
      Self.Emit(#9'.quad 0');
      Self.Emit(#9'.quad 0');
      Continue;
    end;
    { Interface globals: a fat pointer split into two separate labels,
      Name_obj and Name_itab, each an 8-byte zero-initialised slot.  The two
      labels match IntfObjOperand / IntfItabOperand and the QBE backend's
      $Name_obj / $Name_itab convention. }
    if (Self.GlobalType(Name) <> nil) and
       (Self.GlobalType(Name).Kind = tyInterface) then
    begin
      Self.Emit('.balign 8');
      if Copy(Name, 1, 2) <> '.L' then
      begin
        Self.Emit('.globl ' + Name + '_obj');
        Self.Emit('.globl ' + Name + '_itab');
      end;
      Self.Emit(Name + '_obj:');
      Self.Emit(#9'.quad 0');
      Self.Emit(Name + '_itab:');
      Self.Emit(#9'.quad 0');
      Continue;
    end;
    { Records and static arrays: emit a zeroed block of RawSize bytes. }
    if (Self.GlobalType(Name) <> nil) and
       (Self.GlobalType(Name).Kind in [tyRecord, tyStaticArray]) then
    begin
      Sz := Self.GlobalType(Name).RawSize;
      Self.Emit('.balign 8');
      if Copy(Name, 1, 2) <> '.L' then
        Self.Emit('.globl ' + Name);
      Self.Emit(Name + ':');
      Self.Emit(Format(#9'.skip %d', [Sz]));
      Continue;
    end;
    { Float globals need float-specific zero initialisers. }
    if (Self.GlobalType(Name) <> nil) and
       (Self.GlobalType(Name).Kind = tyDouble) then
    begin
      Self.Emit('.balign 8');
      if Copy(Name, 1, 2) <> '.L' then
        Self.Emit('.globl ' + Name);
      Self.Emit(Name + ':');
      Self.Emit(#9'.double 0.0');
      Continue;
    end;
    if (Self.GlobalType(Name) <> nil) and
       (Self.GlobalType(Name).Kind = tySingle) then
    begin
      Self.Emit('.balign 4');
      if Copy(Name, 1, 2) <> '.L' then
        Self.Emit('.globl ' + Name);
      Self.Emit(Name + ':');
      Self.Emit(#9'.float 0.0');
      Continue;
    end;
    Sz := IntByteSize(Self.GlobalType(Name));
    { Align each slot to its own size; pick a zero-initialiser directive of
      matching width so the linker reserves the correct number of bytes. }
    case Sz of
      1: begin Directive := #9'.byte 0'; Self.Emit('.balign 1'); end;
      2: begin Directive := #9'.word 0'; Self.Emit('.balign 2'); end;
      8: begin Directive := #9'.quad 0'; Self.Emit('.balign 8'); end;
    else
      begin Directive := #9'.long 0'; Self.Emit('.balign 4'); end;
    end;
    { Hidden compiler-generated slots (.L-prefixed) stay file-local; named
      program variables are exported like the QBE backend's globals. }
    if Copy(Name, 1, 2) <> '.L' then
      Self.Emit('.globl ' + Name);
    Self.Emit(Name + ':');
    Self.Emit(Directive);
  end;
  { Exception frame slots for the program-main body.  Each is a 512-byte
    zero-initialised block at 16-byte alignment.  File-local (no .globl). }
  for I := 0 to FProgExcFrameCount - 1 do
  begin
    Self.Emit('.balign 16');
    Self.Emit('_exc_frame_' + IntToStr(I) + ':');
    Self.Emit(#9'.skip 512');
  end;
  Self.EmitStrLitSection;
end;

{ ------------------------------------------------------------------ }
{ String literal helpers (M7c)                                         }
{ ------------------------------------------------------------------ }

{ Escape a string for use in an AT&T .ascii directive.
  GNU as accepts the same escapes as C string literals. }
function TX86_64Backend.AsmEscapeString(const AStr: string): string;
var
  I, C, Hi, Lo: Integer;
begin
  Result := '';
  for I := 0 to Length(AStr) - 1 do
  begin
    C := StrAt(AStr, I);
    case C of
      34:  Result := Result + '\"';
      92:  Result := Result + '\\';
      10:  Result := Result + '\n';
      13:  Result := Result + '\r';
      9:   Result := Result + '\t';
    else
      if (C < 32) or (C > 126) then
      begin
        Hi := C shr 4;
        Lo := C and 15;
        if Hi < 10 then Hi := 48 + Hi else Hi := 55 + Hi;
        if Lo < 10 then Lo := 48 + Lo else Lo := 55 + Lo;
        Result := Result + '\' + Chr(Hi) + Chr(Lo)
      end
      else
        Result := Result + Chr(C);
    end;
  end;
end;

{ Evaluate a string literal: register it in the pool if new, then emit
  leaq __sN+12(%rip), %rax so %rax holds the Blaise data pointer. }
procedure TX86_64Backend.EmitStrLitAddr(const AValue: string);
var
  Idx: Integer;
begin
  Idx := FStrLits.IndexOf(AValue);
  if Idx < 0 then
    Idx := FStrLits.Add(AValue);
  Self.Emit(Format(#9'leaq __s%d + 12(%%rip), %%rax', [Idx]));
end;

{ Emit all accumulated string literal blobs to .rodata.
  Each blob: 4-byte refcnt=-1 (immortal), 4-byte length, 4-byte capacity,
  then the ASCII bytes, then a NUL terminator.
  The Blaise string data pointer convention: str_ptr = &header + 12. }
procedure TX86_64Backend.EmitStrLitSection;
var
  I:   Integer;
  Len: Integer;
begin
  if FStrLits.Count = 0 then Exit;
  Self.Emit('.section .rodata');
  for I := 0 to FStrLits.Count - 1 do
  begin
    Len := Length(FStrLits.Strings[I]);
    Self.Emit('.balign 4');
    Self.Emit(Format('__s%d:', [I]));
    Self.Emit(Format(#9'.long -1', []));       { refcnt = immortal }
    Self.Emit(Format(#9'.long %d', [Len]));    { length }
    Self.Emit(Format(#9'.long %d', [Len]));    { capacity }
    if Len > 0 then
      Self.Emit(Format(#9'.ascii "%s"', [Self.AsmEscapeString(FStrLits.Strings[I])]));
    Self.Emit(#9'.byte 0');                    { NUL terminator }
  end;
end;

{ ------------------------------------------------------------------ }
{ Class data section helpers                                           }
{ ------------------------------------------------------------------ }

{ Mangle a name for use as an assembly label: replace characters that are
  invalid in label names with underscores, matching QBE backend's QBEMangle. }
function NativeMangle(const AName: string): string;
var
  I, C: Integer;
begin
  Result := '';
  for I := 0 to Length(AName) - 1 do
  begin
    C := Ord(AName[I]);
    case C of
      60: Result := Result + '_';    { '<' }
      62: ;                          { '>' — skip }
      44: Result := Result + '_';    { ',' }
      36: Result := Result + '_D_';  { '$' }
      64: Result := Result + '_V_';  { '@' }
      94: Result := Result + '_P_';  { '^' }
    else
      Result := Result + Chr(C);
    end;
  end;
end;

function FindMethodInClassDef(AClassDef: TClassTypeDef;
  const AName: string): TMethodDecl;
var
  I: Integer;
  M: TMethodDecl;
begin
  Result := nil;
  for I := 0 to AClassDef.Methods.Count - 1 do
  begin
    M := TMethodDecl(AClassDef.Methods.Items[I]);
    if SameText(M.Name, AName) then
      Exit(M);
  end;
end;

{ Compute the mangled emit name for a class method: ResolvedQbeName if set,
  else TypeName_MethodName, both passed through NativeMangle. }
function MethodEmitNameNative(ADecl: TMethodDecl; const ATypeName, AMethodName: string): string;
begin
  if (ADecl <> nil) and (ADecl.ResolvedQbeName <> '') then
    Result := NativeMangle(ADecl.ResolvedQbeName)
  else if ADecl <> nil then
    Result := NativeMangle(ATypeName + '_' + ADecl.Name)
  else
    Result := NativeMangle(ATypeName + '_' + AMethodName);
end;

{ Emit an immortal class-name string blob and return the label+12 reference
  (the pointer to the character data, past the 12-byte ARC/length header). }
function TX86_64Backend.EmitClassNameString(const AClassName: string): string;
var
  Mangled: string;
  Len:     Integer;
begin
  Mangled := NativeMangle(AClassName);
  Result  := '__cn_' + Mangled + ' + 12';
  { Idempotent: skip if already emitted (MethodAddress and class section may
    both request the same name string). }
  if FClassNameEmitted.ContainsKey(Mangled) then
    Exit;
  FClassNameEmitted.Add(Mangled, True);
  Len := Length(AClassName);
  Self.Emit('.balign 4');
  Self.Emit('__cn_' + Mangled + ':');
  Self.Emit(#9'.long -1');
  Self.Emit(Format(#9'.long %d', [Len]));
  Self.Emit(Format(#9'.long %d', [Len]));
  Self.Emit(Format(#9'.ascii "%s"', [AClassName]));
  Self.Emit(#9'.byte 0');
end;

procedure TX86_64Backend.EmitFieldCleanupFn(const AMangledName: string;
                                            ART: TRecordTypeDesc);
begin
  Self.Emit('.text');
  Self.Emit('.globl _FieldCleanup_' + AMangledName);
  Self.Emit('_FieldCleanup_' + AMangledName + ':');
  Self.Emit(#9'pushq %rbp');
  Self.Emit(#9'movq %rsp, %rbp');
  Self.Emit(#9'movq %rbp, %rsp');
  Self.Emit(#9'popq %rbp');
  Self.Emit(#9'ret');
  Self.Emit('.type _FieldCleanup_' + AMangledName + ', @function');
end;

procedure TX86_64Backend.EmitClassSection(AProg: TProgram);
var
  I, J, S:   Integer;
  TD:        TTypeDecl;
  TDesc:     TTypeDesc;
  RT:        TRecordTypeDesc;
  CD:        TClassTypeDef;
  MD:        TMethodDecl;
  E:         TVTableEntry;
  GI:        TGenericInstance;
  MName:     string;
  ParentStr: string;
  ImplStr:   string;
  MethStr:   string;
  PubCount:  Integer;
  Line:      string;
begin
  { Fixed RTL class-name strings and stubs for TObject and TCustomAttribute. }
  Self.Emit('.data');
  Self.EmitClassNameString('TObject');
  Self.EmitClassNameString('TCustomAttribute');

  { User class data: name strings, method tables, typeinfo, vtables. }
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    CD := TClassTypeDef(TD.Def);

    { Class-name string blob }
    Self.EmitClassNameString(TD.Name);

    { Published-method table: count, then (nameref, codeptr) pairs }
    PubCount := 0;
    for J := 0 to CD.Methods.Count - 1 do
      if TMethodDecl(CD.Methods.Items[J]).IsPublished then
        Inc(PubCount);
    if PubCount > 0 then
    begin
      { Emit name strings for published methods. }
      for J := 0 to CD.Methods.Count - 1 do
      begin
        MD := TMethodDecl(CD.Methods.Items[J]);
        if MD.IsPublished then
          Self.EmitClassNameString(MD.Name);
      end;
      Self.Emit('.balign 8');
      Self.Emit('.globl methods_' + TD.Name);
      Self.Emit('methods_' + TD.Name + ':');
      Self.Emit(Format(#9'.quad %d', [PubCount]));
      for J := 0 to CD.Methods.Count - 1 do
      begin
        MD := TMethodDecl(CD.Methods.Items[J]);
        if not MD.IsPublished then Continue;
        Self.Emit(Format(#9'.quad __cn_%s + 12', [NativeMangle(MD.Name)]));
        Self.Emit(Format(#9'.quad %s', [MethodEmitNameNative(MD, TD.Name, MD.Name)]));
      end;
      MethStr := 'methods_' + TD.Name;
    end
    else
      MethStr := '0';
  end;

  { Generic class instances — emit class-name string blobs. }
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AProg.GenericInstances.Items[I]);
    Self.EmitClassNameString(GI.TypeName);
  end;

  { Typeinfo blocks — must come after all class-name strings are emitted. }
  Self.Emit('.balign 8');
  Self.Emit('typeinfo_TObject:');
  Self.Emit(#9'.quad 0');          { parent = nil }
  Self.Emit(#9'.quad 0');          { impllist = nil }
  Self.Emit(#9'.quad __cn_TObject + 12');
  Self.Emit(#9'.quad 0');          { methods = nil }
  Self.Emit(#9'.quad 8');          { size = 8 (vptr only) }
  Self.Emit(#9'.quad _FieldCleanup_TObject');
  Self.Emit(#9'.quad vtable_TObject');
  Self.Emit(#9'.quad 0');          { attrs = nil }

  Self.Emit('.balign 8');
  Self.Emit('typeinfo_TCustomAttribute:');
  Self.Emit(#9'.quad typeinfo_TObject');
  Self.Emit(#9'.quad 0');
  Self.Emit(#9'.quad __cn_TCustomAttribute + 12');
  Self.Emit(#9'.quad 0');
  Self.Emit(#9'.quad 8');
  Self.Emit(#9'.quad _FieldCleanup_TCustomAttribute');
  Self.Emit(#9'.quad vtable_TCustomAttribute');
  Self.Emit(#9'.quad 0');

  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);

    if RT.Parent <> nil then
      ParentStr := 'typeinfo_' + RT.Parent.Name
    else
      ParentStr := '0';
    if RT.ImplementsCount > 0 then
      ImplStr := 'impllist_' + TD.Name
    else
      ImplStr := '0';

    { Rebuild MethStr for typeinfo (already computed above but not stored). }
    CD := TClassTypeDef(TD.Def);
    PubCount := 0;
    for J := 0 to CD.Methods.Count - 1 do
      if TMethodDecl(CD.Methods.Items[J]).IsPublished then
        Inc(PubCount);
    if PubCount > 0 then
      MethStr := 'methods_' + TD.Name
    else
      MethStr := '0';

    Self.Emit('.balign 8');
    Self.Emit('.globl typeinfo_' + TD.Name);
    Self.Emit('typeinfo_' + TD.Name + ':');
    Self.Emit(#9'.quad ' + ParentStr);
    Self.Emit(#9'.quad ' + ImplStr);
    Self.Emit(Format(#9'.quad __cn_%s + 12', [NativeMangle(TD.Name)]));
    Self.Emit(#9'.quad ' + MethStr);
    Self.Emit(Format(#9'.quad %d', [RT.TotalSize]));
    Self.Emit(#9'.quad _FieldCleanup_' + TD.Name);
    Self.Emit(#9'.quad vtable_' + TD.Name);
    Self.Emit(#9'.quad 0');   { attrs }
  end;

  { Typeinfo blocks for generic class instances. }
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AProg.GenericInstances.Items[I]);
    RT := TRecordTypeDesc(GI.TypeDesc);
    MName := NativeMangle(GI.TypeName);
    if RT.Parent <> nil then
      ParentStr := 'typeinfo_' + NativeMangle(RT.Parent.Name)
    else
      ParentStr := '0';
    if RT.ImplementsCount > 0 then
      ImplStr := 'impllist_' + MName
    else
      ImplStr := '0';
    Self.Emit('.balign 8');
    Self.Emit('.globl typeinfo_' + MName);
    Self.Emit('typeinfo_' + MName + ':');
    Self.Emit(#9'.quad ' + ParentStr);
    Self.Emit(#9'.quad ' + ImplStr);
    Self.Emit(Format(#9'.quad __cn_%s + 12', [MName]));
    Self.Emit(#9'.quad 0');
    Self.Emit(Format(#9'.quad %d', [RT.TotalSize]));
    Self.Emit(#9'.quad _FieldCleanup_' + MName);
    Self.Emit(#9'.quad vtable_' + MName);
    Self.Emit(#9'.quad 0');
  end;

  { Field cleanup functions for the fixed RTL classes. }
  Self.EmitFieldCleanupFn('TObject', nil);
  Self.EmitFieldCleanupFn('TCustomAttribute', nil);
  { Field cleanup for user classes. }
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    Self.EmitFieldCleanupFn(TD.Name, RT);
  end;
  { Field cleanup for generic class instances. }
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AProg.GenericInstances.Items[I]);
    RT := TRecordTypeDesc(GI.TypeDesc);
    Self.EmitFieldCleanupFn(NativeMangle(GI.TypeName), RT);
  end;

  { Vtables — must be in .data (pointers to other data symbols). }
  Self.Emit('.data');
  Self.Emit('.balign 8');
  Self.Emit('vtable_TObject:');
  Self.Emit(#9'.quad typeinfo_TObject');
  Self.Emit(#9'.quad TObject_Destroy');
  Self.Emit(#9'.quad TObject_ToString');

  Self.Emit('.balign 8');
  Self.Emit('vtable_TCustomAttribute:');
  Self.Emit(#9'.quad typeinfo_TCustomAttribute');
  Self.Emit(#9'.quad TObject_Destroy');
  Self.Emit(#9'.quad TObject_ToString');

  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    if not RT.HasVTable then Continue;

    Self.Emit('.balign 8');
    Self.Emit('.globl vtable_' + TD.Name);
    Self.Emit('vtable_' + TD.Name + ':');
    Self.Emit(#9'.quad typeinfo_' + TD.Name);
    for S := 0 to RT.VTableCount - 1 do
    begin
      E := RT.VTableEntryAt(S);
      if E.IsAbstract then
        Line := #9'.quad _AbstractMethodError'
      else
      begin
        { E.ImplName may have a '$' prefix (QBE convention) — strip it for native.
          Use StrAt for 0-based string indexing. }
        if (Length(E.ImplName) > 0) and (StrAt(E.ImplName, 0) = 36) then
          Line := #9'.quad ' + NativeMangle(StrCopyTail(E.ImplName, 1))
        else
          Line := #9'.quad ' + NativeMangle(E.ImplName);
      end;
      Self.Emit(Line);
    end;
  end;

  { Vtables for generic class instances. }
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AProg.GenericInstances.Items[I]);
    RT := TRecordTypeDesc(GI.TypeDesc);
    if not RT.HasVTable then Continue;
    MName := NativeMangle(GI.TypeName);
    Self.Emit('.balign 8');
    Self.Emit('.globl vtable_' + MName);
    Self.Emit('vtable_' + MName + ':');
    Self.Emit(#9'.quad typeinfo_' + MName);
    for S := 0 to RT.VTableCount - 1 do
    begin
      E := RT.VTableEntryAt(S);
      if E.IsAbstract then
        Line := #9'.quad _AbstractMethodError'
      else
      begin
        if (Length(E.ImplName) > 0) and (StrAt(E.ImplName, 0) = 36) then
          Line := #9'.quad ' + NativeMangle(StrCopyTail(E.ImplName, 1))
        else
          Line := #9'.quad ' + NativeMangle(E.ImplName);
      end;
      Self.Emit(Line);
    end;
  end;
end;

{ Lower an interface method call.  The receiver is an interface fat pointer
  (obj + itab) named AObjName; AIntf supplies the method's slot index.  The
  itab is a flat array of method-code pointers (no leading typeinfo slot, in
  contrast to a vtable), so the slot offset is MethodIndex * PtrSize.

  Calling sequence mirrors EmitMethodCallExpr: evaluate args left-to-right onto
  the stack, load the obj (Self) and the resolved code pointer into caller-saved
  scratch (%r10/%r11) that survive the pop loop, pop args into %rsi.. (shifted
  by one for Self in %rdi), set %rdi := obj, then `callq *%r11`. }
procedure TX86_64Backend.EmitInterfaceCall(const AObjName: string;
                                           AIsGlobal: Boolean;
                                           AIntf: TInterfaceTypeDesc;
                                           const AMethName: string;
                                           AArgs: TObjectList);
var
  I, SlotOff, Ps, ArgN: Integer;
  Arg: TASTExpr;
begin
  { x86_64: pointers are 8 bytes (this backend's invariant, like the rest of the
    file).  i386/arm64 backends will be separate TNativeBackend subclasses. }
  Ps := 8;
  ArgN := 0;
  if AArgs <> nil then ArgN := AArgs.Count;
  { Evaluate args left-to-right and push them.  Interface args push two values
    (obj then itab); all other args push one.  Pass nil as the TMethodParam so
    EmitMethodArgPush falls through to scalar for non-interface args. }
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    if (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tyInterface) then
    begin
      { Fabricate a synthetic param descriptor for the interface type. }
      if Arg is TIdentExpr then
      begin
        Self.Emit(Format(#9'movq %s, %%rax',
          [Self.IntfObjOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
        Self.Emit(Format(#9'movq %s, %%rcx',
          [Self.IntfItabOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
        Self.Emit(#9'pushq %rax');   { obj }
        Self.Emit(#9'pushq %rcx');   { itab }
      end
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported interface arg expression in interface dispatch');
    end
    else
    begin
      Self.EmitExprToEax(Arg);
      Self.Emit(#9'pushq %rax');
    end;
  end;
  { Load obj (Self) into %r10 and the itab into %rax, then index the itab. }
  Self.Emit(Format(#9'movq %s, %%r10', [Self.IntfObjOperand(AObjName, AIsGlobal)]));
  Self.Emit(Format(#9'movq %s, %%rax', [Self.IntfItabOperand(AObjName, AIsGlobal)]));
  SlotOff := AIntf.MethodIndex(AMethName) * Ps;
  if SlotOff = 0 then
    Self.Emit(#9'movq (%rax), %r11')
  else
    Self.Emit(Format(#9'movq %d(%%rax), %%r11', [SlotOff]));
  { Pop args into %rsi/%rdx/... (shift by 1 for %rdi = Self).
    Count slots: interface args occupy 2 slots each. }
  SlotOff := 0;
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    if (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tyInterface) then
      Inc(SlotOff, 2)
    else
      Inc(SlotOff);
  end;
  for I := SlotOff - 1 downto 0 do
    Self.Emit(#9'popq ' + SysVArgRegs64[I + 1]);
  Self.Emit(#9'movq %r10, %rdi');
  Self.Emit(#9'callq *%r11');
end;

procedure TX86_64Backend.EmitInterfaceFieldCall(AFld: TFieldInfo;
  AIntf: TInterfaceTypeDesc; const AMethName: string; AArgs: TObjectList);
{ Dispatch an interface method call through a class field.  The fat pointer
  lives at Self + AFld.Offset (obj) and Self + AFld.Offset + 8 (itab). }
var
  I, SlotOff, ArgN: Integer;
  Arg: TASTExpr;
begin
  ArgN := 0;
  if AArgs <> nil then ArgN := AArgs.Count;
  { Push args left-to-right; interface args push obj then itab (2 slots). }
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    if (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tyInterface) then
    begin
      if Arg is TIdentExpr then
      begin
        Self.Emit(Format(#9'movq %s, %%rax',
          [Self.IntfObjOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
        Self.Emit(Format(#9'movq %s, %%rcx',
          [Self.IntfItabOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
        Self.Emit(#9'pushq %rax');   { obj }
        Self.Emit(#9'pushq %rcx');   { itab }
      end
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported interface arg expression in field dispatch');
    end
    else
    begin
      Self.EmitExprToEax(Arg);
      Self.Emit(#9'pushq %rax');
    end;
  end;
  { Load Self and compute field base; use %r11 for base pointer. }
  Self.Emit(Format(#9'movq %s, %%r11', [Self.VarOperand('Self')]));
  if AFld.Offset > 0 then
    Self.Emit(Format(#9'addq $%d, %%r11', [AFld.Offset]));
  { Load obj into %r10, itab into %rax. }
  Self.Emit(#9'movq (%r11), %r10');
  Self.Emit(#9'movq 8(%r11), %rax');
  SlotOff := AIntf.MethodIndex(AMethName) * 8;
  if SlotOff = 0 then
    Self.Emit(#9'movq (%rax), %r11')
  else
    Self.Emit(Format(#9'movq %d(%%rax), %%r11', [SlotOff]));
  { Count total slots then pop in reverse. }
  SlotOff := 0;
  for I := 0 to ArgN - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    if (Arg.ResolvedType <> nil) and (Arg.ResolvedType.Kind = tyInterface) then
      Inc(SlotOff, 2)
    else
      Inc(SlotOff);
  end;
  for I := SlotOff - 1 downto 0 do
    Self.Emit(#9'popq ' + SysVArgRegs64[I + 1]);
  Self.Emit(#9'movq %r10, %rdi');
  Self.Emit(#9'callq *%r11');
end;

{ An interface method maps to one of ARec's vtable slots.  When that slot is
  abstract, the itab entry must point at _AbstractMethodError (the concrete
  symbol does not exist on an abstract base). }
function TX86_64Backend.IsAbstractClassMethod(ARec: TRecordTypeDesc;
                                              const AMethName: string): Boolean;
var
  Slot: Integer;
begin
  Slot := ARec.FindVTableSlot(AMethName);
  if Slot < 0 then
    Result := False
  else
    Result := ARec.VTableEntryAt(Slot).IsAbstract;
end;

{ Emit typeinfo / itab / impllist blocks for interfaces and implementing
  classes.  Mirrors the QBE backend's EmitInterfaceDefs:

    typeinfo_IFoo:        .quad 0            (address IS the identity token)
    itab_TFoo_IFoo:       .quad TFoo_DoIt, .quad TFoo_GetVal   (decl order)
    impllist_TFoo:        .quad typeinfo_IFoo, .quad itab_TFoo_IFoo, .quad 0

  impllist is a NULL-terminated array of (typeinfo, itab) pairs, walked by the
  _GetItab runtime helper for `as`-casts. }
procedure TX86_64Backend.EmitInterfaceDefs(AProg: TProgram);
var
  I, J, K:    Integer;
  TD:         TTypeDecl;
  TDesc:      TTypeDesc;
  IntfDesc:   TInterfaceTypeDesc;
  ClassRT:    TRecordTypeDesc;
  GI:         TGenericInstance;
  GII:        TGenericInterfaceInstance;
  MName:      string;
  MethName:   string;
  MethRef:    string;
  MDecl:      TMethodDecl;
begin
  { Typeinfo blocks for every plain interface. }
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if not (TD.Def is TInterfaceTypeDef) then Continue;
    Self.Emit('.balign 8');
    Self.Emit('.globl typeinfo_' + NativeMangle(TD.Name));
    Self.Emit('typeinfo_' + NativeMangle(TD.Name) + ':');
    Self.Emit(#9'.quad 0');
  end;

  { Typeinfo blocks for generic interface instances. }
  for I := 0 to AProg.GenericIntfInstances.Count - 1 do
  begin
    GII := TGenericInterfaceInstance(AProg.GenericIntfInstances.Items[I]);
    Self.Emit('.balign 8');
    Self.Emit('.globl typeinfo_' + GII.InstName);
    Self.Emit('typeinfo_' + GII.InstName + ':');
    Self.Emit(#9'.quad 0');
  end;

  { Itab and impllist blocks for each implementing class. }
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    ClassRT := TRecordTypeDesc(TDesc);
    if ClassRT.ImplementsCount = 0 then Continue;

    { One itab per implemented interface — a flat array of method-code ptrs in
      interface declaration order. }
    for J := 0 to ClassRT.ImplementsCount - 1 do
    begin
      IntfDesc := ClassRT.ImplementsIntfAt(J);
      Self.Emit('.balign 8');
      Self.Emit('.globl itab_' + NativeMangle(TD.Name) + '_' + NativeMangle(IntfDesc.Name));
      Self.Emit('itab_' + NativeMangle(TD.Name) + '_' + NativeMangle(IntfDesc.Name) + ':');
      for K := 0 to IntfDesc.MethodCount - 1 do
      begin
        MethName := IntfDesc.MethodName(K);
        if Self.IsAbstractClassMethod(ClassRT, MethName) then
          MethRef := '_AbstractMethodError'
        else
          MethRef := NativeMangle(TD.Name) + '_' + MethName;
        Self.Emit(#9'.quad ' + MethRef);
      end;
    end;

    { One impllist per class: NULL-terminated (typeinfo, itab) pairs. }
    Self.Emit('.balign 8');
    Self.Emit('.globl impllist_' + NativeMangle(TD.Name));
    Self.Emit('impllist_' + NativeMangle(TD.Name) + ':');
    for J := 0 to ClassRT.ImplementsCount - 1 do
    begin
      IntfDesc := ClassRT.ImplementsIntfAt(J);
      Self.Emit(#9'.quad typeinfo_' + NativeMangle(IntfDesc.Name));
      Self.Emit(#9'.quad itab_' + NativeMangle(TD.Name) + '_' + NativeMangle(IntfDesc.Name));
    end;
    Self.Emit(#9'.quad 0');
  end;

  { Itab and impllist for generic class instances that implement interfaces. }
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AProg.GenericInstances.Items[I]);
    ClassRT := TRecordTypeDesc(GI.TypeDesc);
    if ClassRT.ImplementsCount = 0 then Continue;
    MName := NativeMangle(GI.TypeName);

    for J := 0 to ClassRT.ImplementsCount - 1 do
    begin
      IntfDesc := ClassRT.ImplementsIntfAt(J);
      Self.Emit('.balign 8');
      Self.Emit('.globl itab_' + MName + '_' + NativeMangle(IntfDesc.Name));
      Self.Emit('itab_' + MName + '_' + NativeMangle(IntfDesc.Name) + ':');
      for K := 0 to IntfDesc.MethodCount - 1 do
      begin
        MethName := IntfDesc.MethodName(K);
        if Self.IsAbstractClassMethod(ClassRT, MethName) then
          MethRef := '_AbstractMethodError'
        else
        begin
          MDecl := FindMethodInClassDef(GI.ClassDef, MethName);
          if (MDecl <> nil) and (MDecl.ResolvedQbeName <> '') then
            MethRef := NativeMangle(MDecl.ResolvedQbeName)
          else
            MethRef := MName + '_' + MethName;
        end;
        Self.Emit(#9'.quad ' + MethRef);
      end;
    end;

    Self.Emit('.balign 8');
    Self.Emit('.globl impllist_' + MName);
    Self.Emit('impllist_' + MName + ':');
    for J := 0 to ClassRT.ImplementsCount - 1 do
    begin
      IntfDesc := ClassRT.ImplementsIntfAt(J);
      Self.Emit(#9'.quad typeinfo_' + NativeMangle(IntfDesc.Name));
      Self.Emit(#9'.quad itab_' + MName + '_' + NativeMangle(IntfDesc.Name));
    end;
    Self.Emit(#9'.quad 0');
  end;
end;

procedure TX86_64Backend.EmitInterfaceAssign(AAsgn: TAssignment);
{ Strong-reference interface assignment.  The LHS fat pointer is (obj, itab).
  In every form the obj slot co-owns the backing class instance: the new obj is
  retained and the prior obj released before the store.  The itab slot points at
  static rodata and is not refcounted. }
var
  Intf:    TInterfaceTypeDesc;
  ClassRT: TRecordTypeDesc;
  AE:      TAsExpr;
  ItabSym: string;
  ObjOp:   string;
  ItabOp:  string;
  LFail:   string;
  LEnd:    string;
  ISFld:   TFieldInfo;
begin
  Intf := TInterfaceTypeDesc(AAsgn.ResolvedLhsType);
  { Implicit Self.Field assignment: the fat pointer lives inside the object at
    Self + FieldOffset (obj) and Self + FieldOffset + 8 (itab).
    Handle entirely here rather than falling through to the ObjOp/ItabOp paths
    below (which use fixed operand strings that could be clobbered by calls). }
  if AAsgn.ImplicitSelfField <> nil then
  begin
    ISFld := TFieldInfo(AAsgn.ImplicitSelfField);
    { Compute Self + FieldOffset into %r15 (callee-saved: survives callq). }
    Self.Emit(#9'pushq %r15');
    Self.Emit(Format(#9'movq %s, %%r15', [Self.VarOperand('Self')]));
    if ISFld.Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%r15', [ISFld.Offset]));
    { Now (%r15) = obj slot, 8(%r15) = itab slot. }
    if AAsgn.Expr.ResolvedType.Kind = tyClass then
    begin
      ClassRT := TRecordTypeDesc(AAsgn.Expr.ResolvedType);
      ItabSym := 'itab_' + NativeMangle(ClassRT.Name) + '_' + NativeMangle(Intf.Name);
      Self.EmitExprToEax(AAsgn.Expr);
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(Format(#9'leaq %s(%%rip), %%rax', [ItabSym]));
      Self.Emit(#9'movq %rax, 8(%r15)');
    end
    else if (AAsgn.Expr.ResolvedType.Kind = tyInterface) and (AAsgn.Expr is TIdentExpr) then
    begin
      { Interface-to-interface: copy from source fat pointer slots. }
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.IntfItabOperand(TIdentExpr(AAsgn.Expr).Name, TIdentExpr(AAsgn.Expr).IsGlobal)]));
      Self.Emit(#9'pushq %rax');
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.IntfObjOperand(TIdentExpr(AAsgn.Expr).Name, TIdentExpr(AAsgn.Expr).IsGlobal)]));
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      Self.Emit(#9'movq (%r15), %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, (%r15)');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movq %rax, 8(%r15)');
    end
    else
      raise ENativeCodeGenError.Create(
        'native backend: unsupported interface-field assignment RHS');
    Self.Emit(#9'popq %r15');
    Exit;
  end;

  { Register a global LHS so EmitDataSection emits its _obj/_itab labels. }
  if not Self.IsLocal(AAsgn.Name) then
    Self.AddGlobal(AAsgn.Name, AAsgn.ResolvedLhsType);
  ObjOp  := Self.IntfObjOperand(AAsgn.Name, AAsgn.IsGlobal);
  ItabOp := Self.IntfItabOperand(AAsgn.Name, AAsgn.IsGlobal);

  { F := nil — release old obj, zero both slots. }
  if AAsgn.Expr is TNilLiteral then
  begin
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(Format(#9'movq $0, %s', [ObjOp]));
    Self.Emit(Format(#9'movq $0, %s', [ItabOp]));
    Exit;
  end;

  { F := T as IFoo — runtime itab lookup via _GetItab(obj, typeinfo_IFoo).
    A nil result means the cast failed; raise EInvalidCast. }
  if (AAsgn.Expr is TAsExpr) and
     (AAsgn.Expr.ResolvedType <> nil) and
     (AAsgn.Expr.ResolvedType.Kind = tyInterface) then
  begin
    AE := TAsExpr(AAsgn.Expr);
    Self.EmitExprToEax(AE.Obj);          { obj -> %rax }
    Self.Emit(#9'pushq %rax');            { keep obj on the stack across calls }
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rsi', [NativeMangle(AE.TypeName)]));
    Self.Emit(#9'callq _GetItab');         { itab -> %rax }
    Self.Emit(#9'pushq %rax');            { keep itab; stack now (itab, obj) }
    LFail := Self.NewLabel('as_fail');
    LEnd  := Self.NewLabel('as_end');
    Self.Emit(#9'testq %rax, %rax');
    Self.Emit(#9'jz ' + LFail);
    { Cast OK: addref new obj, release old, store obj + itab. }
    Self.Emit(#9'movq 8(%rsp), %rdi');     { obj }
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));   { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');              { itab }
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Self.Emit(#9'popq %rax');              { obj }
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(#9'jmp ' + LEnd);
    Self.Emit(LFail + ':');
    Self.Emit(#9'addq $16, %rsp');         { discard pushed obj+itab }
    Self.Emit(#9'callq _Raise_InvalidCast');
    Self.Emit(LEnd + ':');
    Exit;
  end;

  { F := T where T is a class implementing the interface — static itab. }
  if (AAsgn.Expr.ResolvedType <> nil) and
     (AAsgn.Expr.ResolvedType.Kind = tyClass) then
  begin
    ClassRT := TRecordTypeDesc(AAsgn.Expr.ResolvedType);
    ItabSym := 'itab_' + NativeMangle(ClassRT.Name) + '_' + NativeMangle(Intf.Name);
    Self.EmitExprToEax(AAsgn.Expr);       { new obj -> %rax }
    Self.Emit(#9'pushq %rax');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));   { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');              { new obj }
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(Format(#9'leaq %s(%%rip), %%rax', [ItabSym]));
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Exit;
  end;

  { F := G where both sides are interface-typed — copy obj+itab. }
  if (AAsgn.Expr.ResolvedType <> nil) and
     (AAsgn.Expr.ResolvedType.Kind = tyInterface) and
     (AAsgn.Expr is TIdentExpr) then
  begin
    { Load src obj+itab; addref new obj; release old obj; store both. }
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.IntfItabOperand(TIdentExpr(AAsgn.Expr).Name, TIdentExpr(AAsgn.Expr).IsGlobal)]));
    Self.Emit(#9'pushq %rax');             { itab }
    Self.Emit(Format(#9'movq %s, %%rax',
      [Self.IntfObjOperand(TIdentExpr(AAsgn.Expr).Name, TIdentExpr(AAsgn.Expr).IsGlobal)]));
    Self.Emit(#9'pushq %rax');             { obj; stack now (obj, itab) }
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _ClassAddRef');
    Self.Emit(Format(#9'movq %s, %%rdi', [ObjOp]));   { old obj }
    Self.Emit(#9'callq _ClassRelease');
    Self.Emit(#9'popq %rax');              { new obj }
    Self.Emit(Format(#9'movq %%rax, %s', [ObjOp]));
    Self.Emit(#9'popq %rax');              { itab }
    Self.Emit(Format(#9'movq %%rax, %s', [ItabOp]));
    Exit;
  end;

  raise ENativeCodeGenError.Create(
    'native backend: unsupported interface assignment RHS');
end;

procedure TX86_64Backend.EmitClassMethods(AProg: TProgram);
var
  I, J: Integer;
  TD:   TTypeDecl;
  CD:   TClassTypeDef;
  RD:   TRecordTypeDef;
  GI:   TGenericInstance;
  GRI:  TGenericRecordInstance;
  Decl: TMethodDecl;
begin
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if TD.Def is TClassTypeDef then
    begin
      CD := TClassTypeDef(TD.Def);
      for J := 0 to CD.Methods.Count - 1 do
      begin
        Decl := TMethodDecl(CD.Methods.Items[J]);
        if Decl.Body = nil then Continue;
        Self.EmitFunctionDef(Decl);
      end;
    end
    else if TD.Def is TRecordTypeDef then
    begin
      RD := TRecordTypeDef(TD.Def);
      for J := 0 to RD.Methods.Count - 1 do
      begin
        Decl := TMethodDecl(RD.Methods.Items[J]);
        if Decl.Body = nil then Continue;
        Self.EmitFunctionDef(Decl);
      end;
    end;
  end;

  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AProg.GenericInstances.Items[I]);
    for J := 0 to GI.ClassDef.Methods.Count - 1 do
    begin
      Decl := TMethodDecl(GI.ClassDef.Methods.Items[J]);
      if Decl.Body = nil then Continue;
      Self.EmitFunctionDef(Decl);
    end;
  end;

  for I := 0 to AProg.GenericRecordInstances.Count - 1 do
  begin
    GRI := TGenericRecordInstance(AProg.GenericRecordInstances.Items[I]);
    for J := 0 to GRI.RecordDef.Methods.Count - 1 do
    begin
      Decl := TMethodDecl(GRI.RecordDef.Methods.Items[J]);
      if Decl.Body = nil then Continue;
      Self.EmitFunctionDef(Decl);
    end;
  end;
end;

{ ------------------------------------------------------------------ }
{ Frame model                                                          }
{ ------------------------------------------------------------------ }

function TX86_64Backend.IsLocal(const AName: string): Boolean;
begin
  Result := (FFrame <> nil) and FFrame.ContainsKey(AName);
end;


function TX86_64Backend.VarOperand(const AName: string): string;
var
  Off: Integer;
begin
  if (FFrame <> nil) and FFrame.TryGetValue(AName, Off) then
  begin
    { Negative offset: local/param slot below %rbp (-8, -16, ...).
      Positive offset: stack-passed param above %rbp (+16, +24, ...). }
    if Off > 0 then
      Result := Format('%d(%%rbp)', [Off])
    else
      Result := Format('-%d(%%rbp)', [-Off])
  end
  else
    Result := AName + '(%rip)';
end;

function TX86_64Backend.LocalType(const AName: string): TTypeDesc;
begin
  if (FFrameTypes = nil) or (not FFrameTypes.TryGetValue(AName, Result)) then
    Result := nil;
end;

{ The obj half of an interface fat pointer.  Locals: the 16-byte slot base
  (VarOperand returns the low address = obj).  Globals: a dedicated label
  AName + '_obj', registered for emission in EmitDataSection. }
function TX86_64Backend.IntfObjOperand(const AName: string; AIsGlobal: Boolean): string;
begin
  if (not AIsGlobal) and Self.IsLocal(AName) then
    Result := Self.VarOperand(AName)
  else
    Result := AName + '_obj(%rip)';
end;

{ The itab half of an interface fat pointer.  Locals: 8 bytes above the obj
  slot (the slot base address is the obj operand, so add 8 to its rbp offset).
  Globals: a dedicated label AName + '_itab'. }
function TX86_64Backend.IntfItabOperand(const AName: string; AIsGlobal: Boolean): string;
var
  Off: Integer;
begin
  if (not AIsGlobal) and Self.IsLocal(AName) then
  begin
    FFrame.TryGetValue(AName, Off);
    { Off is negative (slot base = obj). itab is 8 bytes higher in memory. }
    Result := Format('%d(%%rbp)', [Off + 8]);
  end
  else
    Result := AName + '_itab(%rip)';
end;

{ Load an integer-family value from memory into %rax, extended to the full
  64-bit register according to AType's width and signedness.  Narrower-than-
  32-bit loads use a sign/zero-extending move; 32-bit signed widens with
  movslq, 32-bit unsigned with a plain movl (which zero-extends the upper 32
  bits on x86-64); 64-bit is a straight movq. }
procedure TX86_64Backend.EmitLoadVar(const AOperand: string; AType: TTypeDesc);
begin
  case IntByteSize(AType) of
    1: if IsUnsignedInt(AType) then
         Self.Emit(Format(#9'movzbq %s, %%rax', [AOperand]))
       else
         Self.Emit(Format(#9'movsbq %s, %%rax', [AOperand]));
    2: if IsUnsignedInt(AType) then
         Self.Emit(Format(#9'movzwq %s, %%rax', [AOperand]))
       else
         Self.Emit(Format(#9'movswq %s, %%rax', [AOperand]));
    8: Self.Emit(Format(#9'movq %s, %%rax', [AOperand]));
  else
    { 4-byte: a movl into %eax zero-extends into %rax.  For a signed Integer
      sign-extend instead so the upper 32 bits carry the sign. }
    if IsUnsignedInt(AType) then
      Self.Emit(Format(#9'movl %s, %%eax', [AOperand]))
    else
      Self.Emit(Format(#9'movslq %s, %%rax', [AOperand]));
  end;
end;

{ Store the value in %rax to memory at the slot's natural width, using the
  matching register sub-view (%al / %ax / %eax / %rax). }
procedure TX86_64Backend.EmitStoreVar(const AOperand: string; AType: TTypeDesc);
begin
  case IntByteSize(AType) of
    1: Self.Emit(Format(#9'movb %%al, %s', [AOperand]));
    2: Self.Emit(Format(#9'movw %%ax, %s', [AOperand]));
    8: Self.Emit(Format(#9'movq %%rax, %s', [AOperand]));
  else
    Self.Emit(Format(#9'movl %%eax, %s', [AOperand]));
  end;
end;

{ Reserve a slot for AName of type AType in the current frame, advancing
  AOffset by the slot size (8 bytes for scalars/pointers; TotalSize rounded
  up to the next 8-byte boundary for records).  Stores the offset as a
  negative integer so VarOperand emits -N(%rbp). }
procedure TX86_64Backend.AddSlot(const AName: string; AType: TTypeDesc;
                                 var AOffset: Integer);
var
  Sz: Integer;
begin
  if (AType <> nil) and (AType.Kind in [tyRecord, tyStaticArray]) then
    Sz := (AType.RawSize + 7) and (-8)
  else if (AType <> nil) and (AType.Kind = tyInterface) then
    Sz := 16   { fat pointer: obj slot (+0) then itab slot (+8) }
  else
    Sz := 8;
  Inc(AOffset, Sz);
  FFrame.Add(AName, -AOffset);
  FFrameTypes.Add(AName, AType);
end;

procedure TX86_64Backend.BuildFrame(ADecl: TMethodDecl);
var
  I, J, K, Offset, StackOff, TryCount, IntIdx2: Integer;
  P:    TMethodParam;
  VD:   TVarDecl;
begin
  Self.ClearFrame;
  FFrame      := TDictionary<>.Create;
  FFrameTypes := TDictionary<>.Create;
  Offset   := 0;
  StackOff := 16;  { first stack arg: +16(%rbp) — above saved %rbp and ret addr }
  { For class methods, Self is the implicit first integer param (%rdi).
    Allocate a pointer-size slot for it; normal params start at IntIdx=1. }
  if ADecl.OwnerTypeName <> '' then
    Self.AddSlot('Self', nil, Offset);  { nil = pointer size (8 bytes) }

  { Params: first 6 integer register slots are register-passed (spilled to
    negative slots in prologue); slots 7+ are on the stack at positive %rbp
    offsets.  Open-array params consume TWO register slots each: data ptr and
    high index.  Track IntIdx2 separately from the logical param index I. }
  begin
    IntIdx2 := 0;
    if (ADecl.OwnerTypeName <> '') or FSretFunc then
      Inc(IntIdx2);  { Self / sret already consumed one register }
    for I := 0 to ADecl.Params.Count - 1 do
    begin
      P := TMethodParam(ADecl.Params.Items[I]);
      if P.IsOpenArray then
      begin
        { Two register slots: data pointer and high index. }
        if IntIdx2 < 6 then
          Self.AddSlot(P.ParamName, nil, Offset)   { nil = pointer-size (8 bytes) }
        else
        begin
          FFrame.Add(P.ParamName, StackOff);
          FFrameTypes.Add(P.ParamName, nil);
          Inc(StackOff, 8);
        end;
        Inc(IntIdx2);
        if IntIdx2 < 6 then
          Self.AddSlot(P.ParamName + '_high', nil, Offset)
        else
        begin
          FFrame.Add(P.ParamName + '_high', StackOff);
          FFrameTypes.Add(P.ParamName + '_high', nil);
          Inc(StackOff, 8);
        end;
        Inc(IntIdx2);
      end
      else if (P.ResolvedType <> nil) and (P.ResolvedType.Kind = tyInterface) then
      begin
        { Interface param: fat pointer = two consecutive integer register slots.
          Allocate a single 16-byte slot (obj at base, itab at base+8) so that
          IntfObjOperand/IntfItabOperand can address both halves.  Two IntIdx
          increments mirror the register-passing convention. }
        if IntIdx2 < 6 then
          Self.AddSlot(P.ParamName, P.ResolvedType, Offset)
        else
        begin
          FFrame.Add(P.ParamName, StackOff);
          FFrameTypes.Add(P.ParamName, P.ResolvedType);
          Inc(StackOff, 16);
        end;
        Inc(IntIdx2);
        { Second slot (itab): if register-passed, no separate frame entry needed
          (AddSlot already reserved 16 bytes at ParamName); if stack-passed the
          itab word sits at StackOff+8 which IntfItabOperand computes from Off+8. }
        Inc(IntIdx2);
      end
      else
      begin
        if IntIdx2 < 6 then
          Self.AddSlot(P.ParamName, P.ResolvedType, Offset)
        else
        begin
          { Stack-passed param: lives at +StackOff(%rbp), pushed by caller. }
          FFrame.Add(P.ParamName, StackOff);
          FFrameTypes.Add(P.ParamName, P.ResolvedType);
          Inc(StackOff, 8);
        end;
        Inc(IntIdx2);
      end;
    end;
  end;
  { Result slot for a function (not a procedure).
    For a record-returning (sret) function the Result IS the caller's buffer —
    we store the incoming sret pointer (%rdi) in an 8-byte slot and dereference
    through it on every field write.  We record the slot as tyPointer so
    VarOperand returns the slot address (not the record address). }
  if ADecl.ResolvedReturnType <> nil then
  begin
    if ADecl.ResolvedReturnType.Kind = tyRecord then
    begin
      FSretFunc := True;
      Self.AddSlot('Result', nil, Offset);  { nil = pointer-size (8 bytes) }
    end
    else
      Self.AddSlot('Result', ADecl.ResolvedReturnType, Offset);
  end;
  { Local var declarations. }
  if ADecl.Body <> nil then
    for I := 0 to ADecl.Body.Decls.Count - 1 do
    begin
      VD := TVarDecl(ADecl.Body.Decls.Items[I]);
      for J := 0 to VD.Names.Count - 1 do
        Self.AddSlot(VD.Names.Strings[J], VD.ResolvedType, Offset);
    end;
  { Pre-allocate 512-byte exception frame slots — one per try/finally or
    try/except in the function body (recursively).  Pre-allocation ensures
    frames live at static %rbp-relative addresses rather than being carved
    from %rsp inside a loop, which would grow the stack by 512 bytes per
    iteration and corrupt parent frame prev-pointers.
    Each slot name is '_exc_frame_N'; VarOperand returns the low-address
    operand (-N(%rbp)), which is what _PushExcFrame expects as the frame base. }
  if ADecl.Body <> nil then
  begin
    TryCount := 0;
    for K := 0 to ADecl.Body.Stmts.Count - 1 do
      TryCount := TryCount + Self.CountTryStmts(TASTStmt(ADecl.Body.Stmts.Items[K]));
    for K := 0 to TryCount - 1 do
    begin
      { Each frame is 512 bytes, 16-byte aligned.  We bump Offset by 512 and
        store the negative offset as the slot base (the lowest address of the
        block, matching alloc16 semantics). }
      Inc(Offset, 512);
      { Align to 16 bytes after the bump. }
      Offset := (Offset + 15) and (-16);
      FFrame.Add('_exc_frame_' + IntToStr(K), -Offset);
      FFrameTypes.Add('_exc_frame_' + IntToStr(K), nil);
    end;
  end;
  { Round the reserved size up to a 16-byte multiple (SysV alignment).
    -16 is the bitmask not(15) in two's complement (Blaise `not` is Boolean). }
  FFrameSize := (Offset + 15) and (-16);
end;

procedure TX86_64Backend.ClearFrame;
begin
  if FFrame <> nil then
  begin
    FFrame.Free;
    FFrame := nil;
  end;
  if FFrameTypes <> nil then
  begin
    FFrameTypes.Free;
    FFrameTypes := nil;
  end;
  FFrameSize    := 0;
  FSretFunc     := False;
  FExcDepth     := 0;
  FExcFrameNext := 0;
  FFinallyStack.Clear;
end;

{ ------------------------------------------------------------------ }
{ Expression lowering                                                  }
{ ------------------------------------------------------------------ }

function TX86_64Backend.IntExprType(AExpr: TASTExpr): TTypeDesc;
var
  T: TTypeDesc;
begin
  if AExpr is TIdentExpr then
  begin
    { Prefer the slot's recorded type (local then global) over the node's
      ResolvedType: the slot type is what the memory actually holds. }
    T := Self.LocalType(TIdentExpr(AExpr).Name);
    if T = nil then
      T := Self.GlobalType(TIdentExpr(AExpr).Name);
    if T <> nil then
    begin
      Exit(T);
    end;
  end;
  Result := AExpr.ResolvedType;
end;

{ Re-narrow the value in %rax to AType, then re-extend so the register again
  holds a value consistent with that type.  Narrowing masks/truncates to the
  low N bits; widening sign- or zero-extends.  A no-op for a value already
  consistent with a 4- or 8-byte type, but harmless to apply. }
procedure TX86_64Backend.EmitNarrowToType(AType: TTypeDesc);
begin
  case IntByteSize(AType) of
    1: if IsUnsignedInt(AType) then
         Self.Emit(#9'movzbq %al, %rax')
       else
         Self.Emit(#9'movsbq %al, %rax');
    2: if IsUnsignedInt(AType) then
         Self.Emit(#9'movzwq %ax, %rax')
       else
         Self.Emit(#9'movswq %ax, %rax');
    8: ;  { already a full 64-bit value }
  else
    { 4-byte: re-establish the upper 32 bits per signedness. }
    if IsUnsignedInt(AType) then
      Self.Emit(#9'movl %eax, %eax')    { zero-extends into %rax }
    else
      Self.Emit(#9'movslq %eax, %rax');
  end;
end;

{ Load a float value from memory into %xmm0. }
procedure TX86_64Backend.EmitLoadFloat(const AOperand: string; AType: TTypeDesc);
begin
  if (AType <> nil) and (AType.Kind = tySingle) then
    Self.Emit(Format(#9'movss %s, %%xmm0', [AOperand]))
  else
    Self.Emit(Format(#9'movsd %s, %%xmm0', [AOperand]));
end;

{ Store %xmm0 into memory. }
procedure TX86_64Backend.EmitStoreFloat(const AOperand: string; AType: TTypeDesc);
begin
  if (AType <> nil) and (AType.Kind = tySingle) then
    Self.Emit(Format(#9'movss %%xmm0, %s', [AOperand]))
  else
    Self.Emit(Format(#9'movsd %%xmm0, %s', [AOperand]));
end;

{ Evaluate a floating-point expression, leaving the result in %xmm0.
  Binary operators: push %xmm0 onto the stack via subq/movsd, evaluate the
  right operand into %xmm0, then pop the left into %xmm1 and combine.
  This mirrors the integer strategy (push %rax) without requiring movaps/movups
  shuffles. }
procedure TX86_64Backend.EmitExprToXmm0(AExpr: TASTExpr);
var
  FL:  TFloatLiteral;
  BE:  TBinaryExpr;
  Ty:  TTypeDesc;
  IsS: Boolean;
begin
  if AExpr is TFloatLiteral then
  begin
    FL  := TFloatLiteral(AExpr);
    Ty  := AExpr.ResolvedType;
    IsS := (Ty <> nil) and (Ty.Kind = tySingle);
    { Use a .rodata constant for the immediate float — x86 has no mov-imm
      for xmm registers.  Emit a file-local label that holds the 8-byte
      (Double) or 4-byte (Single) encoding of the literal. }
    if IsS then
    begin
      Self.Emit(Format(#9'movss .LF%s(%%rip), %%xmm0',
        [IntToStr(FLabelCount)]));
      { Defer the .rodata entry to the data section by registering a synthetic
        global with a special FP-literal tag.  We emit it directly since our
        data section is collected: just write it now in a .section .rodata block. }
      Self.Emit('.section .rodata');
      Self.Emit('.balign 4');
      Self.Emit(Format('.LF%s:', [IntToStr(FLabelCount)]));
      Self.Emit(Format(#9'.float %s', [FL.Value]));
      Self.Emit('.text');
      Inc(FLabelCount);
    end
    else
    begin
      Self.Emit(Format(#9'movsd .LF%s(%%rip), %%xmm0',
        [IntToStr(FLabelCount)]));
      Self.Emit('.section .rodata');
      Self.Emit('.balign 8');
      Self.Emit(Format('.LF%s:', [IntToStr(FLabelCount)]));
      Self.Emit(Format(#9'.double %s', [FL.Value]));
      Self.Emit('.text');
      Inc(FLabelCount);
    end;
    Exit;
  end;

  if AExpr is TIdentExpr then
  begin
    Ty := AExpr.ResolvedType;
    if (Ty = nil) and Self.IsLocal(TIdentExpr(AExpr).Name) then
      Ty := Self.LocalType(TIdentExpr(AExpr).Name);
    if (Ty = nil) then
      Ty := Self.GlobalType(TIdentExpr(AExpr).Name);
    Self.EmitLoadFloat(Self.VarOperand(TIdentExpr(AExpr).Name), Ty);
    Exit;
  end;

  if AExpr is TBinaryExpr then
  begin
    BE  := TBinaryExpr(AExpr);
    IsS := (BE.ResolvedType <> nil) and (BE.ResolvedType.Kind = tySingle);
    { left → %xmm0, push to stack via subq/movsd; right → %xmm0;
      pop left into %xmm1 via movsd/addq. }
    Self.EmitExprToXmm0(BE.Left);
    Self.Emit(#9'subq $8, %rsp');
    if IsS then
      Self.Emit(#9'movss %xmm0, (%rsp)')
    else
      Self.Emit(#9'movsd %xmm0, (%rsp)');
    Self.EmitExprToXmm0(BE.Right);
    if IsS then
    begin
      Self.Emit(#9'movss (%rsp), %xmm1');
      Self.Emit(#9'addq $8, %rsp');
      case BE.Op of
        boAdd:   Self.Emit(#9'addss %xmm0, %xmm1');
        boSub:   Self.Emit(#9'subss %xmm0, %xmm1');  { left - right }
        boMul:   Self.Emit(#9'mulss %xmm0, %xmm1');
        boSlash: Self.Emit(#9'divss %xmm0, %xmm1');
        boEQ, boNE, boLT, boGT, boLE, boGE:
          begin
            Self.Emit(#9'ucomiss %xmm0, %xmm1');  { %xmm1 - %xmm0 }
            case BE.Op of
              boEQ: Self.Emit(#9'sete %al');
              boNE: Self.Emit(#9'setne %al');
              boLT: Self.Emit(#9'setb %al');   { below (CF set) }
              boGT: Self.Emit(#9'seta %al');   { above }
              boLE: Self.Emit(#9'setbe %al');
              boGE: Self.Emit(#9'setae %al');
            end;
            Self.Emit(#9'movzbl %al, %eax');
            Self.Emit(#9'movq %rax, %xmm0');  { comparison result as int in %rax then convert? }
            { Actually we need int result for condition tests — put result in %rax,
              then caller decides if it needs to be in %xmm0.  But EmitExprToXmm0
              is for float expressions; comparisons of floats return int (Boolean).
              Fall through: return the 0/1 in %rax.  The caller (EmitCondBranch)
              actually calls EmitExprToEax and tests %rax.  So we shouldn't reach
              here for comparisons — they go through EmitCondBranch → EmitExprToEax
              which will handle float comparisons. }
          end;
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported float binary operator');
      end;
      { Result is in %xmm1, copy to %xmm0 if not a comparison. }
      if BE.Op in [boAdd, boSub, boMul, boSlash] then
        Self.Emit(#9'movaps %xmm1, %xmm0');
    end
    else
    begin
      Self.Emit(#9'movsd (%rsp), %xmm1');
      Self.Emit(#9'addq $8, %rsp');
      case BE.Op of
        boAdd:   Self.Emit(#9'addsd %xmm0, %xmm1');
        boSub:   Self.Emit(#9'subsd %xmm0, %xmm1');  { left - right }
        boMul:   Self.Emit(#9'mulsd %xmm0, %xmm1');
        boSlash: Self.Emit(#9'divsd %xmm0, %xmm1');
        boEQ, boNE, boLT, boGT, boLE, boGE:
          begin
            Self.Emit(#9'ucomisd %xmm0, %xmm1');
            case BE.Op of
              boEQ: Self.Emit(#9'sete %al');
              boNE: Self.Emit(#9'setne %al');
              boLT: Self.Emit(#9'setb %al');
              boGT: Self.Emit(#9'seta %al');
              boLE: Self.Emit(#9'setbe %al');
              boGE: Self.Emit(#9'setae %al');
            end;
            Self.Emit(#9'movzbl %al, %eax');
            { Float comparisons result in integer 0/1 — return via %rax, not %xmm0. }
            Exit;
          end;
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported float binary operator');
      end;
      Self.Emit(#9'movapd %xmm1, %xmm0');
    end;
    Exit;
  end;

  if AExpr is TFuncCallExpr then
  begin
    { User function call whose return type is float. }
    Self.EmitCall(FuncSymbolOf(TFuncCallExpr(AExpr)),
      TMethodDecl(TFuncCallExpr(AExpr).ResolvedDecl),
      TFuncCallExpr(AExpr).Args);
    { Return value is in %xmm0 per SysV ABI. }
    Exit;
  end;

  raise ENativeCodeGenError.Create(
    'native backend: unsupported float expression form ' + AExpr.ClassName);
end;

{ Evaluate an integer-family expression, leaving a 64-bit-extended value in
  %rax.  Every value flows in the full register held sign- or zero-extended to
  its static type, so mixed-width arithmetic (e.g. Integer promoted into an
  Int64 expression) is correct without per-node width tracking; the final
  store re-narrows to the destination slot's width.  Arithmetic and
  comparisons use 64-bit ops uniformly. }
procedure TX86_64Backend.EmitExprToEax(AExpr: TASTExpr);
var
  BE:  TBinaryExpr;
  FC:  TFuncCallExpr;
  FAE: TFieldAccessExpr;
  SAE: TStringSubscriptExpr;
  MD:  TMethodDecl;
  Unsigned: Boolean;
begin
  if AExpr is TIntLiteral then
  begin
    { movabsq carries the full 64-bit immediate (32-bit movq sign-extends a
      value above 2^31, which is wrong for large Int64 constants). }
    Self.Emit(Format(#9'movabsq $%s, %%rax', [IntToStr(TIntLiteral(AExpr).Value)]));
    Exit;
  end;

  if AExpr is TStringLiteral then
  begin
    Self.EmitStrLitAddr(TStringLiteral(AExpr).Value);
    Exit;
  end;

  if AExpr is TIdentExpr then
  begin
    { Static array identifier: return its base address for subscript use. }
    if (TIdentExpr(AExpr).ResolvedType <> nil) and
       (TIdentExpr(AExpr).ResolvedType.Kind = tyStaticArray) then
    begin
      if Self.IsLocal(TIdentExpr(AExpr).Name) then
        Self.Emit(Format(#9'leaq %s, %%rax', [Self.VarOperand(TIdentExpr(AExpr).Name)]))
      else
        Self.Emit(Format(#9'leaq %s(%%rip), %%rax', [TIdentExpr(AExpr).Name]));
      Exit;
    end;
    if TIdentExpr(AExpr).IsConstant then
      Self.Emit(Format(#9'movabsq $%s, %%rax',
        [IntToStr(TIdentExpr(AExpr).ConstValue)]))
    else if TIdentExpr(AExpr).IsVarParam then
    begin
      Self.Emit(Format(#9'movq %s, %%rcx',
        [Self.VarOperand(TIdentExpr(AExpr).Name)]));
      Self.EmitLoadVar('(%rcx)', Self.IntExprType(AExpr));
    end
    else
      Self.EmitLoadVar(Self.VarOperand(TIdentExpr(AExpr).Name),
        Self.IntExprType(AExpr));
    Exit;
  end;

  if AExpr is TFuncCallExpr then
  begin
    FC := TFuncCallExpr(AExpr);
    { MethodAddress(Instance, 'MethodName') — runtime method table lookup.
      The method name string blob (__cn_Name) must exist in the data section;
      the class section emits it for published methods.  Just reference it here
      via a forward label without re-emitting the blob. }
    if SameText(FC.Name, 'MethodAddress') and (FC.Args.Count = 2) then
    begin
      { Arg0: class instance → class pointer in %rdi }
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      { Arg1: pointer to method name string data (offset +12 past ARC header). }
      if TASTExpr(FC.Args.Items[1]) is TStringLiteral then
        Self.Emit(Format(#9'leaq __cn_%s + 12(%%rip), %%rsi',
          [NativeMangle(TStringLiteral(TASTExpr(FC.Args.Items[1])).Value)]))
      else
        raise ENativeCodeGenError.Create(
          'native backend: MethodAddress second arg must be a string literal');
      Self.Emit(#9'callq _MethodAddress');
      { Result = method code pointer in %rax. }
      Exit;
    end;
    { Length/High/Low built-ins for arrays and strings. }
    if SameText(FC.Name, 'High') and (FC.Args.Count = 1) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) then
    begin
      case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
        tyStaticArray:
          Self.Emit(Format(#9'movq $%d, %%rax',
            [TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).HighBound]));
        tyOpenArray:
        begin
          { Load the _high slot for this open-array param. }
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(FC.Args.Items[0]).Name + '_high')]));
        end;
        tyDynArray:
        begin
          { High(A) = Length(A) - 1; delegate to RTL. }
          Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
          Self.Emit(#9'movq %rax, %rdi');
          Self.Emit(#9'callq _DynArrayLength');
          Self.Emit(#9'movslq %eax, %rax');
          Self.Emit(#9'decq %rax');
        end;
        tyString:
        begin
          Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
          Self.Emit(#9'movq %rax, %rdi');
          Self.Emit(#9'callq _StringLength');
          Self.Emit(#9'movslq %eax, %rax');
          Self.Emit(#9'decq %rax');
        end;
      else
        { Integer/enum types: type-level High (min/max). }
        case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
          tyByte:     Self.Emit(#9'movq $255, %rax');
          tyBoolean:  Self.Emit(#9'movq $1, %rax');
          tySmallInt: Self.Emit(#9'movq $32767, %rax');
          tyWord:     Self.Emit(#9'movq $65535, %rax');
          tyInteger:  Self.Emit(#9'movq $2147483647, %rax');
          tyUInt32:   Self.Emit(#9'movq $4294967295, %rax');
          tyEnum:     Self.Emit(Format(#9'movq $%d, %%rax',
            [TEnumTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).Members.Count - 1]));
        else
          Self.Emit(#9'movq $0, %rax');
        end;
      end;
      Exit;
    end;

    if SameText(FC.Name, 'Low') and (FC.Args.Count = 1) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) then
    begin
      case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
        tyStaticArray:
          Self.Emit(Format(#9'movq $%d, %%rax',
            [TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).LowBound]));
        tySmallInt: Self.Emit(#9'movq $-32768, %rax');
        tyInteger:  Self.Emit(#9'movq $-2147483648, %rax');
      else
        Self.Emit(#9'movq $0, %rax');  { 0 for all array/byte/bool/word/unsigned/open/dyn }
      end;
      Exit;
    end;

    if SameText(FC.Name, 'Length') and (FC.Args.Count = 1) and
       (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) then
    begin
      case TASTExpr(FC.Args.Items[0]).ResolvedType.Kind of
        tyStaticArray:
        begin
          Self.Emit(Format(#9'movq $%d, %%rax',
            [TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).HighBound -
             TStaticArrayTypeDesc(TASTExpr(FC.Args.Items[0]).ResolvedType).LowBound + 1]));
        end;
        tyOpenArray:
        begin
          { Length = High + 1: load _high slot and add 1. }
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(FC.Args.Items[0]).Name + '_high')]));
          Self.Emit(#9'incq %rax');
        end;
        tyDynArray:
        begin
          Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
          Self.Emit(#9'movq %rax, %rdi');
          Self.Emit(#9'callq _DynArrayLength');
          Self.Emit(#9'movslq %eax, %rax');
        end;
      else
        { String: delegate to RTL. }
        Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _StringLength');
        Self.Emit(#9'movslq %eax, %rax');
      end;
      Exit;
    end;
    if SameText(FC.Name, 'Pos') and (FC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringPos');
      Self.Emit(#9'movslq %eax, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'Copy') and (FC.Args.Count = 3) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[2]));
      Self.Emit(#9'movl %eax, %edx');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movl %eax, %esi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringCopy');
      Exit;
    end;
    if SameText(FC.Name, 'UpperCase') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _StringUpperCase');
      Exit;
    end;
    if SameText(FC.Name, 'LowerCase') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _StringLowerCase');
      Exit;
    end;
    if SameText(FC.Name, 'Trim') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _StringTrim');
      Exit;
    end;
    if SameText(FC.Name, 'SameText') and (FC.Args.Count = 2) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[1]));
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringSameText');
      Self.Emit(#9'movslq %eax, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'IntToStr') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
         (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyInt64) then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _Int64ToStr');
      end
      else if (TASTExpr(FC.Args.Items[0]).ResolvedType <> nil) and
              (TASTExpr(FC.Args.Items[0]).ResolvedType.Kind = tyUInt64) then
      begin
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _UInt64ToStr');
      end
      else
      begin
        Self.Emit(#9'movl %eax, %edi');
        Self.Emit(#9'callq _IntToStr');
      end;
      Exit;
    end;
    if SameText(FC.Name, 'StrToInt') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _StrToInt');
      Self.Emit(#9'movslq %eax, %rax');
      Exit;
    end;
    if SameText(FC.Name, 'StrToInt64') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _StrToInt64');
      Exit;
    end;
    if SameText(FC.Name, 'PChar') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      { PChar(str) is identity — the Blaise string data pointer IS the char data. }
      Exit;
    end;
    if SameText(FC.Name, 'string') and (FC.Args.Count = 1) then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _StringFromPChar');
      Exit;
    end;
    { Format(Fmt, Arg1, ...) — built-in that builds an args array and calls
      _StringFormatN; handled specially because it takes a variadic args list. }
    if SameText(FC.Name, 'Format') and (FC.Args.Count >= 1) then
    begin
      Self.EmitFormatCall(FC.Args);
      Exit;
    end;
    if FC.IsIndirectCall then
    begin
      { Bare function-pointer call: load the pointer from the variable slot
        and dispatch via callq *%r10. }
      Self.EmitCallIndirect(
        Self.VarOperand(FC.Name),   { local slot or global RIP-relative }
        TProceduralTypeDesc(FC.ResolvedProcType),
        FC.Args);
      { Normalise the return value width. }
      if FC.ResolvedType <> nil then
        Self.EmitNarrowToType(FC.ResolvedType);
      Exit;
    end;
    { Type cast TypeName(Expr): ResolvedDecl is nil.  Evaluate the operand,
      then truncate/extend to the target integer-family type.  Mirrors the QBE
      backend's cast lowering. }
    if FC.ResolvedDecl = nil then
    begin
      Self.EmitExprToEax(TASTExpr(FC.Args.Items[0]));
      Self.EmitNarrowToType(FC.ResolvedType);
      Exit;
    end;
    Self.EmitCall(FuncSymbolOf(FC), TMethodDecl(FC.ResolvedDecl), FC.Args);
    { Normalise the (32-bit-ABI) return value to the callee's return width so
      it is correctly extended in %rax before entering further arithmetic. }
    if FC.ResolvedType <> nil then
      Self.EmitNarrowToType(FC.ResolvedType);
    Exit;
  end;

  if AExpr is TBinaryExpr then
  begin
    BE := TBinaryExpr(AExpr);
    { String concatenation (boAdd on tyString): call _StringConcat(left, right). }
    if (BE.Op = boAdd) and
       (BE.Left.ResolvedType <> nil) and
       (BE.Left.ResolvedType.Kind = tyString) then
    begin
      Self.EmitExprToEax(BE.Left);
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(BE.Right);
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringConcat');
      Exit;
    end;
    { left -> %rax, save; right -> %rax; left -> %rcx; combine in 64 bits. }
    Self.EmitExprToEax(BE.Left);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(BE.Right);
    Self.Emit(#9'movq %rax, %rcx');   { right in %rcx }
    Self.Emit(#9'popq %rax');          { left in %rax }
    case BE.Op of
      boAdd: Self.Emit(#9'addq %rcx, %rax');
      boSub: Self.Emit(#9'subq %rcx, %rax');
      boMul: Self.Emit(#9'imulq %rcx, %rax');
      boDiv, boMod:
        begin
          { 64-bit divide.  Choose signed vs unsigned by the operand types:
            if either side is an unsigned 64-bit type, use unsigned division
            so the top bit is a magnitude bit, not a sign.  cqto sign-extends
            %rax into %rdx:%rax; for unsigned we zero %rdx instead. }
          Unsigned := IsUnsignedInt(BE.Left.ResolvedType) and
                      IsUnsignedInt(BE.Right.ResolvedType);
          if Unsigned then
          begin
            Self.Emit(#9'xorl %edx, %edx');
            Self.Emit(#9'divq %rcx');
          end
          else
          begin
            Self.Emit(#9'cqto');
            Self.Emit(#9'idivq %rcx');
          end;
          if BE.Op = boMod then
            Self.Emit(#9'movq %rdx, %rax');  { remainder in %rdx }
        end;
      { Signed integer comparisons -> boolean 0/1 in %rax.  AT&T `cmpq B, A`
        computes A - B; setcc yields 0/1, then movzbl clears the rest. }
      boEQ, boNE, boLT, boGT, boLE, boGE:
        begin
          Self.Emit(#9'cmpq %rcx, %rax');
          case BE.Op of
            boEQ: Self.Emit(#9'sete %al');
            boNE: Self.Emit(#9'setne %al');
            boLT: Self.Emit(#9'setl %al');
            boGT: Self.Emit(#9'setg %al');
            boLE: Self.Emit(#9'setle %al');
            boGE: Self.Emit(#9'setge %al');
          end;
          Self.Emit(#9'movzbl %al, %eax');  { 0/1 in %rax (movzbl zero-extends) }
        end;
    else
      raise ENativeCodeGenError.Create(
        'native backend: unsupported binary operator in integer expression');
    end;
    Exit;
  end;

  { Open-array element read: A[I] where A is an open-array parameter.
    The data pointer lives in the _var_A slot (not _var_A_high). }
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr is TIdentExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyOpenArray) then
  begin
    SAE := TStringSubscriptExpr(AExpr);
    { Load data pointer from the param slot into %rcx. }
    Self.Emit(Format(#9'movq %s, %%rcx',
      [Self.VarOperand(TIdentExpr(SAE.StrExpr).Name)]));
    { Index * elem_size → element address. }
    Self.EmitExprToEax(SAE.IndexExpr);
    Self.Emit(Format(#9'imulq $%d, %%rax',
      [TOpenArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType.RawSize]));
    Self.Emit(#9'addq %rcx, %rax');
    Self.EmitLoadVar('(%rax)',
      TOpenArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType);
    Exit;
  end;

  { Dynamic-array element read: A[I] where A is a dynamic array variable.
    Data pointer is stored directly in the variable slot. }
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyDynArray) then
  begin
    SAE := TStringSubscriptExpr(AExpr);
    { Load data pointer. }
    Self.EmitExprToEax(SAE.StrExpr);
    Self.Emit(#9'movq %rax, %rcx');
    { Index * elem_size → element address. }
    Self.EmitExprToEax(SAE.IndexExpr);
    Self.Emit(Format(#9'imulq $%d, %%rax',
      [TDynArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType.RawSize]));
    Self.Emit(#9'addq %rcx, %rax');
    Self.EmitLoadVar('(%rax)',
      TDynArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType);
    Exit;
  end;

  { Static array element read: A[I] where A: array[L..H] of T.
    Uses TStringSubscriptExpr (the parser's postfix-bracket node). }
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyStaticArray) then
  begin
    SAE := TStringSubscriptExpr(AExpr);
    { Base address of array into %rcx. }
    Self.EmitExprToEax(SAE.StrExpr);  { returns base address for tyStaticArray }
    Self.Emit(#9'movq %rax, %rcx');
    { Index into %rax, subtract LowBound, multiply by element size. }
    Self.EmitExprToEax(SAE.IndexExpr);
    if TStaticArrayTypeDesc(SAE.StrExpr.ResolvedType).LowBound <> 0 then
      Self.Emit(Format(#9'subq $%d, %%rax',
        [TStaticArrayTypeDesc(SAE.StrExpr.ResolvedType).LowBound]));
    Self.Emit(Format(#9'imulq $%d, %%rax',
      [TStaticArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType.RawSize]));
    Self.Emit(#9'addq %rcx, %rax');   { %rax = element address }
    Self.EmitLoadVar('(%rax)',
      TStaticArrayTypeDesc(SAE.StrExpr.ResolvedType).ElementType);
    Exit;
  end;

  { String subscript S[I]: calls _OrdAt(str_ptr, index) -> byte value as Integer. }
  if (AExpr is TStringSubscriptExpr) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType <> nil) and
     (TStringSubscriptExpr(AExpr).StrExpr.ResolvedType.Kind = tyString) then
  begin
    SAE := TStringSubscriptExpr(AExpr);
    Self.EmitExprToEax(SAE.StrExpr);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(SAE.IndexExpr);
    Self.Emit(#9'movl %eax, %esi');
    Self.Emit(#9'popq %rdi');
    Self.Emit(#9'callq _OrdAt');
    Self.Emit(#9'movslq %eax, %rax');
    Exit;
  end;

  { Zero-arg interface method call: G.GetVal where G: IFoo.  Dispatched through
    the itab; result (if any) in %rax. }
  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsInterfaceCall then
  begin
    FAE := TFieldAccessExpr(AExpr);
    Self.EmitInterfaceCall(FAE.RecordName, FAE.IsGlobal,
      TInterfaceTypeDesc(FAE.ResolvedClassType), FAE.FieldName, nil);
    if (FAE.ResolvedType <> nil) and
       not (FAE.ResolvedType.Kind in [tyInt64, tyUInt64, tyPointer, tyClass,
                                      tyString, tyPChar, tyInterface]) then
      Self.EmitNarrowToType(FAE.ResolvedType);
    Exit;
  end;

  { Array field subscript read: R.Arr[I] where Arr is an array-typed field.
    Compute the record base address, add FieldInfo.Offset to reach the array
    field, then index into the array (static, dynamic, or open). }
  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsArrayAccess and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) and
     (TFieldAccessExpr(AExpr).Base = nil) then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if FAE.IsVarParam then
    begin
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(FAE.RecordName)]));
    end
    else if Self.IsLocal(FAE.RecordName) then
      Self.Emit(Format(#9'leaq %s, %%rcx', [Self.VarOperand(FAE.RecordName)]))
    else
      Self.Emit(Format(#9'leaq %s(%%rip), %%rcx', [FAE.RecordName]));
    if FAE.FieldInfo.Offset > 0 then
      Self.Emit(Format(#9'addq $%d, %%rcx', [FAE.FieldInfo.Offset]));
    if FAE.FieldInfo.TypeDesc.Kind = tyDynArray then
    begin
      Self.Emit(#9'movq (%rcx), %rcx');
      Self.EmitExprToEax(FAE.PropIndexExpr);
      Self.Emit(Format(#9'imulq $%d, %%rax',
        [TDynArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.RawSize]));
      Self.Emit(#9'addq %rcx, %rax');
      if TDynArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.Kind = tyRecord then
        Exit;
      Self.EmitLoadVar('(%rax)',
        TDynArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType);
    end
    else if FAE.FieldInfo.TypeDesc.Kind = tyStaticArray then
    begin
      Self.Emit(#9'pushq %rcx');
      Self.EmitExprToEax(FAE.PropIndexExpr);
      if TStaticArrayTypeDesc(FAE.FieldInfo.TypeDesc).LowBound <> 0 then
        Self.Emit(Format(#9'subq $%d, %%rax',
          [TStaticArrayTypeDesc(FAE.FieldInfo.TypeDesc).LowBound]));
      Self.Emit(Format(#9'imulq $%d, %%rax',
        [TStaticArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.RawSize]));
      Self.Emit(#9'popq %rcx');
      Self.Emit(#9'addq %rcx, %rax');
      if TStaticArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.Kind = tyRecord then
        Exit;
      Self.EmitLoadVar('(%rax)',
        TStaticArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType);
    end
    else if FAE.FieldInfo.TypeDesc.Kind = tyOpenArray then
    begin
      Self.Emit(#9'movq (%rcx), %rcx');
      Self.EmitExprToEax(FAE.PropIndexExpr);
      Self.Emit(Format(#9'imulq $%d, %%rax',
        [TOpenArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.RawSize]));
      Self.Emit(#9'addq %rcx, %rax');
      if TOpenArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType.Kind = tyRecord then
        Exit;
      Self.EmitLoadVar('(%rax)',
        TOpenArrayTypeDesc(FAE.FieldInfo.TypeDesc).ElementType);
    end;
    Exit;
  end;

  { Record/class field read: Rec.Field or Class.Field.
    Handles local/global record bases and class (pointer-deref) bases. }
  if (AExpr is TFieldAccessExpr) and
     (TFieldAccessExpr(AExpr).FieldInfo <> nil) and
     not TFieldAccessExpr(AExpr).IsMethodCall and
     not TFieldAccessExpr(AExpr).IsConstructorCall and
     (TFieldAccessExpr(AExpr).Base = nil) then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if FAE.IsClassAccess then
    begin
      { Class field: FAE.RecordName is a class variable (holds a pointer).
        Load the pointer (always 8 bytes = movq), then dereference at FieldInfo.Offset. }
      if Self.IsLocal(FAE.RecordName) then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(FAE.RecordName)]))
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%rcx', [FAE.RecordName]));
      Self.EmitLoadVar(Format('%d(%%rcx)', [FAE.FieldInfo.Offset]),
        FAE.FieldInfo.TypeDesc);
    end
    else if FAE.IsImplicitSelf then
    begin
      { Bare field name inside a class method: RecordName is empty/irrelevant;
        load Self from its frame slot, then dereference at FieldInfo.Offset. }
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
      Self.EmitLoadVar(Format('%d(%%rcx)', [FAE.FieldInfo.Offset]),
        FAE.FieldInfo.TypeDesc);
    end
    else if FAE.IsVarParam then
    begin
      { Var-param or record-Self: the slot holds a pointer to the record storage.
        Load the pointer, then dereference at FieldInfo.Offset. }
      if Self.IsLocal(FAE.RecordName) then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(FAE.RecordName)]))
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%rcx', [FAE.RecordName]));
      Self.EmitLoadVar(Format('%d(%%rcx)', [FAE.FieldInfo.Offset]),
        FAE.FieldInfo.TypeDesc);
    end
    else if Self.IsLocal(FAE.RecordName) then
    begin
      if FAE.FieldInfo.Offset = 0 then
        Self.EmitLoadVar(Self.VarOperand(FAE.RecordName), FAE.FieldInfo.TypeDesc)
      else
      begin
        Self.Emit(Format(#9'leaq %s, %%rcx', [Self.VarOperand(FAE.RecordName)]));
        Self.EmitLoadVar(Format('%d(%%rcx)', [FAE.FieldInfo.Offset]),
          FAE.FieldInfo.TypeDesc);
      end;
    end
    else
    begin
      if FAE.FieldInfo.Offset = 0 then
        Self.EmitLoadVar(FAE.RecordName + '(%rip)', FAE.FieldInfo.TypeDesc)
      else
      begin
        Self.Emit(Format(#9'leaq %s(%%rip), %%rcx', [FAE.RecordName]));
        Self.EmitLoadVar(Format('%d(%%rcx)', [FAE.FieldInfo.Offset]),
          FAE.FieldInfo.TypeDesc);
      end;
    end;
    Exit;
  end;

  { Zero-arg method call on a variable: B.GetVal or H.GetValue.
    For class variables Self is the loaded pointer; for record variables Self
    is the address of the record storage. }
  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsMethodCall then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if FAE.ResolvedMethod = nil then
      raise ENativeCodeGenError.Create(
        'native backend: zero-arg method call has no ResolvedMethod');
    MD := TMethodDecl(FAE.ResolvedMethod);
    if MD.IsRecordMethod then
    begin
      if Self.IsLocal(FAE.RecordName) then
        Self.Emit(Format(#9'leaq %s, %%rdi', [Self.VarOperand(FAE.RecordName)]))
      else
        Self.Emit(Format(#9'leaq %s(%%rip), %%rdi', [FAE.RecordName]));
    end
    else
    begin
      if Self.IsLocal(FAE.RecordName) then
        Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(FAE.RecordName)]))
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%rdi', [FAE.RecordName]));
    end;
    if MD.VTableSlot >= 0 then
    begin
      Self.Emit(#9'movq (%rdi), %rax');
      Self.Emit(Format(#9'movq %d(%%rax), %%rax', [(MD.VTableSlot + 1) * 8]));
      Self.Emit(#9'callq *%rax');
    end
    else
      Self.Emit(#9'callq ' + MethodEmitNameNative(
        MD, MD.OwnerTypeName, FAE.FieldName));
    if (MD.ResolvedReturnType <> nil) and
       not IsIntFamily(MD.ResolvedReturnType) and
       not IsFloatFamily(MD.ResolvedReturnType) and
       (MD.ResolvedReturnType.Kind <> tyString) then
      Self.EmitNarrowToType(MD.ResolvedReturnType);
    Exit;
  end;

  { TODO: @Rec.Arr[I] (TAddrOfExpr with TFieldAccessExpr.IsArrayAccess) — not yet lowered in native backend }

  { @FuncName — load the function's code address into %rax.
    The semantic pass sets ResolvedType.Kind = tyProcedural on the inner
    TIdentExpr when it names a standalone procedure or function. }
  if (AExpr is TAddrOfExpr) and
     (TAddrOfExpr(AExpr).Expr is TIdentExpr) and
     (TIdentExpr(TAddrOfExpr(AExpr).Expr).ResolvedType <> nil) and
     (TIdentExpr(TAddrOfExpr(AExpr).Expr).ResolvedType.Kind = tyProcedural) then
  begin
    Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
      [TIdentExpr(TAddrOfExpr(AExpr).Expr).Name]));
    Exit;
  end;

  { TypeName.Create — allocate a new class instance.
    Returns the instance pointer in %rax.  Does NOT do ARC (caller's job). }
  if (AExpr is TFieldAccessExpr) and
     TFieldAccessExpr(AExpr).IsConstructorCall then
  begin
    FAE := TFieldAccessExpr(AExpr);
    if (FAE.ResolvedType = nil) or not (FAE.ResolvedType is TRecordTypeDesc) then
      raise ENativeCodeGenError.Create('native backend: constructor call has no class type');
    { _ClassAlloc(size, fieldcleanup_fn): returns zeroed instance ptr (after header). }
    Self.Emit(Format(#9'movq $%d, %%rdi',
      [TRecordTypeDesc(FAE.ResolvedType).TotalSize]));
    Self.Emit(Format(#9'leaq _FieldCleanup_%s(%%rip), %%rsi',
      [NativeMangle(FAE.ResolvedType.Name)]));
    Self.Emit(#9'callq _ClassAlloc');
    { Store vtable pointer at offset 0 if the class has virtual methods. }
    if TRecordTypeDesc(FAE.ResolvedType).HasVTable then
    begin
      Self.Emit(Format(#9'leaq vtable_%s(%%rip), %%rcx',
        [NativeMangle(FAE.ResolvedType.Name)]));
      Self.Emit(#9'movq %rcx, (%rax)');
    end;
    { Call user-defined zero-arg Create body if present. }
    if FAE.ResolvedMethod <> nil then
    begin
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq ' + MethodEmitNameNative(
        TMethodDecl(FAE.ResolvedMethod), FAE.ResolvedType.Name, FAE.FieldName));
      Self.Emit(#9'popq %rax');
    end;
    { %rax = new instance pointer. }
    Exit;
  end;

  { Class method call: C.Method() or C.Method(args) returning a scalar. }
  if AExpr is TMethodCallExpr then
  begin
    Self.EmitMethodCallExpr(TMethodCallExpr(AExpr));
    Exit;
  end;

  raise ENativeCodeGenError.Create(
    'native backend: unsupported expression form ' + AExpr.ClassName);
end;

{ Emit a class method call: load Self into %rdi, then scalar args starting at
  %rsi/%rdx/etc.  The method symbol is OwnerTypeName_MethodName. }
procedure TX86_64Backend.EmitMethodCallExpr(ACall: TMethodCallExpr);
var
  I:    Integer;
  MD:   TMethodDecl;
  Sym:  string;
  Arg:  TASTExpr;
  RT:   TRecordTypeDesc;
begin
  { Interface method dispatch: receiver is an interface fat pointer; route
    through the itab rather than a static method symbol. }
  if (ACall.ResolvedClassType <> nil) and
     (ACall.ResolvedClassType.Kind = tyInterface) then
  begin
    Self.EmitInterfaceCall(ACall.ObjectName, ACall.IsGlobal,
      TInterfaceTypeDesc(ACall.ResolvedClassType), ACall.Name, ACall.Args);
    Exit;
  end;

  { Constructor call with args: TypeName.Create(args).
    Allocate the instance, save it in %r10, push args, pop into registers,
    call the constructor body, then return the instance in %rax. }
  if ACall.IsConstructorCall then
  begin
    RT := TRecordTypeDesc(ACall.ResolvedClassType);
    Self.Emit(Format(#9'movq $%d, %%rdi', [RT.TotalSize]));
    Self.Emit(Format(#9'leaq _FieldCleanup_%s(%%rip), %%rsi', [NativeMangle(RT.Name)]));
    Self.Emit(#9'callq _ClassAlloc');
    if RT.HasVTable then
    begin
      Self.Emit(Format(#9'leaq vtable_%s(%%rip), %%rcx', [NativeMangle(RT.Name)]));
      Self.Emit(#9'movq %rcx, (%rax)');
    end;
    MD := TMethodDecl(ACall.ResolvedMethod);
    if MD <> nil then
    begin
      Self.Emit(#9'movq %rax, %r10');
      for I := 0 to ACall.Args.Count - 1 do
        Self.EmitMethodArgPush(TMethodParam(MD.Params.Items[I]),
          TASTExpr(ACall.Args.Items[I]));
      for I := CountArgSlots(MD.Params) - 1 downto 0 do
        Self.Emit(#9'popq ' + SysVArgRegs64[I + 1]);
      Self.Emit(#9'movq %r10, %rdi');
      Self.Emit(#9'callq ' + MethodEmitNameNative(MD, RT.Name, ACall.Name));
      Self.Emit(#9'movq %r10, %rax');
    end;
    Exit;
  end;

  MD := TMethodDecl(ACall.ResolvedMethod);
  if MD = nil then
    raise ENativeCodeGenError.Create(
      'native backend: TMethodCallExpr has no ResolvedMethod (' + ACall.Name + ')');
  Sym := MethodEmitNameNative(MD, MD.OwnerTypeName, ACall.Name);

  { Evaluate args left-to-right and push them (var/out args by address). }
  for I := 0 to ACall.Args.Count - 1 do
  begin
    Arg := TASTExpr(ACall.Args.Items[I]);
    Self.EmitMethodArgPush(TMethodParam(MD.Params.Items[I]), Arg);
  end;

  { Load Self (the receiver) into %r10 to survive the pop loop. }
  if ACall.ObjectName <> '' then
  begin
    { Named receiver: load the class pointer (always 8-byte movq). }
    if Self.IsLocal(ACall.ObjectName) then
      Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]))
    else
      Self.Emit(Format(#9'movq %s(%%rip), %%r10', [ACall.ObjectName]));
  end
  else if ACall.ObjExpr <> nil then
  begin
    Self.EmitExprToEax(ACall.ObjExpr);
    Self.Emit(#9'movq %rax, %r10');
  end
  else
  begin
    { Implicit self: load from Self slot. }
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
  end;

  { Pop args into %rsi/%rdx/... (shift by 1 for %rdi = Self).
    Use slot count so interface args (2 slots each) get two pops. }
  for I := CountArgSlots(MD.Params) - 1 downto 0 do
    Self.Emit(#9'popq ' + SysVArgRegs64[I + 1]);
  { Place Self as first arg. }
  Self.Emit(#9'movq %r10, %rdi');
  Self.Emit(#9'callq ' + Sym);
  { Result in %rax (int) or %xmm0 (float). }
end;

procedure TX86_64Backend.EmitMethodArgPush(APar: TMethodParam; AArg: TASTExpr);
var
  ClassRT: TRecordTypeDesc;
  IntfDesc: TInterfaceTypeDesc;
  ItabSym: string;
begin
  if (APar <> nil) and APar.IsVarParam then
  begin
    { Pass the argument's address.  If the arg is itself a var param the slot
      already holds a pointer; otherwise take the address of the local/global. }
    if (AArg is TIdentExpr) and TIdentExpr(AArg).IsVarParam then
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.VarOperand(TIdentExpr(AArg).Name)]))
    else if (AArg is TIdentExpr) and Self.IsLocal(TIdentExpr(AArg).Name) then
      Self.Emit(Format(#9'leaq %s, %%rax',
        [Self.VarOperand(TIdentExpr(AArg).Name)]))
    else if AArg is TIdentExpr then
      Self.Emit(Format(#9'leaq %s(%%rip), %%rax', [TIdentExpr(AArg).Name]))
    else
      raise ENativeCodeGenError.Create(
        'native backend: var/out method argument must be a variable');
    Self.Emit(#9'pushq %rax');
  end
  else if (APar <> nil) and (APar.ResolvedType <> nil) and
          (APar.ResolvedType.Kind = tyInterface) then
  begin
    { Interface param: push obj first (lower register slot), then itab (higher
      register slot).  The pop loop runs high-to-low, so itab (pushed last) is
      popped first into the higher register, obj (pushed first) into the lower. }
    IntfDesc := TInterfaceTypeDesc(APar.ResolvedType);
    if AArg.ResolvedType.Kind = tyClass then
    begin
      { Class expression → interface: emit obj, look up static itab. }
      ClassRT := TRecordTypeDesc(AArg.ResolvedType);
      ItabSym := 'itab_' + NativeMangle(ClassRT.Name) + '_' + NativeMangle(IntfDesc.Name);
      Self.EmitExprToEax(AArg);          { obj -> %rax }
      Self.Emit(#9'pushq %rax');         { push obj }
      Self.Emit(Format(#9'leaq %s(%%rip), %%rax', [ItabSym]));
      Self.Emit(#9'pushq %rax');         { push itab }
    end
    else if AArg is TAsExpr then
    begin
      { T as IFoo: runtime itab lookup. }
      Self.EmitExprToEax(TAsExpr(AArg).Obj);
      Self.Emit(#9'pushq %rax');         { save obj for push below }
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(Format(#9'leaq typeinfo_%s(%%rip), %%rsi',
        [NativeMangle(TAsExpr(AArg).TypeName)]));
      Self.Emit(#9'callq _GetItab');
      Self.Emit(#9'pushq %rax');         { itab on top; obj below }
      { Stack top: itab, below: obj — but we need obj first (lower slot).
        Swap: pop itab into %rcx, leave obj on stack, push itab back. }
      Self.Emit(#9'popq %rcx');          { rcx = itab }
      { %rax is still obj (was saved before callq). Re-load from stack: }
      Self.Emit(#9'movq (%rsp), %rax'); { rax = obj (already on stack) }
      { Stack already has obj; push itab on top. }
      Self.Emit(#9'pushq %rcx');         { itab on top, obj below ✓ }
    end
    else if (AArg is TIdentExpr) and
            TIdentExpr(AArg).IsImplicitSelf and
            (TIdentExpr(AArg).ImplicitFieldInfo <> nil) then
    begin
      { Implicit Self.field of interface type: load from object layout. }
      Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand('Self')]));
      if TFieldInfo(TIdentExpr(AArg).ImplicitFieldInfo).Offset > 0 then
        Self.Emit(Format(#9'addq $%d, %%rax',
          [TFieldInfo(TIdentExpr(AArg).ImplicitFieldInfo).Offset]));
      Self.Emit(#9'movq (%rax), %rcx');  { obj }
      Self.Emit(#9'movq 8(%rax), %rdx'); { itab }
      Self.Emit(#9'pushq %rcx');         { push obj }
      Self.Emit(#9'pushq %rdx');         { push itab }
    end
    else if AArg is TIdentExpr then
    begin
      { Interface variable: load both halves. }
      Self.Emit(Format(#9'movq %s, %%rax',
        [Self.IntfObjOperand(TIdentExpr(AArg).Name, TIdentExpr(AArg).IsGlobal)]));
      Self.Emit(Format(#9'movq %s, %%rcx',
        [Self.IntfItabOperand(TIdentExpr(AArg).Name, TIdentExpr(AArg).IsGlobal)]));
      Self.Emit(#9'pushq %rax');         { push obj }
      Self.Emit(#9'pushq %rcx');         { push itab }
    end
    else
      raise ENativeCodeGenError.Create(
        'native backend: unsupported interface argument expression');
  end
  else
  begin
    Self.EmitExprToEax(AArg);
    Self.Emit(#9'pushq %rax');
  end;
end;

{ Count total integer register slots consumed by a parameter list.
  Most params = 1 slot; interface params = 2 (obj + itab); open-array = 2.
  Used by pop loops so they iterate over slots, not logical arg positions. }
function TX86_64Backend.CountArgSlots(AParams: TObjectList): Integer;
var
  I: Integer;
  P: TMethodParam;
begin
  Result := 0;
  if AParams = nil then Exit;
  for I := 0 to AParams.Count - 1 do
  begin
    P := TMethodParam(AParams.Items[I]);
    if P.IsOpenArray then
      Inc(Result, 2)
    else if (P.ResolvedType <> nil) and (P.ResolvedType.Kind = tyInterface) then
      Inc(Result, 2)
    else
      Inc(Result);
  end;
end;

{ Emit a TMethodCallStmt (class method call in statement position).
  Same as EmitMethodCallExpr but for statement nodes. }
procedure TX86_64Backend.EmitMethodCallStmt(ACall: TMethodCallStmt);
var
  I:   Integer;
  MD:  TMethodDecl;
  Sym: string;
  Arg: TASTExpr;
begin
  { Interface method dispatch (statement position): route through the itab. }
  if (ACall.ResolvedClassType <> nil) and
     (ACall.ResolvedClassType.Kind = tyInterface) then
  begin
    if ACall.IsImplicitSelf and (ACall.ImplicitBaseInfo <> nil) then
      Self.EmitInterfaceFieldCall(ACall.ImplicitBaseInfo,
        TInterfaceTypeDesc(ACall.ResolvedClassType), ACall.Name, ACall.Args)
    else
      Self.EmitInterfaceCall(ACall.ObjectName, ACall.IsGlobal,
        TInterfaceTypeDesc(ACall.ResolvedClassType), ACall.Name, ACall.Args);
    Exit;
  end;

  MD := TMethodDecl(ACall.ResolvedMethod);
  if MD = nil then
    raise ENativeCodeGenError.Create(
      'native backend: TMethodCallStmt has no ResolvedMethod (' + ACall.Name + ')');
  Sym := MethodEmitNameNative(MD, MD.OwnerTypeName, ACall.Name);

  { Evaluate args left-to-right and push them (var/out args by address). }
  for I := 0 to ACall.Args.Count - 1 do
  begin
    Arg := TASTExpr(ACall.Args.Items[I]);
    Self.EmitMethodArgPush(TMethodParam(MD.Params.Items[I]), Arg);
  end;

  { Load Self (the receiver) into %r10 (movq for class pointer). }
  if ACall.ObjectName <> '' then
  begin
    if Self.IsLocal(ACall.ObjectName) then
      Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand(ACall.ObjectName)]))
    else
      Self.Emit(Format(#9'movq %s(%%rip), %%r10', [ACall.ObjectName]));
  end
  else if ACall.ObjExpr <> nil then
  begin
    Self.EmitExprToEax(ACall.ObjExpr);
    Self.Emit(#9'movq %rax, %r10');
  end
  else
    Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));

  { Pop args into %rsi/%rdx/... (shift by 1 for %rdi = Self).
    Use slot count so interface args (2 slots each) get two pops. }
  for I := CountArgSlots(MD.Params) - 1 downto 0 do
    Self.Emit(#9'popq ' + SysVArgRegs64[I + 1]);
  Self.Emit(#9'movq %r10, %rdi');
  Self.Emit(#9'callq ' + Sym);
end;

procedure TX86_64Backend.EmitInheritedCall(ACall: TInheritedCallStmt);
var
  I:   Integer;
  MD:  TMethodDecl;
  Sym: string;
  Par: TMethodParam;
begin
  { `inherited` on TObject (no parent body) is a no-op. }
  MD := TMethodDecl(ACall.ResolvedMethod);
  if MD = nil then Exit;
  Sym := MethodEmitNameNative(MD, MD.OwnerTypeName, ACall.Name);

  { Evaluate args left-to-right and push them. }
  for I := 0 to ACall.Args.Count - 1 do
  begin
    Par := TMethodParam(MD.Params.Items[I]);
    Self.EmitMethodArgPush(Par, TASTExpr(ACall.Args.Items[I]));
  end;

  { Self is the current method's Self slot. }
  Self.Emit(Format(#9'movq %s, %%r10', [Self.VarOperand('Self')]));
  { Pop args into %rsi/%rdx/... (shift by 1 for %rdi = Self).
    Use slot count so interface args (2 slots each) get two pops. }
  for I := CountArgSlots(MD.Params) - 1 downto 0 do
    Self.Emit(#9'popq ' + SysVArgRegs64[I + 1]);
  Self.Emit(#9'movq %r10, %rdi');
  Self.Emit(#9'callq ' + Sym);

  { A value-returning parent stores its result into the current Result slot,
    so `Result := ...` is unnecessary for `inherited F;` to set Result. }
  if (MD.ResolvedReturnType <> nil) and (MD.ResolvedReturnType.Kind <> tyVoid) then
  begin
    if IsFloatFamily(MD.ResolvedReturnType) then
      Self.EmitStoreFloat(Self.VarOperand('Result'), MD.ResolvedReturnType)
    else
      Self.EmitStoreVar(Self.VarOperand('Result'), MD.ResolvedReturnType);
  end;
end;

procedure TX86_64Backend.EmitCondBranch(AExpr: TASTExpr;
                                        const ATrueLabel, AFalseLabel: string);
var
  BE: TBinaryExpr;
  IsS: Boolean;
begin
  { Float comparison: ucomisd/ucomiss sets CF/ZF directly; use conditional
    jumps that map CF/ZF to the comparison operator.  The result is a direct
    branch without materialising a 0/1 in %rax. }
  if (AExpr is TBinaryExpr) then
  begin
    BE  := TBinaryExpr(AExpr);
    if IsFloatFamily(BE.Left.ResolvedType) or IsFloatFamily(BE.Right.ResolvedType) then
    begin
      IsS := (BE.Left.ResolvedType <> nil) and (BE.Left.ResolvedType.Kind = tySingle);
      Self.EmitExprToXmm0(BE.Left);
      Self.Emit(#9'subq $8, %rsp');
      if IsS then Self.Emit(#9'movss %xmm0, (%rsp)')
      else        Self.Emit(#9'movsd %xmm0, (%rsp)');
      Self.EmitExprToXmm0(BE.Right);
      if IsS then
      begin
        Self.Emit(#9'movss (%rsp), %xmm1');
        Self.Emit(#9'addq $8, %rsp');
        Self.Emit(#9'ucomiss %xmm0, %xmm1');  { compare left(%xmm1) vs right(%xmm0) }
      end
      else
      begin
        Self.Emit(#9'movsd (%rsp), %xmm1');
        Self.Emit(#9'addq $8, %rsp');
        Self.Emit(#9'ucomisd %xmm0, %xmm1');
      end;
      { ucomisd %xmm0, %xmm1 computes xmm1 - xmm0 conceptually for flags.
        CF=1 means xmm1 < xmm0.  ZF=1 means equal. }
      case BE.Op of
        boEQ: begin Self.Emit(#9'je '  + ATrueLabel); end;
        boNE: begin Self.Emit(#9'jne ' + ATrueLabel); end;
        boLT: begin Self.Emit(#9'jb '  + ATrueLabel); end;  { below: CF }
        boGT: begin Self.Emit(#9'ja '  + ATrueLabel); end;  { above: ~CF & ~ZF }
        boLE: begin Self.Emit(#9'jbe ' + ATrueLabel); end;
        boGE: begin Self.Emit(#9'jae ' + ATrueLabel); end;
      else
        raise ENativeCodeGenError.Create(
          'native backend: unsupported float comparison operator');
      end;
      Self.Emit(#9'jmp ' + AFalseLabel);
      Exit;
    end;
  end;

  { Integer condition: evaluate to a 0/1 (or any nonzero=true) value in %eax. }
  Self.EmitExprToEax(AExpr);
  Self.Emit(#9'testq %rax, %rax');
  Self.Emit(#9'jne ' + ATrueLabel);
  Self.Emit(#9'jmp ' + AFalseLabel);
end;

{ ------------------------------------------------------------------ }
{ Statement lowering                                                   }
{ ------------------------------------------------------------------ }

procedure TX86_64Backend.EmitWrite(ACall: TProcCall; ANewline: Boolean);
var
  I:       Integer;
  ArgExpr: TASTExpr;
  K:       TTypeKind;
begin
  { One _SysWrite* call (fd=1) per integer argument, then a trailing newline
    for WriteLn.  The writer is chosen by the argument's type, matching the
    QBE backend exactly:
      UInt64                       -> _SysWriteUInt64 (64-bit unsigned)
      other 8-byte (Int64)         -> _SysWriteInt64  (64-bit signed)
      UInt32 / Word (unsigned-32)  -> _SysWriteUInt64, zero-extended, so a
                                      value above 2^31 prints as a large
                                      positive number, not a signed wrap
      Boolean                      -> _SysWriteBool   (prints True/False)
      everything else (Integer,
        Byte, Enum, ...)           -> _SysWriteInt    (32-bit signed; their
                                      value range is non-negative there)
    The value is already in %rax 64-bit-extended (unsigned narrow loads
    zero-extend), so the unsigned-32 path needs no extra extension.
    M5 handles integer-family arguments only. }
  for I := 0 to ACall.Args.Count - 1 do
  begin
    ArgExpr := TASTExpr(ACall.Args.Items[I]);
    if ArgExpr.ResolvedType <> nil then
      K := ArgExpr.ResolvedType.Kind
    else
      K := tyInteger;
    if K in [tyString, tyPChar] then
    begin
      Self.EmitExprToEax(ArgExpr);
      Self.Emit(#9'movq %rax, %rsi');
      Self.Emit(#9'movl $1, %edi');
      Self.Emit(#9'callq _SysWriteStr');
    end
    else if K = tyDouble then
    begin
      Self.EmitExprToXmm0(ArgExpr);
      Self.Emit(#9'movl $1, %edi');
      Self.Emit(#9'callq _SysWriteDouble');
    end
    else if K = tySingle then
    begin
      Self.EmitExprToXmm0(ArgExpr);
      Self.Emit(#9'movl $1, %edi');
      Self.Emit(#9'callq _SysWriteSingle');
    end
    else if K = tyBoolean then
    begin
      Self.EmitExprToEax(ArgExpr);
      Self.Emit(#9'movl %eax, %esi');
      Self.Emit(#9'movl $1, %edi');
      Self.Emit(#9'callq _SysWriteBool');
    end
    else
    begin
      Self.EmitExprToEax(ArgExpr);     { value -> %rax (64-bit-extended) }
      if K = tyUInt64 then
      begin
        Self.Emit(#9'movq %rax, %rsi');  { arg2 = value (64-bit) }
        Self.Emit(#9'movl $1, %edi');    { arg1 = fd (stdout) }
        Self.Emit(#9'callq _SysWriteUInt64');
      end
      else if K = tyInt64 then
      begin
        Self.Emit(#9'movq %rax, %rsi');
        Self.Emit(#9'movl $1, %edi');
        Self.Emit(#9'callq _SysWriteInt64');
      end
      else if K in [tyUInt32, tyWord] then
      begin
        Self.Emit(#9'movq %rax, %rsi');  { zero-extended 32-bit value }
        Self.Emit(#9'movl $1, %edi');
        Self.Emit(#9'callq _SysWriteUInt64');
      end
      else
      begin
        Self.Emit(#9'movl %eax, %esi');  { arg2 = value (low 32 bits) }
        Self.Emit(#9'movl $1, %edi');    { arg1 = fd (stdout) }
        Self.Emit(#9'callq _SysWriteInt');
      end;
    end;
  end;
  if ANewline then
  begin
    Self.Emit(#9'movl $1, %edi');    { fd = stdout }
    Self.Emit(#9'callq _SysWriteNewline');
  end;
end;

procedure TX86_64Backend.EmitForStmt(AFor: TForStmt);
var
  VarOp, EndSlot:              string;
  LCond, LBody, LNext, LEnd:  string;
  VarType:                     TTypeDesc;
begin
  if Self.IsLocal(AFor.VarName) then
    VarType := Self.LocalType(AFor.VarName)
  else
  begin
    VarType := AFor.StartExpr.ResolvedType;
    Self.AddGlobal(AFor.VarName, VarType);
  end;
  VarOp   := Self.VarOperand(AFor.VarName);
  EndSlot := Self.NewLabel('forend');
  Self.AddGlobal(EndSlot, VarType);
  LCond := Self.NewLabel('fcond');
  LBody := Self.NewLabel('fbody');
  LNext := Self.NewLabel('fnext');
  LEnd  := Self.NewLabel('fend');

  Self.EmitExprToEax(AFor.StartExpr);
  Self.EmitStoreVar(VarOp, VarType);
  Self.EmitExprToEax(AFor.EndExpr);
  Self.EmitStoreVar(EndSlot + '(%rip)', VarType);

  Self.Emit(LCond + ':');
  Self.EmitLoadVar(VarOp, VarType);
  Self.Emit(#9'pushq %rax');
  Self.EmitLoadVar(EndSlot + '(%rip)', VarType);
  Self.Emit(#9'movq %rax, %rcx');
  Self.Emit(#9'popq %rax');
  Self.Emit(#9'cmpq %rcx, %rax');
  if AFor.IsDownTo then
    Self.Emit(#9'jge ' + LBody)
  else
    Self.Emit(#9'jle ' + LBody);
  Self.Emit(#9'jmp ' + LEnd);

  Self.Emit(LBody + ':');
  FBreakLabels.Push(LEnd);
  FBreakExcDepths.Push(FExcDepth);
  FContinueLabels.Push(LNext);
  FContinueExcDepths.Push(FExcDepth);
  Self.EmitStmt(AFor.Body);
  FContinueExcDepths.Pop;
  FContinueLabels.Pop;
  FBreakExcDepths.Pop;
  FBreakLabels.Pop;

  Self.Emit(LNext + ':');
  Self.EmitLoadVar(VarOp, VarType);
  if AFor.IsDownTo then
    Self.Emit(#9'subq $1, %rax')
  else
    Self.Emit(#9'addq $1, %rax');
  Self.EmitStoreVar(VarOp, VarType);
  Self.Emit(#9'jmp ' + LCond);
  Self.Emit(LEnd + ':');
end;

{ ------------------------------------------------------------------ }
{ Exception handling                                                   }
{ ------------------------------------------------------------------ }

function TX86_64Backend.CountTryStmts(AStmt: TASTStmt): Integer;
var
  I:    Integer;
  TFS:  TTryFinallyStmt;
  TES:  TTryExceptStmt;
  Cmp:  TCompoundStmt;
  IfS:  TIfStmt;
  WhS:  TWhileStmt;
  ForS: TForStmt;
  RepS: TRepeatStmt;
  H:    TExceptHandlerClause;
begin
  Result := 0;
  if AStmt = nil then Exit;
  if AStmt is TTryFinallyStmt then
  begin
    TFS := TTryFinallyStmt(AStmt);
    Result := 1;
    for I := 0 to TFS.TryBody.Stmts.Count - 1 do
      Result := Result + Self.CountTryStmts(TASTStmt(TFS.TryBody.Stmts.Items[I]));
    for I := 0 to TFS.FinallyBody.Stmts.Count - 1 do
      Result := Result + Self.CountTryStmts(TASTStmt(TFS.FinallyBody.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TTryExceptStmt then
  begin
    TES := TTryExceptStmt(AStmt);
    Result := 1;
    for I := 0 to TES.TryBody.Stmts.Count - 1 do
      Result := Result + Self.CountTryStmts(TASTStmt(TES.TryBody.Stmts.Items[I]));
    for I := 0 to TES.Handlers.Count - 1 do
    begin
      H := TExceptHandlerClause(TES.Handlers.Items[I]);
      Result := Result + Self.CountTryStmts(H.Body);
    end;
    if TES.ElseBody <> nil then
      for I := 0 to TES.ElseBody.Stmts.Count - 1 do
        Result := Result + Self.CountTryStmts(TASTStmt(TES.ElseBody.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TCompoundStmt then
  begin
    Cmp := TCompoundStmt(AStmt);
    for I := 0 to Cmp.Stmts.Count - 1 do
      Result := Result + Self.CountTryStmts(TASTStmt(Cmp.Stmts.Items[I]));
    Exit;
  end;
  if AStmt is TIfStmt then
  begin
    IfS := TIfStmt(AStmt);
    Exit(Self.CountTryStmts(IfS.ThenStmt) + Self.CountTryStmts(IfS.ElseStmt));
  end;
  if AStmt is TWhileStmt then
  begin
    WhS := TWhileStmt(AStmt);
    Exit(Self.CountTryStmts(WhS.Body));
  end;
  if AStmt is TForStmt then
  begin
    ForS := TForStmt(AStmt);
    Exit(Self.CountTryStmts(ForS.Body));
  end;
  if AStmt is TRepeatStmt then
  begin
    RepS := TRepeatStmt(AStmt);
    for I := 0 to RepS.Body.Stmts.Count - 1 do
      Result := Result + Self.CountTryStmts(TASTStmt(RepS.Body.Stmts.Items[I]));
    Exit;
  end;
end;

{ Unwind exception frames from FExcDepth down to ATargetDepth+1.
  For each frame: pop it; if it is a try/finally frame, also emit the
  finally body inline.  try/except frames have a nil FFinallyStack entry. }
procedure TX86_64Backend.EmitExcUnwind(ATargetDepth: Integer);
var
  I, J:    Integer;
  FinBody: TCompoundStmt;
begin
  for I := FExcDepth downto ATargetDepth + 1 do
  begin
    Self.Emit(#9'callq _PopExcFrame');
    if I - 1 < FFinallyStack.Count then
    begin
      FinBody := FFinallyStack.Get(I - 1);
      if FinBody <> nil then
        for J := 0 to FinBody.Stmts.Count - 1 do
          Self.EmitStmt(TASTStmt(FinBody.Stmts.Items[J]));
    end;
  end;
end;

procedure TX86_64Backend.EmitTryFinallyStmt(AStmt: TTryFinallyStmt);
var
  LblTry:    string;
  LblFinExc: string;
  LblEnd:    string;
  FrameSlot: string;
  I:         Integer;
begin
  LblTry    := Self.NewLabel('try_body');
  LblFinExc := Self.NewLabel('fin_exc');
  LblEnd    := Self.NewLabel('fin_end');

  { Use the next pre-allocated 512-byte frame slot from BuildFrame. }
  FrameSlot := '_exc_frame_' + IntToStr(FExcFrameNext);
  Inc(FExcFrameNext);

  { _PushExcFrame wants the frame base address in %rdi. }
  Self.Emit(Format(#9'leaq %s, %%rdi', [Self.VarOperand(FrameSlot)]));
  Self.Emit(#9'callq _PushExcFrame');
  Inc(FExcDepth);
  FFinallyStack.Add(AStmt.FinallyBody);

  { _blaise_setjmp(frame): returns 0 on normal entry, 1 on exception longjmp. }
  Self.Emit(Format(#9'leaq %s, %%rdi', [Self.VarOperand(FrameSlot)]));
  Self.Emit(#9'callq _blaise_setjmp');
  Self.Emit(#9'testl %eax, %eax');
  Self.Emit(#9'jnz ' + LblFinExc);
  Self.Emit(#9'jmp ' + LblTry);

  { Normal path: run try body, pop frame, run finally, done. }
  Self.Emit(LblTry + ':');
  for I := 0 to AStmt.TryBody.Stmts.Count - 1 do
    Self.EmitStmt(TASTStmt(AStmt.TryBody.Stmts.Items[I]));
  Self.Emit(#9'callq _PopExcFrame');
  Dec(FExcDepth);
  FFinallyStack.Delete(FFinallyStack.Count - 1);
  for I := 0 to AStmt.FinallyBody.Stmts.Count - 1 do
    Self.EmitStmt(TASTStmt(AStmt.FinallyBody.Stmts.Items[I]));
  Self.Emit(#9'jmp ' + LblEnd);

  { Exception path: capture exception, pop frame, run finally, re-raise. }
  Self.Emit(LblFinExc + ':');
  Self.Emit(#9'callq _CurrentException');
  Self.Emit(#9'pushq %rax');   { save exception pointer across finally body }
  Self.Emit(#9'callq _PopExcFrame');
  Dec(FExcDepth);
  for I := 0 to AStmt.FinallyBody.Stmts.Count - 1 do
    Self.EmitStmt(TASTStmt(AStmt.FinallyBody.Stmts.Items[I]));
  Self.Emit(#9'popq %rdi');    { restore saved exception }
  Self.Emit(#9'callq _Reraise');
  Self.Emit(#9'jmp ' + LblEnd);  { unreachable; satisfies assembler block exit }

  Self.Emit(LblEnd + ':');
end;

procedure TX86_64Backend.EmitTryExceptStmt(AStmt: TTryExceptStmt);
var
  LblTry:    string;
  LblExcept: string;
  LblEnd:    string;
  LblBody:   string;
  LblNext:   string;
  FrameSlot: string;
  I, J:      Integer;
  H:         TExceptHandlerClause;
begin
  LblTry    := Self.NewLabel('try_body');
  LblExcept := Self.NewLabel('except_handler');
  LblEnd    := Self.NewLabel('except_end');

  FrameSlot := '_exc_frame_' + IntToStr(FExcFrameNext);
  Inc(FExcFrameNext);

  Self.Emit(Format(#9'leaq %s, %%rdi', [Self.VarOperand(FrameSlot)]));
  Self.Emit(#9'callq _PushExcFrame');
  Inc(FExcDepth);
  { Push nil so FFinallyStack stays index-aligned with FExcDepth.
    A non-local exit crossing a try/except frame only pops it — no body to run. }
  FFinallyStack.Add(nil);

  Self.Emit(Format(#9'leaq %s, %%rdi', [Self.VarOperand(FrameSlot)]));
  Self.Emit(#9'callq _blaise_setjmp');
  Self.Emit(#9'testl %eax, %eax');
  Self.Emit(#9'jnz ' + LblExcept);
  Self.Emit(#9'jmp ' + LblTry);

  { Normal path: run try body, pop frame on clean exit. }
  Self.Emit(LblTry + ':');
  for I := 0 to AStmt.TryBody.Stmts.Count - 1 do
    Self.EmitStmt(TASTStmt(AStmt.TryBody.Stmts.Items[I]));
  Self.Emit(#9'callq _PopExcFrame');
  Dec(FExcDepth);
  FFinallyStack.Delete(FFinallyStack.Count - 1);
  Self.Emit(#9'jmp ' + LblEnd);

  { Exception path: dispatch handlers. }
  Self.Emit(LblExcept + ':');

  if AStmt.Handlers.Count > 0 then
  begin
    { Capture current exception while our frame is still on the stack. }
    Self.Emit(#9'callq _CurrentException');
    Self.Emit(#9'pushq %rax');   { save exception across _PopExcFrame }
    Self.Emit(#9'callq _PopExcFrame');
    Dec(FExcDepth);
    FFinallyStack.Delete(FFinallyStack.Count - 1);
    Self.Emit(#9'popq %r15');    { exception in %r15 (callee-saved — survives handler bodies) }

    for I := 0 to AStmt.Handlers.Count - 1 do
    begin
      H := TExceptHandlerClause(AStmt.Handlers[I]);
      LblBody := Self.NewLabel('exc_handler_body');
      LblNext := Self.NewLabel('exc_handler_next');

      { _IsInstance(obj, typeinfo): returns non-zero if obj is an instance of the type. }
      Self.Emit(#9'movq %r15, %rdi');
      Self.Emit(#9'leaq typeinfo_' + H.TypeName + '(%rip), %rsi');
      Self.Emit(#9'callq _IsInstance');
      Self.Emit(#9'testl %eax, %eax');
      Self.Emit(#9'jnz ' + LblBody);
      Self.Emit(#9'jmp ' + LblNext);

      Self.Emit(LblBody + ':');
      if H.VarName <> '' then
      begin
        { Retain the exception to balance the scope-exit release (the handler
          var is a class local; EmitFunctionDef will emit a release at epilogue
          only for string vars, but we retain here to match QBE backend ARC).
          The handler var slot is a pre-declared local: assign %r15 into it. }
        Self.Emit(#9'movq %r15, %rdi');
        Self.Emit(#9'callq _ClassAddRef');
        if Self.IsLocal(H.VarName) then
          Self.Emit(Format(#9'movq %%r15, %s', [Self.VarOperand(H.VarName)]))
        else
          Self.Emit(Format(#9'movq %%r15, %s(%%rip)', [H.VarName]));
      end;
      for J := 0 to H.Body.Stmts.Count - 1 do
        Self.EmitStmt(TASTStmt(H.Body.Stmts.Items[J]));
      Self.Emit(#9'jmp ' + LblEnd);

      Self.Emit(LblNext + ':');
    end;

    { No handler matched: run else body if any, otherwise re-raise. }
    if AStmt.ElseBody <> nil then
    begin
      for J := 0 to AStmt.ElseBody.Stmts.Count - 1 do
        Self.EmitStmt(TASTStmt(AStmt.ElseBody.Stmts.Items[J]));
      Self.Emit(#9'jmp ' + LblEnd);
    end
    else
    begin
      Self.Emit(#9'movq %r15, %rdi');
      Self.Emit(#9'callq _Reraise');
      Self.Emit(#9'jmp ' + LblEnd);
    end;
  end
  else
  begin
    { Plain catch-all except body. }
    Self.Emit(#9'callq _PopExcFrame');
    Dec(FExcDepth);
    FFinallyStack.Delete(FFinallyStack.Count - 1);
    for I := 0 to AStmt.ExceptBody.Stmts.Count - 1 do
      Self.EmitStmt(TASTStmt(AStmt.ExceptBody.Stmts.Items[I]));
    Self.Emit(#9'jmp ' + LblEnd);
  end;

  Self.Emit(LblEnd + ':');
end;

procedure TX86_64Backend.EmitRaiseStmt(AStmt: TRaiseStmt);
begin
  if AStmt.Expr <> nil then
  begin
    Self.EmitExprToEax(AStmt.Expr);
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _Raise');
  end
  else
  begin
    { Bare re-raise: retrieve the current exception then re-raise it. }
    Self.Emit(#9'callq _CurrentException');
    Self.Emit(#9'movq %rax, %rdi');
    Self.Emit(#9'callq _Reraise');
  end;
end;

procedure TX86_64Backend.EmitStmt(AStmt: TASTStmt);
var
  PC:    TProcCall;
  Comp:  TCompoundStmt;
  IfS:   TIfStmt;
  WhileS: TWhileStmt;
  RepS:  TRepeatStmt;
  Asgn:  TAssignment;
  FA:    TFieldAssignment;
  SSA:   TStaticSubscriptAssign;
  I:     Integer;
  LThen, LElse, LEnd:    string;
  LCond, LBody:          string;
  FDynArgName: string;
  FDynElemSz:  Integer;
begin
  if AStmt is TAssignment then
  begin
    Asgn := TAssignment(AStmt);
    { Method-pointer (of-object) assignment from a TMethod/TAddProc cast:
      P := TAddProc(M) — both sides are 16-byte Code+Data blocks.
      Emit as memcpy(dest, src, 16). }
    if (Asgn.ResolvedLhsType <> nil) and
       (Asgn.ResolvedLhsType.Kind = tyProcedural) and
       (TProceduralTypeDesc(Asgn.ResolvedLhsType).IsMethodPtr) and
       (Asgn.Expr is TFuncCallExpr) and
       (TFuncCallExpr(Asgn.Expr).ResolvedDecl = nil) and
       (TFuncCallExpr(Asgn.Expr).Args.Count = 1) then
    begin
      { Destination address → %rdi }
      if Self.IsLocal(Asgn.Name) then
        Self.Emit(Format(#9'leaq %s, %%rdi', [Self.VarOperand(Asgn.Name)]))
      else
        Self.Emit(Format(#9'leaq %s(%%rip), %%rdi', [Asgn.Name]));
      { Source address: the cast argument (a TMethod record or another method ptr). }
      if TASTExpr(TFuncCallExpr(Asgn.Expr).Args.Items[0]) is TIdentExpr then
      begin
        if Self.IsLocal(TIdentExpr(TASTExpr(TFuncCallExpr(Asgn.Expr).Args.Items[0])).Name) then
          Self.Emit(Format(#9'leaq %s, %%rsi',
            [Self.VarOperand(TIdentExpr(TASTExpr(TFuncCallExpr(Asgn.Expr).Args.Items[0])).Name)]))
        else
          Self.Emit(Format(#9'leaq %s(%%rip), %%rsi',
            [TIdentExpr(TASTExpr(TFuncCallExpr(Asgn.Expr).Args.Items[0])).Name]));
      end
      else
        raise ENativeCodeGenError.Create(
          'native backend: method-ptr cast source must be a simple variable');
      Self.Emit(#9'movq $16, %rdx');
      Self.Emit(#9'callq memcpy');
      Exit;
    end;
    { sret assignment: LHS is a record variable; RHS is a record-returning call.
      Pass the destination buffer address as the hidden first arg (%rdi). }
    if (Asgn.ResolvedLhsType <> nil) and
       (Asgn.ResolvedLhsType.Kind = tyRecord) and
       (Asgn.Expr is TFuncCallExpr) and
       (TFuncCallExpr(Asgn.Expr).ResolvedDecl <> nil) and
       (TMethodDecl(TFuncCallExpr(Asgn.Expr).ResolvedDecl).ResolvedReturnType <> nil) and
       (TMethodDecl(TFuncCallExpr(Asgn.Expr).ResolvedDecl).ResolvedReturnType.Kind = tyRecord) then
    begin
      { Compute destination address: local → leaq N(%rbp); global → leaq sym(%rip). }
      if Self.IsLocal(Asgn.Name) then
        Self.EmitSretCall(
          FuncSymbolOf(TFuncCallExpr(Asgn.Expr)),
          TMethodDecl(TFuncCallExpr(Asgn.Expr).ResolvedDecl),
          TFuncCallExpr(Asgn.Expr).Args,
          Self.VarOperand(Asgn.Name))
      else
        Self.EmitSretCall(
          FuncSymbolOf(TFuncCallExpr(Asgn.Expr)),
          TMethodDecl(TFuncCallExpr(Asgn.Expr).ResolvedDecl),
          TFuncCallExpr(Asgn.Expr).Args,
          Asgn.Name + '(%rip)');
      Exit;
    end;
    if IsFloatFamily(Asgn.ResolvedLhsType) then
    begin
      { Float assignment: value → %xmm0, then store. }
      Self.EmitExprToXmm0(Asgn.Expr);
      { If LHS is Single and RHS is Double (e.g. a float literal which defaults
        to Double), convert via cvtsd2ss so we store the correct 4-byte value. }
      if (Asgn.ResolvedLhsType.Kind = tySingle) and
         (Asgn.Expr.ResolvedType <> nil) and
         (Asgn.Expr.ResolvedType.Kind = tyDouble) then
        Self.Emit(#9'cvtsd2ss %xmm0, %xmm0');
      if Self.IsLocal(Asgn.Name) then
        Self.EmitStoreFloat(Self.VarOperand(Asgn.Name), Self.LocalType(Asgn.Name))
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        Self.EmitStoreFloat(Asgn.Name + '(%rip)', Asgn.ResolvedLhsType);
      end;
    end
    else if (Asgn.ResolvedLhsType <> nil) and
            (Asgn.ResolvedLhsType.Kind = tyString) then
    begin
      { String assignment: _StringAddRef(new); _StringRelease(old); store.
        Same ARC pattern as class assignment. }
      Self.EmitExprToEax(Asgn.Expr);
      Self.Emit(#9'pushq %rax');
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _StringAddRef');
      if Self.IsLocal(Asgn.Name) then
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(Asgn.Name)]))
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%rax', [Asgn.Name]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _StringRelease');
      Self.Emit(#9'popq %rax');
      if Self.IsLocal(Asgn.Name) then
        Self.Emit(Format(#9'movq %%rax, %s', [Self.VarOperand(Asgn.Name)]))
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        Self.Emit(Format(#9'movq %%rax, %s(%%rip)', [Asgn.Name]));
      end;
    end
    else if (Asgn.ResolvedLhsType <> nil) and
            (Asgn.ResolvedLhsType.Kind = tyInterface) then
    begin
      Self.EmitInterfaceAssign(Asgn);
    end
    else if (Asgn.ResolvedLhsType <> nil) and
            (Asgn.ResolvedLhsType.Kind = tyClass) then
    begin
      { Class assignment: new := eval(RHS); _ClassAddRef(new); old := load(LHS);
        _ClassRelease(old); store(LHS) := new. }
      Self.EmitExprToEax(Asgn.Expr);   { new instance -> %rax }
      Self.Emit(#9'pushq %rax');         { save new }
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassAddRef');
      { Load the old value — always a pointer (8 bytes), use movq. }
      if Self.IsLocal(Asgn.Name) then
        Self.Emit(Format(#9'movq %s, %%rax', [Self.VarOperand(Asgn.Name)]))
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%rax', [Asgn.Name]));
      Self.Emit(#9'movq %rax, %rdi');
      Self.Emit(#9'callq _ClassRelease');
      Self.Emit(#9'popq %rax');          { restore new }
      { Store the new value. }
      if Self.IsLocal(Asgn.Name) then
        Self.Emit(Format(#9'movq %%rax, %s', [Self.VarOperand(Asgn.Name)]))
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        Self.Emit(Format(#9'movq %%rax, %s(%%rip)', [Asgn.Name]));
      end;
    end
    else
    begin
      Self.EmitExprToEax(Asgn.Expr);   { value -> %rax (64-bit-extended) }
      if Asgn.IsVarParam then
      begin
        Self.Emit(Format(#9'movq %s, %%rcx',
          [Self.VarOperand(Asgn.Name)]));
        Self.EmitStoreVar('(%rcx)', Asgn.ResolvedLhsType);
      end
      else if Self.IsLocal(Asgn.Name) then
        Self.EmitStoreVar(Self.VarOperand(Asgn.Name), Self.LocalType(Asgn.Name))
      else
      begin
        Self.AddGlobal(Asgn.Name, Asgn.ResolvedLhsType);
        Self.EmitStoreVar(Asgn.Name + '(%rip)', Asgn.ResolvedLhsType);
      end;
    end;
    Exit;
  end;

  if AStmt is TForStmt then
  begin
    Self.EmitForStmt(TForStmt(AStmt));
    Exit;
  end;

  if AStmt is TProcCall then
  begin
    PC := TProcCall(AStmt);
    if SameText(PC.Name, 'WriteLn') then
    begin
      Self.EmitWrite(PC, True);
      Exit;
    end;
    if SameText(PC.Name, 'Write') then
    begin
      Self.EmitWrite(PC, False);
      Exit;
    end;
    { Delete(S, Idx, Count): S := _StringDelete(S, Idx, Count) with ARC. }
    if SameText(PC.Name, 'Delete') and (PC.Args.Count = 3) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[2]));
      Self.Emit(#9'movl %eax, %edx');
      Self.Emit(#9'popq %rax');
      Self.Emit(#9'movl %eax, %esi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringDelete');
      { Assign result back: addref new, release old, store. }
      if TASTExpr(PC.Args.Items[0]) is TIdentExpr then
      begin
        Self.Emit(#9'pushq %rax');
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _StringAddRef');
        if Self.IsLocal(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name) then
          Self.Emit(Format(#9'movq %s, %%rdi',
            [Self.VarOperand(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rdi',
            [TIdentExpr(TASTExpr(PC.Args.Items[0])).Name]));
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rax');
        if Self.IsLocal(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name) then
          Self.Emit(Format(#9'movq %%rax, %s',
            [Self.VarOperand(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name)]))
        else
          Self.Emit(Format(#9'movq %%rax, %s(%%rip)',
            [TIdentExpr(TASTExpr(PC.Args.Items[0])).Name]));
      end;
      Exit;
    end;
    { SetLength(A, N) for dynamic arrays: A := _DynArraySetLength(A, N, ElemSize). }
    if SameText(PC.Name, 'SetLength') and (PC.Args.Count = 2) and
       (TASTExpr(PC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(PC.Args.Items[0]).ResolvedType.Kind = tyDynArray) then
    begin
      if TASTExpr(PC.Args.Items[0]) is TIdentExpr then
      begin
        FDynArgName := TIdentExpr(TASTExpr(PC.Args.Items[0])).Name;
        FDynElemSz :=
          TDynArrayTypeDesc(TASTExpr(PC.Args.Items[0]).ResolvedType).ElementType.RawSize;
        { Load current data ptr into %rdi. }
        if Self.IsLocal(FDynArgName) then
          Self.Emit(Format(#9'movq %s, %%rdi', [Self.VarOperand(FDynArgName)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rdi', [FDynArgName]));
        { New length into %esi. }
        Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
        Self.Emit(#9'movl %eax, %esi');
        { Element size into %edx. }
        Self.Emit(Format(#9'movl $%d, %%edx', [FDynElemSz]));
        Self.Emit(#9'callq _DynArraySetLength');
        { Store new data ptr back. }
        if Self.IsLocal(FDynArgName) then
          Self.Emit(Format(#9'movq %%rax, %s', [Self.VarOperand(FDynArgName)]))
        else
          Self.Emit(Format(#9'movq %%rax, %s(%%rip)', [FDynArgName]));
      end;
      Exit;
    end;
    { SetLength(S, N): S := _StringSetLength(S, N) with ARC. }
    if SameText(PC.Name, 'SetLength') and (PC.Args.Count = 2) and
       (TASTExpr(PC.Args.Items[0]).ResolvedType <> nil) and
       (TASTExpr(PC.Args.Items[0]).ResolvedType.Kind = tyString) then
    begin
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[0]));
      Self.Emit(#9'pushq %rax');
      Self.EmitExprToEax(TASTExpr(PC.Args.Items[1]));
      Self.Emit(#9'movl %eax, %esi');
      Self.Emit(#9'popq %rdi');
      Self.Emit(#9'callq _StringSetLength');
      if TASTExpr(PC.Args.Items[0]) is TIdentExpr then
      begin
        Self.Emit(#9'pushq %rax');
        Self.Emit(#9'movq %rax, %rdi');
        Self.Emit(#9'callq _StringAddRef');
        if Self.IsLocal(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name) then
          Self.Emit(Format(#9'movq %s, %%rdi',
            [Self.VarOperand(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name)]))
        else
          Self.Emit(Format(#9'movq %s(%%rip), %%rdi',
            [TIdentExpr(TASTExpr(PC.Args.Items[0])).Name]));
        Self.Emit(#9'callq _StringRelease');
        Self.Emit(#9'popq %rax');
        if Self.IsLocal(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name) then
          Self.Emit(Format(#9'movq %%rax, %s',
            [Self.VarOperand(TIdentExpr(TASTExpr(PC.Args.Items[0])).Name)]))
        else
          Self.Emit(Format(#9'movq %%rax, %s(%%rip)',
            [TIdentExpr(TASTExpr(PC.Args.Items[0])).Name]));
      end;
      Exit;
    end;
    if PC.IsIndirectCall then
    begin
      if (PC.ResolvedProcType <> nil) and
         TProceduralTypeDesc(PC.ResolvedProcType).IsMethodPtr then
        Self.EmitMethodPtrCall(Self.VarOperand(PC.Name),
          TProceduralTypeDesc(PC.ResolvedProcType), PC.Args)
      else
        Self.EmitCallIndirect(
          Self.VarOperand(PC.Name),
          TProceduralTypeDesc(PC.ResolvedProcType),
          PC.Args);
      Exit;
    end;
    { User procedure call (result, if any, ignored in statement position). }
    Self.EmitCall(FuncSymbolFromDecl(TMethodDecl(PC.ResolvedDecl)),
      TMethodDecl(PC.ResolvedDecl), PC.Args);
    Exit;
  end;

  if AStmt is TCompoundStmt then
  begin
    Comp := TCompoundStmt(AStmt);
    for I := 0 to Comp.Stmts.Count - 1 do
      Self.EmitStmt(TASTStmt(Comp.Stmts.Items[I]));
    Exit;
  end;

  if AStmt is TIfStmt then
  begin
    IfS   := TIfStmt(AStmt);
    LThen := Self.NewLabel('then');
    LEnd  := Self.NewLabel('ifend');
    if IfS.ElseStmt <> nil then
      LElse := Self.NewLabel('else')
    else
      LElse := LEnd;
    Self.EmitCondBranch(IfS.Condition, LThen, LElse);
    Self.Emit(LThen + ':');
    Self.EmitStmt(IfS.ThenStmt);
    Self.Emit(#9'jmp ' + LEnd);
    if IfS.ElseStmt <> nil then
    begin
      Self.Emit(LElse + ':');
      Self.EmitStmt(IfS.ElseStmt);
      Self.Emit(#9'jmp ' + LEnd);
    end;
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt is TTryFinallyStmt then
  begin
    Self.EmitTryFinallyStmt(TTryFinallyStmt(AStmt));
    Exit;
  end;

  if AStmt is TTryExceptStmt then
  begin
    Self.EmitTryExceptStmt(TTryExceptStmt(AStmt));
    Exit;
  end;

  if AStmt is TRaiseStmt then
  begin
    Self.EmitRaiseStmt(TRaiseStmt(AStmt));
    Exit;
  end;

  if AStmt is TWhileStmt then
  begin
    WhileS := TWhileStmt(AStmt);
    LCond  := Self.NewLabel('wcond');
    LBody  := Self.NewLabel('wbody');
    LEnd   := Self.NewLabel('wend');
    Self.Emit(LCond + ':');
    Self.EmitCondBranch(WhileS.Condition, LBody, LEnd);
    Self.Emit(LBody + ':');
    FBreakLabels.Push(LEnd);
    FBreakExcDepths.Push(FExcDepth);
    FContinueLabels.Push(LCond);
    FContinueExcDepths.Push(FExcDepth);
    Self.EmitStmt(WhileS.Body);
    FContinueExcDepths.Pop;
    FContinueLabels.Pop;
    FBreakExcDepths.Pop;
    FBreakLabels.Pop;
    Self.Emit(#9'jmp ' + LCond);
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt is TRepeatStmt then
  begin
    RepS  := TRepeatStmt(AStmt);
    LBody := Self.NewLabel('rbody');
    LCond := Self.NewLabel('rcond');
    LEnd  := Self.NewLabel('rend');
    Self.Emit(LBody + ':');
    FBreakLabels.Push(LEnd);
    FBreakExcDepths.Push(FExcDepth);
    FContinueLabels.Push(LCond);
    FContinueExcDepths.Push(FExcDepth);
    for I := 0 to RepS.Body.Stmts.Count - 1 do
      Self.EmitStmt(TASTStmt(RepS.Body.Stmts.Items[I]));
    FContinueExcDepths.Pop;
    FContinueLabels.Pop;
    FBreakExcDepths.Pop;
    FBreakLabels.Pop;
    Self.Emit(LCond + ':');
    Self.EmitCondBranch(RepS.Condition, LEnd, LBody);
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt is TBreakStmt then
  begin
    if FBreakLabels.Count = 0 then
      raise ENativeCodeGenError.Create('break outside loop');
    Self.EmitExcUnwind(FBreakExcDepths.Peek);
    Self.Emit(#9'jmp ' + FBreakLabels.Peek);
    Exit;
  end;

  if AStmt is TContinueStmt then
  begin
    if FContinueLabels.Count = 0 then
      raise ENativeCodeGenError.Create('continue outside loop');
    Self.EmitExcUnwind(FContinueExcDepths.Peek);
    Self.Emit(#9'jmp ' + FContinueLabels.Peek);
    Exit;
  end;

  if AStmt is TExitStmt then
  begin
    if TExitStmt(AStmt).ResultAssign <> nil then
      Self.EmitStmt(TExitStmt(AStmt).ResultAssign);
    Self.EmitExcUnwind(0);
    if FExitLabel <> '' then
      Self.Emit(#9'jmp ' + FExitLabel)
    else
    begin
      Self.Emit(#9'movl $0, %eax');
      Self.Emit(#9'leave');
      Self.Emit(#9'ret');
    end;
    Exit;
  end;

  if AStmt is TMethodCallStmt then
  begin
    { Class method call in statement position (result discarded). }
    Self.EmitMethodCallStmt(TMethodCallStmt(AStmt));
    Exit;
  end;

  if AStmt is TInheritedCallStmt then
  begin
    Self.EmitInheritedCall(TInheritedCallStmt(AStmt));
    Exit;
  end;

  if AStmt is TFieldAssignment then
  begin
    FA := TFieldAssignment(AStmt);
    if FA.FieldInfo = nil then
      raise ENativeCodeGenError.Create(
        'native backend: field assignment has no resolved field info');
    Self.EmitExprToEax(FA.Expr);
    { Compute destination address: base address + field byte offset. }
    if FSretFunc and (FA.RecordName = 'Result') then
    begin
      { In a sret function, Result holds a pointer to the caller's buffer.
        Load the pointer, then write through it. }
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Result')]));
      Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]),
        FA.FieldInfo.TypeDesc);
    end
    else if FA.IsClassAccess then
    begin
      { TODO: ARC for class fields — [Unretained] must release owned RHS, normal fields need addref/release }
      { Class field write: load the class ptr from its slot (movq), store through it. }
      Self.Emit(#9'pushq %rax');
      if Self.IsLocal(FA.RecordName) then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(FA.RecordName)]))
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%rcx', [FA.RecordName]));
      Self.Emit(#9'popq %rax');
      Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
    end
    else if FA.IsImplicitSelf then
    begin
      { TODO: ARC for implicit-Self class fields — [Unretained] must release owned RHS }
      { Bare field assignment inside a class method: write through Self. }
      Self.Emit(#9'pushq %rax');
      Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand('Self')]));
      Self.Emit(#9'popq %rax');
      Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
    end
    else if FA.IsVarParam then
    begin
      { Var-param or record-Self: the slot holds a pointer to the record storage. }
      Self.Emit(#9'pushq %rax');
      if Self.IsLocal(FA.RecordName) then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(FA.RecordName)]))
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%rcx', [FA.RecordName]));
      Self.Emit(#9'popq %rax');
      Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]), FA.FieldInfo.TypeDesc);
    end
    else if Self.IsLocal(FA.RecordName) then
    begin
      { Local record: VarOperand gives the base address of the record block. }
      if FA.FieldInfo.Offset = 0 then
        Self.EmitStoreVar(Self.VarOperand(FA.RecordName), FA.FieldInfo.TypeDesc)
      else
      begin
        Self.Emit(Format(#9'leaq %s, %%rcx', [Self.VarOperand(FA.RecordName)]));
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]),
          FA.FieldInfo.TypeDesc);
      end;
    end
    else
    begin
      { Global record: name(%rip) is the base. }
      if FA.FieldInfo.Offset = 0 then
        Self.EmitStoreVar(FA.RecordName + '(%rip)', FA.FieldInfo.TypeDesc)
      else
      begin
        Self.Emit(Format(#9'leaq %s(%%rip), %%rcx', [FA.RecordName]));
        Self.EmitStoreVar(Format('%d(%%rcx)', [FA.FieldInfo.Offset]),
          FA.FieldInfo.TypeDesc);
      end;
    end;
    Exit;
  end;

  if AStmt is TStaticSubscriptAssign then
  begin
    SSA := TStaticSubscriptAssign(AStmt);
    if (SSA.ResolvedArrayType <> nil) and
       (SSA.ResolvedArrayType.Kind = tyDynArray) then
    begin
      { Dynamic array element write: A[I] := V.
        Data pointer lives directly in the variable slot. }
      Self.EmitExprToEax(SSA.ValueExpr);
      Self.Emit(#9'pushq %rax');
      { Index * elem_size. }
      Self.EmitExprToEax(SSA.IndexExpr);
      Self.Emit(Format(#9'imulq $%d, %%rax',
        [TDynArrayTypeDesc(SSA.ResolvedArrayType).ElementType.RawSize]));
      { Base pointer into %rcx. }
      if Self.IsLocal(SSA.ArrayName) then
        Self.Emit(Format(#9'movq %s, %%rcx', [Self.VarOperand(SSA.ArrayName)]))
      else
        Self.Emit(Format(#9'movq %s(%%rip), %%rcx', [SSA.ArrayName]));
      Self.Emit(#9'addq %rcx, %rax');
      Self.Emit(#9'movq %rax, %rcx');
      Self.Emit(#9'popq %rax');
      Self.EmitStoreVar('(%rcx)', TDynArrayTypeDesc(SSA.ResolvedArrayType).ElementType);
      Exit;
    end;
    { Static array element write. }
    if (SSA.ResolvedArrayType = nil) or
       (SSA.ResolvedArrayType.Kind <> tyStaticArray) then
      raise ENativeCodeGenError.Create(
        'native backend: static subscript assign on non-static-array');
    { Compute element address: base + (Index - LowBound) * ElemSize }
    { Evaluate value first, push to preserve across address computation. }
    Self.EmitExprToEax(SSA.ValueExpr);
    Self.Emit(#9'pushq %rax');
    { Compute index offset into %rax. }
    Self.EmitExprToEax(SSA.IndexExpr);
    if TStaticArrayTypeDesc(SSA.ResolvedArrayType).LowBound <> 0 then
      Self.Emit(Format(#9'subq $%d, %%rax',
        [TStaticArrayTypeDesc(SSA.ResolvedArrayType).LowBound]));
    Self.Emit(Format(#9'imulq $%d, %%rax',
      [TStaticArrayTypeDesc(SSA.ResolvedArrayType).ElementType.RawSize]));
    { Base address into %rcx. }
    if Self.IsLocal(SSA.ArrayName) then
      Self.Emit(Format(#9'leaq %s, %%rcx', [Self.VarOperand(SSA.ArrayName)]))
    else
      Self.Emit(Format(#9'leaq %s(%%rip), %%rcx', [SSA.ArrayName]));
    Self.Emit(#9'addq %rcx, %rax');   { %rax = element address }
    Self.Emit(#9'movq %rax, %rcx');   { save element address to %rcx }
    Self.Emit(#9'popq %rax');          { restore value }
    Self.EmitStoreVar('(%rcx)', TStaticArrayTypeDesc(SSA.ResolvedArrayType).ElementType);
    Exit;
  end;

  raise ENativeCodeGenError.Create(
    'native backend: unsupported statement ' + AStmt.ClassName);
end;

{ ------------------------------------------------------------------ }
{ Calls and function definitions                                       }
{ ------------------------------------------------------------------ }

{ Allocate stack storage for an inline open-array literal, fill elements in
  order, and leave a pointer to element 0 in %rax.  Returns the bytes allocated
  on the stack; caller must addq that after the call to reclaim them. }
function TX86_64Backend.EmitOpenArrayLiteral(ALit: TArrayLiteralExpr): Integer;
var
  OAType:   TOpenArrayTypeDesc;
  ElemType: TTypeDesc;
  ElemSize: Integer;
  TotalSz:  Integer;
  I:        Integer;
begin
  OAType   := TOpenArrayTypeDesc(ALit.ResolvedType);
  ElemType := OAType.ElementType;
  ElemSize := ElemType.RawSize;
  TotalSz  := ALit.Elements.Count * ElemSize;
  if TotalSz < 1 then TotalSz := 1;
  { Align to 16 bytes for ABI compliance. }
  TotalSz := (TotalSz + 15) and (-16);
  Self.Emit(Format(#9'subq $%d, %%rsp', [TotalSz]));
  Self.Emit(#9'movq %rsp, %rax');  { %rax = base of element storage }
  for I := 0 to ALit.Elements.Count - 1 do
  begin
    Self.EmitExprToEax(TASTExpr(ALit.Elements.Items[I]));
    case ElemSize of
      1: Self.Emit(Format(#9'movb %%al, %d(%%rsp)', [I * ElemSize]));
      2: Self.Emit(Format(#9'movw %%ax, %d(%%rsp)', [I * ElemSize]));
      4: Self.Emit(Format(#9'movl %%eax, %d(%%rsp)', [I * ElemSize]));
    else
      Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [I * ElemSize]));
    end;
  end;
  { Re-load %rax with the base ptr (EmitExprToEax may have clobbered it). }
  Self.Emit(#9'movq %rsp, %rax');
  Exit(TotalSz);
end;

{ Emit a direct call.  SysV AMD64: integer args in rdi/rsi/rdx/rcx/r8/r9;
  float args in xmm0..xmm5 (independent counters).  Stack args (args 7+ in
  total, after registers are exhausted) go right-to-left.  For M6 the common
  cases are:
    - all-integer params: existing push/pop strategy (up to 8 args).
    - all-float params: evaluate left-to-right into %xmm0..%xmmN directly.
    - mixed int+float params (e.g. _SysWriteDouble): evaluate left-to-right;
      integer args push to stack then pop to int regs; float args evaluated
      directly into xmm regs.  All args must fit in registers (≤6 each). }
procedure TX86_64Backend.EmitCall(const AFuncSym: string; ADecl: TMethodDecl;
                                  AArgs: TObjectList);
var
  I:              Integer;
  Arg:            TASTExpr;
  IsVar:          Boolean;
  IsOA:           Boolean;
  ParamType:      TTypeDesc;
  HasFloat:       Boolean;
  SlotCount:      Integer;
  IntIdx, XmmIdx: Integer;
  AllocSz, SlotOff: Integer;
  ExtraStackBytes: Integer;
  CleanUp:        Integer;
begin
  { Detect whether any arg is float-typed.
    Also compute SlotCount: open-array args expand to 2 register slots each. }
  HasFloat  := False;
  SlotCount := 0;
  for I := 0 to AArgs.Count - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    IsOA := (ADecl <> nil) and (I < ADecl.Params.Count) and
            TMethodParam(ADecl.Params.Items[I]).IsOpenArray;
    ParamType := nil;
    if (ADecl <> nil) and (I < ADecl.Params.Count) then
      ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
    if ParamType = nil then
      ParamType := Arg.ResolvedType;
    if IsFloatFamily(ParamType) then
      HasFloat := True;
    if IsOA or ((ParamType <> nil) and (ParamType.Kind = tyInterface)) then
      Inc(SlotCount, 2)
    else
      Inc(SlotCount);
  end;

  ExtraStackBytes := 0;

  if not HasFloat then
  begin
    { Pure integer (or var-param/open-array) call: push/pop strategy.
      Open-array arg A pushes: data ptr first, then high index.
      SlotCount counts register slots after expansion. }
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsVarParam;
      IsOA  := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsOpenArray;
      if IsOA then
      begin
        { Push data pointer. }
        if Arg is TArrayLiteralExpr then
        begin
          { Inline literal [a, b, c]: allocate stack storage and fill.
            ExtraStackBytes accumulates bytes to reclaim after the call. }
          ExtraStackBytes := ExtraStackBytes +
            Self.EmitOpenArrayLiteral(TArrayLiteralExpr(Arg));
          { %rax = data ptr; high = Count-1. }
          Self.Emit(#9'pushq %rax');
          Self.Emit(Format(#9'pushq $%d',
            [TArrayLiteralExpr(Arg).Elements.Count - 1]));
        end
        else if (Arg is TIdentExpr) and
                (TIdentExpr(Arg).ResolvedType <> nil) and
                (TIdentExpr(Arg).ResolvedType.Kind = tyStaticArray) then
        begin
          { Static array coerced to open array: push base ptr + compile-time high. }
          if Self.IsLocal(TIdentExpr(Arg).Name) then
            Self.Emit(Format(#9'leaq %s, %%rax',
              [Self.VarOperand(TIdentExpr(Arg).Name)]))
          else
            Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
              [TIdentExpr(Arg).Name]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(Format(#9'pushq $%d',
            [TStaticArrayTypeDesc(TIdentExpr(Arg).ResolvedType).HighBound -
             TStaticArrayTypeDesc(TIdentExpr(Arg).ResolvedType).LowBound]));
        end
        else
        begin
          { Open-array param forwarded to another open-array param:
            push both data ptr and high from the caller's local slots. }
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(Arg).Name)]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(Arg).Name + '_high')]));
          Self.Emit(#9'pushq %rax');
        end;
      end
      else if IsVar then
      begin
        if (Arg is TIdentExpr) and TIdentExpr(Arg).IsVarParam then
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(Arg).Name)]))
        else if (Arg is TIdentExpr) and Self.IsLocal(TIdentExpr(Arg).Name) then
          Self.Emit(Format(#9'leaq %s, %%rax',
            [Self.VarOperand(TIdentExpr(Arg).Name)]))
        else if Arg is TIdentExpr then
          Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
            [TIdentExpr(Arg).Name]));
        Self.Emit(#9'pushq %rax');
      end
      else if (ParamType <> nil) and (ParamType.Kind = tyInterface) then
      begin
        { Interface param: push obj first (lower slot), then itab (higher slot).
          Pop loop runs high-to-low, so itab is popped first into the higher reg. }
        if (ADecl <> nil) and (I < ADecl.Params.Count) then
          Self.EmitMethodArgPush(TMethodParam(ADecl.Params.Items[I]), Arg)
        else if Arg is TIdentExpr then
        begin
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.IntfObjOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(Format(#9'movq %s, %%rcx',
            [Self.IntfItabOperand(TIdentExpr(Arg).Name, TIdentExpr(Arg).IsGlobal)]));
          Self.Emit(#9'pushq %rax');
          Self.Emit(#9'pushq %rcx');
        end
        else
          raise ENativeCodeGenError.Create(
            'native backend: unsupported interface arg expression in EmitCall');
      end
      else
      begin
        Self.EmitExprToEax(Arg);
        Self.Emit(#9'pushq %rax');
      end;
    end;

    { Note: for open-array args the pushes are ordered as (high, ptr) on the
      stack (last pushed is high) but the pop order reverses back so register
      I=0 gets ptr and I=1 gets high — the two pushes above are in order
      (ptr first, then high) so they pop in reverse: high first (higher slot),
      ptr second (lower slot). This yields %rdi=ptr, %rsi=high for the first
      open-array arg, matching what the callee spills in its prologue. }
    if SlotCount <= 6 then
    begin
      for I := SlotCount - 1 downto 0 do
        Self.Emit(#9'popq ' + SysVArgRegs64[I]);
    end
    else
    begin
      if SlotCount > 8 then
        raise ENativeCodeGenError.Create(
          'native backend: more than 8 argument slots not yet supported');
      for I := SlotCount - 1 downto 6 do
      begin
        if (I - 6) = 0 then Self.Emit(#9'popq %r10')
        else               Self.Emit(#9'popq %r11');
      end;
      for I := 5 downto 0 do
        Self.Emit(#9'popq ' + SysVArgRegs64[I]);
      for I := SlotCount - 1 downto 6 do
      begin
        if (I - 6) = 0 then Self.Emit(#9'pushq %r10')
        else               Self.Emit(#9'pushq %r11');
      end;
    end;
  end
  else
  begin
    { Mixed or pure-float call.  Strategy:
      1. Pre-allocate N×8 bytes on the stack (N = total args, 16-byte aligned).
      2. Evaluate each arg left-to-right into its fixed slot I×8(%rsp).
         Integer args use %rax → movq; float args use %xmm0 → movsd.
      3. After all evaluations, load into the right registers, tracking
         separate IntIdx / XmmIdx counters for the two register files.
      4. Reclaim the pre-allocated block. }
    AllocSz := ((AArgs.Count * 8 + 15) and (-16));
    if AllocSz > 0 then
      Self.Emit(Format(#9'subq $%d, %%rsp', [AllocSz]));

    { Pass 1: evaluate args left-to-right into fixed stack slots. }
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      ParamType := nil;
      if (ADecl <> nil) and (I < ADecl.Params.Count) then
        ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := Arg.ResolvedType;
      IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
               TMethodParam(ADecl.Params.Items[I]).IsVarParam;
      SlotOff := I * 8;

      if IsFloatFamily(ParamType) then
      begin
        Self.EmitExprToXmm0(Arg);
        if (ParamType <> nil) and (ParamType.Kind = tySingle) then
          Self.Emit(Format(#9'movss %%xmm0, %d(%%rsp)', [SlotOff]))
        else
          Self.Emit(Format(#9'movsd %%xmm0, %d(%%rsp)', [SlotOff]));
      end
      else if IsVar then
      begin
        if (Arg is TIdentExpr) and TIdentExpr(Arg).IsVarParam then
          Self.Emit(Format(#9'movq %s, %%rax',
            [Self.VarOperand(TIdentExpr(Arg).Name)]))
        else if (Arg is TIdentExpr) and Self.IsLocal(TIdentExpr(Arg).Name) then
          Self.Emit(Format(#9'leaq %s, %%rax',
            [Self.VarOperand(TIdentExpr(Arg).Name)]))
        else if Arg is TIdentExpr then
          Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
            [TIdentExpr(Arg).Name]));
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
      end
      else
      begin
        Self.EmitExprToEax(Arg);
        Self.Emit(Format(#9'movq %%rax, %d(%%rsp)', [SlotOff]));
      end;
    end;

    { Pass 2: load from slots into registers using separate int/xmm counters. }
    IntIdx := 0;
    XmmIdx := 0;
    for I := 0 to AArgs.Count - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I]);
      ParamType := nil;
      if (ADecl <> nil) and (I < ADecl.Params.Count) then
        ParamType := TMethodParam(ADecl.Params.Items[I]).ResolvedType;
      if ParamType = nil then
        ParamType := Arg.ResolvedType;
      SlotOff := I * 8;

      if IsFloatFamily(ParamType) then
      begin
        if XmmIdx >= 6 then
          raise ENativeCodeGenError.Create('native backend: too many float args');
        if (ParamType <> nil) and (ParamType.Kind = tySingle) then
          Self.Emit(Format(#9'movss %d(%%rsp), %s', [SlotOff, SysVXmmArgRegs[XmmIdx]]))
        else
          Self.Emit(Format(#9'movsd %d(%%rsp), %s', [SlotOff, SysVXmmArgRegs[XmmIdx]]));
        Inc(XmmIdx);
      end
      else
      begin
        if IntIdx >= 6 then
          raise ENativeCodeGenError.Create('native backend: too many int args');
        Self.Emit(Format(#9'movq %d(%%rsp), %s', [SlotOff, SysVArgRegs64[IntIdx]]));
        Inc(IntIdx);
      end;
    end;

    { Reclaim pre-allocated area before the call. }
    if AllocSz > 0 then
      Self.Emit(Format(#9'addq $%d, %%rsp', [AllocSz]));
  end;

  Self.Emit(#9'callq ' + AFuncSym);
  { Caller cleans up stack args (SysV caller-cleans-up convention) and any
    extra bytes allocated by EmitOpenArrayLiteral for inline array literals. }
  if (not HasFloat) then
  begin
    CleanUp := ExtraStackBytes;
    if SlotCount > 6 then
      Inc(CleanUp, (SlotCount - 6) * 8);
    if CleanUp > 0 then
      Self.Emit(Format(#9'addq $%d, %%rsp', [CleanUp]));
  end;
end;

{ Spill the incoming argument register at index AIdx into the param slot
  AOperand, using the register sub-view matching the param's width. }
procedure TX86_64Backend.EmitSpillArg(AIdx: Integer; const AOperand: string;
                                      AType: TTypeDesc);
begin
  case IntByteSize(AType) of
    1: Self.Emit(Format(#9'movb %s, %s', [SysVArgRegs8[AIdx],  AOperand]));
    2: Self.Emit(Format(#9'movw %s, %s', [SysVArgRegs16[AIdx], AOperand]));
    8: Self.Emit(Format(#9'movq %s, %s', [SysVArgRegs64[AIdx], AOperand]));
  else
    Self.Emit(Format(#9'movl %s, %s', [SysVArgRegs[AIdx], AOperand]));
  end;
end;

{ Emit a call through a bare function pointer held in APtrOperand (an AT&T
  memory operand).  Loads the pointer into %r10 (caller-saved scratch, not
  clobbered by arg evaluation in %rax), sets up args exactly as EmitCall does,
  then dispatches via `callq *%r10`.  AProcType supplies the param signature
  for var/out param detection; nil means all value params. }
procedure TX86_64Backend.EmitCallIndirect(const APtrOperand: string;
                                          AProcType: TProceduralTypeDesc;
                                          AArgs: TObjectList);
var
  I:     Integer;
  Arg:   TASTExpr;
  IsVar: Boolean;
begin
  { Load the function pointer before pushing args — %r10 is caller-saved and
    not touched by EmitExprToEax, so it survives the arg-evaluation loop. }
  Self.Emit(Format(#9'movq %s, %%r10', [APtrOperand]));

  for I := 0 to AArgs.Count - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    IsVar := (AProcType <> nil) and (I < AProcType.Params.Count) and
             TProcParamInfo(AProcType.Params.Items[I]).IsVarParam;
    if IsVar then
    begin
      if (Arg is TIdentExpr) and TIdentExpr(Arg).IsVarParam then
        Self.Emit(Format(#9'movq %s, %%rax',
          [Self.VarOperand(TIdentExpr(Arg).Name)]))
      else if (Arg is TIdentExpr) and Self.IsLocal(TIdentExpr(Arg).Name) then
        Self.Emit(Format(#9'leaq %s, %%rax',
          [Self.VarOperand(TIdentExpr(Arg).Name)]))
      else if Arg is TIdentExpr then
        Self.Emit(Format(#9'leaq %s(%%rip), %%rax',
          [TIdentExpr(Arg).Name]));
      Self.Emit(#9'pushq %rax');
    end
    else
    begin
      Self.EmitExprToEax(Arg);
      Self.Emit(#9'pushq %rax');
    end;
  end;

  { Pop args into registers (same as EmitCall; ≤6 args assumed for now). }
  if AArgs.Count > 6 then
    raise ENativeCodeGenError.Create(
      'native backend: indirect call with more than 6 arguments not yet supported');
  for I := AArgs.Count - 1 downto 0 do
    Self.Emit(#9'popq ' + SysVArgRegs64[I]);

  Self.Emit(#9'callq *%r10');
end;

{ Emit a call to a record-returning function using the sret convention.
  ASretAddr is the AT&T operand for the destination buffer already allocated
  by the caller.  Strategy:
    1. leaq ASretAddr → %r10  (save addr before arg eval clobbers %rax/%rdi)
    2. Evaluate each normal arg (push/pop strategy for integer args)
    3. Pop into %rsi/%rdx/... (index 1..N)
    4. movq %r10, %rdi  (hidden first arg = sret ptr)
    5. callq AFuncSym
  All args must be integer-family value params (≤5 since %rdi is taken by sret). }
procedure TX86_64Backend.EmitSretCall(const AFuncSym: string; ADecl: TMethodDecl;
                                      AArgs: TObjectList; const ASretAddr: string);
var
  I:   Integer;
  Arg: TASTExpr;
begin
  { Save the destination address in %r10 (caller-saved scratch that survives
    arg evaluation and the memset call). }
  Self.Emit(Format(#9'leaq %s, %%r10', [ASretAddr]));
  { Zero the destination buffer via memset(%r10, 0, size), mirroring the QBE
    backend.  ADecl.ResolvedReturnType.Kind = tyRecord here. }
  if (ADecl <> nil) and (ADecl.ResolvedReturnType <> nil) then
  begin
    Self.Emit(#9'movq %r10, %rdi');
    Self.Emit(#9'xorl %esi, %esi');
    Self.Emit(Format(#9'movq $%d, %%rdx',
      [TRecordTypeDesc(ADecl.ResolvedReturnType).TotalSize]));
    Self.Emit(#9'callq memset');
    { Reload %r10 after the call (memset may have clobbered caller-saves). }
    Self.Emit(Format(#9'leaq %s, %%r10', [ASretAddr]));
  end;
  { Evaluate normal args left-to-right and push onto the stack. }
  for I := 0 to AArgs.Count - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    Self.EmitExprToEax(Arg);
    Self.Emit(#9'pushq %rax');
  end;
  { Pop into arg registers starting at index 1 (index 0 = %rdi is the sret ptr). }
  if AArgs.Count > 5 then
    raise ENativeCodeGenError.Create(
      'native backend: sret call with more than 5 explicit args not yet supported');
  for I := AArgs.Count - 1 downto 0 do
    Self.Emit(#9'popq ' + SysVArgRegs64[I + 1]);
  { Place the sret pointer as the first integer arg. }
  Self.Emit(#9'movq %r10, %rdi');
  Self.Emit(#9'callq ' + AFuncSym);
end;

{ Emit a method-pointer (of-object) call through a TMethod block.
  APtrOperand is the AT&T memory operand for the 16-byte Code+Data block.
  Load Code into %r10, Data into %rdi, push/pop other args, then callq *%r10. }
procedure TX86_64Backend.EmitMethodPtrCall(const APtrOperand: string;
                                           AProcType: TProceduralTypeDesc;
                                           AArgs: TObjectList);
var
  I:     Integer;
  Arg:   TASTExpr;
begin
  { Get the base address of the TMethod block into %rcx. }
  Self.Emit(Format(#9'leaq %s, %%rcx', [APtrOperand]));
  { Load Code (offset 0) into %r10 for later dispatch. }
  Self.Emit(#9'movq (%rcx), %r10');
  { Load Data (offset 8) into %r11 to survive arg evaluation. }
  Self.Emit(#9'movq 8(%rcx), %r11');

  { Evaluate normal args left-to-right and push them. }
  for I := 0 to AArgs.Count - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    Self.EmitExprToEax(Arg);
    Self.Emit(#9'pushq %rax');
  end;
  { Pop args into %rsi/%rdx/... (index 1+; index 0 = %rdi = Self = Data). }
  if AArgs.Count > 5 then
    raise ENativeCodeGenError.Create(
      'native backend: method-ptr call with more than 5 explicit args');
  for I := AArgs.Count - 1 downto 0 do
    Self.Emit(#9'popq ' + SysVArgRegs64[I + 1]);
  { Place Data (Self) as first arg. }
  Self.Emit(#9'movq %r11, %rdi');
  { Dispatch through Code pointer. }
  Self.Emit(#9'callq *%r10');
end;

{ True when AType is an integer-family type the backend can place in a
  general-purpose register (Byte..Int64).  Floats, records, strings, etc. are
  not yet handled and must fail loudly. }
function IsIntFamily(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and
    (AType.Kind in [tyInteger, tyUInt32, tyInt64, tyUInt64,
                    tySmallInt, tyWord, tyByte, tyBoolean, tyEnum]);
end;

{ Emit a Format(Fmt, Arg1, ..., ArgN) call via the RTL's _StringFormatN.
  The args array layout (matching the QBE backend and blaise_str.pas):
    slot[I] at arr + I*16:  [0..7] = type tag (0=int, 1=string); [8..15] = value.
  We allocate the array on the stack via subq, fill it, then call the RTL. }
{ Emit a Format(Fmt, Arg1, ..., ArgN) call via the RTL's _StringFormatN.
  Stack layout at the callq:
    [%rbp - old_frame ... fmt_ptr ... arr[0]...arr[N-1]] → then call
  The args array layout (matching the QBE backend and blaise_str.pas):
    slot[I] at arr + I*16: [0..7]=type tag (0=int, 1=str); [8..15]=value. }
{ Emit a Format(Fmt, Arg1, ..., ArgN) call via the RTL's _StringFormatN.
  The args array layout (matching the QBE backend):
    slot[I] at arr + I*16: [0..7]=type tag (0=int, 1=str); [8..15]=value.
  Stack discipline: evaluate fmt first and push it (so later push/pop from
  nested expr evaluation cannot overwrite the array we build below it). }
procedure TX86_64Backend.EmitFormatCall(AArgs: TObjectList);
var
  I:         Integer;
  FmtCount:  Integer;
  Arg:       TASTExpr;
  IsIntArg:  Boolean;
  TotalSize: Integer;
begin
  FmtCount := AArgs.Count - 1;
  { Evaluate the format string and save it on the stack first, so that
    the args-array allocation lives below it and expression push/pop during
    argument evaluation cannot corrupt the array area. }
  Self.EmitExprToEax(TASTExpr(AArgs.Items[0]));
  Self.Emit(#9'pushq %rax');     { [%rsp] = fmt ptr }
  if FmtCount > 0 then
  begin
    TotalSize := ((FmtCount * 16) + 15) and (-16);
    Self.Emit(Format(#9'subq $%d, %%rsp', [TotalSize]));
    Self.Emit(#9'movq %rsp, %r11');
    for I := 0 to FmtCount - 1 do
    begin
      Arg := TASTExpr(AArgs.Items[I + 1]);
      IsIntArg := (Arg.ResolvedType = nil) or
        (Arg.ResolvedType.Kind in [tyInteger, tyBoolean, tyByte, tyUInt32,
                                    tyInt64, tyUInt64, tySmallInt, tyWord, tyEnum]);
      if IsIntArg then
        Self.Emit(Format(#9'movq $0, %d(%%r11)', [I * 16]))
      else
        Self.Emit(Format(#9'movq $1, %d(%%r11)', [I * 16]));
      Self.EmitExprToEax(Arg);
      Self.Emit(Format(#9'movq %%rax, %d(%%r11)', [I * 16 + 8]));
    end;
    { Set up args for the call.  The array at %r11 must remain under %rsp
      during the callq (so the call's return-addr push does not overwrite it).
      Load fmt from its pushed location above the array:
        fmt is at %rsp + TotalSize (the push happened before the subq). }
    Self.Emit(Format(#9'movq %d(%%rsp), %%rdi', [TotalSize]));
    Self.Emit(#9'movq %r11, %rsi');
    Self.Emit(Format(#9'movl $%d, %%edx', [FmtCount]));
    Self.Emit(#9'callq _StringFormatN');
    { Now clean up: array + saved fmt ptr. }
    Self.Emit(Format(#9'addq $%d, %%rsp', [TotalSize + 8]));
  end
  else
  begin
    Self.Emit(#9'popq %rdi');
    Self.Emit(#9'xorl %esi, %esi');
    Self.Emit(#9'xorl %edx, %edx');
    Self.Emit(#9'callq _StringFormatN');
  end;
end;

{ Emit a standalone procedure/function definition.  Frame layout mirrors the
  reference (FPC -O- and the QBE backend): params, Result and locals each get
  an 8-byte-aligned %rbp-relative slot sized by their type; the prologue
  spills the incoming argument registers into the param slots at their width;
  the body runs through the slots; a function returns its Result slot
  (64-bit-extended) in %rax/%eax.  M5 supports integer-family value
  parameters and integer-family/void return. }
procedure TX86_64Backend.EmitFunctionDef(ADecl: TMethodDecl);
var
  I, J:        Integer;
  P:           TMethodParam;
  Sym:         string;
  IntIdx:      Integer;
  XmmIdx:      Integer;
begin
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    if P.IsOpenArray then Continue;  { open array: (ptr, high) pair — always ok }
    if P.IsVarParam then Continue;  { var/out: always a pointer — ok }
    if not IsIntFamily(P.ResolvedType) and not IsFloatFamily(P.ResolvedType) and
       ((P.ResolvedType = nil) or
        not (P.ResolvedType.Kind in [tyString, tyPChar, tyPointer,
                                     tyClass, tyInterface,
                                     tyOpenArray, tyDynArray])) then
      raise ENativeCodeGenError.Create(
        'native backend: unsupported parameter type (param ' + P.ParamName + ')');
  end;
  if (ADecl.ResolvedReturnType <> nil) and
     not IsIntFamily(ADecl.ResolvedReturnType) and
     not IsFloatFamily(ADecl.ResolvedReturnType) and
     not (ADecl.ResolvedReturnType.Kind in [tyRecord, tyString, tyPChar, tyPointer, tyClass]) then
    raise ENativeCodeGenError.Create(
      'native backend: unsupported return type (function ' + ADecl.Name + ')');

  Sym := FuncSymbolFromDecl(ADecl);
  Self.BuildFrame(ADecl);

  Self.Emit('.text');
  Self.Emit('.globl ' + Sym);
  Self.Emit(Sym + ':');
  Self.Emit(#9'pushq %rbp');
  Self.Emit(#9'movq %rsp, %rbp');
  if FFrameSize > 0 then
    Self.Emit(Format(#9'subq $%d, %%rsp', [FFrameSize]));
  { Spill incoming argument registers into param slots.  SysV AMD64 passes
    integer args in %rdi/%rsi/... and float args in %xmm0/%xmm1/... independently.
    Track separate counters: IntIdx for integer params, XmmIdx for float params.
    For sret functions the hidden first integer arg (%rdi) is the destination
    buffer pointer; spill it into the Result slot first, then continue with
    the normal params starting at IntIdx=1. }
  IntIdx := 0;
  XmmIdx := 0;
  if FSretFunc then
  begin
    { Save the sret buffer pointer from %rdi into the Result slot. }
    Self.Emit(Format(#9'movq %%rdi, %s', [Self.VarOperand('Result')]));
    IntIdx := 1;
  end;
  if ADecl.OwnerTypeName <> '' then
  begin
    { Class method: spill Self from the first int arg register into its slot. }
    Self.Emit(Format(#9'movq %s, %s',
      [SysVArgRegs64[IntIdx], Self.VarOperand('Self')]));
    Inc(IntIdx);
  end;
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    if P.IsOpenArray then
    begin
      { Open array: two consecutive integer registers — data ptr then high index. }
      if IntIdx < 6 then
      begin
        Self.Emit(Format(#9'movq %s, %s',
          [SysVArgRegs64[IntIdx], Self.VarOperand(P.ParamName)]));
        Inc(IntIdx);
      end;
      if IntIdx < 6 then
      begin
        Self.Emit(Format(#9'movq %s, %s',
          [SysVArgRegs64[IntIdx], Self.VarOperand(P.ParamName + '_high')]));
        Inc(IntIdx);
      end;
    end
    else if IsFloatFamily(P.ResolvedType) then
    begin
      if XmmIdx < 6 then
      begin
        if (P.ResolvedType <> nil) and (P.ResolvedType.Kind = tySingle) then
          Self.Emit(Format(#9'movss %s, %s',
            [SysVXmmArgRegs[XmmIdx], Self.VarOperand(P.ParamName)]))
        else
          Self.Emit(Format(#9'movsd %s, %s',
            [SysVXmmArgRegs[XmmIdx], Self.VarOperand(P.ParamName)]));
        Inc(XmmIdx);
      end;
    end
    else if (P.ResolvedType <> nil) and (P.ResolvedType.Kind = tyInterface) then
    begin
      { Interface param: spill obj register into the 16-byte slot base,
        itab register into base+8.  IntfItabOperand computes Off+8 from the
        frame entry, which lands correctly because AddSlot reserved 16 bytes. }
      if IntIdx < 6 then
      begin
        Self.Emit(Format(#9'movq %s, %s',
          [SysVArgRegs64[IntIdx], Self.VarOperand(P.ParamName)]));
        Inc(IntIdx);
      end;
      if IntIdx < 6 then
      begin
        Self.Emit(Format(#9'movq %s, %s',
          [SysVArgRegs64[IntIdx], Self.IntfItabOperand(P.ParamName, False)]));
        Inc(IntIdx);
      end;
    end
    else if P.IsVarParam then
    begin
      if IntIdx < 6 then
      begin
        Self.Emit(Format(#9'movq %s, %s',
          [SysVArgRegs64[IntIdx], Self.VarOperand(P.ParamName)]));
        Inc(IntIdx);
      end;
    end
    else
    begin
      if IntIdx < 6 then
      begin
        Self.EmitSpillArg(IntIdx, Self.VarOperand(P.ParamName), P.ResolvedType);
        Inc(IntIdx);
      end;
    end;
  end;
  { Initialise Result to 0 (defined default), like the QBE backend.
    For sret functions Result IS the caller's buffer (already zeroed by caller). }
  if (ADecl.ResolvedReturnType <> nil) and not FSretFunc then
  begin
    if IsFloatFamily(ADecl.ResolvedReturnType) then
    begin
      { Zero %xmm0 by xorpd/xorps. }
      if ADecl.ResolvedReturnType.Kind = tySingle then
        Self.Emit(#9'xorps %xmm0, %xmm0')
      else
        Self.Emit(#9'xorpd %xmm0, %xmm0');
      Self.EmitStoreFloat(Self.VarOperand('Result'), ADecl.ResolvedReturnType);
    end
    else
    begin
      Self.Emit(#9'xorl %eax, %eax');
      Self.EmitStoreVar(Self.VarOperand('Result'), ADecl.ResolvedReturnType);
    end;
  end;
  { Zero-initialise ARC-managed local slots (string / interface) so the first
    assignment's release-old step sees nil, not stack garbage, and so an unused
    local releases nil at the epilogue.  Interface locals zero both halves of
    the fat pointer. }
  if ADecl.Body <> nil then
    for I := 0 to ADecl.Body.Decls.Count - 1 do
    begin
      if TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType = nil then Continue;
      if TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.Kind = tyString then
        for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
          Self.Emit(Format(#9'movq $0, %s',
            [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]))
      else if TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.Kind = tyInterface then
        for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
        begin
          Self.Emit(Format(#9'movq $0, %s',
            [Self.IntfObjOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J], False)]));
          Self.Emit(Format(#9'movq $0, %s',
            [Self.IntfItabOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J], False)]));
        end;
    end;
  { Body.  FExitLabel directs Exit statements to the epilogue. }
  FExitLabel := Self.NewLabel('exit');
  if ADecl.Body <> nil then
    for I := 0 to ADecl.Body.Stmts.Count - 1 do
      Self.EmitStmt(TASTStmt(ADecl.Body.Stmts.Items[I]));
  { Epilogue: Exit lands here; load Result into %rax (int) or %xmm0 (float).
    For sret functions the caller's buffer already holds the result — just ret. }
  Self.Emit(FExitLabel + ':');
  if (ADecl.ResolvedReturnType <> nil) and not FSretFunc then
  begin
    if IsFloatFamily(ADecl.ResolvedReturnType) then
      Self.EmitLoadFloat(Self.VarOperand('Result'), ADecl.ResolvedReturnType)
    else
      Self.EmitLoadVar(Self.VarOperand('Result'), ADecl.ResolvedReturnType);
  end;
  { Release ARC-managed local string vars (not params, not Result).
    Result is returned to the caller who owns it; params are caller-owned.

    TODO(arc): the native backend does not yet retain string/class/interface
    *value* params on entry and release them on exit (the QBE backend does —
    see the entry/exit ARC loops in uCodeGenQBE.pas; interfaces ARC through the
    object slot of their fat pointer).  When that retain/release is added here,
    it MUST skip params where P.IsConstParam is True (as well as IsVarParam /
    IsOpenArray): a const param's object is kept alive by the caller for the
    whole call, so no callee-side retain/release is needed.  See the matching
    `or Par.IsConstParam` guards in uCodeGenQBE.pas. }
  if ADecl.Body <> nil then
  begin
    for I := 0 to ADecl.Body.Decls.Count - 1 do
    begin
      if TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType = nil then Continue;
      { String locals: release the string. }
      if TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.Kind = tyString then
        for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
        begin
          Self.Emit(Format(#9'movq %s, %%rdi',
            [Self.VarOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J])]));
          Self.Emit(#9'callq _StringRelease');
        end
      { Interface locals: release the obj half of the fat pointer; the itab is
        static rodata and is not refcounted. }
      else if TVarDecl(ADecl.Body.Decls.Items[I]).ResolvedType.Kind = tyInterface then
        for J := 0 to TVarDecl(ADecl.Body.Decls.Items[I]).Names.Count - 1 do
        begin
          Self.Emit(Format(#9'movq %s, %%rdi',
            [Self.IntfObjOperand(TVarDecl(ADecl.Body.Decls.Items[I]).Names.Strings[J], False)]));
          Self.Emit(#9'callq _ClassRelease');
        end;
    end;
  end;
  Self.Emit(#9'movq %rbp, %rsp');
  Self.Emit(#9'popq %rbp');
  Self.Emit(#9'ret');
  Self.Emit('.type ' + Sym + ', @function');

  FExitLabel := '';
  Self.ClearFrame;
end;

{ Emit the program entry function.

  The Blaise runtime expects an exported `main(argc, argv)` returning int.  It
  must call $_SetArgs(argc, argv) before any program code, then run the body,
  then return 0.  This mirrors the QBE backend's $main shape (see the QBE IR
  for an empty program).

  The body statements are lowered between the _SetArgs call and the return-0
  epilogue.  After `pushq %rbp` the stack is 16-byte aligned, and expression
  evaluation balances its push/pop pairs, so %rsp stays aligned at every call
  site. }
procedure TX86_64Backend.EmitProgram(AProg: TProgram);
var
  I, J:  Integer;
  VD:    TVarDecl;
  Decl:  TMethodDecl;
begin
  { Register declared program-level variables as global slots. }
  for I := 0 to AProg.Block.Decls.Count - 1 do
  begin
    VD := TVarDecl(AProg.Block.Decls.Items[I]);
    if IsIntFamily(VD.ResolvedType) or IsFloatFamily(VD.ResolvedType) or
       ((VD.ResolvedType <> nil) and
        (VD.ResolvedType.Kind in [tyRecord, tyStaticArray, tyClass,
                                  tyProcedural, tyPointer, tyString, tyPChar,
                                  tyDynArray])) then
      for J := 0 to VD.Names.Count - 1 do
        Self.AddGlobal(VD.Names.Strings[J], VD.ResolvedType);
  end;

  { Class method bodies before standalone procedures. }
  Self.EmitClassMethods(AProg);

  { Standalone procedures/functions, then $main. }
  for I := 0 to AProg.Block.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(AProg.Block.ProcDecls.Items[I]);
    if Decl.OwnerTypeName <> '' then Continue;     { class methods: above }
    if Decl.TypeParams <> nil then Continue;       { generic templates: skip }
    if Decl.Body = nil then Continue;              { forward decls }
    if Decl.IsExternal then Continue;              { external: later }
    Self.EmitFunctionDef(Decl);
  end;

  { Concrete generic function instances. }
  for I := 0 to AProg.GenericFuncInstances.Count - 1 do
    Self.EmitFunctionDef(
      TGenericFuncInstance(AProg.GenericFuncInstances.Items[I]).MethodDecl);

  { Pre-count try stmts in the program body so VarOperand resolves
    _exc_frame_N as globals (FFrame is nil in main, so the global path is
    taken).  The actual .bss labels are emitted in EmitDataSection. }
  FProgExcFrameCount := 0;
  for I := 0 to AProg.Block.Stmts.Count - 1 do
    FProgExcFrameCount := FProgExcFrameCount +
      Self.CountTryStmts(TASTStmt(AProg.Block.Stmts.Items[I]));
  { Reset exc-frame state before emitting the program body. }
  FExcDepth     := 0;
  FExcFrameNext := 0;
  FFinallyStack.Clear;

  Self.Emit('.text');
  Self.Emit('.globl main');
  Self.Emit('main:');
  { Prologue: establish a frame.  argc is in %edi, argv in %rsi per SysV. }
  Self.Emit(#9'pushq %rbp');
  Self.Emit(#9'movq %rsp, %rbp');
  { _SetArgs(argc, argv): args already in %edi/%rsi — pass through. }
  Self.Emit(#9'callq _SetArgs');
  { Program body. }
  FExitLabel := Self.NewLabel('main_exit');
  for I := 0 to AProg.Block.Stmts.Count - 1 do
    Self.EmitStmt(TASTStmt(AProg.Block.Stmts.Items[I]));
  { Epilogue: Exit lands here; return 0. }
  Self.Emit(FExitLabel + ':');
  FExitLabel := '';
  Self.Emit(#9'movl $0, %eax');
  Self.Emit(#9'leave');
  Self.Emit(#9'ret');
  Self.Emit('.type main, @function');
  { Mark the stack non-executable (matches QBE output). }
  Self.Emit('.section .note.GNU-stack,"",@progbits');

  { Data section: all registered global integer/float/record slots. }
  Self.EmitDataSection;
  { Class data section: typeinfo, vtables, field-cleanup functions. }
  Self.EmitClassSection(AProg);
  { Interface data: typeinfo tokens, itabs, impllists.  Emitted after the class
    section so the class-name strings and method symbols it references exist. }
  Self.Emit('.data');
  Self.EmitInterfaceDefs(AProg);
end;

end.
