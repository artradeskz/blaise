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
  SysUtils, contnrs, Generics.Collections, uAST, uSymbolTable,
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
      loop's end-label (break) or condition-label (continue). }
    FBreakLabels:    TStack<string>;
    FContinueLabels: TStack<string>;
    { Exit label: when non-empty, Exit jumps here (function epilogue).  Empty
      in program $main where Exit maps to a bare return. }
    FExitLabel: string;

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

    { True when AName is a slot in the current function frame. }
    function IsLocal(const AName: string): Boolean;
    { The AT&T operand addressing AName: "-N(%rbp)" for a frame local,
      "name(%rip)" for a global. }
    function VarOperand(const AName: string): string;
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
    { Emit a direct call to a user procedure/function; result (if any) in %eax.
      ADecl is the callee's declaration (needed for var/out param handling);
      nil for type-cast calls. }
    procedure EmitCall(const AFuncSym: string; ADecl: TMethodDecl;
                       AArgs: TObjectList);
    { Evaluate an integer expression; result left in %rax (64-bit-extended). }
    procedure EmitExprToEax(AExpr: TASTExpr);
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
    tyByte, tyBoolean:           Result := 1;
    tySmallInt, tyWord:          Result := 2;
    tyInteger, tyUInt32, tyEnum: Result := 4;
    tyInt64, tyUInt64:           Result := 8;
  else
    Result := 4;
  end;
end;

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
    Result := ADecl.ResolvedQbeName
  else if ADecl <> nil then
    Result := ADecl.Name
  else
    Result := '';
end;

function FuncSymbolOf(ACall: TFuncCallExpr): string;
begin
  Result := FuncSymbolFromDecl(TMethodDecl(ACall.ResolvedDecl));
  if Result = '' then
    Result := ACall.Name;
end;

constructor TX86_64Backend.Create(const ATarget: TTargetDesc);
begin
  inherited Create(ATarget);
  FLabelCount     := 0;
  FDataGlobals    := TOrderedDictionary<string, TTypeDesc>.Create;
  FBreakLabels    := TStack<string>.Create;
  FContinueLabels := TStack<string>.Create;
  FFrame          := nil;
  FFrameTypes     := nil;
  FFrameSize      := 0;
  FExitLabel      := '';
end;

destructor TX86_64Backend.Destroy;
begin
  Self.ClearFrame;
  FContinueLabels.Free;
  FBreakLabels.Free;
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
  if FDataGlobals.Count = 0 then
    Exit;
  Self.Emit('.data');
  for I := 0 to FDataGlobals.Count - 1 do
  begin
    Name := FDataGlobals.Keys[I];
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
    Result := Format('-%d(%%rbp)', [Off])
  else
    Result := AName + '(%rip)';
end;

function TX86_64Backend.LocalType(const AName: string): TTypeDesc;
begin
  if (FFrameTypes = nil) or (not FFrameTypes.TryGetValue(AName, Result)) then
    Result := nil;
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

{ Reserve an 8-byte-aligned slot for AName of type AType, advancing AOffset.
  Every slot is rounded to 8 so an Int64 (or any wider local added later) is
  naturally aligned and a narrow slot never straddles an 8-byte boundary.
  Naive but correct; a packed layout is a later optimisation. }
procedure TX86_64Backend.AddSlot(const AName: string; AType: TTypeDesc;
                                 var AOffset: Integer);
begin
  Inc(AOffset, 8);
  FFrame.Add(AName, AOffset);
  FFrameTypes.Add(AName, AType);
end;

procedure TX86_64Backend.BuildFrame(ADecl: TMethodDecl);
var
  I, J, Offset: Integer;
  P:    TMethodParam;
  VD:   TVarDecl;
begin
  Self.ClearFrame;
  FFrame      := TDictionary<string, Integer>.Create;
  FFrameTypes := TDictionary<string, TTypeDesc>.Create;
  Offset := 0;
  { Params first (spilled from arg registers in the prologue). }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    Self.AddSlot(P.ParamName, P.ResolvedType, Offset);
  end;
  { Result slot for a function (not a procedure). }
  if ADecl.ResolvedReturnType <> nil then
    Self.AddSlot('Result', ADecl.ResolvedReturnType, Offset);
  { Local var declarations. }
  if ADecl.Body <> nil then
    for I := 0 to ADecl.Body.Decls.Count - 1 do
    begin
      VD := TVarDecl(ADecl.Body.Decls.Items[I]);
      for J := 0 to VD.Names.Count - 1 do
        Self.AddSlot(VD.Names.Strings[J], VD.ResolvedType, Offset);
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
  FFrameSize := 0;
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
  Unsigned: Boolean;
begin
  if AExpr is TIntLiteral then
  begin
    { movabsq carries the full 64-bit immediate (32-bit movq sign-extends a
      value above 2^31, which is wrong for large Int64 constants). }
    Self.Emit(Format(#9'movabsq $%s, %%rax', [IntToStr(TIntLiteral(AExpr).Value)]));
    Exit;
  end;

  if AExpr is TIdentExpr then
  begin
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
    if FC.IsIndirectCall then
      raise ENativeCodeGenError.Create(
        'native backend: indirect (procedural-type) calls not yet supported');
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

  raise ENativeCodeGenError.Create(
    'native backend: unsupported expression form ' + AExpr.ClassName);
end;

procedure TX86_64Backend.EmitCondBranch(AExpr: TASTExpr;
                                        const ATrueLabel, AFalseLabel: string);
begin
  { Evaluate the condition to a 0/1 (or any nonzero=true) value in %eax, then
    branch.  testl sets ZF when %eax is zero. }
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
      everything else (Integer,
        Byte, Boolean, Enum, ...)  -> _SysWriteInt    (32-bit signed; their
                                      value range is non-negative there)
    The value is already in %rax 64-bit-extended (unsigned narrow loads
    zero-extend), so the unsigned-32 path needs no extra extension.
    M5 handles integer-family arguments only. }
  for I := 0 to ACall.Args.Count - 1 do
  begin
    ArgExpr := TASTExpr(ACall.Args.Items[I]);
    Self.EmitExprToEax(ArgExpr);     { value -> %rax (64-bit-extended) }
    if ArgExpr.ResolvedType <> nil then
      K := ArgExpr.ResolvedType.Kind
    else
      K := tyInteger;
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
  FContinueLabels.Push(LNext);
  Self.EmitStmt(AFor.Body);
  FBreakLabels.Pop;
  FContinueLabels.Pop;

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

procedure TX86_64Backend.EmitStmt(AStmt: TASTStmt);
var
  PC:    TProcCall;
  Comp:  TCompoundStmt;
  IfS:   TIfStmt;
  WhileS: TWhileStmt;
  RepS:  TRepeatStmt;
  Asgn:  TAssignment;
  I:     Integer;
  LThen, LElse, LEnd:    string;
  LCond, LBody:          string;
begin
  if AStmt is TAssignment then
  begin
    Asgn := TAssignment(AStmt);
    Self.EmitExprToEax(Asgn.Expr);     { value -> %rax (64-bit-extended) }
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
    if PC.IsIndirectCall then
      raise ENativeCodeGenError.Create(
        'native backend: indirect (procedural-type) calls not yet supported');
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
    FContinueLabels.Push(LCond);
    Self.EmitStmt(WhileS.Body);
    FBreakLabels.Pop;
    FContinueLabels.Pop;
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
    FContinueLabels.Push(LCond);
    for I := 0 to RepS.Body.Stmts.Count - 1 do
      Self.EmitStmt(TASTStmt(RepS.Body.Stmts.Items[I]));
    FBreakLabels.Pop;
    FContinueLabels.Pop;
    Self.Emit(LCond + ':');
    Self.EmitCondBranch(RepS.Condition, LEnd, LBody);
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt is TBreakStmt then
  begin
    if FBreakLabels.Count = 0 then
      raise ENativeCodeGenError.Create('break outside loop');
    Self.Emit(#9'jmp ' + FBreakLabels.Peek);
    Exit;
  end;

  if AStmt is TContinueStmt then
  begin
    if FContinueLabels.Count = 0 then
      raise ENativeCodeGenError.Create('continue outside loop');
    Self.Emit(#9'jmp ' + FContinueLabels.Peek);
    Exit;
  end;

  if AStmt is TExitStmt then
  begin
    if TExitStmt(AStmt).ResultAssign <> nil then
      Self.EmitStmt(TExitStmt(AStmt).ResultAssign);
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

  raise ENativeCodeGenError.Create(
    'native backend: unsupported statement ' + AStmt.ClassName);
end;

{ ------------------------------------------------------------------ }
{ Calls and function definitions                                       }
{ ------------------------------------------------------------------ }

{ Emit a direct call.  Integer value arguments are passed in the SysV integer
  registers (edi, esi, edx, ecx, r8d, r9d).  Each argument is fully evaluated
  to %eax and pushed; once all are on the stack they are popped into the arg
  registers, so a complex argument expression cannot clobber an already-set
  arg register.  The pushes balance the pops, keeping %rsp 16-aligned at the
  call.  Result (if any) is left in %eax. }
procedure TX86_64Backend.EmitCall(const AFuncSym: string; ADecl: TMethodDecl;
                                  AArgs: TObjectList);
var
  I:     Integer;
  Arg:   TASTExpr;
  IsVar: Boolean;
begin
  if AArgs.Count > 6 then
    raise ENativeCodeGenError.Create(
      'native backend: more than 6 arguments not yet supported');
  { Evaluate left-to-right, pushing each result.  For var/out params push the
    address of the actual argument instead of its value. }
  for I := 0 to AArgs.Count - 1 do
  begin
    Arg := TASTExpr(AArgs.Items[I]);
    IsVar := (ADecl <> nil) and (I < ADecl.Params.Count) and
             TMethodParam(ADecl.Params.Items[I]).IsVarParam;
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
  { Pop into argument registers in reverse so register i gets argument i. }
  for I := AArgs.Count - 1 downto 0 do
    Self.Emit(#9'popq ' + SysVArgRegs64[I]);
  Self.Emit(#9'callq ' + AFuncSym);
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

{ True when AType is an integer-family type the backend can place in a
  general-purpose register (Byte..Int64).  Floats, records, strings, etc. are
  not yet handled and must fail loudly. }
function IsIntFamily(AType: TTypeDesc): Boolean;
begin
  Result := (AType <> nil) and
    (AType.Kind in [tyInteger, tyUInt32, tyInt64, tyUInt64,
                    tySmallInt, tyWord, tyByte, tyBoolean, tyEnum]);
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
  I:   Integer;
  P:   TMethodParam;
  Sym: string;
begin
  { Reject what the backend does not handle yet, loudly. }
  if ADecl.Params.Count > 6 then
    raise ENativeCodeGenError.Create(
      'native backend: more than 6 parameters not yet supported');
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    if not IsIntFamily(P.ResolvedType) then
      raise ENativeCodeGenError.Create(
        'native backend: only integer-family parameters supported (param ' +
        P.ParamName + ')');
  end;
  if (ADecl.ResolvedReturnType <> nil) and
     not IsIntFamily(ADecl.ResolvedReturnType) then
    raise ENativeCodeGenError.Create(
      'native backend: only integer-family or void return supported (function ' +
      ADecl.Name + ')');

  Sym := FuncSymbolFromDecl(ADecl);
  Self.BuildFrame(ADecl);

  Self.Emit('.text');
  Self.Emit('.globl ' + Sym);
  Self.Emit(Sym + ':');
  Self.Emit(#9'pushq %rbp');
  Self.Emit(#9'movq %rsp, %rbp');
  if FFrameSize > 0 then
    Self.Emit(Format(#9'subq $%d, %%rsp', [FFrameSize]));
  { Spill incoming argument registers into the param slots.  Var/out params
    arrive as pointers (always 64-bit); value params spill at their width. }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    if P.IsVarParam then
      Self.Emit(Format(#9'movq %s, %s',
        [SysVArgRegs64[I], Self.VarOperand(P.ParamName)]))
    else
      Self.EmitSpillArg(I, Self.VarOperand(P.ParamName), P.ResolvedType);
  end;
  { Initialise Result to 0 (defined default), like the QBE backend.  Zero in
    %rax then store at the slot's width. }
  if ADecl.ResolvedReturnType <> nil then
  begin
    Self.Emit(#9'xorl %eax, %eax');
    Self.EmitStoreVar(Self.VarOperand('Result'), ADecl.ResolvedReturnType);
  end;
  { Body.  FExitLabel directs Exit statements to the epilogue. }
  FExitLabel := Self.NewLabel('exit');
  if ADecl.Body <> nil then
    for I := 0 to ADecl.Body.Stmts.Count - 1 do
      Self.EmitStmt(TASTStmt(ADecl.Body.Stmts.Items[I]));
  { Epilogue: Exit lands here; load Result into %rax, restore frame, return. }
  Self.Emit(FExitLabel + ':');
  if ADecl.ResolvedReturnType <> nil then
    Self.EmitLoadVar(Self.VarOperand('Result'), ADecl.ResolvedReturnType);
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
  { Register declared program-level integer-family variables as global slots,
    so even unused declarations get a definition (matching the QBE backend). }
  for I := 0 to AProg.Block.Decls.Count - 1 do
  begin
    VD := TVarDecl(AProg.Block.Decls.Items[I]);
    if IsIntFamily(VD.ResolvedType) then
      for J := 0 to VD.Names.Count - 1 do
        Self.AddGlobal(VD.Names.Strings[J], VD.ResolvedType);
  end;

  { Standalone procedures/functions first, then $main. }
  for I := 0 to AProg.Block.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(AProg.Block.ProcDecls.Items[I]);
    if Decl.OwnerTypeName <> '' then Continue;     { class methods: later }
    if Decl.TypeParams <> nil then Continue;       { generic templates: later }
    if Decl.Body = nil then Continue;              { forward decls }
    if Decl.IsExternal then Continue;              { external: later }
    Self.EmitFunctionDef(Decl);
  end;

  Self.Emit('.text');
  Self.Emit('.globl main');
  Self.Emit('main:');
  { Prologue: establish a frame.  argc is in %edi, argv in %rsi per SysV. }
  Self.Emit(#9'pushq %rbp');
  Self.Emit(#9'movq %rsp, %rbp');
  { _SetArgs(argc, argv): args already in %edi/%rsi — pass through. }
  Self.Emit(#9'callq _SetArgs');
  { Program body. }
  for I := 0 to AProg.Block.Stmts.Count - 1 do
    Self.EmitStmt(TASTStmt(AProg.Block.Stmts.Items[I]));
  { Epilogue: return 0. }
  Self.Emit(#9'movl $0, %eax');
  Self.Emit(#9'leave');
  Self.Emit(#9'ret');
  Self.Emit('.type main, @function');
  { Mark the stack non-executable (matches QBE output). }
  Self.Emit('.section .note.GNU-stack,"",@progbits');

  { Data section: all registered global integer slots. }
  Self.EmitDataSection;
end;

end.
