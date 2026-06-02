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
    { Names of 4-byte global integer slots to define in the .data section:
      program-level variables plus hidden for-loop end-value slots.  Collected
      during code emission and written once at the end.  Append-and-iterate-
      once access; a TStringList (small N = number of globals) suffices and
      gives free dedup via IndexOf. }
    FDataGlobals: TStringList;

    { Current function's stack frame: maps a local name (param, var, or Result)
      to its negative %rbp-relative byte offset.  nil while emitting program
      $main (whose top-level vars are globals, not frame slots).  Built once per
      function then looked up by name on every ident read and assignment — a
      key->value map, so TDictionary is the right container for the access
      pattern. }
    FFrame:     TDictionary<string, Integer>;
    FFrameSize: Integer;        { bytes to reserve for locals (16-aligned) }

    { Allocate a fresh local assembly label (".L<prefix><N>"). }
    function NewLabel(const APrefix: string): string;
    { Register a 4-byte global integer slot (idempotent). }
    procedure AddGlobal(const AName: string);
    { Emit the accumulated .data section (one slot per registered global). }
    procedure EmitDataSection;

    { True when AName is a slot in the current function frame. }
    function IsLocal(const AName: string): Boolean;
    { The AT&T operand addressing AName: "-N(%rbp)" for a frame local,
      "name(%rip)" for a global. }
    function VarOperand(const AName: string): string;
    { Build FFrame for a function: assign offsets to params, Result, locals. }
    procedure BuildFrame(ADecl: TMethodDecl);
    { Tear down the current frame. }
    procedure ClearFrame;

    procedure EmitProgram(AProg: TProgram); override;
    { Emit a standalone procedure/function definition. }
    procedure EmitFunctionDef(ADecl: TMethodDecl);
    { Lower one statement. }
    procedure EmitStmt(AStmt: TASTStmt);
    { Lower a Write/WriteLn call (ANewline = WriteLn). }
    procedure EmitWrite(ACall: TProcCall; ANewline: Boolean);
    { Lower a for loop. }
    procedure EmitForStmt(AFor: TForStmt);
    { Emit a direct call to a user procedure/function; result (if any) in %eax. }
    procedure EmitCall(const AFuncSym: string; AArgs: TObjectList);
    { Evaluate an integer expression; result left in %eax. }
    procedure EmitExprToEax(AExpr: TASTExpr);
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
  FLabelCount  := 0;
  FDataGlobals := TStringList.Create;
  FFrame       := nil;
  FFrameSize   := 0;
end;

destructor TX86_64Backend.Destroy;
begin
  Self.ClearFrame;
  FDataGlobals.Free;
  inherited Destroy;
end;

function TX86_64Backend.NewLabel(const APrefix: string): string;
begin
  Result := '.L' + APrefix + IntToStr(FLabelCount);
  Inc(FLabelCount);
end;

procedure TX86_64Backend.AddGlobal(const AName: string);
begin
  if FDataGlobals.IndexOf(AName) < 0 then
    FDataGlobals.Add(AName);
end;

procedure TX86_64Backend.EmitDataSection;
var
  I: Integer;
begin
  if FDataGlobals.Count = 0 then
    Exit;
  Self.Emit('.data');
  for I := 0 to FDataGlobals.Count - 1 do
  begin
    Self.Emit('.balign 4');
    { Hidden compiler-generated slots (.L-prefixed) stay file-local; named
      program variables are exported like the QBE backend's globals. }
    if Copy(FDataGlobals.Strings[I], 1, 2) <> '.L' then
      Self.Emit('.globl ' + FDataGlobals.Strings[I]);
    Self.Emit(FDataGlobals.Strings[I] + ':');
    Self.Emit(#9'.long 0');
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

procedure TX86_64Backend.BuildFrame(ADecl: TMethodDecl);
var
  I, J, Offset: Integer;
  P:    TMethodParam;
  VD:   TVarDecl;
begin
  Self.ClearFrame;
  FFrame := TDictionary<string, Integer>.Create;
  Offset := 0;
  { Params first (spilled from arg registers in the prologue).  Each name gets
    a 4-byte slot; the running Offset is the negative %rbp displacement. }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    Inc(Offset, 4);
    FFrame.Add(P.ParamName, Offset);
  end;
  { Result slot for a function (not a procedure). }
  if ADecl.ResolvedReturnType <> nil then
  begin
    Inc(Offset, 4);
    FFrame.Add('Result', Offset);
  end;
  { Local var declarations. }
  if ADecl.Body <> nil then
    for I := 0 to ADecl.Body.Decls.Count - 1 do
    begin
      VD := TVarDecl(ADecl.Body.Decls.Items[I]);
      for J := 0 to VD.Names.Count - 1 do
      begin
        Inc(Offset, 4);
        FFrame.Add(VD.Names.Strings[J], Offset);
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
  FFrameSize := 0;
end;

{ ------------------------------------------------------------------ }
{ Expression lowering                                                  }
{ ------------------------------------------------------------------ }

procedure TX86_64Backend.EmitExprToEax(AExpr: TASTExpr);
var
  BE: TBinaryExpr;
begin
  if AExpr is TIntLiteral then
  begin
    Self.Emit(Format(#9'movl $%d, %%eax', [TIntLiteral(AExpr).Value]));
    Exit;
  end;

  if AExpr is TIdentExpr then
  begin
    { Named integer constant -> immediate; otherwise an integer variable loaded
      from its frame slot (function local) or RIP-relative (program global). }
    if TIdentExpr(AExpr).IsConstant then
      Self.Emit(Format(#9'movl $%d, %%eax', [TIdentExpr(AExpr).ConstValue]))
    else
      Self.Emit(Format(#9'movl %s, %%eax',
        [Self.VarOperand(TIdentExpr(AExpr).Name)]));
    Exit;
  end;

  if AExpr is TFuncCallExpr then
  begin
    if TFuncCallExpr(AExpr).IsIndirectCall then
      raise ENativeCodeGenError.Create(
        'native backend: indirect (procedural-type) calls not yet supported');
    Self.EmitCall(FuncSymbolOf(TFuncCallExpr(AExpr)), TFuncCallExpr(AExpr).Args);
    Exit;
  end;

  if AExpr is TBinaryExpr then
  begin
    BE := TBinaryExpr(AExpr);
    { left -> %eax, save; right -> %eax; left -> %ecx; combine. }
    Self.EmitExprToEax(BE.Left);
    Self.Emit(#9'pushq %rax');
    Self.EmitExprToEax(BE.Right);
    Self.Emit(#9'movl %eax, %ecx');   { right in %ecx }
    Self.Emit(#9'popq %rax');          { left in %eax }
    case BE.Op of
      boAdd: Self.Emit(#9'addl %ecx, %eax');
      boSub: Self.Emit(#9'subl %ecx, %eax');
      boMul: Self.Emit(#9'imull %ecx, %eax');
      boDiv:
        begin
          { signed 32-bit divide: sign-extend %eax into %edx:%eax, idiv %ecx,
            quotient in %eax. }
          Self.Emit(#9'cltd');
          Self.Emit(#9'idivl %ecx');
        end;
      boMod:
        begin
          Self.Emit(#9'cltd');
          Self.Emit(#9'idivl %ecx');
          Self.Emit(#9'movl %edx, %eax');  { remainder in %edx }
        end;
      { Signed integer comparisons -> boolean 0/1 in %eax.  AT&T `cmpl B, A`
        computes A - B, so with left in %eax and right in %ecx, `cmpl %ecx,
        %eax` sets flags for (left ? right); setcc then yields the 0/1. }
      boEQ, boNE, boLT, boGT, boLE, boGE:
        begin
          Self.Emit(#9'cmpl %ecx, %eax');
          case BE.Op of
            boEQ: Self.Emit(#9'sete %al');
            boNE: Self.Emit(#9'setne %al');
            boLT: Self.Emit(#9'setl %al');
            boGT: Self.Emit(#9'setg %al');
            boLE: Self.Emit(#9'setle %al');
            boGE: Self.Emit(#9'setge %al');
          end;
          Self.Emit(#9'movzbl %al, %eax');  { zero-extend the byte result }
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
  Self.Emit(#9'testl %eax, %eax');
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
begin
  { One _SysWriteInt(fd=1, value) per integer argument; then a trailing
    newline for WriteLn.  M2 handles integer arguments only. }
  for I := 0 to ACall.Args.Count - 1 do
  begin
    ArgExpr := TASTExpr(ACall.Args.Items[I]);
    Self.EmitExprToEax(ArgExpr);     { value -> %eax }
    Self.Emit(#9'movl %eax, %esi');  { arg2 = value }
    Self.Emit(#9'movl $1, %edi');    { arg1 = fd (stdout) }
    Self.Emit(#9'callq _SysWriteInt');
  end;
  if ANewline then
  begin
    Self.Emit(#9'movl $1, %edi');    { fd = stdout }
    Self.Emit(#9'callq _SysWriteNewline');
  end;
end;

procedure TX86_64Backend.EmitForStmt(AFor: TForStmt);
var
  VarOp, EndSlot:        string;
  LCond, LBody, LEnd:    string;
begin
  { Pascal `for` evaluates the end expression once.  Stash it in a hidden
    global slot, initialise the loop variable, then loop:
      cond: if (i <= end) [downto: i >= end] goto body else end
      body: <body>; i := i +/- 1; goto cond
    The loop variable may be a function-local (frame slot) or a program global;
    VarOperand picks the right addressing.  Only register it as a .data global
    when it is not a frame local. }
  if not Self.IsLocal(AFor.VarName) then
    Self.AddGlobal(AFor.VarName);
  VarOp   := Self.VarOperand(AFor.VarName);
  EndSlot := Self.NewLabel('forend');  { hidden file-local slot for the end value }
  Self.AddGlobal(EndSlot);
  LCond := Self.NewLabel('fcond');
  LBody := Self.NewLabel('fbody');
  LEnd  := Self.NewLabel('fend');

  { i := start }
  Self.EmitExprToEax(AFor.StartExpr);
  Self.Emit(Format(#9'movl %%eax, %s', [VarOp]));
  { endslot := end (evaluated once) }
  Self.EmitExprToEax(AFor.EndExpr);
  Self.Emit(Format(#9'movl %%eax, %s(%%rip)', [EndSlot]));

  Self.Emit(LCond + ':');
  { compare i against end }
  Self.Emit(Format(#9'movl %s, %%eax', [VarOp]));
  Self.Emit(Format(#9'movl %s(%%rip), %%ecx', [EndSlot]));
  Self.Emit(#9'cmpl %ecx, %eax');     { computes i - end }
  if AFor.IsDownTo then
    Self.Emit(#9'jge ' + LBody)       { continue while i >= end }
  else
    Self.Emit(#9'jle ' + LBody);      { continue while i <= end }
  Self.Emit(#9'jmp ' + LEnd);

  Self.Emit(LBody + ':');
  Self.EmitStmt(AFor.Body);
  { i := i +/- 1 }
  Self.Emit(Format(#9'movl %s, %%eax', [VarOp]));
  if AFor.IsDownTo then
    Self.Emit(#9'subl $1, %eax')
  else
    Self.Emit(#9'addl $1, %eax');
  Self.Emit(Format(#9'movl %%eax, %s', [VarOp]));
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
    Self.EmitExprToEax(Asgn.Expr);     { value -> %eax }
    { A function-local frame slot (including Result), or a program global.
      Blaise returns values via Result, so no function-name-as-result case. }
    if Self.IsLocal(Asgn.Name) then
      Self.Emit(Format(#9'movl %%eax, %s', [Self.VarOperand(Asgn.Name)]))
    else
    begin
      Self.AddGlobal(Asgn.Name);
      Self.Emit(Format(#9'movl %%eax, %s(%%rip)', [Asgn.Name]));
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
    Self.EmitCall(FuncSymbolFromDecl(TMethodDecl(PC.ResolvedDecl)), PC.Args);
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
    Self.EmitStmt(WhileS.Body);
    Self.Emit(#9'jmp ' + LCond);
    Self.Emit(LEnd + ':');
    Exit;
  end;

  if AStmt is TRepeatStmt then
  begin
    RepS  := TRepeatStmt(AStmt);
    LBody := Self.NewLabel('rbody');
    LEnd  := Self.NewLabel('rend');
    Self.Emit(LBody + ':');
    for I := 0 to RepS.Body.Stmts.Count - 1 do
      Self.EmitStmt(TASTStmt(RepS.Body.Stmts.Items[I]));
    { repeat exits when the condition is TRUE: branch true->end, false->body. }
    Self.EmitCondBranch(RepS.Condition, LEnd, LBody);
    Self.Emit(LEnd + ':');
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
procedure TX86_64Backend.EmitCall(const AFuncSym: string; AArgs: TObjectList);
var
  I: Integer;
begin
  if AArgs.Count > 6 then
    raise ENativeCodeGenError.Create(
      'native backend: more than 6 arguments not yet supported');
  { Evaluate left-to-right, pushing each result. }
  for I := 0 to AArgs.Count - 1 do
  begin
    Self.EmitExprToEax(TASTExpr(AArgs.Items[I]));
    Self.Emit(#9'pushq %rax');
  end;
  { Pop into argument registers in reverse so register i gets argument i. }
  for I := AArgs.Count - 1 downto 0 do
  begin
    Self.Emit(#9'popq %rax');
    Self.Emit(Format(#9'movl %%eax, %s', [SysVArgRegs[I]]));
  end;
  Self.Emit(#9'callq ' + AFuncSym);
end;

{ Emit a standalone procedure/function definition.  Frame layout mirrors the
  reference (FPC -O- and the QBE backend): params and locals each get a 4-byte
  %rbp-relative slot; the prologue spills the incoming argument registers into
  the param slots; the body runs through the slots; a function returns its
  Result slot in %eax.  M5 supports integer value parameters and integer/void
  return only. }
procedure TX86_64Backend.EmitFunctionDef(ADecl: TMethodDecl);
var
  I:   Integer;
  P:   TMethodParam;
  Sym: string;
begin
  { Reject what M5 does not handle yet, loudly. }
  if ADecl.Params.Count > 6 then
    raise ENativeCodeGenError.Create(
      'native backend: more than 6 parameters not yet supported');
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    if P.IsVarParam then
      raise ENativeCodeGenError.Create(
        'native backend: var/out parameters not yet supported');
    if (P.ResolvedType = nil) or (P.ResolvedType.Kind <> tyInteger) then
      raise ENativeCodeGenError.Create(
        'native backend: only Integer parameters supported (param ' +
        P.ParamName + ')');
  end;
  if (ADecl.ResolvedReturnType <> nil) and
     (ADecl.ResolvedReturnType.Kind <> tyInteger) then
    raise ENativeCodeGenError.Create(
      'native backend: only Integer or void return supported (function ' +
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
  { Spill incoming argument registers into the param slots. }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    P := TMethodParam(ADecl.Params.Items[I]);
    Self.Emit(Format(#9'movl %s, %s', [SysVArgRegs[I], Self.VarOperand(P.ParamName)]));
  end;
  { Initialise Result to 0 (defined default), like the QBE backend. }
  if ADecl.ResolvedReturnType <> nil then
    Self.Emit(Format(#9'movl $0, %s', [Self.VarOperand('Result')]));
  { Body. }
  if ADecl.Body <> nil then
    for I := 0 to ADecl.Body.Stmts.Count - 1 do
      Self.EmitStmt(TASTStmt(ADecl.Body.Stmts.Items[I]));
  { Epilogue: load Result into %eax (functions), restore frame, return. }
  if ADecl.ResolvedReturnType <> nil then
    Self.Emit(Format(#9'movl %s, %%eax', [Self.VarOperand('Result')]));
  Self.Emit(#9'movq %rbp, %rsp');
  Self.Emit(#9'popq %rbp');
  Self.Emit(#9'ret');
  Self.Emit('.type ' + Sym + ', @function');

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
  { Register declared program-level integer variables as global slots, so even
    unused declarations get a definition (matching the QBE backend). }
  for I := 0 to AProg.Block.Decls.Count - 1 do
  begin
    VD := TVarDecl(AProg.Block.Decls.Items[I]);
    if (VD.ResolvedType <> nil) and (VD.ResolvedType.Kind = tyInteger) then
      for J := 0 to VD.Names.Count - 1 do
        Self.AddGlobal(VD.Names.Strings[J]);
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
