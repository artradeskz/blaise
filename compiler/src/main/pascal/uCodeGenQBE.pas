{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

unit uCodeGenQBE;

{$mode objfpc}{$H+}

{ QBE IR emitter for Blaise.
  String layout: Phase 1 uses raw NUL-terminated bytes (no ARC header).
  WriteLn/Write are built-ins resolved directly to libc printf calls.
  Records are stack-allocated; field access uses pointer arithmetic. }

interface

uses
  SysUtils, StrUtils, Classes, uAST, uSymbolTable;

type
  ECodeGenError = class(Exception);

  TCodeGenQBE = class
  private
    FOutput:       TStringList;
    FStrLits:      TStringList;  { index → raw value; label = $__s<index> }
    FTempCount:    Integer;
    FLabelCount:   Integer;
    FCurrentBlock: TBlock;       { block currently being emitted; set by EmitBlock }
    FBreakLabels:  TStringList;  { stack of active loop-end labels; top = innermost }
    FExitLabel:    string;       { label to jmp to for 'exit'; '' = main program }

    function  AllocTemp: string;
    function  AllocLabel(const APrefix: string): string;
    function  EmitStrLit(const AValue: string): string;
    procedure EmitLine(const ALine: string);
    procedure EmitDataSection;
    procedure EmitMainHeader;
    procedure EmitMainFooter;
    procedure EmitTypeInfoDefs(AProg: TProgram);
    procedure EmitVTableDefs(AProg: TProgram);
    procedure EmitMethodDefs(AProg: TProgram);
    procedure EmitInterfaceDefs(AProg: TProgram);
    procedure EmitFieldCleanupDefs(AProg: TProgram);
    procedure EmitFieldCleanupFn(const AMangledName: string;
                                 ARec: TRecordTypeDesc);
    procedure EmitMethodDef(const ATypeName: string; AMethod: TMethodDecl);
    procedure EmitStandaloneDefs(AProg: TProgram);
    procedure EmitStandaloneDef(ADecl: TMethodDecl);
    procedure EmitFuncDef(ADecl: TMethodDecl; AExported: Boolean);
    procedure EmitBlock(ABlock: TBlock);
    procedure EmitVarAllocs(ABlock: TBlock);
    procedure EmitParamAllocs(AMethod: TMethodDecl; AClassType: TRecordTypeDesc);
    procedure EmitArcCleanup(ABlock: TBlock);
    procedure EmitExcPathArcCleanup(ABlock: TBlock);
    procedure EmitStmt(AStmt: TASTStmt);
    procedure EmitIfStmt(AStmt: TIfStmt);
    procedure EmitWhileStmt(AStmt: TWhileStmt);
    procedure EmitForStmt(AStmt: TForStmt);
    procedure EmitTryFinallyStmt(AStmt: TTryFinallyStmt);
    procedure EmitTryExceptStmt(AStmt: TTryExceptStmt);
    procedure EmitRaiseStmt(AStmt: TRaiseStmt);
    procedure EmitCompoundStmt(AStmt: TCompoundStmt);
    procedure EmitAssignment(AAssign: TAssignment);
    procedure EmitFieldAssignment(AAssign: TFieldAssignment);
    procedure EmitMethodCall(ACall: TMethodCallStmt);
    procedure EmitProcCall(ACall: TProcCall);
    procedure EmitPointerWrite(AStmt: TPointerWriteStmt);
    procedure EmitWrite(ACall: TProcCall; ANewline: Boolean);
    function  EmitExpr(AExpr: TASTExpr): string;
    function  EmitIsExpr(AExpr: TIsExpr): string;
    function  EmitAsExpr(AExpr: TAsExpr): string;
    { Returns a QBE temp holding a pointer to the storage of a record or class
      instance referenced by AExpr.  Used by chained field access to traverse
      base nodes without loading record aggregates as scalars. }
    function  EmitInstancePtr(AExpr: TASTExpr): string;
    function  FieldPtr(const ARecordVar: string; AOffset: Integer): string;
    function  QbeTypeOf(AType: TTypeDesc): string;
    function  QbeEscapeString(const AStr: string): string;
    { Mangle a type name for use in QBE symbols: '<' → '_', '>' → '', ',' → '_' }
    function  QBEMangle(const AName: string): string;
  public
    constructor Create;
    destructor Destroy; override;
    procedure Generate(AProg: TProgram);
    procedure GenerateUnit(AUnit: TUnit);
    function  GetOutput: string;
  end;

implementation

constructor TCodeGenQBE.Create;
begin
  inherited Create;
  FOutput       := TStringList.Create;
  FStrLits      := TStringList.Create;
  FBreakLabels  := TStringList.Create;
  FTempCount    := 0;
end;

destructor TCodeGenQBE.Destroy;
begin
  FBreakLabels.Free;
  FOutput.Free;
  FStrLits.Free;
  inherited Destroy;
end;

function TCodeGenQBE.AllocTemp: string;
begin
  Result := Format('%%_t%d', [FTempCount]);
  Inc(FTempCount);
end;

function TCodeGenQBE.AllocLabel(const APrefix: string): string;
begin
  Result := Format('%s_%d', [APrefix, FLabelCount]);
  Inc(FLabelCount);
end;

function TCodeGenQBE.EmitStrLit(const AValue: string): string;
var
  Idx: Integer;
begin
  Idx := FStrLits.IndexOf(AValue);
  if Idx < 0 then
    Idx := FStrLits.Add(AValue);
  Result := Format('$__s%d', [Idx]);
end;

procedure TCodeGenQBE.EmitLine(const ALine: string);
begin
  FOutput.Add(ALine);
end;

procedure TCodeGenQBE.EmitDataSection;
var
  I:       Integer;
  StrLen:  Integer;
begin
  { Each literal has a 12-byte ARC header: refcnt=-1 (immortal), length, capacity.
    The string pointer IS the header pointer; char data begins at ptr+12. }
  if FStrLits.Count > 0 then
  begin
    EmitLine('# String literals');
    for I := 0 to FStrLits.Count - 1 do
    begin
      StrLen := Length(FStrLits[I]);
      EmitLine(Format('data $__s%d = { w -1, w %d, w %d, b "%s", b 0 }',
        [I, StrLen, StrLen, QbeEscapeString(FStrLits[I])]));
    end;
  end;
  { printf format strings. Always emitted: a program with no string literals
    can still call WriteLn(Integer) or a bare WriteLn, and those reference
    $__fmt_d_nl / $__fmt_nl unconditionally. Omitting these definitions
    produces a link-time "undefined reference" failure that the IR-only test
    harness cannot see. }
  EmitLine('data $__fmt_s_nl = { b "%s\n", b 0 }');
  EmitLine('data $__fmt_s    = { b "%s", b 0 }');
  EmitLine('data $__fmt_d_nl = { b "%d\n", b 0 }');
  EmitLine('data $__fmt_d    = { b "%d", b 0 }');
  EmitLine('data $__fmt_nl   = { b "\n", b 0 }');
  EmitLine('');
end;

procedure TCodeGenQBE.EmitMainHeader;
begin
  EmitLine('export function w $main() {');
  EmitLine('@start');
end;

procedure TCodeGenQBE.EmitMainFooter;
begin
  EmitLine('  ret 0');
  EmitLine('}');
end;

function TCodeGenQBE.QbeTypeOf(AType: TTypeDesc): string;
begin
  case AType.Kind of
    tyInteger, tyUInt32, tyBoolean, tyByte: Result := 'w';
    tyInt64, tyString:                      Result := 'l';
    tyRecord:                               Result := 'l';  { pointer to aggregate }
    tyClass:                                Result := 'l';  { heap pointer }
    tyPointer:                              Result := 'l';  { pointer (typed or untyped) }
  else
    Result := 'w';
  end;
end;

procedure TCodeGenQBE.EmitVarAllocs(ABlock: TBlock);
var
  I, J:     Integer;
  Decl:     TVarDecl;
  VarName:  string;
  RT:       TRecordTypeDesc;
  RecSize:  Integer;
  RecAlign: Integer;
begin
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(ABlock.Decls[I]);
    if Decl.ResolvedType = nil then
      raise ECodeGenError.CreateFmt(
        'Variable ''%s'' has no resolved type — semantic pass required',
        [Decl.Names[0]]);

    for J := 0 to Decl.Names.Count - 1 do
    begin
      VarName := Decl.Names[J];
      case Decl.ResolvedType.Kind of
        tyInteger, tyUInt32, tyBoolean, tyByte:
          begin
            EmitLine(Format('  %%_var_%s =l alloc4 1', [VarName]));
            EmitLine(Format('  storew 0, %%_var_%s', [VarName]));
          end;

        tyInt64:
          begin
            EmitLine(Format('  %%_var_%s =l alloc8 1', [VarName]));
            EmitLine(Format('  storel 0, %%_var_%s', [VarName]));
          end;

        tyString:
          begin
            EmitLine(Format('  %%_var_%s =l alloc8 1', [VarName]));
            EmitLine(Format('  storel 0, %%_var_%s', [VarName]));
          end;

        tyRecord:
          begin
            RT       := TRecordTypeDesc(Decl.ResolvedType);
            RecSize  := RT.TotalSize;
            RecAlign := RT.MaxAlign;
            if RecAlign >= 8 then
              EmitLine(Format('  %%_var_%s =l alloc8 %d', [VarName, RecSize]))
            else
              EmitLine(Format('  %%_var_%s =l alloc4 %d', [VarName, RecSize]));
            { Zero-initialise record storage: Pascal records default to 0 and
              QBE's SSA checker requires every loaded slot to have at least
              one prior store. }
            if RecSize > 0 then
              EmitLine(Format('  call $memset(l %%_var_%s, w 0, l %d)',
                [VarName, RecSize]));
          end;

        tyClass:
          begin
            { Class var holds a heap pointer — allocate one pointer slot, nil-init }
            EmitLine(Format('  %%_var_%s =l alloc8 1', [VarName]));
            EmitLine(Format('  storel 0, %%_var_%s', [VarName]));
          end;

        tyPointer:
          begin
            { Pointer var (typed or untyped) — allocate one pointer slot, nil-init }
            EmitLine(Format('  %%_var_%s =l alloc8 1', [VarName]));
            EmitLine(Format('  storel 0, %%_var_%s', [VarName]));
          end;

        tyInterface:
          begin
            { Interface var = fat pointer: obj slot + itab slot, both nil-init }
            EmitLine(Format('  %%_var_%s_obj  =l alloc8 1', [VarName]));
            EmitLine(Format('  storel 0, %%_var_%s_obj',    [VarName]));
            EmitLine(Format('  %%_var_%s_itab =l alloc8 1', [VarName]));
            EmitLine(Format('  storel 0, %%_var_%s_itab',   [VarName]));
          end;

      else
        raise ECodeGenError.CreateFmt(
          'Unsupported type kind %d for variable ''%s''',
          [Ord(Decl.ResolvedType.Kind), VarName]);
      end;
    end;
  end;
end;

procedure TCodeGenQBE.EmitArcCleanup(ABlock: TBlock);
{ Release every ARC-managed local variable (string, class, or interface) at
  block exit.  Mirrors the insertion pattern used at assignment sites: each
  slot holds one retained reference from its first assignment; scope exit
  must balance that with one release.  Interface vars carry a fat pointer
  (obj + itab); only the obj slot is refcounted. }
var
  I, J:    Integer;
  Decl:    TVarDecl;
  VarName: string;
  ValTemp: string;
  RelFn:   string;
begin
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(ABlock.Decls[I]);
    if Decl.ResolvedType = nil then Continue;
    if Decl.ResolvedType.IsString then
      RelFn := '$_StringRelease'
    else if Decl.ResolvedType.Kind = tyClass then
      RelFn := '$_ClassRelease'
    else if Decl.ResolvedType.Kind = tyInterface then
      RelFn := '$_ClassRelease'  { obj slot release; itab is static }
    else
      Continue;
    for J := 0 to Decl.Names.Count - 1 do
    begin
      VarName := Decl.Names[J];
      ValTemp := AllocTemp;
      if Decl.ResolvedType.Kind = tyInterface then
        EmitLine(Format('  %s =l loadl %%_var_%s_obj', [ValTemp, VarName]))
      else
        EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, VarName]));
      EmitLine(Format('  call %s(l %s)', [RelFn, ValTemp]));
    end;
  end;
end;

procedure TCodeGenQBE.EmitBlock(ABlock: TBlock);
var
  I: Integer;
begin
  FCurrentBlock := ABlock;
  EmitVarAllocs(ABlock);
  for I := 0 to ABlock.Stmts.Count - 1 do
    EmitStmt(TASTStmt(ABlock.Stmts[I]));
  { Fall-through to exit label so 'exit' and normal flow share cleanup. }
  if FExitLabel <> '' then
  begin
    EmitLine(Format('  jmp @%s', [FExitLabel]));
    EmitLine('@' + FExitLabel);
  end;
  EmitArcCleanup(ABlock);
end;

procedure TCodeGenQBE.EmitExcPathArcCleanup(ABlock: TBlock);
var
  I, J:    Integer;
  Decl:    TVarDecl;
  VarName: string;
  ValTemp: string;
  RelFn:   string;
  IsIntf:  Boolean;
begin
  if ABlock = nil then Exit;
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(ABlock.Decls[I]);
    if Decl.ResolvedType = nil then Continue;
    IsIntf := False;
    if Decl.ResolvedType.IsString then
      RelFn := '$_StringRelease'
    else if Decl.ResolvedType.Kind = tyClass then
      RelFn := '$_ClassRelease'
    else if Decl.ResolvedType.Kind = tyInterface then
    begin
      RelFn  := '$_ClassRelease';
      IsIntf := True;
    end
    else
      Continue;
    for J := 0 to Decl.Names.Count - 1 do
    begin
      VarName := Decl.Names[J];
      ValTemp := AllocTemp;
      if IsIntf then
      begin
        EmitLine(Format('  %s =l loadl %%_var_%s_obj', [ValTemp, VarName]));
        EmitLine(Format('  call %s(l %s)', [RelFn, ValTemp]));
        { Zero only the obj slot; the itab slot holds a static pointer
          and nilling it would break a subsequent method call on this
          variable if it survives the unwind. }
        EmitLine(Format('  storel 0, %%_var_%s_obj', [VarName]));
      end
      else
      begin
        EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, VarName]));
        EmitLine(Format('  call %s(l %s)', [RelFn, ValTemp]));
        EmitLine(Format('  storel 0, %%_var_%s', [VarName]));
      end;
    end;
  end;
end;

procedure TCodeGenQBE.EmitStmt(AStmt: TASTStmt);
var
  DeadLbl: string;
begin
  if AStmt is TTryFinallyStmt then
    EmitTryFinallyStmt(TTryFinallyStmt(AStmt))
  else if AStmt is TTryExceptStmt then
    EmitTryExceptStmt(TTryExceptStmt(AStmt))
  else if AStmt is TRaiseStmt then
    EmitRaiseStmt(TRaiseStmt(AStmt))
  else if AStmt is TForStmt then
    EmitForStmt(TForStmt(AStmt))
  else if AStmt is TWhileStmt then
    EmitWhileStmt(TWhileStmt(AStmt))
  else if AStmt is TIfStmt then
    EmitIfStmt(TIfStmt(AStmt))
  else if AStmt is TCompoundStmt then
    EmitCompoundStmt(TCompoundStmt(AStmt))
  else if AStmt is TFieldAssignment then
    EmitFieldAssignment(TFieldAssignment(AStmt))
  else if AStmt is TPointerWriteStmt then
    EmitPointerWrite(TPointerWriteStmt(AStmt))
  else if AStmt is TAssignment then
    EmitAssignment(TAssignment(AStmt))
  else if AStmt is TMethodCallStmt then
    EmitMethodCall(TMethodCallStmt(AStmt))
  else if AStmt is TProcCall then
    EmitProcCall(TProcCall(AStmt))
  else if AStmt is TExitStmt then
  begin
    if FExitLabel <> '' then
      EmitLine(Format('  jmp @%s', [FExitLabel]))
    else
      EmitLine('  ret 0');
    { QBE basic blocks must follow a terminator with a new labelled block. }
    DeadLbl := AllocLabel('after_exit');
    EmitLine('@' + DeadLbl);
  end
  else if AStmt is TBreakStmt then
  begin
    if FBreakLabels.Count = 0 then
      raise ECodeGenError.Create('break outside loop');
    EmitLine(Format('  jmp @%s',
      [FBreakLabels[FBreakLabels.Count - 1]]));
    DeadLbl := AllocLabel('after_break');
    EmitLine('@' + DeadLbl);
  end
  else
    raise ECodeGenError.Create('Unknown statement node type');
end;

procedure TCodeGenQBE.EmitIfStmt(AStmt: TIfStmt);
var
  CondTemp:  string;
  LblThen:   string;
  LblElse:   string;
  LblEnd:    string;
begin
  LblThen := AllocLabel('if_then');
  LblEnd  := AllocLabel('if_end');

  CondTemp := EmitExpr(AStmt.Condition);

  if AStmt.ElseStmt <> nil then
  begin
    LblElse := AllocLabel('if_else');
    EmitLine(Format('  jnz %s, @%s, @%s', [CondTemp, LblThen, LblElse]));
    EmitLine('@' + LblThen);
    EmitStmt(AStmt.ThenStmt);
    EmitLine(Format('  jmp @%s', [LblEnd]));
    EmitLine('@' + LblElse);
    EmitStmt(AStmt.ElseStmt);
    EmitLine(Format('  jmp @%s', [LblEnd]));
  end
  else
  begin
    EmitLine(Format('  jnz %s, @%s, @%s', [CondTemp, LblThen, LblEnd]));
    EmitLine('@' + LblThen);
    EmitStmt(AStmt.ThenStmt);
    EmitLine(Format('  jmp @%s', [LblEnd]));
  end;

  EmitLine('@' + LblEnd);
end;

procedure TCodeGenQBE.EmitTryFinallyStmt(AStmt: TTryFinallyStmt);
var
  LblTry:    string;
  LblFinExc: string;
  LblEnd:    string;
  FrameTemp: string;
  SjrTemp:   string;
  ExcTemp:   string;
  I:         Integer;
begin
  LblTry    := AllocLabel('try_body');
  LblFinExc := AllocLabel('fin_exc');
  LblEnd    := AllocLabel('fin_end');

  { Stack-allocate exception frame (512 bytes, 16-byte aligned).
    jbuf is at offset 0 so frame ptr can be passed directly to setjmp.
    512 bytes accommodates jmp_buf on Linux x86_64 (200 B) and macOS ARM64 (~312 B). }
  FrameTemp := AllocTemp;
  EmitLine(Format('  %s =l alloc16 512', [FrameTemp]));
  EmitLine(Format('  call $_PushExcFrame(l %s)', [FrameTemp]));

  SjrTemp := AllocTemp;
  EmitLine(Format('  %s =w call $setjmp(l %s)', [SjrTemp, FrameTemp]));
  EmitLine(Format('  jnz %s, @%s, @%s', [SjrTemp, LblFinExc, LblTry]));

  { Normal path: run try body, pop frame, run finally body }
  EmitLine('@' + LblTry);
  for I := 0 to AStmt.TryBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.TryBody.Stmts[I]));
  EmitLine('  call $_PopExcFrame()');
  for I := 0 to AStmt.FinallyBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.FinallyBody.Stmts[I]));
  EmitLine(Format('  jmp @%s', [LblEnd]));

  { Exception path: capture exception, pop frame, run finally body, release
    in-scope ARC vars (prevent leaks on unwind), then re-raise }
  EmitLine('@' + LblFinExc);
  ExcTemp := AllocTemp;
  EmitLine(Format('  %s =l call $_CurrentException()', [ExcTemp]));
  EmitLine('  call $_PopExcFrame()');
  for I := 0 to AStmt.FinallyBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.FinallyBody.Stmts[I]));
  EmitExcPathArcCleanup(FCurrentBlock);
  EmitLine(Format('  call $_Reraise(l %s)', [ExcTemp]));
  EmitLine(Format('  jmp @%s', [LblEnd]));  { unreachable — satisfies QBE block exit }

  EmitLine('@' + LblEnd);
end;

procedure TCodeGenQBE.EmitTryExceptStmt(AStmt: TTryExceptStmt);
var
  LblTry:    string;
  LblExcept: string;
  LblEnd:    string;
  FrameTemp: string;
  SjrTemp:   string;
  I:         Integer;
begin
  LblTry    := AllocLabel('try_body');
  LblExcept := AllocLabel('except_handler');
  LblEnd    := AllocLabel('except_end');

  { Stack-allocate exception frame (512 bytes, 16-byte aligned).
    Matches the size contract in blaise_exc.c — must hold jmp_buf (200 B on
    Linux x86_64, ~312 B on macOS ARM64) plus two pointer fields. }
  FrameTemp := AllocTemp;
  EmitLine(Format('  %s =l alloc16 512', [FrameTemp]));
  EmitLine(Format('  call $_PushExcFrame(l %s)', [FrameTemp]));

  SjrTemp := AllocTemp;
  EmitLine(Format('  %s =w call $setjmp(l %s)', [SjrTemp, FrameTemp]));
  EmitLine(Format('  jnz %s, @%s, @%s', [SjrTemp, LblExcept, LblTry]));

  { Normal path: run try body, pop frame on clean exit }
  EmitLine('@' + LblTry);
  for I := 0 to AStmt.TryBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.TryBody.Stmts[I]));
  EmitLine('  call $_PopExcFrame()');
  EmitLine(Format('  jmp @%s', [LblEnd]));

  { Exception path: frame still at top (exception set), pop then handle }
  EmitLine('@' + LblExcept);
  EmitLine('  call $_PopExcFrame()');
  for I := 0 to AStmt.ExceptBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.ExceptBody.Stmts[I]));
  EmitLine(Format('  jmp @%s', [LblEnd]));

  EmitLine('@' + LblEnd);
end;

procedure TCodeGenQBE.EmitRaiseStmt(AStmt: TRaiseStmt);
var
  ObjTemp: string;
begin
  if AStmt.Expr <> nil then
  begin
    ObjTemp := EmitExpr(AStmt.Expr);
    EmitLine(Format('  call $_Raise(l %s)', [ObjTemp]));
  end
  else
    { Bare re-raise: pass null; RTL retrieves current exception }
    EmitLine('  call $_Raise(l 0)');
end;

procedure TCodeGenQBE.EmitForStmt(AStmt: TForStmt);
var
  LblCond:  string;
  LblBody:  string;
  LblEnd:   string;
  StartT:   string;
  EndT:     string;
  CurT:     string;
  CmpT:     string;
  StepT:    string;
  CmpOp:    string;
  StepOp:   string;
begin
  LblCond := AllocLabel('for_cond');
  LblBody := AllocLabel('for_body');
  LblEnd  := AllocLabel('for_end');

  { Evaluate start and store into loop variable }
  StartT := EmitExpr(AStmt.StartExpr);
  EmitLine(Format('  storew %s, %%_var_%s', [StartT, AStmt.VarName]));

  { Evaluate end value once into a temp }
  EndT := EmitExpr(AStmt.EndExpr);

  { Jump to condition (terminates current block) }
  EmitLine(Format('  jmp @%s', [LblCond]));

  { Condition block: test loop variable against end value }
  EmitLine('@' + LblCond);
  CurT := AllocTemp;
  EmitLine(Format('  %s =w loadw %%_var_%s', [CurT, AStmt.VarName]));
  CmpT := AllocTemp;
  if AStmt.IsDownTo then
    CmpOp := 'csgew'   { I >= End }
  else
    CmpOp := 'cslew';  { I <= End }
  EmitLine(Format('  %s =w %s %s, %s', [CmpT, CmpOp, CurT, EndT]));
  EmitLine(Format('  jnz %s, @%s, @%s', [CmpT, LblBody, LblEnd]));

  { Body block }
  EmitLine('@' + LblBody);
  FBreakLabels.Add(LblEnd);
  try
    EmitStmt(AStmt.Body);
  finally
    FBreakLabels.Delete(FBreakLabels.Count - 1);
  end;

  { Increment or decrement loop variable }
  CurT  := AllocTemp;
  StepT := AllocTemp;
  EmitLine(Format('  %s =w loadw %%_var_%s', [CurT, AStmt.VarName]));
  if AStmt.IsDownTo then
    StepOp := 'sub'
  else
    StepOp := 'add';
  EmitLine(Format('  %s =w %s %s, 1', [StepT, StepOp, CurT]));
  EmitLine(Format('  storew %s, %%_var_%s', [StepT, AStmt.VarName]));
  EmitLine(Format('  jmp @%s', [LblCond]));

  { Continuation block }
  EmitLine('@' + LblEnd);
end;

procedure TCodeGenQBE.EmitWhileStmt(AStmt: TWhileStmt);
var
  LblCond: string;
  LblBody: string;
  LblEnd:  string;
  CondTemp: string;
begin
  LblCond := AllocLabel('while_cond');
  LblBody := AllocLabel('while_body');
  LblEnd  := AllocLabel('while_end');

  { Jump into the condition block (terminates current block) }
  EmitLine(Format('  jmp @%s', [LblCond]));

  { Condition evaluation block }
  EmitLine('@' + LblCond);
  CondTemp := EmitExpr(AStmt.Condition);
  EmitLine(Format('  jnz %s, @%s, @%s', [CondTemp, LblBody, LblEnd]));

  { Loop body block }
  EmitLine('@' + LblBody);
  FBreakLabels.Add(LblEnd);
  try
    EmitStmt(AStmt.Body);
  finally
    FBreakLabels.Delete(FBreakLabels.Count - 1);
  end;
  EmitLine(Format('  jmp @%s', [LblCond]));

  { Continuation block }
  EmitLine('@' + LblEnd);
end;

procedure TCodeGenQBE.EmitCompoundStmt(AStmt: TCompoundStmt);
var
  I: Integer;
begin
  for I := 0 to AStmt.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.Stmts[I]));
end;

procedure TCodeGenQBE.EmitAssignment(AAssign: TAssignment);
var
  ValTemp, OldTemp, QType, StoreInstr, PtrTemp: string;
  IntfDesc:  TInterfaceTypeDesc;
  ClassRT:   TRecordTypeDesc;
  ItabName:  string;
  AE:        TAsExpr;
  ObjTemp:   string;
  ItabTemp:  string;
  CheckTemp: string;
  LblOk:     string;
  LblFail:   string;
  LblEnd:    string;
begin
  if AAssign.Expr.ResolvedType = nil then
    raise ECodeGenError.CreateFmt(
      'Expression in assignment to ''%s'' has no resolved type', [AAssign.Name]);

  { Interface as-cast: F := T as IFoo — use _GetItab for runtime itab lookup.
    ARC: the obj slot holds a strong reference to the backing class instance,
    so retain the new obj and release the prior contents of F's obj slot
    before storing.  The itab slot is a pointer to static rodata and is not
    refcounted. }
  if (AAssign.ResolvedLhsType <> nil) and
     (AAssign.ResolvedLhsType.Kind = tyInterface) and
     (AAssign.Expr is TAsExpr) and
     (AAssign.Expr.ResolvedType.Kind = tyInterface) then
  begin
    AE        := TAsExpr(AAssign.Expr);
    IntfDesc  := TInterfaceTypeDesc(AAssign.ResolvedLhsType);
    ObjTemp   := EmitExpr(AE.Obj);
    ItabTemp  := AllocTemp;
    EmitLine(Format('  %s =l call $_GetItab(l %s, l $typeinfo_%s)',
      [ItabTemp, ObjTemp, AE.TypeName]));
    CheckTemp := AllocTemp;
    LblOk   := AllocLabel('as_ok');
    LblFail := AllocLabel('as_fail');
    LblEnd  := AllocLabel('as_end');
    EmitLine(Format('  %s =w cnel %s, 0', [CheckTemp, ItabTemp]));
    EmitLine(Format('  jnz %s, @%s, @%s', [CheckTemp, LblOk, LblFail]));
    EmitLine('@' + LblFail);
    EmitLine('  call $_Raise_InvalidCast()');
    EmitLine(Format('  jmp @%s', [LblEnd]));
    EmitLine('@' + LblOk);
    OldTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_%s_obj', [OldTemp, AAssign.Name]));
    EmitLine(Format('  call $_ClassAddRef(l %s)',  [ObjTemp]));
    EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
    EmitLine(Format('  storel %s, %%_var_%s_obj',  [ObjTemp, AAssign.Name]));
    EmitLine(Format('  storel %s, %%_var_%s_itab', [ItabTemp, AAssign.Name]));
    EmitLine('@' + LblEnd);
    Exit;
  end;

  { Interface direct assignment: F := T where T is a class implementing the
    interface.  Under ARC, the obj slot co-owns the backing class instance
    and must be retained on store / released when overwritten. }
  if (AAssign.ResolvedLhsType <> nil) and
     (AAssign.ResolvedLhsType.Kind = tyInterface) and
     (AAssign.Expr.ResolvedType.Kind = tyClass) then
  begin
    IntfDesc := TInterfaceTypeDesc(AAssign.ResolvedLhsType);
    ClassRT  := TRecordTypeDesc(AAssign.Expr.ResolvedType);
    ItabName := '$itab_' + ClassRT.Name + '_' + IntfDesc.Name;
    ValTemp  := EmitExpr(AAssign.Expr);
    OldTemp  := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_%s_obj', [OldTemp, AAssign.Name]));
    EmitLine(Format('  call $_ClassAddRef(l %s)',  [ValTemp]));
    EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
    EmitLine(Format('  storel %s, %%_var_%s_obj',  [ValTemp, AAssign.Name]));
    EmitLine(Format('  storel %s, %%_var_%s_itab', [ItabName, AAssign.Name]));
    Exit;
  end;

  { Interface-to-interface direct assignment: F := G where both sides are
    interface-typed.  Copy obj and itab from G's fat pointer to F's; retain
    the backing object and release F's prior obj reference. }
  if (AAssign.ResolvedLhsType <> nil) and
     (AAssign.ResolvedLhsType.Kind = tyInterface) and
     (AAssign.Expr.ResolvedType.Kind = tyInterface) and
     (AAssign.Expr is TIdentExpr) then
  begin
    ObjTemp  := AllocTemp;
    ItabTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_%s_obj',
      [ObjTemp, TIdentExpr(AAssign.Expr).Name]));
    EmitLine(Format('  %s =l loadl %%_var_%s_itab',
      [ItabTemp, TIdentExpr(AAssign.Expr).Name]));
    OldTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_%s_obj', [OldTemp, AAssign.Name]));
    EmitLine(Format('  call $_ClassAddRef(l %s)',  [ObjTemp]));
    EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
    EmitLine(Format('  storel %s, %%_var_%s_obj',  [ObjTemp, AAssign.Name]));
    EmitLine(Format('  storel %s, %%_var_%s_itab', [ItabTemp, AAssign.Name]));
    Exit;
  end;

  if AAssign.IsVarParam then
  begin
    { Var param: load the stored pointer, then store the value through it }
    QType   := QbeTypeOf(AAssign.Expr.ResolvedType);
    ValTemp := EmitExpr(AAssign.Expr);
    PtrTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_%s', [PtrTemp, AAssign.Name]));
    if QType = 'w' then StoreInstr := 'storew'
                   else StoreInstr := 'storel';
    EmitLine(Format('  %s %s, %s', [StoreInstr, ValTemp, PtrTemp]));
  end
  else if AAssign.Expr.ResolvedType.IsString then
  begin
    { ARC: load old, compute new, retain new, release old, store new }
    OldTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_%s', [OldTemp, AAssign.Name]));
    ValTemp := EmitExpr(AAssign.Expr);
    EmitLine(Format('  call $_StringAddRef(l %s)', [ValTemp]));
    EmitLine(Format('  call $_StringRelease(l %s)', [OldTemp]));
    EmitLine(Format('  storel %s, %%_var_%s', [ValTemp, AAssign.Name]));
  end
  else if AAssign.Expr.ResolvedType.Kind = tyClass then
  begin
    { ARC: load old class reference, evaluate new, retain new, release old,
      store new.  Matches the string ARC idiom one-for-one. }
    OldTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_%s', [OldTemp, AAssign.Name]));
    ValTemp := EmitExpr(AAssign.Expr);
    EmitLine(Format('  call $_ClassAddRef(l %s)', [ValTemp]));
    EmitLine(Format('  call $_ClassRelease(l %s)', [OldTemp]));
    EmitLine(Format('  storel %s, %%_var_%s', [ValTemp, AAssign.Name]));
  end
  else
  begin
    QType   := QbeTypeOf(AAssign.Expr.ResolvedType);
    ValTemp := EmitExpr(AAssign.Expr);
    if QType = 'w' then StoreInstr := 'storew'
                   else StoreInstr := 'storel';
    EmitLine(Format('  %s %s, %%_var_%s', [StoreInstr, ValTemp, AAssign.Name]));
  end;
end;

function TCodeGenQBE.EmitInstancePtr(AExpr: TASTExpr): string;
var
  Id:     TIdentExpr;
  Fld:    TFieldAccessExpr;
  Base:   string;
  Ptr:    string;
  Loaded: string;
begin
  if AExpr is TIdentExpr then
  begin
    Id := TIdentExpr(AExpr);
    if (AExpr.ResolvedType <> nil) and (AExpr.ResolvedType.Kind = tyClass) then
    begin
      Loaded := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [Loaded, Id.Name]));
      Result := Loaded;
    end
    else
      Result := Format('%%_var_%s', [Id.Name]);  { inline record }
    Exit;
  end;

  if AExpr is TFieldAccessExpr then
  begin
    Fld := TFieldAccessExpr(AExpr);
    if Fld.Base <> nil then
      Base := EmitInstancePtr(Fld.Base)
    else
    begin
      { Leaf: RecordName-based access, same rules as for TIdentExpr. }
      if (Fld.ResolvedType = nil) then
        raise ECodeGenError.Create('Chained base has no resolved type');
      if Fld.IsClassAccess then
      begin
        Loaded := AllocTemp;
        EmitLine(Format('  %s =l loadl %%_var_%s', [Loaded, Fld.RecordName]));
        Base := Loaded;
      end
      else
        Base := Format('%%_var_%s', [Fld.RecordName]);
    end;
    if Fld.FieldInfo = nil then
      raise ECodeGenError.Create(
        'Chained field access ''' + Fld.FieldName + ''' has no resolved field info');
    if Fld.FieldInfo.Offset > 0 then
    begin
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d',
        [Ptr, Base, Fld.FieldInfo.Offset]));
    end
    else
      Ptr := Base;
    { If this field is a class pointer, load it to get the heap object pointer.
      If it is an inline record, the pointer itself points to the storage. }
    if Fld.FieldInfo.TypeDesc.Kind = tyClass then
    begin
      Loaded := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [Loaded, Ptr]));
      Result := Loaded;
    end
    else
      Result := Ptr;
    Exit;
  end;

  raise ECodeGenError.Create('EmitInstancePtr: unsupported base expression');
end;

function TCodeGenQBE.FieldPtr(const ARecordVar: string; AOffset: Integer): string;
var
  PtrTemp: string;
begin
  if AOffset = 0 then
  begin
    Result := Format('%%_var_%s', [ARecordVar]);
  end
  else
  begin
    PtrTemp := AllocTemp;
    EmitLine(Format('  %s =l add %%_var_%s, %d', [PtrTemp, ARecordVar, AOffset]));
    Result := PtrTemp;
  end;
end;

procedure TCodeGenQBE.EmitFieldAssignment(AAssign: TFieldAssignment);
var
  Ptr, PtrTemp, ValTemp, OldTemp, QType, StoreInstr: string;
  IsArc: Boolean;
  IsStr: Boolean;
begin
  if AAssign.FieldInfo = nil then
    raise ECodeGenError.CreateFmt(
      'Field assignment ''%s.%s'' has no resolved field info',
      [AAssign.RecordName, AAssign.FieldName]);

  ValTemp := EmitExpr(AAssign.Expr);

  if AAssign.IsClassAccess then
  begin
    { Load the heap pointer stored in the class variable }
    PtrTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_%s', [PtrTemp, AAssign.RecordName]));
    if AAssign.FieldInfo.Offset > 0 then
    begin
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', [Ptr, PtrTemp, AAssign.FieldInfo.Offset]));
    end
    else
      Ptr := PtrTemp;
  end
  else
    Ptr := FieldPtr(AAssign.RecordName, AAssign.FieldInfo.Offset);

  IsStr := AAssign.FieldInfo.TypeDesc.IsString;
  IsArc := IsStr or (AAssign.FieldInfo.TypeDesc.Kind = tyClass);
  if IsArc then
  begin
    { ARC for ARC-managed field storage: retain the new value and release the
      old field contents before overwriting, so neither reference leaks. }
    OldTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', [OldTemp, Ptr]));
    if IsStr then
    begin
      EmitLine(Format('  call $_StringAddRef(l %s)',  [ValTemp]));
      EmitLine(Format('  call $_StringRelease(l %s)', [OldTemp]));
    end
    else
    begin
      EmitLine(Format('  call $_ClassAddRef(l %s)',   [ValTemp]));
      EmitLine(Format('  call $_ClassRelease(l %s)',  [OldTemp]));
    end;
    EmitLine(Format('  storel %s, %s', [ValTemp, Ptr]));
  end
  else
  begin
    QType := QbeTypeOf(AAssign.FieldInfo.TypeDesc);
    if QType = 'w' then StoreInstr := 'storew'
                   else StoreInstr := 'storel';
    EmitLine(Format('  %s %s, %s', [StoreInstr, ValTemp, Ptr]));
  end;
end;

procedure TCodeGenQBE.EmitMethodCall(ACall: TMethodCallStmt);
var
  RT:       TRecordTypeDesc;
  MDecl:    TMethodDecl;
  SelfTemp: string;
  Par:      TMethodParam;
  ArgTemp:  string;
  ArgLine:  string;
  I:        Integer;
  QType:    string;
  FuncName: string;
  VTblTemp: string;
  FPtrTemp: string;
  SlotOff:  Integer;
  IntfDesc: TInterfaceTypeDesc;
begin
  { Interface method dispatch: load obj + itab, index by method slot }
  if (ACall.ResolvedClassType <> nil) and
     (ACall.ResolvedClassType.Kind = tyInterface) then
  begin
    IntfDesc := TInterfaceTypeDesc(ACall.ResolvedClassType);
    SelfTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_%s_obj', [SelfTemp, ACall.ObjectName]));
    VTblTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_%s_itab', [VTblTemp, ACall.ObjectName]));
    SlotOff  := IntfDesc.MethodIndex(ACall.Name) * 8;
    FPtrTemp := AllocTemp;
    if SlotOff = 0 then
      EmitLine(Format('  %s =l loadl %s', [FPtrTemp, VTblTemp]))
    else
    begin
      ArgTemp := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', [ArgTemp, VTblTemp, SlotOff]));
      EmitLine(Format('  %s =l loadl %s',   [FPtrTemp, ArgTemp]));
    end;
    EmitLine(Format('  call %s(l %s)', [FPtrTemp, SelfTemp]));
    Exit;
  end;

  { Built-in Free: release the instance (decrement refcount; free at zero)
    and nil out the slot.  Under universal ARC, Free is a sanctioned synonym
    for immediate release — if other references remain, the block survives
    until their scope exits release them too.  Zeroing the slot makes a
    subsequent scope-exit release a safe no-op. }
  if (ACall.ResolvedMethod = nil) and SameText(ACall.Name, 'Free') then
  begin
    SelfTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_%s', [SelfTemp, ACall.ObjectName]));
    EmitLine(Format('  call $_ClassRelease(l %s)', [SelfTemp]));
    EmitLine(Format('  storel 0, %%_var_%s', [ACall.ObjectName]));
    Exit;
  end;

  RT    := TRecordTypeDesc(ACall.ResolvedClassType);
  MDecl := TMethodDecl(ACall.ResolvedMethod);

  { Load the object pointer (Self) from the caller's variable slot }
  SelfTemp := AllocTemp;
  EmitLine(Format('  %s =l loadl %%_var_%s', [SelfTemp, ACall.ObjectName]));

  { Build argument string: l Self, then each explicit arg }
  ArgLine := Format('l %s', [SelfTemp]);
  for I := 0 to ACall.Args.Count - 1 do
  begin
    Par     := TMethodParam(MDecl.Params[I]);
    ArgTemp := EmitExpr(TASTExpr(ACall.Args[I]));
    QType   := QbeTypeOf(Par.ResolvedType);
    ArgLine := ArgLine + Format(', %s %s', [QType, ArgTemp]);
  end;

  if MDecl.VTableSlot >= 0 then
  begin
    { Virtual dispatch: load vptr from instance[0], then load fptr from vtable.
      Slot 0 of vtable is typeinfo, so method N is at offset (N+1)*8. }
    VTblTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %s', [VTblTemp, SelfTemp]));
    FPtrTemp := AllocTemp;
    SlotOff  := (MDecl.VTableSlot + 1) * 8;
    ArgTemp  := AllocTemp;
    EmitLine(Format('  %s =l add %s, %d', [ArgTemp, VTblTemp, SlotOff]));
    EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
    EmitLine(Format('  call %s(%s)', [FPtrTemp, ArgLine]));
  end
  else
  begin
    { Static dispatch }
    if MDecl.OwnerTypeName <> '' then
      FuncName := '$' + MDecl.OwnerTypeName + '_' + ACall.Name
    else
      FuncName := '$' + RT.Name + '_' + ACall.Name;
    EmitLine(Format('  call %s(%s)', [FuncName, ArgLine]));
  end;
end;

procedure TCodeGenQBE.EmitParamAllocs(AMethod: TMethodDecl;
  AClassType: TRecordTypeDesc);
var
  I:   Integer;
  Par: TMethodParam;
begin
  { Self: store incoming pointer into a local slot }
  EmitLine('  %_var_Self =l alloc8 1');
  EmitLine('  storel %_par_Self, %_var_Self');

  { Explicit params }
  for I := 0 to AMethod.Params.Count - 1 do
  begin
    Par := TMethodParam(AMethod.Params[I]);
    if Par.IsVarParam then
    begin
      { Var param arrives as a pointer — spill pointer into a local slot }
      EmitLine(Format('  %%_var_%s =l alloc8 1', [Par.ParamName]));
      EmitLine(Format('  storel %%_par_%s, %%_var_%s',
        [Par.ParamName, Par.ParamName]));
    end
    else
    case Par.ResolvedType.Kind of
      tyInteger, tyUInt32, tyBoolean, tyByte:
        begin
          EmitLine(Format('  %%_var_%s =l alloc4 1', [Par.ParamName]));
          EmitLine(Format('  storew %%_par_%s, %%_var_%s',
            [Par.ParamName, Par.ParamName]));
        end;
      tyInt64, tyString, tyClass:
        begin
          EmitLine(Format('  %%_var_%s =l alloc8 1', [Par.ParamName]));
          EmitLine(Format('  storel %%_par_%s, %%_var_%s',
            [Par.ParamName, Par.ParamName]));
        end;
    else
      EmitLine(Format('  %%_var_%s =l alloc8 1', [Par.ParamName]));
      EmitLine(Format('  storel %%_par_%s, %%_var_%s',
        [Par.ParamName, Par.ParamName]));
    end;
  end;
end;

procedure TCodeGenQBE.EmitMethodDef(const ATypeName: string;
  AMethod: TMethodDecl);
var
  Sig:           string;
  I:             Integer;
  Par:           TMethodParam;
  FuncName:      string;
  IsFunc:        Boolean;
  RetQType:      string;
  RetTemp:       string;
  SavedExitLbl:  string;
  ValTemp:       string;
begin
  FuncName := '$' + ATypeName + '_' + AMethod.Name;
  IsFunc   := AMethod.ResolvedReturnType <> nil;

  { Build parameter signature: l %_par_Self [, qtype %_par_Name ...] }
  Sig := 'l %_par_Self';
  for I := 0 to AMethod.Params.Count - 1 do
  begin
    Par := TMethodParam(AMethod.Params[I]);
    if Par.IsVarParam then
      Sig := Sig + Format(', l %%_par_%s', [Par.ParamName])
    else
      Sig := Sig + Format(', %s %%_par_%s',
        [QbeTypeOf(Par.ResolvedType), Par.ParamName]);
  end;

  if IsFunc then
  begin
    RetQType := QbeTypeOf(AMethod.ResolvedReturnType);
    EmitLine(Format('function %s %s(%s) {', [RetQType, FuncName, Sig]));
  end
  else
    EmitLine(Format('function %s(%s) {', [FuncName, Sig]));

  EmitLine('@start');
  EmitParamAllocs(AMethod, nil);

  { ARC: addref class value params on entry — balances the release pass at
    method exit.  Strings in method params are not ARC-managed yet (existing
    gap); classes are covered here because the whole Phase 3 follow-up is
    specifically about class ARC parity. }
  for I := 0 to AMethod.Params.Count - 1 do
  begin
    Par := TMethodParam(AMethod.Params[I]);
    if Par.IsVarParam then Continue;
    if Par.ResolvedType.Kind = tyClass then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_ClassAddRef(l %s)', [ValTemp]));
    end;
  end;

  { For function methods, allocate a zero-initialised Result slot }
  if IsFunc then
  begin
    if RetQType = 'w' then
    begin
      EmitLine('  %_var_Result =l alloc4 1');
      EmitLine('  storew 0, %_var_Result');
    end
    else
    begin
      EmitLine('  %_var_Result =l alloc8 1');
      EmitLine('  storel 0, %_var_Result');
    end;
  end;

  SavedExitLbl := FExitLabel;
  FExitLabel   := AllocLabel('method_exit');
  try
    EmitBlock(AMethod.Body);
  finally
    FExitLabel := SavedExitLbl;
  end;

  { ARC: release class value params on exit. }
  for I := 0 to AMethod.Params.Count - 1 do
  begin
    Par := TMethodParam(AMethod.Params[I]);
    if Par.IsVarParam then Continue;
    if Par.ResolvedType.Kind = tyClass then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [ValTemp]));
    end;
  end;

  if IsFunc then
  begin
    RetTemp := AllocTemp;
    if RetQType = 'w' then
      EmitLine(Format('  %s =w loadw %%_var_Result', [RetTemp]))
    else
      EmitLine(Format('  %s =l loadl %%_var_Result', [RetTemp]));
    EmitLine(Format('  ret %s', [RetTemp]));
  end
  else
    EmitLine('  ret');

  EmitLine('}');
  EmitLine('');
end;

procedure TCodeGenQBE.EmitTypeInfoDefs(AProg: TProgram);
{ Emit one $typeinfo_T data item per class type.
  Layout: { l parent_typeinfo_or_zero, l impllist_or_zero }
  TypeInfo is at vtable slot 0; _IsInstance walks parent chain.
  impllist is NULL-terminated array of {typeinfo_intf, itab} pairs for _ImplementsInterface.

  TObject is the built-in root class; any user class with an explicit
  `class(TObject, IFoo)` parent list resolves Parent to TObject's
  TRecordTypeDesc, so we emit a typeinfo stub for TObject unconditionally
  to satisfy the linker.  Its parent slot is nil and its impllist slot
  is nil because TObject implements no interfaces. }
var
  I:         Integer;
  TD:        TTypeDecl;
  TDesc:     TTypeDesc;
  RT:        TRecordTypeDesc;
  GI:        TGenericInstance;
  ParentStr: string;
  ImplStr:   string;
  MName:     string;
begin
  EmitLine('data $typeinfo_TObject = { l 0, l 0 }');

  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    if RT.Parent <> nil then
      ParentStr := '$typeinfo_' + RT.Parent.Name
    else
      ParentStr := '0';
    if RT.ImplementsCount > 0 then
      ImplStr := '$impllist_' + TD.Name
    else
      ImplStr := '0';
    EmitLine('data $typeinfo_' + TD.Name +
             ' = { l ' + ParentStr + ', l ' + ImplStr + ' }');
  end;

  { Generic instances }
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI    := TGenericInstance(AProg.GenericInstances[I]);
    RT    := TRecordTypeDesc(GI.TypeDesc);
    MName := QBEMangle(GI.TypeName);
    if RT.Parent <> nil then
      ParentStr := '$typeinfo_' + QBEMangle(RT.Parent.Name)
    else
      ParentStr := '0';
    ImplStr := '0';
    EmitLine('data $typeinfo_' + MName + ' = { l ' + ParentStr + ', l ' + ImplStr + ' }');
  end;

  EmitLine('');
end;

procedure TCodeGenQBE.EmitVTableDefs(AProg: TProgram);
{ Vtable layout: slot 0 = $typeinfo_T pointer, slots 1..N = virtual method ptrs.
  Dispatch uses (VTableSlot + 1) * 8 to skip the typeinfo slot. }
var
  I, S:  Integer;
  TD:    TTypeDecl;
  TDesc: TTypeDesc;
  RT:    TRecordTypeDesc;
  GI:    TGenericInstance;
  E:     TVTableEntry;
  Line:  string;
  MName: string;
begin
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    if not RT.HasVTable then Continue;
    { TypeInfo pointer is always the first vtable entry }
    Line := 'data $vtable_' + TD.Name + ' = { l $typeinfo_' + TD.Name;
    for S := 0 to RT.VTableCount - 1 do
    begin
      E    := RT.VTableEntryAt(S);
      Line := Line + ', l ' + E.ImplName;
    end;
    Line := Line + ' }';
    EmitLine(Line);
  end;

  { Generic instances }
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI    := TGenericInstance(AProg.GenericInstances[I]);
    RT    := TRecordTypeDesc(GI.TypeDesc);
    if not RT.HasVTable then Continue;
    MName := QBEMangle(GI.TypeName);
    Line  := 'data $vtable_' + MName + ' = { l $typeinfo_' + MName;
    for S := 0 to RT.VTableCount - 1 do
    begin
      E    := RT.VTableEntryAt(S);
      Line := Line + ', l ' + QBEMangle(E.ImplName);
    end;
    Line := Line + ' }';
    EmitLine(Line);
  end;

  EmitLine('');
end;

procedure TCodeGenQBE.EmitInterfaceDefs(AProg: TProgram);
{ Emit typeinfo blocks for interfaces and itab/impllist blocks for class-interface pairs.
  Interface typeinfo: data $typeinfo_IFoo = { l 0 }  (address IS the identity token)
  Itab: data $itab_TFoo_IFoo = { l $TFoo_DoIt, l $TFoo_GetVal }
  Impllist: data $impllist_TFoo = { l $typeinfo_IFoo, l $itab_TFoo_IFoo, l 0 }
  Methods in declaration order; impllist is NULL-terminated {ti, itab} pair array. }
var
  I, J, K:     Integer;
  TD:          TTypeDecl;
  TDesc:       TTypeDesc;
  IntfDesc:    TInterfaceTypeDesc;
  ClassRT:     TRecordTypeDesc;
  ItabLine:    string;
  ImplLine:    string;
  MethName:    string;
  IntfMangle:  string;
  GII:         TGenericInterfaceInstance;
begin
  { Typeinfo blocks for every plain interface }
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls[I]);
    if not (TD.Def is TInterfaceTypeDef) then Continue;
    EmitLine('data $typeinfo_' + TD.Name + ' = { l 0 }');
  end;

  { Typeinfo blocks for generic interface instantiations }
  for I := 0 to AProg.GenericIntfInstances.Count - 1 do
  begin
    GII := TGenericInterfaceInstance(AProg.GenericIntfInstances[I]);
    EmitLine('data $typeinfo_' + GII.InstName + ' = { l 0 }');
  end;

  { Itab and impllist blocks for each implementing class }
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    ClassRT := TRecordTypeDesc(TDesc);
    if ClassRT.ImplementsCount = 0 then Continue;

    { One itab per interface }
    for J := 0 to ClassRT.ImplementsCount - 1 do
    begin
      IntfDesc   := ClassRT.ImplementsIntfAt(J);
      IntfMangle := QBEMangle(IntfDesc.Name);
      ItabLine   := 'data $itab_' + TD.Name + '_' + IntfMangle + ' = {';
      for K := 0 to IntfDesc.MethodCount - 1 do
      begin
        MethName := IntfDesc.MethodName(K);
        if K = 0 then
          ItabLine := ItabLine + ' l $' + TD.Name + '_' + MethName
        else
          ItabLine := ItabLine + ', l $' + TD.Name + '_' + MethName;
      end;
      ItabLine := ItabLine + ' }';
      EmitLine(ItabLine);
    end;

    { One impllist per class: NULL-terminated {typeinfo_intf, itab} pairs }
    ImplLine := 'data $impllist_' + TD.Name + ' = {';
    for J := 0 to ClassRT.ImplementsCount - 1 do
    begin
      IntfDesc   := ClassRT.ImplementsIntfAt(J);
      IntfMangle := QBEMangle(IntfDesc.Name);
      if J = 0 then
        ImplLine := ImplLine + ' l $typeinfo_' + IntfMangle +
                               ', l $itab_' + TD.Name + '_' + IntfMangle
      else
        ImplLine := ImplLine + ', l $typeinfo_' + IntfMangle +
                               ', l $itab_' + TD.Name + '_' + IntfMangle;
    end;
    ImplLine := ImplLine + ', l 0 }';
    EmitLine(ImplLine);
  end;
  EmitLine('');
end;

procedure TCodeGenQBE.EmitFieldCleanupFn(const AMangledName: string;
                                         ARec: TRecordTypeDesc);
{ Emit a QBE function $_FieldCleanup_<Name>(l %self) that releases every
  ARC-managed field the instance holds.  The function is invoked from
  _ClassRelease at refcount zero, before the backing block is freed.

  The most-derived class's cleanup is authoritative: inherited fields are
  already merged into this class's Fields list by the semantic analyser
  (see uSemantic.pas — parent fields are copied into the derived
  TRecordTypeDesc during Pass 2), so iterating Fields here covers own and
  inherited fields uniformly.  We therefore do not chain to a parent
  cleanup — doing so would release each inherited field twice.

  A cleanup function is emitted for every class even when it has no
  ARC-managed fields — the no-op call keeps the constructor call site
  uniform and is negligible at runtime. }
var
  I:      Integer;
  F:      TFieldInfo;
  Temp:   string;
  PtrT:   string;
begin
  EmitLine(Format('function $_FieldCleanup_%s(l %%self) {', [AMangledName]));
  EmitLine('@start');
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields[I]);
    if F.TypeDesc = nil then Continue;
    if not (F.TypeDesc.IsString or (F.TypeDesc.Kind = tyClass)) then
      Continue;
    Temp := AllocTemp;
    if F.Offset > 0 then
    begin
      PtrT := AllocTemp;
      EmitLine(Format('  %s =l add %%self, %d', [PtrT, F.Offset]));
    end
    else
      PtrT := '%self';
    EmitLine(Format('  %s =l loadl %s', [Temp, PtrT]));
    if F.TypeDesc.IsString then
      EmitLine(Format('  call $_StringRelease(l %s)', [Temp]))
    else
      EmitLine(Format('  call $_ClassRelease(l %s)', [Temp]));
  end;
  EmitLine('  ret');
  EmitLine('}');
  EmitLine('');
end;

procedure TCodeGenQBE.EmitFieldCleanupDefs(AProg: TProgram);
{ Emit a _FieldCleanup_<T> function for every declared class and every
  generic class instantiation.  The constructor lowering references these
  functions by name; see the _ClassAlloc call in EmitExpr. }
var
  I:     Integer;
  TD:    TTypeDecl;
  TDesc: TTypeDesc;
  RT:    TRecordTypeDesc;
  GI:    TGenericInstance;
begin
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls[I]);
    if not (TD.Def is TClassTypeDef) then Continue;
    TDesc := AProg.SymbolTable.FindType(TD.Name);
    if (TDesc = nil) or not (TDesc is TRecordTypeDesc) then Continue;
    RT := TRecordTypeDesc(TDesc);
    EmitFieldCleanupFn(TD.Name, RT);
  end;
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AProg.GenericInstances[I]);
    RT := TRecordTypeDesc(GI.TypeDesc);
    EmitFieldCleanupFn(QBEMangle(GI.TypeName), RT);
  end;
end;

procedure TCodeGenQBE.EmitMethodDefs(AProg: TProgram);
var
  I, J:  Integer;
  TD:    TTypeDecl;
  CD:    TClassTypeDef;
  GI:    TGenericInstance;
  MDecl: TMethodDecl;
begin
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls[I]);
    if not (TD.Def is TClassTypeDef) then
      Continue;
    CD := TClassTypeDef(TD.Def);
    for J := 0 to CD.Methods.Count - 1 do
      if TMethodDecl(CD.Methods[J]).Body <> nil then
        EmitMethodDef(TD.Name, TMethodDecl(CD.Methods[J]));
  end;

  { Generic instances — emit with mangled type name }
  for I := 0 to AProg.GenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(AProg.GenericInstances[I]);
    for J := 0 to GI.ClassDef.Methods.Count - 1 do
    begin
      MDecl := TMethodDecl(GI.ClassDef.Methods[J]);
      if MDecl.Body <> nil then
        EmitMethodDef(QBEMangle(GI.TypeName), MDecl);
    end;
  end;
end;

procedure TCodeGenQBE.EmitFuncDef(ADecl: TMethodDecl; AExported: Boolean);
var
  Sig:          string;
  I:            Integer;
  Par:          TMethodParam;
  FuncName:     string;
  IsFunc:       Boolean;
  RetQType:     string;
  RetTemp:      string;
  ValTemp:      string;
  Prefix:       string;
  SavedExitLbl: string;
begin
  FuncName := '$' + QBEMangle(ADecl.Name);
  IsFunc   := ADecl.ResolvedReturnType <> nil;
  if AExported then Prefix := 'export ' else Prefix := '';

  Sig := '';
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params[I]);
    if Sig <> '' then Sig := Sig + ', ';
    if Par.IsVarParam then
      Sig := Sig + Format('l %%_par_%s', [Par.ParamName])
    else
      Sig := Sig + Format('%s %%_par_%s', [QbeTypeOf(Par.ResolvedType), Par.ParamName]);
  end;

  if IsFunc then
  begin
    RetQType := QbeTypeOf(ADecl.ResolvedReturnType);
    EmitLine(Format('%sfunction %s %s(%s) {', [Prefix, RetQType, FuncName, Sig]));
  end
  else
    EmitLine(Format('%sfunction %s(%s) {', [Prefix, FuncName, Sig]));

  EmitLine('@start');

  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params[I]);
    if Par.IsVarParam then
    begin
      { Var param: spill the pointer into a local slot }
      EmitLine(Format('  %%_var_%s =l alloc8 1', [Par.ParamName]));
      EmitLine(Format('  storel %%_par_%s, %%_var_%s',
        [Par.ParamName, Par.ParamName]));
    end
    else
    begin
      case Par.ResolvedType.Kind of
        tyInteger, tyUInt32, tyBoolean, tyByte:
          begin
            EmitLine(Format('  %%_var_%s =l alloc4 1', [Par.ParamName]));
            EmitLine(Format('  storew %%_par_%s, %%_var_%s',
              [Par.ParamName, Par.ParamName]));
          end;
      else
        EmitLine(Format('  %%_var_%s =l alloc8 1', [Par.ParamName]));
        EmitLine(Format('  storel %%_par_%s, %%_var_%s',
          [Par.ParamName, Par.ParamName]));
      end;
    end;
  end;

  { ARC: addref string and class value params on entry (callee owns a
    retained copy that is balanced by the release pass at function exit). }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params[I]);
    if Par.IsVarParam then Continue;
    if Par.ResolvedType.Kind = tyString then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_StringAddRef(l %s)', [ValTemp]));
    end
    else if Par.ResolvedType.Kind = tyClass then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_ClassAddRef(l %s)', [ValTemp]));
    end;
  end;

  if IsFunc then
  begin
    if RetQType = 'w' then
    begin
      EmitLine('  %_var_Result =l alloc4 1');
      EmitLine('  storew 0, %_var_Result');
    end
    else
    begin
      EmitLine('  %_var_Result =l alloc8 1');
      EmitLine('  storel 0, %_var_Result');
    end;
  end;

  SavedExitLbl := FExitLabel;
  FExitLabel   := AllocLabel('func_exit');
  try
    EmitBlock(ADecl.Body);
  finally
    FExitLabel := SavedExitLbl;
  end;

  { ARC: release string and class value params on exit (balances the
    addref inserted at function entry). }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params[I]);
    if Par.IsVarParam then Continue;
    if Par.ResolvedType.Kind = tyString then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_StringRelease(l %s)', [ValTemp]));
    end
    else if Par.ResolvedType.Kind = tyClass then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_ClassRelease(l %s)', [ValTemp]));
    end;
  end;

  if IsFunc then
  begin
    RetTemp := AllocTemp;
    if RetQType = 'w' then
      EmitLine(Format('  %s =w loadw %%_var_Result', [RetTemp]))
    else
      EmitLine(Format('  %s =l loadl %%_var_Result', [RetTemp]));
    EmitLine(Format('  ret %s', [RetTemp]));
  end
  else
    EmitLine('  ret');

  EmitLine('}');
  EmitLine('');
end;

procedure TCodeGenQBE.EmitStandaloneDef(ADecl: TMethodDecl);
begin
  EmitFuncDef(ADecl, False);
end;

procedure TCodeGenQBE.EmitStandaloneDefs(AProg: TProgram);
var
  I:    Integer;
  Decl: TMethodDecl;
begin
  for I := 0 to AProg.Block.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(AProg.Block.ProcDecls[I]);
    { Class method impls had their body transferred — skip here. }
    if Decl.OwnerTypeName <> '' then Continue;
    { Generic templates — concrete instances are emitted via GenericFuncInstances. }
    if Decl.TypeParams <> nil then Continue;
    EmitStandaloneDef(Decl);
  end;
  { Emit each concrete generic function instance }
  for I := 0 to AProg.GenericFuncInstances.Count - 1 do
    EmitStandaloneDef(
      TGenericFuncInstance(AProg.GenericFuncInstances[I]).MethodDecl);
end;

procedure TCodeGenQBE.EmitProcCall(ACall: TProcCall);
var
  UCaseName: string;
  MDecl:     TMethodDecl;
  Par:       TMethodParam;
  ArgTemp:   string;
  ArgLine:   string;
  I:         Integer;
begin
  { User-defined procedure }
  if ACall.ResolvedDecl <> nil then
  begin
    MDecl   := TMethodDecl(ACall.ResolvedDecl);
    ArgLine := '';
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params[I]);
      if ArgLine <> '' then ArgLine := ArgLine + ', ';
      if Par.IsVarParam then
        { Pass address of the variable — skip the load }
        ArgLine := ArgLine + Format('l %%_var_%s',
          [TIdentExpr(TASTExpr(ACall.Args[I])).Name])
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(ACall.Args[I]));
        ArgLine := ArgLine + Format('%s %s', [QbeTypeOf(Par.ResolvedType), ArgTemp]);
      end;
    end;
    EmitLine(Format('  call $%s(%s)', [QBEMangle(ACall.Name), ArgLine]));
    Exit;
  end;

  { Built-in }
  UCaseName := UpperCase(ACall.Name);
  if UCaseName = 'WRITELN' then
    EmitWrite(ACall, True)
  else if UCaseName = 'WRITE' then
    EmitWrite(ACall, False)
  else if UCaseName = 'FREEMEM' then
  begin
    ArgTemp := EmitExpr(TASTExpr(ACall.Args[0]));
    EmitLine(Format('  call $free(l %s)', [ArgTemp]));
  end
  else
    raise ECodeGenError.CreateFmt(
      'Unknown procedure ''%s'' at line %d', [ACall.Name, ACall.Line]);
end;

procedure TCodeGenQBE.EmitPointerWrite(AStmt: TPointerWriteStmt);
var
  PtrTemp:    string;
  ValTemp:    string;
  QType:      string;
  StoreInstr: string;
begin
  PtrTemp := EmitExpr(AStmt.PtrExpr);
  ValTemp := EmitExpr(AStmt.ValExpr);
  QType   := QbeTypeOf(AStmt.BaseTy);
  if QType = 'w' then StoreInstr := 'storew'
                 else StoreInstr := 'storel';
  EmitLine(Format('  %s %s, %s', [StoreInstr, ValTemp, PtrTemp]));
end;

procedure TCodeGenQBE.EmitWrite(ACall: TProcCall; ANewline: Boolean);
var
  ArgExpr:  TASTExpr;
  ArgTemp:  string;
  CharPtr:  string;
  IsString: Boolean;
  I:        Integer;
begin
  if ACall.Args.Count = 0 then
  begin
    if ANewline then
      EmitLine('  call $printf(l $__fmt_nl)');
    Exit;
  end;

  { Emit one printf call per argument.  All formatting is plain ("%d" or "%s")
    with no trailing newline; a final "\n" is emitted after the last arg when
    ANewline is set (i.e. WriteLn rather than Write). }
  for I := 0 to ACall.Args.Count - 1 do
  begin
    ArgExpr  := TASTExpr(ACall.Args[I]);
    IsString := (ArgExpr.ResolvedType <> nil) and ArgExpr.ResolvedType.IsString;
    ArgTemp  := EmitExpr(ArgExpr);
    if IsString then
    begin
      { String pointer is the header pointer; char data starts at ptr+12. }
      CharPtr := AllocTemp;
      EmitLine(Format('  %s =l add %s, 12', [CharPtr, ArgTemp]));
      EmitLine(Format('  call $printf(l $__fmt_s, ..., l %s)', [CharPtr]));
    end
    else
      EmitLine(Format('  call $printf(l $__fmt_d, ..., w %s)', [ArgTemp]));
  end;

  if ANewline then
    EmitLine('  call $printf(l $__fmt_nl)');
end;

function TCodeGenQBE.EmitExpr(AExpr: TASTExpr): string;
var
  T, L, R:    string;
  Op:         string;
  BinExpr:    TBinaryExpr;
  FldAccess:  TFieldAccessExpr;
  MCallExpr:  TMethodCallExpr;
  Ptr:        string;
  QType:      string;
  LoadInstr:  string;
  SelfTemp:   string;
  ArgLine:    string;
  ArgTemp:    string;
  Par:        TMethodParam;
  MDecl:      TMethodDecl;
  RT:         TRecordTypeDesc;
  FuncName:   string;
  I:          Integer;
  IntfDesc:   TInterfaceTypeDesc;
  VTblTemp:   string;
  FPtrTemp:   string;
  SlotOff:    Integer;
begin
  if AExpr is TFuncCallExpr then
  begin
    { Standalone function call expression }
    with TFuncCallExpr(AExpr) do
    begin
      { SizeOf(TypeName) → integer literal = byte size of the type }
      if SameText(Name, 'SizeOf') then
      begin
        T := AllocTemp;
        EmitLine(Format('  %s =w copy %d',
          [T, TASTExpr(Args[0]).ResolvedType.ByteSize]));
        Result := T;
        Exit;
      end;

      { GetMem(N) → malloc(N) → pointer }
      if SameText(Name, 'GetMem') then
      begin
        ArgTemp := EmitExpr(TASTExpr(Args[0]));
        T := AllocTemp;
        { Extend arg to l for malloc }
        L := AllocTemp;
        EmitLine(Format('  %s =l extsw %s', [L, ArgTemp]));
        EmitLine(Format('  %s =l call $malloc(l %s)', [T, L]));
        Result := T;
        Exit;
      end;

      { ReallocMem(P, N) → realloc(P, N) → pointer }
      if SameText(Name, 'ReallocMem') then
      begin
        L := EmitExpr(TASTExpr(Args[0]));
        R := EmitExpr(TASTExpr(Args[1]));
        ArgTemp := AllocTemp;
        EmitLine(Format('  %s =l extsw %s', [ArgTemp, R]));
        T := AllocTemp;
        EmitLine(Format('  %s =l call $realloc(l %s, l %s)', [T, L, ArgTemp]));
        Result := T;
        Exit;
      end;

      { Type cast TypeName(Expr) — ResolvedDecl is nil; just copy with target QBE type }
      if ResolvedDecl = nil then
      begin
        ArgTemp := EmitExpr(TASTExpr(Args[0]));
        T       := AllocTemp;
        QType   := QbeTypeOf(ResolvedType);
        if QType = 'w' then
          EmitLine(Format('  %s =w copy %s', [T, ArgTemp]))
        else
          EmitLine(Format('  %s =l copy %s', [T, ArgTemp]));
        Result := T;
        Exit;
      end;

      MDecl    := TMethodDecl(ResolvedDecl);
      QType    := QbeTypeOf(MDecl.ResolvedReturnType);
      FuncName := '$' + QBEMangle(Name);
      ArgLine  := '';
      for I := 0 to Args.Count - 1 do
      begin
        Par     := TMethodParam(MDecl.Params[I]);
        ArgTemp := EmitExpr(TASTExpr(Args[I]));
        if ArgLine <> '' then ArgLine := ArgLine + ', ';
        ArgLine := ArgLine + Format('%s %s', [QbeTypeOf(Par.ResolvedType), ArgTemp]);
      end;
      T := AllocTemp;
      EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FuncName, ArgLine]));
      Result := T;
    end;
    Exit;
  end;

  if AExpr is TMethodCallExpr then
  begin
    MCallExpr := TMethodCallExpr(AExpr);

    { Interface method call expression: dispatch through itab }
    if (MCallExpr.ResolvedClassType <> nil) and
       (MCallExpr.ResolvedClassType.Kind = tyInterface) then
    begin
      IntfDesc := TInterfaceTypeDesc(MCallExpr.ResolvedClassType);
      SelfTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s_obj',
        [SelfTemp, MCallExpr.ObjectName]));
      VTblTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s_itab',
        [VTblTemp, MCallExpr.ObjectName]));
      SlotOff := IntfDesc.MethodIndex(MCallExpr.Name) * 8;
      FPtrTemp := AllocTemp;
      if SlotOff = 0 then
        EmitLine(Format('  %s =l loadl %s', [FPtrTemp, VTblTemp]))
      else
      begin
        ArgTemp := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', [ArgTemp, VTblTemp, SlotOff]));
        EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
      end;
      { Evaluate arguments before the call }
      ArgLine := Format('l %s', [SelfTemp]);
      for I := 0 to MCallExpr.Args.Count - 1 do
      begin
        ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args[I]));
        ArgLine := ArgLine + Format(', w %s', [ArgTemp]);
      end;
      T := AllocTemp;
      EmitLine(Format('  %s =w call %s(%s)', [T, FPtrTemp, ArgLine]));
      Result := T;
      Exit;
    end;

    RT        := TRecordTypeDesc(MCallExpr.ResolvedClassType);
    MDecl     := TMethodDecl(MCallExpr.ResolvedMethod);
    if MDecl.OwnerTypeName <> '' then
      FuncName := '$' + MDecl.OwnerTypeName + '_' + MCallExpr.Name
    else
      FuncName := '$' + RT.Name + '_' + MCallExpr.Name;
    QType     := QbeTypeOf(MDecl.ResolvedReturnType);

    { Load the object pointer (Self) }
    SelfTemp := AllocTemp;
    EmitLine(Format('  %s =l loadl %%_var_%s', [SelfTemp, MCallExpr.ObjectName]));

    { Build argument string }
    ArgLine := Format('l %s', [SelfTemp]);
    for I := 0 to MCallExpr.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params[I]);
      if Par.IsVarParam then
        { Pass address of the variable directly — do not load through it }
        ArgLine := ArgLine + Format(', l %%_var_%s',
          [TIdentExpr(TASTExpr(MCallExpr.Args[I])).Name])
      else
      begin
        ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args[I]));
        ArgLine := ArgLine + Format(', %s %s', [QbeTypeOf(Par.ResolvedType), ArgTemp]);
      end;
    end;

    T := AllocTemp;
    if MDecl.VTableSlot >= 0 then
    begin
      { Virtual dispatch: load vptr then function pointer from vtable }
      VTblTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %s', [VTblTemp, SelfTemp]));
      FPtrTemp := AllocTemp;
      SlotOff  := (MDecl.VTableSlot + 1) * 8;
      ArgTemp  := AllocTemp;
      EmitLine(Format('  %s =l add %s, %d', [ArgTemp, VTblTemp, SlotOff]));
      EmitLine(Format('  %s =l loadl %s', [FPtrTemp, ArgTemp]));
      EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FPtrTemp, ArgLine]));
    end
    else
      EmitLine(Format('  %s =%s call %s(%s)', [T, QType, FuncName, ArgLine]));
    Result := T;
    Exit;
  end;

  if AExpr is TNilLiteral then
  begin
    T := AllocTemp;
    EmitLine(Format('  %s =l copy 0', [T]));
    Result := T;
    Exit;
  end;

  if AExpr is TIntLiteral then
  begin
    T := AllocTemp;
    EmitLine(Format('  %s =w copy %d', [T, TIntLiteral(AExpr).Value]));
    Result := T;
  end
  else if AExpr is TStringLiteral then
  begin
    Result := EmitStrLit(TStringLiteral(AExpr).Value);
  end
  else if AExpr is TFieldAccessExpr then
  begin
    FldAccess := TFieldAccessExpr(AExpr);
    { Chained access: compute base storage pointer, then load the field from
      (base_ptr + offset) using the field's QBE type. }
    if FldAccess.Base <> nil then
    begin
      L := EmitInstancePtr(FldAccess.Base);
      if FldAccess.FieldInfo = nil then
        raise ECodeGenError.CreateFmt(
          'Chained field ''%s'' has no resolved field info', [FldAccess.FieldName]);
      if FldAccess.FieldInfo.Offset > 0 then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d',
          [Ptr, L, FldAccess.FieldInfo.Offset]));
      end
      else
        Ptr := L;
      QType := QbeTypeOf(FldAccess.FieldInfo.TypeDesc);
      T     := AllocTemp;
      if QType = 'w' then LoadInstr := 'loadw'
                     else LoadInstr := 'loadl';
      EmitLine(Format('  %s =%s %s %s', [T, QType, LoadInstr, Ptr]));
      Result := T;
      Exit;
    end;
    if FldAccess.IsConstructorCall then
    begin
      { TypeName.Create — allocate zeroed instance on heap.  _ClassAlloc
        prefixes a 16-byte header (refcount + field-cleanup fn pointer)
        before the returned pointer (see blaise_arc.c).  The user pointer
        still points at the vptr, so field offsets are unchanged.  The
        cleanup fn is invoked by _ClassRelease before free() when the
        refcount reaches zero and is responsible for releasing any
        ARC-managed fields. }
      T := AllocTemp;
      EmitLine(Format('  %s =l call $_ClassAlloc(l %d, l $_FieldCleanup_%s)',
        [T, TRecordTypeDesc(FldAccess.ResolvedType).TotalSize,
         QBEMangle(FldAccess.ResolvedType.Name)]));
      { Store vtable pointer at offset 0 if this class has virtual methods }
      if TRecordTypeDesc(FldAccess.ResolvedType).HasVTable then
        EmitLine(Format('  storel $vtable_%s, %s',
          [QBEMangle(FldAccess.ResolvedType.Name), T]));
      Result := T;
    end
    else if FldAccess.PropRead <> nil then
    begin
      { Method-backed property read: load Self pointer and call getter }
      L := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [L, FldAccess.RecordName]));
      T     := AllocTemp;
      QType := QbeTypeOf(FldAccess.PropRead.TypeDesc);
      EmitLine(Format('  %s =%s call $%s_%s(l %s)',
        [T, QType, QBEMangle(FldAccess.PropOwnerType),
         FldAccess.PropRead.ReadMethod, L]));
      Result := T;
    end
    else if FldAccess.IsClassAccess then
    begin
      { Load heap pointer, then load field }
      L := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [L, FldAccess.RecordName]));
      if FldAccess.FieldInfo.Offset > 0 then
      begin
        Ptr := AllocTemp;
        EmitLine(Format('  %s =l add %s, %d', [Ptr, L, FldAccess.FieldInfo.Offset]));
      end
      else
        Ptr := L;
      QType := QbeTypeOf(FldAccess.FieldInfo.TypeDesc);
      T     := AllocTemp;
      if QType = 'w' then LoadInstr := 'loadw'
                     else LoadInstr := 'loadl';
      EmitLine(Format('  %s =%s %s %s', [T, QType, LoadInstr, Ptr]));
      Result := T;
    end
    else
    begin
      { Record field access }
      if FldAccess.FieldInfo = nil then
        raise ECodeGenError.CreateFmt(
          'Field access ''%s.%s'' has no resolved field info',
          [FldAccess.RecordName, FldAccess.FieldName]);
      Ptr   := FieldPtr(FldAccess.RecordName, FldAccess.FieldInfo.Offset);
      QType := QbeTypeOf(FldAccess.FieldInfo.TypeDesc);
      T     := AllocTemp;
      if QType = 'w' then LoadInstr := 'loadw'
                     else LoadInstr := 'loadl';
      EmitLine(Format('  %s =%s %s %s', [T, QType, LoadInstr, Ptr]));
      Result := T;
    end;
  end
  else if AExpr is TIdentExpr then
  begin
    T := AllocTemp;
    if TIdentExpr(AExpr).IsConstant then
    begin
      EmitLine(Format('  %s =w copy %d', [T, TIdentExpr(AExpr).ConstValue]));
    end
    else if TIdentExpr(AExpr).IsVarParam then
    begin
      { Var param: load pointer, then dereference }
      Ptr := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [Ptr, TIdentExpr(AExpr).Name]));
      QType := QbeTypeOf(AExpr.ResolvedType);
      if QType = 'l' then
        EmitLine(Format('  %s =l loadl %s', [T, Ptr]))
      else
        EmitLine(Format('  %s =w loadw %s', [T, Ptr]));
    end
    else if (AExpr.ResolvedType <> nil) and (QbeTypeOf(AExpr.ResolvedType) = 'l') then
    begin
      EmitLine(Format('  %s =l loadl %%_var_%s', [T, TIdentExpr(AExpr).Name]));
    end
    else
    begin
      EmitLine(Format('  %s =w loadw %%_var_%s', [T, TIdentExpr(AExpr).Name]));
    end;
    Result := T;
  end
  else if AExpr is TBinaryExpr then
  begin
    BinExpr := TBinaryExpr(AExpr);
    L := EmitExpr(BinExpr.Left);
    R := EmitExpr(BinExpr.Right);
    T := AllocTemp;
    { String concatenation: delegate to RTL }
    if (BinExpr.Op = boAdd) and
       (BinExpr.Left.ResolvedType <> nil) and
       BinExpr.Left.ResolvedType.IsString then
    begin
      EmitLine(Format('  %s =l call $_StringConcat(l %s, l %s)', [T, L, R]));
      Result := T;
      Exit;
    end;
    { Pointer arithmetic: Pointer +/- Integer — scale offset by sizeof(base) }
    if (BinExpr.Op in [boAdd, boSub]) and
       (BinExpr.Left.ResolvedType <> nil) and
       (BinExpr.Left.ResolvedType.Kind = tyPointer) then
    begin
      { Scale the integer offset to bytes.  QBE pointer/int ops are both l. }
      ArgTemp := AllocTemp;
      EmitLine(Format('  %s =l extsw %s', [ArgTemp, R]));
      if BinExpr.Op = boAdd then
        EmitLine(Format('  %s =l add %s, %s', [T, L, ArgTemp]))
      else
        EmitLine(Format('  %s =l sub %s, %s', [T, L, ArgTemp]));
      Result := T;
      Exit;
    end;
    { String equality/inequality: content comparison via RTL helper }
    if (BinExpr.Left.ResolvedType <> nil) and
       BinExpr.Left.ResolvedType.IsString and
       (BinExpr.Op in [boEQ, boNE]) then
    begin
      EmitLine(Format('  %s =w call $_StringEquals(l %s, l %s)', [T, L, R]));
      if BinExpr.Op = boNE then
      begin
        ArgTemp := AllocTemp;
        EmitLine(Format('  %s =w ceqw %s, 0', [ArgTemp, T]));
        T := ArgTemp;
      end;
      Result := T;
      Exit;
    end;
    { Use long (pointer) comparison instructions when operands are class/nil }
    if (BinExpr.Left.ResolvedType <> nil) and
       (BinExpr.Left.ResolvedType.Kind in [tyClass, tyNil]) then
    begin
      case BinExpr.Op of
        boEQ: Op := 'ceql';
        boNE: Op := 'cnel';
      else
        Op := 'ceql';
      end;
      EmitLine(Format('  %s =w %s %s, %s', [T, Op, L, R]));
    end
    else
    begin
      case BinExpr.Op of
        boAdd: Op := 'add';
        boSub: Op := 'sub';
        boMul: Op := 'mul';
        boDiv: Op := 'div';
        boEQ:  Op := 'ceqw';
        boNE:  Op := 'cnew';
        boLT:  Op := 'csltw';
        boGT:  Op := 'csgtw';
        boLE:  Op := 'cslew';
        boGE:  Op := 'csgew';
        boAnd: Op := 'and';
        boOr:  Op := 'or';
      else
        Op := 'add';
      end;
      EmitLine(Format('  %s =w %s %s, %s', [T, Op, L, R]));
    end;
    Result := T;
  end
  else if AExpr is TNotExpr then
  begin
    { Logical not on Boolean (0/1): xor with 1 flips the low bit. }
    L := EmitExpr(TNotExpr(AExpr).Expr);
    T := AllocTemp;
    EmitLine(Format('  %s =w xor %s, 1', [T, L]));
    Result := T;
  end
  else if AExpr is TDerefExpr then
  begin
    { P^ — load the value at the pointer address }
    T     := EmitExpr(TDerefExpr(AExpr).Expr);
    QType := QbeTypeOf(AExpr.ResolvedType);
    L     := AllocTemp;
    if QType = 'w' then
      EmitLine(Format('  %s =w loadw %s', [L, T]))
    else
      EmitLine(Format('  %s =l loadl %s', [L, T]));
    Result := L;
  end
  else if AExpr is TIsExpr then
    Result := EmitIsExpr(TIsExpr(AExpr))
  else if AExpr is TAsExpr then
    Result := EmitAsExpr(TAsExpr(AExpr))
  else
    raise ECodeGenError.Create('Unknown expression node type');
end;

function TCodeGenQBE.EmitIsExpr(AExpr: TIsExpr): string;
var
  ObjTemp: string;
  ResTemp: string;
begin
  ObjTemp := EmitExpr(AExpr.Obj);
  ResTemp := AllocTemp;
  if (AExpr.ResolvedTargetType <> nil) and
     (AExpr.ResolvedTargetType.Kind = tyInterface) then
    EmitLine(Format('  %s =w call $_ImplementsInterface(l %s, l $typeinfo_%s)',
      [ResTemp, ObjTemp, AExpr.TypeName]))
  else
    EmitLine(Format('  %s =w call $_IsInstance(l %s, l $typeinfo_%s)',
      [ResTemp, ObjTemp, AExpr.TypeName]));
  Result := ResTemp;
end;

function TCodeGenQBE.EmitAsExpr(AExpr: TAsExpr): string;
var
  ObjTemp:  string;
  OkTemp:   string;
  SlotTemp: string;
  ResTemp:  string;
  LblOk:    string;
  LblFail:  string;
  LblEnd:   string;
begin
  ObjTemp  := EmitExpr(AExpr.Obj);
  SlotTemp := AllocTemp;
  EmitLine(Format('  %s =l alloc8 1', [SlotTemp]));

  OkTemp  := AllocTemp;
  LblOk   := AllocLabel('as_ok');
  LblFail := AllocLabel('as_fail');
  LblEnd  := AllocLabel('as_end');

  EmitLine(Format('  %s =w call $_IsInstance(l %s, l $typeinfo_%s)',
    [OkTemp, ObjTemp, AExpr.TypeName]));
  EmitLine(Format('  jnz %s, @%s, @%s', [OkTemp, LblOk, LblFail]));

  EmitLine('@' + LblFail);
  EmitLine('  call $_Raise_InvalidCast()');
  EmitLine(Format('  storel 0, %s', [SlotTemp]));  { unreachable; satisfies SSA }
  EmitLine(Format('  jmp @%s', [LblEnd]));

  EmitLine('@' + LblOk);
  EmitLine(Format('  storel %s, %s', [ObjTemp, SlotTemp]));
  EmitLine(Format('  jmp @%s', [LblEnd]));

  EmitLine('@' + LblEnd);
  ResTemp := AllocTemp;
  EmitLine(Format('  %s =l loadl %s', [ResTemp, SlotTemp]));
  Result := ResTemp;
end;

function TCodeGenQBE.QBEMangle(const AName: string): string;
var
  I: Integer;
begin
  Result := '';
  for I := 1 to Length(AName) do
    case AName[I] of
      '<': Result := Result + '_';
      '>': { skip — closing bracket dropped };
      ',': Result := Result + '_';
    else
      Result := Result + AName[I];
    end;
end;

function TCodeGenQBE.QbeEscapeString(const AStr: string): string;
var
  I: Integer;
  C: Char;
begin
  Result := '';
  for I := 1 to Length(AStr) do
  begin
    C := AStr[I];
    case C of
      '"':  Result := Result + '\"';
      '\':  Result := Result + '\\';
      #10:  Result := Result + '\n';
      #13:  Result := Result + '\r';
      #9:   Result := Result + '\t';
      else if (Ord(C) < 32) or (Ord(C) > 126) then
        Result := Result + Format('\%02x', [Ord(C)])
      else
        Result := Result + C;
    end;
  end;
end;

procedure TCodeGenQBE.Generate(AProg: TProgram);
var
  Body:        TStringList;
  SavedOutput: TStringList;
begin
  FOutput.Clear;
  FStrLits.Clear;
  FTempCount  := 0;
  FLabelCount := 0;

  Body := TStringList.Create;
  try
    SavedOutput := FOutput;
    FOutput := Body;
    try
      EmitFieldCleanupDefs(AProg);
      EmitMethodDefs(AProg);
      EmitStandaloneDefs(AProg);
      FExitLabel := 'main_exit';
      EmitMainHeader;
      EmitBlock(AProg.Block);
      EmitMainFooter;
      FExitLabel := '';
    finally
      FOutput := SavedOutput;
    end;

    EmitLine('# Generated by Blaise Compiler (Phase 2)');
    EmitLine('# Source: ' + AProg.Name);
    EmitLine('');
    EmitDataSection;
    EmitInterfaceDefs(AProg);
    EmitTypeInfoDefs(AProg);
    EmitVTableDefs(AProg);
    FOutput.AddStrings(Body);
  finally
    Body.Free;
  end;
end;

procedure TCodeGenQBE.GenerateUnit(AUnit: TUnit);
var
  I:         Integer;
  ImplDecl:  TMethodDecl;
  IntfNames: TStringList;
  Body:      TStringList;
  SavedOut:  TStringList;
begin
  FOutput.Clear;
  FStrLits.Clear;
  FTempCount  := 0;
  FLabelCount := 0;

  IntfNames := TStringList.Create;
  try
    IntfNames.CaseSensitive := False;
    for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
      IntfNames.Add(TMethodDecl(AUnit.IntfBlock.ProcDecls[I]).Name);

    Body := TStringList.Create;
    try
      SavedOut := FOutput;
      FOutput  := Body;
      try
        for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
        begin
          ImplDecl := TMethodDecl(AUnit.ImplBlock.ProcDecls[I]);
          EmitFuncDef(ImplDecl, IntfNames.IndexOf(ImplDecl.Name) >= 0);
        end;
      finally
        FOutput := SavedOut;
      end;

      EmitLine('# Generated by Blaise Compiler (Phase 2)');
      EmitLine('# Unit: ' + AUnit.Name);
      EmitLine('');
      EmitDataSection;
      FOutput.AddStrings(Body);
    finally
      Body.Free;
    end;
  finally
    IntfNames.Free;
  end;
end;

function TCodeGenQBE.GetOutput: string;
begin
  Result := FOutput.Text;
end;

end.
