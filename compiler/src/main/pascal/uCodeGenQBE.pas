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
    FOutput:     TStringList;
    FStrLits:    TStringList;  { index → raw value; label = $__s<index> }
    FTempCount:  Integer;
    FLabelCount: Integer;

    function  AllocTemp: string;
    function  AllocLabel(const APrefix: string): string;
    function  EmitStrLit(const AValue: string): string;
    procedure EmitLine(const ALine: string);
    procedure EmitDataSection;
    procedure EmitMainHeader;
    procedure EmitMainFooter;
    procedure EmitMethodDefs(AProg: TProgram);
    procedure EmitMethodDef(const ATypeName: string; AMethod: TMethodDecl);
    procedure EmitStandaloneDefs(AProg: TProgram);
    procedure EmitStandaloneDef(ADecl: TMethodDecl);
    procedure EmitFuncDef(ADecl: TMethodDecl; AExported: Boolean);
    procedure EmitBlock(ABlock: TBlock);
    procedure EmitVarAllocs(ABlock: TBlock);
    procedure EmitParamAllocs(AMethod: TMethodDecl; AClassType: TRecordTypeDesc);
    procedure EmitStringCleanup(ABlock: TBlock);
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
    procedure EmitWrite(ACall: TProcCall; ANewline: Boolean);
    function  EmitExpr(AExpr: TASTExpr): string;
    function  FieldPtr(const ARecordVar: string; AOffset: Integer): string;
    function  QbeTypeOf(AType: TTypeDesc): string;
    function  QbeEscapeString(const AStr: string): string;
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
  FOutput    := TStringList.Create;
  FStrLits   := TStringList.Create;
  FTempCount := 0;
end;

destructor TCodeGenQBE.Destroy;
begin
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
  if FStrLits.Count = 0 then
    Exit;
  EmitLine('# String literals');
  { Each literal has a 12-byte ARC header: refcnt=-1 (immortal), length, capacity.
    The string pointer IS the header pointer; char data begins at ptr+12. }
  for I := 0 to FStrLits.Count - 1 do
  begin
    StrLen := Length(FStrLits[I]);
    EmitLine(Format('data $__s%d = { w -1, w %d, w %d, b "%s", b 0 }',
      [I, StrLen, StrLen, QbeEscapeString(FStrLits[I])]));
  end;
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
          EmitLine(Format('  %%_var_%s =l alloc4 1', [VarName]));

        tyInt64:
          EmitLine(Format('  %%_var_%s =l alloc8 1', [VarName]));

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
          end;

        tyClass:
          begin
            { Class var holds a heap pointer — allocate one pointer slot, nil-init }
            EmitLine(Format('  %%_var_%s =l alloc8 1', [VarName]));
            EmitLine(Format('  storel 0, %%_var_%s', [VarName]));
          end;

      else
        raise ECodeGenError.CreateFmt(
          'Unsupported type kind %d for variable ''%s''',
          [Ord(Decl.ResolvedType.Kind), VarName]);
      end;
    end;
  end;
end;

procedure TCodeGenQBE.EmitStringCleanup(ABlock: TBlock);
var
  I, J:    Integer;
  Decl:    TVarDecl;
  VarName: string;
  ValTemp: string;
begin
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(ABlock.Decls[I]);
    if (Decl.ResolvedType <> nil) and Decl.ResolvedType.IsString then
      for J := 0 to Decl.Names.Count - 1 do
      begin
        VarName := Decl.Names[J];
        ValTemp := AllocTemp;
        EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, VarName]));
        EmitLine(Format('  call $_StringRelease(l %s)', [ValTemp]));
      end;
  end;
end;

procedure TCodeGenQBE.EmitBlock(ABlock: TBlock);
var
  I: Integer;
begin
  EmitVarAllocs(ABlock);
  for I := 0 to ABlock.Stmts.Count - 1 do
    EmitStmt(TASTStmt(ABlock.Stmts[I]));
  EmitStringCleanup(ABlock);
end;

procedure TCodeGenQBE.EmitStmt(AStmt: TASTStmt);
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
  else if AStmt is TAssignment then
    EmitAssignment(TAssignment(AStmt))
  else if AStmt is TMethodCallStmt then
    EmitMethodCall(TMethodCallStmt(AStmt))
  else if AStmt is TProcCall then
    EmitProcCall(TProcCall(AStmt))
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
  I: Integer;
begin
  { Simplified model: emit try body then finally body sequentially.
    Full stack-unwinding requires RTL support (future phase). }
  for I := 0 to AStmt.TryBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.TryBody.Stmts[I]));
  for I := 0 to AStmt.FinallyBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.FinallyBody.Stmts[I]));
end;

procedure TCodeGenQBE.EmitTryExceptStmt(AStmt: TTryExceptStmt);
var
  LblExcept: string;
  LblEnd:    string;
  I:         Integer;
begin
  LblExcept := AllocLabel('except_handler');
  LblEnd    := AllocLabel('except_end');

  { Emit try body — exception dispatch requires RTL support (future phase) }
  for I := 0 to AStmt.TryBody.Stmts.Count - 1 do
    EmitStmt(TASTStmt(AStmt.TryBody.Stmts[I]));

  { Skip except handler in normal execution }
  EmitLine(Format('  jmp @%s', [LblEnd]));

  { Except handler block — reachable only via raise dispatch (future) }
  EmitLine('@' + LblExcept);
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
  EmitStmt(AStmt.Body);

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
  EmitStmt(AStmt.Body);
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
begin
  if AAssign.Expr.ResolvedType = nil then
    raise ECodeGenError.CreateFmt(
      'Expression in assignment to ''%s'' has no resolved type', [AAssign.Name]);

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
  else
  begin
    QType   := QbeTypeOf(AAssign.Expr.ResolvedType);
    ValTemp := EmitExpr(AAssign.Expr);
    if QType = 'w' then StoreInstr := 'storew'
                   else StoreInstr := 'storel';
    EmitLine(Format('  %s %s, %%_var_%s', [StoreInstr, ValTemp, AAssign.Name]));
  end;
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
  Ptr, PtrTemp, ValTemp, QType, StoreInstr: string;
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

  QType := QbeTypeOf(AAssign.FieldInfo.TypeDesc);
  if QType = 'w' then StoreInstr := 'storew'
                 else StoreInstr := 'storel';
  EmitLine(Format('  %s %s, %s', [StoreInstr, ValTemp, Ptr]));
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
begin
  RT     := TRecordTypeDesc(ACall.ResolvedClassType);
  MDecl  := TMethodDecl(ACall.ResolvedMethod);

  { Load the object pointer (Self) from the caller's variable slot }
  SelfTemp := AllocTemp;
  EmitLine(Format('  %s =l loadl %%_var_%s', [SelfTemp, ACall.ObjectName]));

  { Use OwnerTypeName so inherited methods resolve to the defining class }
  if MDecl.OwnerTypeName <> '' then
    FuncName := '$' + MDecl.OwnerTypeName + '_' + ACall.Name
  else
    FuncName := '$' + RT.Name + '_' + ACall.Name;

  { Build argument string: l Self, then each explicit arg }
  ArgLine := Format('l %s', [SelfTemp]);
  for I := 0 to ACall.Args.Count - 1 do
  begin
    Par     := TMethodParam(MDecl.Params[I]);
    ArgTemp := EmitExpr(TASTExpr(ACall.Args[I]));
    QType   := QbeTypeOf(Par.ResolvedType);
    ArgLine := ArgLine + Format(', %s %s', [QType, ArgTemp]);
  end;

  EmitLine(Format('  call %s(%s)', [FuncName, ArgLine]));
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
  Sig:      string;
  I:        Integer;
  Par:      TMethodParam;
  FuncName: string;
  IsFunc:   Boolean;
  RetQType: string;
  RetTemp:  string;
begin
  FuncName := '$' + ATypeName + '_' + AMethod.Name;
  IsFunc   := AMethod.ResolvedReturnType <> nil;

  { Build parameter signature: l %_par_Self [, qtype %_par_Name ...] }
  Sig := 'l %_par_Self';
  for I := 0 to AMethod.Params.Count - 1 do
  begin
    Par := TMethodParam(AMethod.Params[I]);
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

  EmitBlock(AMethod.Body);

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

procedure TCodeGenQBE.EmitMethodDefs(AProg: TProgram);
var
  I, J: Integer;
  TD:   TTypeDecl;
  CD:   TClassTypeDef;
begin
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls[I]);
    if not (TD.Def is TClassTypeDef) then
      Continue;
    CD := TClassTypeDef(TD.Def);
    for J := 0 to CD.Methods.Count - 1 do
      EmitMethodDef(TD.Name, TMethodDecl(CD.Methods[J]));
  end;
end;

procedure TCodeGenQBE.EmitFuncDef(ADecl: TMethodDecl; AExported: Boolean);
var
  Sig:      string;
  I:        Integer;
  Par:      TMethodParam;
  FuncName: string;
  IsFunc:   Boolean;
  RetQType: string;
  RetTemp:  string;
  ValTemp:  string;
  Prefix:   string;
begin
  FuncName := '$' + ADecl.Name;
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

  { ARC: addref string value params on entry (callee owns a copy) }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params[I]);
    if (not Par.IsVarParam) and (Par.ResolvedType.Kind = tyString) then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_StringAddRef(l %s)', [ValTemp]));
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

  EmitBlock(ADecl.Body);

  { ARC: release string value params on exit }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params[I]);
    if (not Par.IsVarParam) and (Par.ResolvedType.Kind = tyString) then
    begin
      ValTemp := AllocTemp;
      EmitLine(Format('  %s =l loadl %%_var_%s', [ValTemp, Par.ParamName]));
      EmitLine(Format('  call $_StringRelease(l %s)', [ValTemp]));
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
  I: Integer;
begin
  for I := 0 to AProg.Block.ProcDecls.Count - 1 do
    EmitStandaloneDef(TMethodDecl(AProg.Block.ProcDecls[I]));
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
    EmitLine(Format('  call $%s(%s)', [ACall.Name, ArgLine]));
    Exit;
  end;

  { Built-in }
  UCaseName := UpperCase(ACall.Name);
  if UCaseName = 'WRITELN' then
    EmitWrite(ACall, True)
  else if UCaseName = 'WRITE' then
    EmitWrite(ACall, False)
  else
    raise ECodeGenError.CreateFmt(
      'Unknown procedure ''%s'' at line %d', [ACall.Name, ACall.Line]);
end;

procedure TCodeGenQBE.EmitWrite(ACall: TProcCall; ANewline: Boolean);
var
  ArgExpr:  TASTExpr;
  ArgTemp:  string;
  CharPtr:  string;
  FmtLabel: string;
  IsString: Boolean;
begin
  if ACall.Args.Count = 0 then
  begin
    if ANewline then
      EmitLine('  call $printf(l $__fmt_nl)');
    Exit;
  end;

  if ACall.Args.Count > 1 then
    raise ECodeGenError.CreateFmt(
      'Write/WriteLn takes at most 1 argument (line %d)', [ACall.Line]);

  ArgExpr  := TASTExpr(ACall.Args[0]);
  IsString := (ArgExpr.ResolvedType <> nil) and ArgExpr.ResolvedType.IsString;
  ArgTemp  := EmitExpr(ArgExpr);

  if IsString then
    FmtLabel := IfThen(ANewline, '$__fmt_s_nl', '$__fmt_s')
  else
    FmtLabel := IfThen(ANewline, '$__fmt_d_nl', '$__fmt_d');

  if IsString then
  begin
    { String pointer is the header pointer; char data starts at ptr+12. }
    CharPtr := AllocTemp;
    EmitLine(Format('  %s =l add %s, 12', [CharPtr, ArgTemp]));
    EmitLine(Format('  call $printf(l %s, ..., l %s)', [FmtLabel, CharPtr]));
  end
  else
    EmitLine(Format('  call $printf(l %s, ..., w %s)', [FmtLabel, ArgTemp]));
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
begin
  if AExpr is TFuncCallExpr then
  begin
    { Standalone function call expression }
    with TFuncCallExpr(AExpr) do
    begin
      MDecl    := TMethodDecl(ResolvedDecl);
      QType    := QbeTypeOf(MDecl.ResolvedReturnType);
      FuncName := '$' + Name;
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
      Par     := TMethodParam(MDecl.Params[I]);
      ArgTemp := EmitExpr(TASTExpr(MCallExpr.Args[I]));
      ArgLine := ArgLine + Format(', %s %s', [QbeTypeOf(Par.ResolvedType), ArgTemp]);
    end;

    T := AllocTemp;
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
    if FldAccess.IsConstructorCall then
    begin
      { TypeName.Create — allocate instance on heap }
      T := AllocTemp;
      EmitLine(Format('  %s =l call $malloc(l %d)',
        [T, TRecordTypeDesc(FldAccess.ResolvedType).TotalSize]));
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
    if TIdentExpr(AExpr).IsVarParam then
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
      else
        Op := 'add';
      end;
      EmitLine(Format('  %s =w %s %s, %s', [T, Op, L, R]));
    end;
    Result := T;
  end
  else
    raise ECodeGenError.Create('Unknown expression node type');
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
      EmitMethodDefs(AProg);
      EmitStandaloneDefs(AProg);
      EmitMainHeader;
      EmitBlock(AProg.Block);
      EmitMainFooter;
    finally
      FOutput := SavedOutput;
    end;

    EmitLine('# Generated by Blaise Compiler (Phase 2)');
    EmitLine('# Source: ' + AProg.Name);
    EmitLine('');
    EmitDataSection;
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
