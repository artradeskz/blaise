unit uSemantic;

{$mode objfpc}{$H+}

// Semantic analysis pass — walks the AST produced by uParser and:
//   1. Resolves record/class type declarations and registers them in the symbol table.
//   2. Indexes class methods for dispatch lookup.
//   3. Analyses method bodies with Self and explicit params in scope.
//   4. Resolves every identifier to a TSymbol in the symbol table.
//   5. Infers and annotates every expression node with ResolvedType.
//   6. Type-checks assignments, field assignments, and method calls.
//   7. Validates procedure/function calls.
//   8. Raises ESemanticError with source position on any violation.

interface

uses
  SysUtils, Classes, contnrs, uAST, uSymbolTable;

type
  ESemanticError = class(Exception);

  TSemanticAnalyser = class
  private
    FTable:       TSymbolTable;
    FProg:        TProgram;      { current program being analysed; set in Analyse }
    FMethodIndex: TStringList;  { 'TypeName.MethodName' → TMethodDecl (not owned) }
    FProcIndex:   TStringList;  { 'ProcName' → TMethodDecl (not owned) }

    { Generic type instantiation: resolves 'TBox<Integer>' on demand. }
    function  FindTypeOrInstantiate(const AName: string): TTypeDesc;
    function  InstantiateGeneric(const ATypeName: string): TRecordTypeDesc;

    procedure AnalyseBlock(ABlock: TBlock);
    procedure AnalyseTypeDecls(ABlock: TBlock);
    procedure LinkClassMethodImpls(ABlock: TBlock);
    procedure AnalyseMethodBodies(ABlock: TBlock);
    procedure AnalyseMethodDecl(AMethod: TMethodDecl; AClassType: TRecordTypeDesc);
    procedure AnalyseStandaloneDecls(ABlock: TBlock);
    procedure AnalyseStandaloneBodies(ABlock: TBlock);
    procedure AnalyseStandaloneDecl(ADecl: TMethodDecl);
    procedure AnalyseVarDecls(ABlock: TBlock);
    procedure AnalyseStmts(ABlock: TBlock);
    procedure AnalyseStmt(AStmt: TASTStmt);
    procedure AnalyseAssignment(AAssign: TAssignment);
    procedure AnalyseFieldAssignment(AAssign: TFieldAssignment);
    procedure AnalyseProcCall(ACall: TProcCall);
    procedure AnalyseMethodCall(ACall: TMethodCallStmt);
    function  AnalyseMethodCallExpr(AExpr: TMethodCallExpr): TTypeDesc;
    function  AnalyseFuncCallExpr(AExpr: TFuncCallExpr): TTypeDesc;
    function  AnalyseExpr(AExpr: TASTExpr): TTypeDesc;
    function  AnalyseBinaryExpr(ABin: TBinaryExpr): TTypeDesc;
    function  AnalyseFieldAccess(AAccess: TFieldAccessExpr): TTypeDesc;
    function  AnalyseIsExpr(AExpr: TIsExpr): TTypeDesc;
    function  AnalyseAsExpr(AExpr: TAsExpr): TTypeDesc;

    procedure AnalyseCompoundBody(ABody: TCompoundStmt);
    function  FindMethodDecl(const ATypeName, AMethodName: string): TMethodDecl;

    procedure SemanticError(const AMsg: string; ALine, ACol: Integer);
    procedure CheckTypesMatch(AExpected, AActual: TTypeDesc;
      const AContext: string; ALine, ACol: Integer);
    { Returns True if AActual is AExpected or a subclass of AExpected. }
    function  IsSubtypeOf(AActual, AExpected: TTypeDesc): Boolean;
  public
    constructor Create;
    destructor Destroy; override;
    procedure Analyse(AProg: TProgram);
    procedure AnalyseUnit(AUnit: TUnit);
  end;

implementation

constructor TSemanticAnalyser.Create;
begin
  inherited Create;
  FTable       := TSymbolTable.Create;
  FMethodIndex := TStringList.Create;
  FMethodIndex.CaseSensitive := False;
  FProcIndex   := TStringList.Create;
  FProcIndex.CaseSensitive := False;
end;

destructor TSemanticAnalyser.Destroy;
begin
  FProcIndex.Free;
  FMethodIndex.Free;
  FTable.Free;
  inherited Destroy;
end;

procedure TSemanticAnalyser.SemanticError(const AMsg: string; ALine, ACol: Integer);
begin
  raise ESemanticError.CreateFmt('%s at line %d col %d', [AMsg, ALine, ACol]);
end;

function TSemanticAnalyser.IsSubtypeOf(AActual, AExpected: TTypeDesc): Boolean;
var
  Walk: TRecordTypeDesc;
begin
  Result := AActual = AExpected;
  if Result then Exit;
  if (AActual = nil) or (AExpected = nil) then Exit;
  if (AActual.Kind <> tyClass) or (AExpected.Kind <> tyClass) then Exit;
  Walk := TRecordTypeDesc(AActual).Parent;
  while Walk <> nil do
  begin
    if Walk = AExpected then
    begin
      Result := True;
      Exit;
    end;
    Walk := Walk.Parent;
  end;
end;

procedure TSemanticAnalyser.CheckTypesMatch(AExpected, AActual: TTypeDesc;
  const AContext: string; ALine, ACol: Integer);
var
  RT: TRecordTypeDesc;
  I:  Integer;
begin
  if AExpected = AActual then
    Exit;
  { nil is compatible with any class or interface type }
  if (AActual.Kind = tyNil) and (AExpected.Kind in [tyClass, tyInterface]) then
    Exit;
  { subtype assignment: TDerived → TBase is allowed }
  if IsSubtypeOf(AActual, AExpected) then
    Exit;
  { class → interface: allowed when the class implements that interface }
  if (AExpected.Kind = tyInterface) and (AActual.Kind = tyClass) then
  begin
    RT := TRecordTypeDesc(AActual);
    for I := 0 to RT.ImplementsCount - 1 do
      if RT.ImplementsIntfAt(I) = AExpected then
        Exit;
  end;
  SemanticError(
    Format('Type mismatch in %s: expected ''%s'' but got ''%s''',
      [AContext, AExpected.Name, AActual.Name]),
    ALine, ACol);
end;

procedure TSemanticAnalyser.Analyse(AProg: TProgram);
begin
  FProg := AProg;
  AnalyseBlock(AProg.Block);
  { Transfer symbol table ownership to the program so that TTypeDesc
    objects (referenced by ResolvedType pointers on AST nodes) outlive
    this analyser. }
  AProg.SymbolTable := FTable;
  FTable := nil;
end;

procedure TSemanticAnalyser.AnalyseUnit(AUnit: TUnit);
var
  I, J:     Integer;
  MDecl:    TMethodDecl;
  ImplDecl: TMethodDecl;
  ImplIdx:  Integer;
  Par:      TMethodParam;
  ParType:  TTypeDesc;
  Sym:      TSymbol;
begin
  FTable.PushScope;
  try
    { Resolve interface type declarations }
    AnalyseTypeDecls(AUnit.IntfBlock);

    { Register interface forward declaration signatures }
    for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
    begin
      MDecl := TMethodDecl(AUnit.IntfBlock.ProcDecls[I]);

      for J := 0 to MDecl.Params.Count - 1 do
      begin
        Par     := TMethodParam(MDecl.Params[J]);
        ParType := FTable.FindType(Par.TypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown type ''%s'' for parameter ''%s''',
              [Par.TypeName, Par.ParamName]),
            MDecl.Line, MDecl.Col);
        Par.ResolvedType := ParType;
      end;

      if MDecl.ReturnTypeName <> '' then
      begin
        ParType := FTable.FindType(MDecl.ReturnTypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown return type ''%s'' for ''%s''',
              [MDecl.ReturnTypeName, MDecl.Name]),
            MDecl.Line, MDecl.Col);
        MDecl.ResolvedReturnType := ParType;
      end;

      FProcIndex.AddObject(MDecl.Name, MDecl);

      if MDecl.ReturnTypeName <> '' then
        Sym := TSymbol.Create(MDecl.Name, skFunction, MDecl.ResolvedReturnType)
      else
        Sym := TSymbol.Create(MDecl.Name, skProcedure, nil);
      if not FTable.Define(Sym) then
      begin
        Sym.Free;
        SemanticError(Format('Duplicate identifier ''%s''', [MDecl.Name]),
          MDecl.Line, MDecl.Col);
      end;
    end;

    { Process implementation declarations }
    for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
    begin
      ImplDecl := TMethodDecl(AUnit.ImplBlock.ProcDecls[I]);

      for J := 0 to ImplDecl.Params.Count - 1 do
      begin
        Par     := TMethodParam(ImplDecl.Params[J]);
        ParType := FTable.FindType(Par.TypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown type ''%s'' for parameter ''%s''',
              [Par.TypeName, Par.ParamName]),
            ImplDecl.Line, ImplDecl.Col);
        Par.ResolvedType := ParType;
      end;

      if ImplDecl.ReturnTypeName <> '' then
      begin
        ParType := FTable.FindType(ImplDecl.ReturnTypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown return type ''%s'' for ''%s''',
              [ImplDecl.ReturnTypeName, ImplDecl.Name]),
            ImplDecl.Line, ImplDecl.Col);
        ImplDecl.ResolvedReturnType := ParType;
      end;

      ImplIdx := FProcIndex.IndexOf(ImplDecl.Name);
      if ImplIdx >= 0 then
      begin
        { Matched an interface forward decl — verify param count }
        MDecl := TMethodDecl(FProcIndex.Objects[ImplIdx]);
        if MDecl.Params.Count <> ImplDecl.Params.Count then
          SemanticError(
            Format('Signature mismatch for ''%s'': interface has %d params, implementation has %d',
              [ImplDecl.Name, MDecl.Params.Count, ImplDecl.Params.Count]),
            ImplDecl.Line, ImplDecl.Col);
        { Update index to point to the full implementation }
        FProcIndex.Objects[ImplIdx] := ImplDecl;
      end
      else
      begin
        { Impl-only declaration — register symbol and index it }
        FProcIndex.AddObject(ImplDecl.Name, ImplDecl);
        if ImplDecl.ReturnTypeName <> '' then
          Sym := TSymbol.Create(ImplDecl.Name, skFunction, ImplDecl.ResolvedReturnType)
        else
          Sym := TSymbol.Create(ImplDecl.Name, skProcedure, nil);
        if not FTable.Define(Sym) then
        begin
          Sym.Free;
          SemanticError(Format('Duplicate identifier ''%s''', [ImplDecl.Name]),
            ImplDecl.Line, ImplDecl.Col);
        end;
      end;
    end;

    { Verify every interface declaration has a matching implementation }
    for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
    begin
      MDecl   := TMethodDecl(AUnit.IntfBlock.ProcDecls[I]);
      ImplIdx := FProcIndex.IndexOf(MDecl.Name);
      if (ImplIdx < 0) or
         (TMethodDecl(FProcIndex.Objects[ImplIdx]).Body = nil) then
        SemanticError(
          Format('Interface function ''%s'' has no implementation', [MDecl.Name]),
          MDecl.Line, MDecl.Col);
    end;

    { Analyse all implementation bodies }
    for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
      AnalyseStandaloneDecl(TMethodDecl(AUnit.ImplBlock.ProcDecls[I]));
  finally
    FTable.PopScope;
  end;
end;

procedure TSemanticAnalyser.LinkClassMethodImpls(ABlock: TBlock);
var
  I:    Integer;
  Decl: TMethodDecl;
  Key:  string;
  Idx:  Integer;
  CD:   TMethodDecl;
begin
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(ABlock.ProcDecls[I]);
    if Decl.OwnerTypeName = '' then Continue;
    Key := Decl.OwnerTypeName + '.' + Decl.Name;
    Idx := FMethodIndex.IndexOf(Key);
    if Idx < 0 then
      SemanticError(
        Format('Method ''%s'' is not declared in class ''%s''',
          [Decl.Name, Decl.OwnerTypeName]),
        Decl.Line, Decl.Col);
    CD := TMethodDecl(FMethodIndex.Objects[Idx]);
    if CD.Body <> nil then
      SemanticError(
        Format('Method ''%s.%s'' already has an inline body',
          [Decl.OwnerTypeName, Decl.Name]),
        Decl.Line, Decl.Col);
    { Transfer the body; after this, AnalyseMethodBodies will find and analyse it }
    CD.Body   := Decl.Body;
    Decl.Body := nil;
  end;
end;

function TSemanticAnalyser.FindTypeOrInstantiate(const AName: string): TTypeDesc;
begin
  Result := FTable.FindType(AName);
  if (Result = nil) and (Pos('<', AName) > 0) then
    Result := InstantiateGeneric(AName);
end;

function TSemanticAnalyser.InstantiateGeneric(const ATypeName: string): TRecordTypeDesc;
var
  BracPos:  Integer;
  BaseName: string;
  ArgsStr:  string;
  Args:     TStringList;
  Templ:    TGenericTypeDef;
  ClonedCD: TClassTypeDef;
  I, J, K:  Integer;
  FDecl:    TFieldDecl;
  NewFDecl: TFieldDecl;
  MDecl:    TMethodDecl;
  NewMDecl: TMethodDecl;
  Par:      TMethodParam;
  NewPar:   TMethodParam;
  Sym:      TSymbol;
  Key:      string;
  FldType:  TTypeDesc;
  FldName:  string;
  ParType:  TTypeDesc;
  RT:       TRecordTypeDesc;
  GI:       TGenericInstance;
  Subst:    string;
begin
  Result := nil;

  { Parse 'BaseName<Arg1,Arg2>' }
  BracPos := Pos('<', ATypeName);
  if BracPos = 0 then Exit;
  BaseName := Copy(ATypeName, 1, BracPos - 1);
  ArgsStr  := Copy(ATypeName, BracPos + 1, Length(ATypeName) - BracPos - 1);

  Args := TStringList.Create;
  try
    while ArgsStr <> '' do
    begin
      BracPos := Pos(',', ArgsStr);
      if BracPos > 0 then
      begin
        Args.Add(Trim(Copy(ArgsStr, 1, BracPos - 1)));
        ArgsStr := Trim(Copy(ArgsStr, BracPos + 1, MaxInt));
      end
      else
      begin
        Args.Add(Trim(ArgsStr));
        ArgsStr := '';
      end;
    end;

    Templ := TGenericTypeDef(FTable.FindGeneric(BaseName));
    if Templ = nil then Exit;
    if Args.Count <> Templ.ParamNames.Count then Exit;

    { Create the concrete class type descriptor — defined globally so the
      symbol survives scope pops and is visible after analysis completes. }
    RT  := FTable.NewClassType(ATypeName);
    Sym := TSymbol.Create(ATypeName, skType, RT);
    FTable.DefineGlobal(Sym);

    { Build substituted clone of the class definition }
    ClonedCD             := TClassTypeDef.Create;
    ClonedCD.ParentName  := Templ.ClassDef.ParentName;
    for I := 0 to Templ.ClassDef.ImplementsNames.Count - 1 do
      ClonedCD.ImplementsNames.Add(Templ.ClassDef.ImplementsNames[I]);

    { Clone fields with type-param substitution }
    for I := 0 to Templ.ClassDef.Fields.Count - 1 do
    begin
      FDecl    := TFieldDecl(Templ.ClassDef.Fields[I]);
      NewFDecl := TFieldDecl.Create;
      for J := 0 to FDecl.Names.Count - 1 do
        NewFDecl.Names.Add(FDecl.Names[J]);
      Subst := FDecl.TypeName;
      for K := 0 to Templ.ParamNames.Count - 1 do
        if SameText(Subst, Templ.ParamNames[K]) then
        begin
          Subst := Args[K];
          Break;
        end;
      NewFDecl.TypeName := Subst;
      ClonedCD.Fields.Add(NewFDecl);
    end;

    { Clone method declarations (shared body — OwnBody = False) }
    for I := 0 to Templ.ClassDef.Methods.Count - 1 do
    begin
      MDecl            := TMethodDecl(Templ.ClassDef.Methods[I]);
      NewMDecl         := TMethodDecl.Create;
      NewMDecl.Name          := MDecl.Name;
      NewMDecl.OwnerTypeName := ATypeName;
      NewMDecl.IsVirtual     := MDecl.IsVirtual;
      NewMDecl.IsOverride    := MDecl.IsOverride;
      NewMDecl.Body          := MDecl.Body;
      NewMDecl.OwnBody       := False;

      for J := 0 to MDecl.Params.Count - 1 do
      begin
        Par    := TMethodParam(MDecl.Params[J]);
        NewPar := TMethodParam.Create;
        NewPar.ParamName  := Par.ParamName;
        NewPar.IsVarParam := Par.IsVarParam;
        Subst := Par.TypeName;
        for K := 0 to Templ.ParamNames.Count - 1 do
          if SameText(Subst, Templ.ParamNames[K]) then
          begin
            Subst := Args[K];
            Break;
          end;
        NewPar.TypeName := Subst;
        NewMDecl.Params.Add(NewPar);
      end;

      Subst := MDecl.ReturnTypeName;
      for K := 0 to Templ.ParamNames.Count - 1 do
        if SameText(Subst, Templ.ParamNames[K]) then
        begin
          Subst := Args[K];
          Break;
        end;
      NewMDecl.ReturnTypeName := Subst;

      ClonedCD.Methods.Add(NewMDecl);
    end;

    { Pre-pass: vtable slots (before fields so vptr is counted in offsets) }
    for J := 0 to ClonedCD.Methods.Count - 1 do
    begin
      NewMDecl := TMethodDecl(ClonedCD.Methods[J]);
      if NewMDecl.IsVirtual then
        RT.AddVTableSlot(NewMDecl.Name, '$' + ATypeName + '_' + NewMDecl.Name)
      else if NewMDecl.IsOverride then
        RT.OverrideVTableSlot(
          RT.FindVTableSlot(NewMDecl.Name),
          '$' + ATypeName + '_' + NewMDecl.Name);
    end;

    { Resolve fields }
    for J := 0 to ClonedCD.Fields.Count - 1 do
    begin
      NewFDecl := TFieldDecl(ClonedCD.Fields[J]);
      FldType  := FindTypeOrInstantiate(NewFDecl.TypeName);
      if FldType = nil then
        SemanticError(
          Format('Unknown type ''%s'' for field in ''%s''', [NewFDecl.TypeName, ATypeName]),
          0, 0);
      NewFDecl.ResolvedType := FldType;
      for K := 0 to NewFDecl.Names.Count - 1 do
      begin
        FldName := NewFDecl.Names[K];
        RT.AddField(FldName, FldType);
      end;
    end;

    { Resolve method signatures and index them }
    for J := 0 to ClonedCD.Methods.Count - 1 do
    begin
      NewMDecl := TMethodDecl(ClonedCD.Methods[J]);
      Key      := ATypeName + '.' + NewMDecl.Name;
      FMethodIndex.AddObject(Key, NewMDecl);

      if NewMDecl.IsVirtual or NewMDecl.IsOverride then
        NewMDecl.VTableSlot := RT.FindVTableSlot(NewMDecl.Name);

      for K := 0 to NewMDecl.Params.Count - 1 do
      begin
        Par     := TMethodParam(NewMDecl.Params[K]);
        ParType := FindTypeOrInstantiate(Par.TypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown type ''%s'' for param ''%s'' in ''%s''',
              [Par.TypeName, Par.ParamName, ATypeName]),
            0, 0);
        Par.ResolvedType := ParType;
      end;

      if NewMDecl.ReturnTypeName <> '' then
      begin
        ParType := FindTypeOrInstantiate(NewMDecl.ReturnTypeName);
        if ParType = nil then
          SemanticError(
            Format('Unknown return type ''%s'' for method ''%s'' in ''%s''',
              [NewMDecl.ReturnTypeName, NewMDecl.Name, ATypeName]),
            0, 0);
        NewMDecl.ResolvedReturnType := ParType;
      end;
    end;

    { Analyse method bodies with concrete types in scope }
    for J := 0 to ClonedCD.Methods.Count - 1 do
    begin
      NewMDecl := TMethodDecl(ClonedCD.Methods[J]);
      if NewMDecl.Body <> nil then
        AnalyseMethodDecl(NewMDecl, RT);
    end;

    { Register the instantiation for codegen }
    GI          := TGenericInstance.Create;
    GI.TypeName := ATypeName;
    GI.ClassDef := ClonedCD;
    GI.TypeDesc := RT;
    FProg.GenericInstances.Add(GI);

    Result := RT;
  finally
    Args.Free;
  end;
end;

procedure TSemanticAnalyser.AnalyseBlock(ABlock: TBlock);
begin
  { Type declarations are registered in the outer scope so they remain visible
    after the block scope is popped — needed for var declarations and the
    transferred symbol table used by codegen. }
  AnalyseTypeDecls(ABlock);
  { Link standalone TTypeName.MethodName implementations to their class method
    declarations, transferring the body so AnalyseMethodBodies can process it. }
  LinkClassMethodImpls(ABlock);
  AnalyseMethodBodies(ABlock);
  FTable.PushScope;
  try
    AnalyseVarDecls(ABlock);
    { Register standalone proc/func signatures before analysing bodies so that
      mutually-recursive calls resolve correctly. }
    AnalyseStandaloneDecls(ABlock);
    AnalyseStandaloneBodies(ABlock);
    AnalyseStmts(ABlock);
  finally
    FTable.PopScope;
  end;
end;

procedure TSemanticAnalyser.AnalyseTypeDecls(ABlock: TBlock);
var
  I, J, K:    Integer;
  L:          Integer;
  TD:         TTypeDecl;
  FieldList:  TObjectList;
  MethodList: TObjectList;
  FDecl:      TFieldDecl;
  MDecl:      TMethodDecl;
  Par:        TMethodParam;
  ParType:    TTypeDesc;
  RT:         TRecordTypeDesc;
  ParentRT:   TRecordTypeDesc;
  ParentSym:  TSymbol;
  FldType:    TTypeDesc;
  FldName:    string;
  Sym:        TSymbol;
  Key:        string;
  FldInfo:    TFieldInfo;
  IntfDesc:   TInterfaceTypeDesc;
  IntfName:   string;
  IntfSym:    TSymbol;
  ITD:        TInterfaceTypeDef;
begin
  { Pass 1 — register all type symbols with empty descriptors.
    This allows self-referential field types to resolve in pass 2. }
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls[I]);
    if TD.Def is TRecordTypeDef then
      RT := FTable.NewRecordType(TD.Name)
    else if TD.Def is TClassTypeDef then
      RT := FTable.NewClassType(TD.Name)
    else if TD.Def is TGenericTypeDef then
    begin
      { Register as template — no concrete type symbol; instantiated on demand }
      FTable.RegisterGeneric(TD.Name, TD.Def);
      Continue;
    end
    else if TD.Def is TInterfaceTypeDef then
    begin
      IntfDesc := FTable.NewInterfaceType(TD.Name);
      Sym      := TSymbol.Create(TD.Name, skType, IntfDesc);
      if not FTable.Define(Sym) then
      begin
        Sym.Free;
        SemanticError(Format('Duplicate type name ''%s''', [TD.Name]), TD.Line, TD.Col);
      end;
      Continue;
    end
    else
    begin
      SemanticError('Only record, class, or interface type definitions are supported',
        TD.Line, TD.Col);
      Continue;
    end;
    Sym := TSymbol.Create(TD.Name, skType, RT);
    if not FTable.Define(Sym) then
    begin
      Sym.Free;
      SemanticError(Format('Duplicate type name ''%s''', [TD.Name]), TD.Line, TD.Col);
    end;
  end;

  { Pass 2 — resolve parent, fields, and method signatures for each type. }
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls[I]);

    { Generic templates have no concrete descriptor — skip }
    if TD.Def is TGenericTypeDef then Continue;

    { Interface types: register methods and resolve optional parent }
    if TD.Def is TInterfaceTypeDef then
    begin
      ITD      := TInterfaceTypeDef(TD.Def);
      IntfSym  := FTable.Lookup(TD.Name);
      IntfDesc := TInterfaceTypeDesc(IntfSym.TypeDesc);
      if ITD.ParentName <> '' then
      begin
        Sym := FTable.Lookup(ITD.ParentName);
        if (Sym = nil) or not (Sym.TypeDesc is TInterfaceTypeDesc) then
          SemanticError(
            Format('Unknown parent interface ''%s'' for ''%s''',
              [ITD.ParentName, TD.Name]),
            TD.Line, TD.Col);
        IntfDesc.Parent := TInterfaceTypeDesc(Sym.TypeDesc);
        { Inherit parent methods }
        for J := 0 to IntfDesc.Parent.MethodCount - 1 do
          IntfDesc.AddMethod(IntfDesc.Parent.MethodName(J));
      end;
      for J := 0 to ITD.Methods.Count - 1 do
        IntfDesc.AddMethod(TMethodDecl(ITD.Methods[J]).Name);
      Continue;
    end;

    Sym := FTable.Lookup(TD.Name);
    RT  := TRecordTypeDesc(Sym.TypeDesc);

    if TD.Def is TRecordTypeDef then
    begin
      FieldList  := TRecordTypeDef(TD.Def).Fields;
      MethodList := nil;
    end
    else
    begin
      FieldList  := TClassTypeDef(TD.Def).Fields;
      MethodList := TClassTypeDef(TD.Def).Methods;

      { Copy inherited fields and vtable from parent class first }
      if TClassTypeDef(TD.Def).ParentName <> '' then
      begin
        ParentSym := FTable.Lookup(TClassTypeDef(TD.Def).ParentName);
        if (ParentSym = nil) or not (ParentSym.TypeDesc is TRecordTypeDesc) then
          SemanticError(
            Format('Unknown parent class ''%s'' for ''%s''',
              [TClassTypeDef(TD.Def).ParentName, TD.Name]),
            TD.Line, TD.Col);
        ParentRT     := TRecordTypeDesc(ParentSym.TypeDesc);
        RT.Parent    := ParentRT;
        RT.CopyVTableFrom(ParentRT);
        for K := 0 to ParentRT.Fields.Count - 1 do
        begin
          FldInfo := TFieldInfo(ParentRT.Fields[K]);
          RT.AddField(FldInfo.Name, FldInfo.TypeDesc);
        end;
      end;

      { Pre-pass: register vtable slots for virtual/override methods BEFORE
        adding own fields, so that field offsets correctly account for the vptr. }
      if MethodList <> nil then
        for J := 0 to MethodList.Count - 1 do
        begin
          MDecl := TMethodDecl(MethodList[J]);
          if MDecl.IsVirtual then
            RT.AddVTableSlot(MDecl.Name, '$' + TD.Name + '_' + MDecl.Name)
          else if MDecl.IsOverride then
            RT.OverrideVTableSlot(
              RT.FindVTableSlot(MDecl.Name),
              '$' + TD.Name + '_' + MDecl.Name);
        end;
    end;

    { Resolve own field declarations (offsets now include vptr if HasVTable) }
    for J := 0 to FieldList.Count - 1 do
    begin
      FDecl   := TFieldDecl(FieldList[J]);
      FldType := FTable.FindType(FDecl.TypeName);
      if FldType = nil then
        SemanticError(
          Format('Unknown type ''%s'' for field', [FDecl.TypeName]),
          FDecl.Line, FDecl.Col);
      FDecl.ResolvedType := FldType;
      for K := 0 to FDecl.Names.Count - 1 do
      begin
        FldName := FDecl.Names[K];
        RT.AddField(FldName, FldType);
      end;
    end;

    { Index class methods, record VTableSlot on MDecl, resolve param/return types }
    if MethodList <> nil then
      for J := 0 to MethodList.Count - 1 do
      begin
        MDecl               := TMethodDecl(MethodList[J]);
        MDecl.OwnerTypeName := TD.Name;
        Key                 := TD.Name + '.' + MDecl.Name;
        FMethodIndex.AddObject(Key, MDecl);

        { Retrieve the vtable slot assigned in the pre-pass above }
        if MDecl.IsVirtual or MDecl.IsOverride then
        begin
          MDecl.VTableSlot := RT.FindVTableSlot(MDecl.Name);
          if MDecl.IsOverride and (MDecl.VTableSlot < 0) then
            SemanticError(
              Format('Method ''%s'' marked override but no virtual base method found',
                [MDecl.Name]),
              MDecl.Line, MDecl.Col);
        end;

        for K := 0 to MDecl.Params.Count - 1 do
        begin
          Par     := TMethodParam(MDecl.Params[K]);
          ParType := FTable.FindType(Par.TypeName);
          if ParType = nil then
            SemanticError(
              Format('Unknown type ''%s'' for parameter ''%s''',
                [Par.TypeName, Par.ParamName]),
              MDecl.Line, MDecl.Col);
          Par.ResolvedType := ParType;
        end;

        if MDecl.ReturnTypeName <> '' then
        begin
          ParType := FTable.FindType(MDecl.ReturnTypeName);
          if ParType = nil then
            SemanticError(
              Format('Unknown return type ''%s'' for method ''%s''',
                [MDecl.ReturnTypeName, MDecl.Name]),
              MDecl.Line, MDecl.Col);
          MDecl.ResolvedReturnType := ParType;
        end;
      end;

    { Verify class implements all methods of each declared interface }
    if TD.Def is TClassTypeDef then
      for L := 0 to TClassTypeDef(TD.Def).ImplementsNames.Count - 1 do
      begin
        IntfName := TClassTypeDef(TD.Def).ImplementsNames[L];
        IntfSym  := FTable.Lookup(IntfName);
        if (IntfSym = nil) or not (IntfSym.TypeDesc is TInterfaceTypeDesc) then
          SemanticError(
            Format('Unknown interface ''%s'' in implements list of ''%s''',
              [IntfName, TD.Name]),
            TD.Line, TD.Col);
        IntfDesc := TInterfaceTypeDesc(IntfSym.TypeDesc);
        RT.AddImplements(IntfDesc);
        for J := 0 to IntfDesc.MethodCount - 1 do
        begin
          Key := IntfDesc.MethodName(J);
          if RT.FindField(Key) = nil then
          begin
            { Check method exists in class — search method list }
            MDecl := nil;
            if TD.Def is TClassTypeDef then
              for K := 0 to TClassTypeDef(TD.Def).Methods.Count - 1 do
                if SameText(TMethodDecl(TClassTypeDef(TD.Def).Methods[K]).Name, Key) then
                begin
                  MDecl := TMethodDecl(TClassTypeDef(TD.Def).Methods[K]);
                  Break;
                end;
            if MDecl = nil then
              SemanticError(
                Format('Class ''%s'' does not implement method ''%s'' from interface ''%s''',
                  [TD.Name, Key, IntfName]),
                TD.Line, TD.Col);
          end;
        end;
      end;
  end;
end;

procedure TSemanticAnalyser.AnalyseMethodBodies(ABlock: TBlock);
var
  I, J:  Integer;
  TD:    TTypeDecl;
  CD:    TClassTypeDef;
  RT:    TRecordTypeDesc;
  Sym:   TSymbol;
begin
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls[I]);
    if not (TD.Def is TClassTypeDef) then
      Continue;
    CD  := TClassTypeDef(TD.Def);
    Sym := FTable.Lookup(TD.Name);
    if (Sym = nil) or not (Sym.TypeDesc is TRecordTypeDesc) then
      Continue;
    RT := TRecordTypeDesc(Sym.TypeDesc);
    for J := 0 to CD.Methods.Count - 1 do
      AnalyseMethodDecl(TMethodDecl(CD.Methods[J]), RT);
  end;
end;

procedure TSemanticAnalyser.AnalyseMethodDecl(
  AMethod: TMethodDecl; AClassType: TRecordTypeDesc);
var
  I:    Integer;
  Par:  TMethodParam;
  Sym:  TSymbol;
begin
  FTable.PushScope;
  try
    { Define Self as a variable of the class type }
    Sym := TSymbol.Create('Self', skVariable, AClassType);
    FTable.Define(Sym);

    { For function methods, define Result as a writable variable }
    if AMethod.ResolvedReturnType <> nil then
    begin
      Sym := TSymbol.Create('Result', skVariable, AMethod.ResolvedReturnType);
      FTable.Define(Sym);
    end;

    { Define explicit parameters }
    for I := 0 to AMethod.Params.Count - 1 do
    begin
      Par := TMethodParam(AMethod.Params[I]);
      if Par.ResolvedType = nil then
        SemanticError(
          Format('Parameter ''%s'' has unresolved type', [Par.ParamName]),
          AMethod.Line, AMethod.Col);
      if Par.IsVarParam then
        Sym := TSymbol.Create(Par.ParamName, skVarParameter, Par.ResolvedType)
      else
        Sym := TSymbol.Create(Par.ParamName, skParameter, Par.ResolvedType);
      if not FTable.Define(Sym) then
      begin
        Sym.Free;
        SemanticError(
          Format('Duplicate parameter name ''%s''', [Par.ParamName]),
          AMethod.Line, AMethod.Col);
      end;
    end;

    { Analyse the method body block (pushes its own inner scope) }
    AnalyseBlock(AMethod.Body);
  finally
    FTable.PopScope;
  end;
end;

function TSemanticAnalyser.FindMethodDecl(
  const ATypeName, AMethodName: string): TMethodDecl;
var
  CurrName: string;
  Idx:      Integer;
  Key:      string;
  Sym:      TSymbol;
  RT:       TRecordTypeDesc;
begin
  CurrName := ATypeName;
  while CurrName <> '' do
  begin
    Key := CurrName + '.' + AMethodName;
    Idx := FMethodIndex.IndexOf(Key);
    if Idx >= 0 then
    begin
      Result := TMethodDecl(FMethodIndex.Objects[Idx]);
      Exit;
    end;
    { Walk to parent }
    Sym := FTable.Lookup(CurrName);
    if (Sym <> nil) and (Sym.TypeDesc is TRecordTypeDesc) then
    begin
      RT := TRecordTypeDesc(Sym.TypeDesc);
      if RT.Parent <> nil then
        CurrName := RT.Parent.Name
      else
        Break;
    end
    else
      Break;
  end;
  Result := nil;
end;

procedure TSemanticAnalyser.AnalyseStandaloneDecls(ABlock: TBlock);
var
  I, J:    Integer;
  ADecl:   TMethodDecl;
  Par:     TMethodParam;
  ParType: TTypeDesc;
  RetType: TTypeDesc;
  Sym:     TSymbol;
begin
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    ADecl := TMethodDecl(ABlock.ProcDecls[I]);
    { Class method implementations have their body transferred; skip them here }
    if ADecl.OwnerTypeName <> '' then Continue;

    { Resolve parameter types }
    for J := 0 to ADecl.Params.Count - 1 do
    begin
      Par     := TMethodParam(ADecl.Params[J]);
      ParType := FTable.FindType(Par.TypeName);
      if ParType = nil then
        SemanticError(
          Format('Unknown type ''%s'' for parameter ''%s'' of ''%s''',
            [Par.TypeName, Par.ParamName, ADecl.Name]),
          ADecl.Line, ADecl.Col);
      Par.ResolvedType := ParType;
    end;

    { Resolve return type for functions }
    if ADecl.ReturnTypeName <> '' then
    begin
      RetType := FTable.FindType(ADecl.ReturnTypeName);
      if RetType = nil then
        SemanticError(
          Format('Unknown return type ''%s'' for function ''%s''',
            [ADecl.ReturnTypeName, ADecl.Name]),
          ADecl.Line, ADecl.Col);
      ADecl.ResolvedReturnType := RetType;
    end;

    { Index for call resolution }
    FProcIndex.AddObject(ADecl.Name, ADecl);

    { Register in symbol table }
    if ADecl.ReturnTypeName <> '' then
      Sym := TSymbol.Create(ADecl.Name, skFunction, ADecl.ResolvedReturnType)
    else
      Sym := TSymbol.Create(ADecl.Name, skProcedure, nil);

    if not FTable.Define(Sym) then
    begin
      Sym.Free;
      SemanticError(
        Format('Duplicate identifier ''%s''', [ADecl.Name]),
        ADecl.Line, ADecl.Col);
    end;
  end;
end;

procedure TSemanticAnalyser.AnalyseStandaloneDecl(ADecl: TMethodDecl);
var
  I:   Integer;
  Par: TMethodParam;
  Sym: TSymbol;
begin
  FTable.PushScope;
  try
    { Define Result for functions }
    if ADecl.ResolvedReturnType <> nil then
    begin
      Sym := TSymbol.Create('Result', skVariable, ADecl.ResolvedReturnType);
      FTable.Define(Sym);
    end;

    { Define explicit parameters }
    for I := 0 to ADecl.Params.Count - 1 do
    begin
      Par := TMethodParam(ADecl.Params[I]);
      if Par.IsVarParam then
        Sym := TSymbol.Create(Par.ParamName, skVarParameter, Par.ResolvedType)
      else
        Sym := TSymbol.Create(Par.ParamName, skParameter, Par.ResolvedType);
      if not FTable.Define(Sym) then
      begin
        Sym.Free;
        SemanticError(
          Format('Duplicate parameter name ''%s''', [Par.ParamName]),
          ADecl.Line, ADecl.Col);
      end;
    end;

    AnalyseBlock(ADecl.Body);
  finally
    FTable.PopScope;
  end;
end;

procedure TSemanticAnalyser.AnalyseStandaloneBodies(ABlock: TBlock);
var
  I:     Integer;
  ADecl: TMethodDecl;
begin
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    ADecl := TMethodDecl(ABlock.ProcDecls[I]);
    { Class method implementations have their body transferred; skip them here }
    if ADecl.OwnerTypeName <> '' then Continue;
    AnalyseStandaloneDecl(ADecl);
  end;
end;

procedure TSemanticAnalyser.AnalyseVarDecls(ABlock: TBlock);
var
  I, J:    Integer;
  Decl:    TVarDecl;
  Typ:     TTypeDesc;
  VarName: string;
  Sym:     TSymbol;
begin
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    Decl := TVarDecl(ABlock.Decls[I]);

    Typ := FindTypeOrInstantiate(Decl.TypeName);
    if Typ = nil then
      SemanticError(
        Format('Unknown type ''%s''', [Decl.TypeName]),
        Decl.Line, Decl.Col);

    Decl.ResolvedType := Typ;

    for J := 0 to Decl.Names.Count - 1 do
    begin
      VarName := Decl.Names[J];
      Sym := TSymbol.Create(VarName, skVariable, Typ);
      if not FTable.Define(Sym) then
      begin
        Sym.Free;
        SemanticError(
          Format('Duplicate identifier ''%s''', [VarName]),
          Decl.Line, Decl.Col);
      end;
    end;
  end;
end;

procedure TSemanticAnalyser.AnalyseCompoundBody(ABody: TCompoundStmt);
var
  I: Integer;
begin
  for I := 0 to ABody.Stmts.Count - 1 do
    AnalyseStmt(TASTStmt(ABody.Stmts[I]));
end;

procedure TSemanticAnalyser.AnalyseStmts(ABlock: TBlock);
var
  I: Integer;
begin
  for I := 0 to ABlock.Stmts.Count - 1 do
    AnalyseStmt(TASTStmt(ABlock.Stmts[I]));
end;

procedure TSemanticAnalyser.AnalyseStmt(AStmt: TASTStmt);
var
  IfS:       TIfStmt;
  CmpS:      TCompoundStmt;
  ForS:      TForStmt;
  I:         Integer;
  CondType:  TTypeDesc;
  VarSym:    TSymbol;
  StartType: TTypeDesc;
  EndType:   TTypeDesc;
begin
  if AStmt is TForStmt then
  begin
    ForS := TForStmt(AStmt);
    VarSym := FTable.Lookup(ForS.VarName);
    if VarSym = nil then
      SemanticError(
        Format('Undeclared loop variable ''%s''', [ForS.VarName]),
        ForS.Line, ForS.Col);
    if VarSym.Kind <> skVariable then
      SemanticError(
        Format('''%s'' is not a variable', [ForS.VarName]),
        ForS.Line, ForS.Col);
    if not VarSym.TypeDesc.IsOrdinal then
      SemanticError(
        Format('Loop variable ''%s'' must be an ordinal type, got ''%s''',
          [ForS.VarName, VarSym.TypeDesc.Name]),
        ForS.Line, ForS.Col);
    StartType := AnalyseExpr(ForS.StartExpr);
    CheckTypesMatch(VarSym.TypeDesc, StartType,
      'for-loop start expression', ForS.Line, ForS.Col);
    EndType := AnalyseExpr(ForS.EndExpr);
    CheckTypesMatch(VarSym.TypeDesc, EndType,
      'for-loop end expression', ForS.Line, ForS.Col);
    AnalyseStmt(ForS.Body);
  end
  else if AStmt is TWhileStmt then
  begin
    with TWhileStmt(AStmt) do
    begin
      CondType := AnalyseExpr(Condition);
      if CondType.Kind <> tyBoolean then
        SemanticError(
          Format('while condition must be Boolean, got ''%s''', [CondType.Name]),
          AStmt.Line, AStmt.Col);
      AnalyseStmt(Body);
    end;
  end
  else if AStmt is TIfStmt then
  begin
    IfS      := TIfStmt(AStmt);
    CondType := AnalyseExpr(IfS.Condition);
    if CondType.Kind <> tyBoolean then
      SemanticError(
        Format('if condition must be Boolean, got ''%s''', [CondType.Name]),
        IfS.Line, IfS.Col);
    AnalyseStmt(IfS.ThenStmt);
    if IfS.ElseStmt <> nil then
      AnalyseStmt(IfS.ElseStmt);
  end
  else if AStmt is TCompoundStmt then
  begin
    CmpS := TCompoundStmt(AStmt);
    for I := 0 to CmpS.Stmts.Count - 1 do
      AnalyseStmt(TASTStmt(CmpS.Stmts[I]));
  end
  else if AStmt is TTryFinallyStmt then
  begin
    with TTryFinallyStmt(AStmt) do
    begin
      AnalyseCompoundBody(TryBody);
      AnalyseCompoundBody(FinallyBody);
    end;
  end
  else if AStmt is TTryExceptStmt then
  begin
    with TTryExceptStmt(AStmt) do
    begin
      AnalyseCompoundBody(TryBody);
      AnalyseCompoundBody(ExceptBody);
    end;
  end
  else if AStmt is TRaiseStmt then
  begin
    with TRaiseStmt(AStmt) do
    begin
      if Expr <> nil then
      begin
        CondType := AnalyseExpr(Expr);
        if CondType.Kind <> tyClass then
          SemanticError(
            Format('raise expression must be a class instance, got ''%s''',
              [CondType.Name]),
            AStmt.Line, AStmt.Col);
      end;
    end;
  end
  else if AStmt is TFieldAssignment then
    AnalyseFieldAssignment(TFieldAssignment(AStmt))
  else if AStmt is TAssignment then
    AnalyseAssignment(TAssignment(AStmt))
  else if AStmt is TMethodCallStmt then
    AnalyseMethodCall(TMethodCallStmt(AStmt))
  else if AStmt is TProcCall then
    AnalyseProcCall(TProcCall(AStmt));
end;

procedure TSemanticAnalyser.AnalyseMethodCall(ACall: TMethodCallStmt);
var
  ObjSym:  TSymbol;
  RT:      TRecordTypeDesc;
  MDecl:   TMethodDecl;
  Par:     TMethodParam;
  ArgType: TTypeDesc;
  I:       Integer;
begin
  ObjSym := FTable.Lookup(ACall.ObjectName);
  if ObjSym = nil then
    SemanticError(
      Format('Undeclared variable ''%s''', [ACall.ObjectName]),
      ACall.Line, ACall.Col);
  if ObjSym.Kind <> skVariable then
    SemanticError(
      Format('''%s'' is not a variable', [ACall.ObjectName]),
      ACall.Line, ACall.Col);
  if not (ObjSym.TypeDesc.Kind in [tyClass, tyInterface]) then
    SemanticError(
      Format('''%s'' is not a class or interface variable', [ACall.ObjectName]),
      ACall.Line, ACall.Col);

  { Interface method call: look up method in interface type descriptor }
  if ObjSym.TypeDesc.Kind = tyInterface then
  begin
    if not TInterfaceTypeDesc(ObjSym.TypeDesc).HasMethod(ACall.Name) then
      SemanticError(
        Format('Interface ''%s'' has no method ''%s''',
          [ObjSym.TypeDesc.Name, ACall.Name]),
        ACall.Line, ACall.Col);
    { Args for interface methods not checked in Phase 3 (no param info stored) }
    ACall.ResolvedClassType := ObjSym.TypeDesc;
    ACall.ResolvedMethod    := nil;  { nil = interface dispatch, not class dispatch }
    Exit;
  end;

  RT    := TRecordTypeDesc(ObjSym.TypeDesc);
  MDecl := FindMethodDecl(RT.Name, ACall.Name);
  if MDecl = nil then
  begin
    { Free is a built-in: if Self <> nil then free(Self). No user-defined method needed. }
    if SameText(ACall.Name, 'Free') and (ACall.Args.Count = 0) then
    begin
      ACall.ResolvedClassType := RT;
      ACall.ResolvedMethod    := nil;  { nil signals built-in Free to codegen }
      Exit;
    end;
    SemanticError(
      Format('Class ''%s'' has no method ''%s''', [RT.Name, ACall.Name]),
      ACall.Line, ACall.Col);
  end;

  if ACall.Args.Count <> MDecl.Params.Count then
    SemanticError(
      Format('Method ''%s.%s'' expects %d argument(s) but got %d',
        [RT.Name, ACall.Name, MDecl.Params.Count, ACall.Args.Count]),
      ACall.Line, ACall.Col);

  for I := 0 to ACall.Args.Count - 1 do
  begin
    ArgType := AnalyseExpr(TASTExpr(ACall.Args[I]));
    Par     := TMethodParam(MDecl.Params[I]);
    CheckTypesMatch(Par.ResolvedType, ArgType,
      Format('argument %d of ''%s''', [I + 1, ACall.Name]),
      ACall.Line, ACall.Col);
  end;

  ACall.ResolvedClassType := RT;
  ACall.ResolvedMethod    := MDecl;
end;

procedure TSemanticAnalyser.AnalyseAssignment(AAssign: TAssignment);
var
  VarSym:   TSymbol;
  ExprType: TTypeDesc;
begin
  VarSym := FTable.Lookup(AAssign.Name);
  if VarSym = nil then
    SemanticError(
      Format('Undeclared variable ''%s''', [AAssign.Name]),
      AAssign.Line, AAssign.Col);
  if not (VarSym.Kind in [skVariable, skVarParameter]) then
    SemanticError(
      Format('''%s'' is not a variable', [AAssign.Name]),
      AAssign.Line, AAssign.Col);

  AAssign.IsVarParam      := (VarSym.Kind = skVarParameter);
  AAssign.ResolvedLhsType := VarSym.TypeDesc;

  ExprType := AnalyseExpr(AAssign.Expr);
  CheckTypesMatch(VarSym.TypeDesc, ExprType, 'assignment', AAssign.Line, AAssign.Col);
end;

procedure TSemanticAnalyser.AnalyseFieldAssignment(AAssign: TFieldAssignment);
var
  RecSym:   TSymbol;
  RT:       TRecordTypeDesc;
  FldInfo:  TFieldInfo;
  ExprType: TTypeDesc;
begin
  RecSym := FTable.Lookup(AAssign.RecordName);
  if RecSym = nil then
    SemanticError(
      Format('Undeclared variable ''%s''', [AAssign.RecordName]),
      AAssign.Line, AAssign.Col);
  if RecSym.Kind <> skVariable then
    SemanticError(
      Format('''%s'' is not a variable', [AAssign.RecordName]),
      AAssign.Line, AAssign.Col);
  if not (RecSym.TypeDesc.Kind in [tyRecord, tyClass]) then
    SemanticError(
      Format('''%s'' is not a record or class variable', [AAssign.RecordName]),
      AAssign.Line, AAssign.Col);

  AAssign.IsClassAccess := RecSym.TypeDesc.Kind = tyClass;

  RT      := TRecordTypeDesc(RecSym.TypeDesc);
  FldInfo := RT.FindField(AAssign.FieldName);
  if FldInfo = nil then
    SemanticError(
      Format('Type ''%s'' has no field ''%s''',
        [AAssign.RecordName, AAssign.FieldName]),
      AAssign.Line, AAssign.Col);

  AAssign.FieldInfo := FldInfo;
  ExprType := AnalyseExpr(AAssign.Expr);
  CheckTypesMatch(FldInfo.TypeDesc, ExprType, 'field assignment',
    AAssign.Line, AAssign.Col);
end;

procedure TSemanticAnalyser.AnalyseProcCall(ACall: TProcCall);
var
  Sym:     TSymbol;
  MDecl:   TMethodDecl;
  Par:     TMethodParam;
  ArgType: TTypeDesc;
  Idx:     Integer;
  I:       Integer;
begin
  Sym := FTable.Lookup(ACall.Name);
  if Sym = nil then
    SemanticError(
      Format('Undeclared procedure ''%s''', [ACall.Name]),
      ACall.Line, ACall.Col);
  if not (Sym.Kind in [skProcedure, skFunction]) then
    SemanticError(
      Format('''%s'' is not a procedure or function', [ACall.Name]),
      ACall.Line, ACall.Col);

  { For user-defined procs/funcs, validate arg count and types }
  Idx := FProcIndex.IndexOf(ACall.Name);
  if Idx >= 0 then
  begin
    MDecl := TMethodDecl(FProcIndex.Objects[Idx]);
    if ACall.Args.Count <> MDecl.Params.Count then
      SemanticError(
        Format('Procedure ''%s'' expects %d argument(s) but got %d',
          [ACall.Name, MDecl.Params.Count, ACall.Args.Count]),
        ACall.Line, ACall.Col);
    for I := 0 to ACall.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params[I]);
      if Par.IsVarParam then
      begin
        { var parameter: argument must be a simple variable }
        if not (TASTExpr(ACall.Args[I]) is TIdentExpr) then
          SemanticError(
            Format('var argument %d of ''%s'' must be a variable',
              [I + 1, ACall.Name]),
            ACall.Line, ACall.Col);
        ArgType := AnalyseExpr(TASTExpr(ACall.Args[I]));
        CheckTypesMatch(Par.ResolvedType, ArgType,
          Format('var argument %d of ''%s''', [I + 1, ACall.Name]),
          ACall.Line, ACall.Col);
      end
      else
      begin
        ArgType := AnalyseExpr(TASTExpr(ACall.Args[I]));
        CheckTypesMatch(Par.ResolvedType, ArgType,
          Format('argument %d of ''%s''', [I + 1, ACall.Name]),
          ACall.Line, ACall.Col);
      end;
    end;
    ACall.ResolvedDecl := MDecl;
  end
  else
  begin
    { Built-in (WriteLn/Write) — just analyse arg expressions }
    for I := 0 to ACall.Args.Count - 1 do
      AnalyseExpr(TASTExpr(ACall.Args[I]));
  end;
end;

function TSemanticAnalyser.AnalyseFuncCallExpr(AExpr: TFuncCallExpr): TTypeDesc;
var
  Sym:     TSymbol;
  MDecl:   TMethodDecl;
  Par:     TMethodParam;
  ArgType: TTypeDesc;
  Idx:     Integer;
  I:       Integer;
begin
  Sym := FTable.Lookup(AExpr.Name);
  if Sym = nil then
    SemanticError(
      Format('Undeclared function ''%s''', [AExpr.Name]),
      AExpr.Line, AExpr.Col);
  if Sym.Kind <> skFunction then
    SemanticError(
      Format('''%s'' is not a function', [AExpr.Name]),
      AExpr.Line, AExpr.Col);

  Idx := FProcIndex.IndexOf(AExpr.Name);
  if Idx < 0 then
    SemanticError(
      Format('Cannot find declaration for function ''%s''', [AExpr.Name]),
      AExpr.Line, AExpr.Col);

  MDecl := TMethodDecl(FProcIndex.Objects[Idx]);

  if AExpr.Args.Count <> MDecl.Params.Count then
    SemanticError(
      Format('Function ''%s'' expects %d argument(s) but got %d',
        [AExpr.Name, MDecl.Params.Count, AExpr.Args.Count]),
      AExpr.Line, AExpr.Col);

  for I := 0 to AExpr.Args.Count - 1 do
  begin
    ArgType := AnalyseExpr(TASTExpr(AExpr.Args[I]));
    Par     := TMethodParam(MDecl.Params[I]);
    CheckTypesMatch(Par.ResolvedType, ArgType,
      Format('argument %d of ''%s''', [I + 1, AExpr.Name]),
      AExpr.Line, AExpr.Col);
  end;

  AExpr.ResolvedDecl := MDecl;
  Result := MDecl.ResolvedReturnType;
end;

function TSemanticAnalyser.AnalyseMethodCallExpr(AExpr: TMethodCallExpr): TTypeDesc;
var
  ObjSym:  TSymbol;
  RT:      TRecordTypeDesc;
  MDecl:   TMethodDecl;
  Par:     TMethodParam;
  ArgType: TTypeDesc;
  I:       Integer;
begin
  ObjSym := FTable.Lookup(AExpr.ObjectName);
  if ObjSym = nil then
    SemanticError(
      Format('Undeclared variable ''%s''', [AExpr.ObjectName]),
      AExpr.Line, AExpr.Col);
  if ObjSym.Kind <> skVariable then
    SemanticError(
      Format('''%s'' is not a variable', [AExpr.ObjectName]),
      AExpr.Line, AExpr.Col);
  if ObjSym.TypeDesc.Kind <> tyClass then
    SemanticError(
      Format('''%s'' is not a class variable', [AExpr.ObjectName]),
      AExpr.Line, AExpr.Col);

  RT    := TRecordTypeDesc(ObjSym.TypeDesc);
  MDecl := FindMethodDecl(RT.Name, AExpr.Name);
  if MDecl = nil then
    SemanticError(
      Format('Class ''%s'' has no method ''%s''', [RT.Name, AExpr.Name]),
      AExpr.Line, AExpr.Col);
  if MDecl.ResolvedReturnType = nil then
    SemanticError(
      Format('Method ''%s.%s'' is a procedure (no return value)',
        [RT.Name, AExpr.Name]),
      AExpr.Line, AExpr.Col);

  if AExpr.Args.Count <> MDecl.Params.Count then
    SemanticError(
      Format('Method ''%s.%s'' expects %d argument(s) but got %d',
        [RT.Name, AExpr.Name, MDecl.Params.Count, AExpr.Args.Count]),
      AExpr.Line, AExpr.Col);

  for I := 0 to AExpr.Args.Count - 1 do
  begin
    ArgType := AnalyseExpr(TASTExpr(AExpr.Args[I]));
    Par     := TMethodParam(MDecl.Params[I]);
    CheckTypesMatch(Par.ResolvedType, ArgType,
      Format('argument %d of ''%s''', [I + 1, AExpr.Name]),
      AExpr.Line, AExpr.Col);
  end;

  AExpr.ResolvedClassType := RT;
  AExpr.ResolvedMethod    := MDecl;
  Result := MDecl.ResolvedReturnType;
end;

function TSemanticAnalyser.AnalyseExpr(AExpr: TASTExpr): TTypeDesc;
var
  Sym: TSymbol;
begin
  if AExpr is TNilLiteral then
    Result := FTable.TypeNil
  else if AExpr is TIntLiteral then
    Result := FTable.TypeInteger
  else if AExpr is TStringLiteral then
    Result := FTable.TypeString
  else if AExpr is TIdentExpr then
  begin
    Sym := FTable.Lookup(TIdentExpr(AExpr).Name);
    if Sym = nil then
      SemanticError(
        Format('Undeclared identifier ''%s''', [TIdentExpr(AExpr).Name]),
        AExpr.Line, AExpr.Col);
    TIdentExpr(AExpr).IsVarParam := (Sym.Kind = skVarParameter);
    Result := Sym.TypeDesc;
  end
  else if AExpr is TFuncCallExpr then
    Result := AnalyseFuncCallExpr(TFuncCallExpr(AExpr))
  else if AExpr is TMethodCallExpr then
    Result := AnalyseMethodCallExpr(TMethodCallExpr(AExpr))
  else if AExpr is TFieldAccessExpr then
    Result := AnalyseFieldAccess(TFieldAccessExpr(AExpr))
  else if AExpr is TBinaryExpr then
    Result := AnalyseBinaryExpr(TBinaryExpr(AExpr))
  else if AExpr is TIsExpr then
    Result := AnalyseIsExpr(TIsExpr(AExpr))
  else if AExpr is TAsExpr then
    Result := AnalyseAsExpr(TAsExpr(AExpr))
  else
    SemanticError('Unknown expression node', AExpr.Line, AExpr.Col);

  AExpr.ResolvedType := Result;
end;

function TSemanticAnalyser.AnalyseFieldAccess(AAccess: TFieldAccessExpr): TTypeDesc;
var
  RecSym:  TSymbol;
  RT:      TRecordTypeDesc;
  FldInfo: TFieldInfo;
begin
  RecSym := FTable.Lookup(AAccess.RecordName);
  if RecSym = nil then
    SemanticError(
      Format('Undeclared identifier ''%s''', [AAccess.RecordName]),
      AAccess.Line, AAccess.Col);

  { Constructor call: TypeName.Create }
  if RecSym.Kind = skType then
  begin
    if RecSym.TypeDesc.Kind <> tyClass then
      SemanticError(
        Format('Cannot call constructor on non-class type ''%s''',
          [AAccess.RecordName]),
        AAccess.Line, AAccess.Col);
    if not SameText(AAccess.FieldName, 'Create') then
      SemanticError(
        Format('Unknown class method ''%s'' on type ''%s''',
          [AAccess.FieldName, AAccess.RecordName]),
        AAccess.Line, AAccess.Col);
    AAccess.IsConstructorCall := True;
    Result := RecSym.TypeDesc;
    Exit;
  end;

  { Field access on variable }
  if RecSym.Kind <> skVariable then
    SemanticError(
      Format('''%s'' is not a variable or type', [AAccess.RecordName]),
      AAccess.Line, AAccess.Col);

  if not (RecSym.TypeDesc.Kind in [tyRecord, tyClass]) then
    SemanticError(
      Format('''%s'' is not a record or class', [AAccess.RecordName]),
      AAccess.Line, AAccess.Col);

  AAccess.IsClassAccess := RecSym.TypeDesc.Kind = tyClass;

  RT      := TRecordTypeDesc(RecSym.TypeDesc);
  FldInfo := RT.FindField(AAccess.FieldName);
  if FldInfo = nil then
    SemanticError(
      Format('Type ''%s'' has no field ''%s''',
        [AAccess.RecordName, AAccess.FieldName]),
      AAccess.Line, AAccess.Col);

  AAccess.FieldInfo := FldInfo;
  Result := FldInfo.TypeDesc;
end;

function TSemanticAnalyser.AnalyseBinaryExpr(ABin: TBinaryExpr): TTypeDesc;
var
  LType, RType: TTypeDesc;
begin
  LType := AnalyseExpr(ABin.Left);
  RType := AnalyseExpr(ABin.Right);

  if IsComparisonOp(ABin.Op) then
  begin
    { nil can be compared with class types }
    if not (
      (LType = RType) or
      ((LType.Kind = tyNil) and (RType.Kind = tyClass)) or
      ((LType.Kind = tyClass) and (RType.Kind = tyNil))
    ) then
      CheckTypesMatch(LType, RType,
        Format('comparison ''%s''', [BinaryOpName(ABin.Op)]),
        ABin.Line, ABin.Col);
    Result := FTable.TypeBoolean;
  end
  else
  begin
    { String concatenation: s1 + s2 → string }
    if (ABin.Op = boAdd) and LType.IsString and RType.IsString then
    begin
      Result := FTable.TypeString;
      Exit;
    end;

    if not LType.IsNumeric then
      SemanticError(
        Format('Left operand of ''%s'' must be numeric, got ''%s''',
          [BinaryOpName(ABin.Op), LType.Name]),
        ABin.Line, ABin.Col);
    if not RType.IsNumeric then
      SemanticError(
        Format('Right operand of ''%s'' must be numeric, got ''%s''',
          [BinaryOpName(ABin.Op), RType.Name]),
        ABin.Line, ABin.Col);
    CheckTypesMatch(LType, RType, 'binary expression', ABin.Line, ABin.Col);
    Result := LType;
  end;
end;

function TSemanticAnalyser.AnalyseIsExpr(AExpr: TIsExpr): TTypeDesc;
var
  ObjType:    TTypeDesc;
  TargetType: TTypeDesc;
begin
  ObjType := AnalyseExpr(AExpr.Obj);
  if ObjType.Kind <> tyClass then
    SemanticError(
      Format('''is'' requires a class instance on the left, got ''%s''',
        [ObjType.Name]),
      AExpr.Line, AExpr.Col);

  TargetType := FTable.FindType(AExpr.TypeName);
  if (TargetType = nil) or
     ((TargetType.Kind <> tyClass) and (TargetType.Kind <> tyInterface)) then
    SemanticError(
      Format('''is'' requires a class or interface type name on the right, got ''%s''',
        [AExpr.TypeName]),
      AExpr.Line, AExpr.Col);

  AExpr.ResolvedTargetType := TargetType;
  Result := FTable.TypeBoolean;
end;

function TSemanticAnalyser.AnalyseAsExpr(AExpr: TAsExpr): TTypeDesc;
var
  ObjType:    TTypeDesc;
  TargetType: TTypeDesc;
begin
  ObjType := AnalyseExpr(AExpr.Obj);
  if ObjType.Kind <> tyClass then
    SemanticError(
      Format('''as'' requires a class instance on the left, got ''%s''',
        [ObjType.Name]),
      AExpr.Line, AExpr.Col);

  TargetType := FTable.FindType(AExpr.TypeName);
  if (TargetType = nil) or
     ((TargetType.Kind <> tyClass) and (TargetType.Kind <> tyInterface)) then
    SemanticError(
      Format('''as'' requires a class or interface type name on the right, got ''%s''',
        [AExpr.TypeName]),
      AExpr.Line, AExpr.Col);

  Result := TargetType;
end;

end.
