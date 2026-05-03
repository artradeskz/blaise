{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

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
    FTable:                TSymbolTable;
    FProg:                 TProgram;      { current program being analysed; set in Analyse }
    FMethodIndex:          TStringList;  { 'TypeName.MethodName' → TMethodDecl (not owned) }
    FProcIndex:            TStringList;  { 'ProcName' → TMethodDecl (not owned) }
    FGenericFuncTemplates: TStringList;  { base name → TMethodDecl template (not owned) }
    FLoopDepth:            Integer;      { depth of enclosing while/for — Break only legal if > 0 }
    FScopeDepth:           Integer;      { mirrors FTable scope depth; used to detect main-level globals }
    FCurrentClass:         TRecordTypeDesc;  { class being analysed (set in AnalyseMethodDecl) }
    FCurrentLocalBlock:    TBlock;       { block currently being stmt-analysed; for-in injects synthetic TVarDecl here }
    FForInCounter:         Integer;      { counter for generating unique __forin_N variable names }

    { Generic type instantiation: resolves 'TBox<Integer>' on demand. }
    function  FindTypeOrInstantiate(const AName: string): TTypeDesc;

    { Resolves a parameter's type, handling both plain types and open arrays.
      For IsOpenArray params, creates and registers a TOpenArrayTypeDesc. }
    function  ResolveParamType(APar: TMethodParam;
                ALoc: Integer; ACol: Integer): TTypeDesc;
    function  InstantiateGeneric(const ATypeName: string): TRecordTypeDesc;
    function  InstantiateGenericInterface(const ATypeName: string): TInterfaceTypeDesc;
    function  SubstTypeParam(const ATypeName: string;
                AParamNames, AArgs: TStringList): string;

    { Resolves scope-bound type params inside a generic type name such as
      'TGenEnum<T>' when 'T' is bound in the current scope as a skType symbol.
      Returns the canonical name (e.g. 'TGenEnum<Integer>') suitable for
      FindTypeOrInstantiate. Has no effect on names without '<'. }
    function  ResolveScopeBoundTypeParams(const ATypeName: string): string;

    { Generic function instantiation: resolves 'Identity<Integer>' on demand. }
    function  InstantiateGenericFunc(const AInstName: string): TMethodDecl;

    procedure AnalyseBlock(ABlock: TBlock);
    procedure AnalyseConstDecls(ABlock: TBlock);
    procedure AnalyseTypeDecls(ABlock: TBlock);
    procedure LinkClassMethodImpls(ABlock: TBlock);
    procedure LinkGenericClassMethodImpls(ABlock: TBlock);
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
    procedure AnalyseInheritedCall(ACall: TInheritedCallStmt);
    procedure AnalyseCaseStmt(AStmt: TCaseStmt);
    function  AnalyseMethodCallExpr(AExpr: TMethodCallExpr): TTypeDesc;
    function  AnalyseFuncCallExpr(AExpr: TFuncCallExpr): TTypeDesc;
    function  AnalyseExpr(AExpr: TASTExpr): TTypeDesc;
    function  AnalyseBinaryExpr(ABin: TBinaryExpr): TTypeDesc;
    function  AnalyseFieldAccess(AAccess: TFieldAccessExpr): TTypeDesc;
    function  AnalyseIsExpr(AExpr: TIsExpr): TTypeDesc;
    function  AnalyseAsExpr(AExpr: TAsExpr): TTypeDesc;
    function  AnalyseDerefExpr(AExpr: TDerefExpr): TTypeDesc;
    function  AnalyseAddrOfExpr(AExpr: TAddrOfExpr): TTypeDesc;
    function  AnalyseStringSubscriptExpr(AExpr: TStringSubscriptExpr): TTypeDesc;
    function  AnalyseArrayLiteralExpr(AExpr: TArrayLiteralExpr): TTypeDesc;
    function  AnalyseSetLiteralExpr(AExpr: TArrayLiteralExpr; ASetType: TSetTypeDesc): TTypeDesc;
    procedure CoerceToCharOrd(ALit: TStringLiteral);
    procedure AnalysePointerWriteStmt(AStmt: TPointerWriteStmt);
    procedure AnalyseStaticSubscriptAssign(AStmt: TStaticSubscriptAssign);

    procedure AnalyseCompoundBody(ABody: TCompoundStmt);
    function  FindMethodDecl(const ATypeName, AMethodName: string): TMethodDecl;
    { Attribute helpers.  AttrMatches performs the Delphi-style suffix-drop
      lookup: [Weak] and [WeakAttribute] both resolve to the recognised
      attribute 'Weak'.  HasWeakAttribute scans an attribute list for
      any form of the Weak marker. }
    function  AttrMatches(const AAttrName, ACanonical: string): Boolean;
    function  HasWeakAttribute(AAttrs: TStringList): Boolean;

    procedure SemanticError(const AMsg: string; ALine, ACol: Integer);
    procedure CheckTypesMatch(AExpected, AActual: TTypeDesc;
      const AContext: string; ALine, ACol: Integer);
    { Returns True if AActual is AExpected or a subclass of AExpected. }
    function  IsSubtypeOf(AActual, AExpected: TTypeDesc): Boolean;
    { Validates a generic type parameter's constraint against a concrete type
      argument name.  Raises ESemanticError on constraint violation.
      AConstraint: '' (no constraint), 'class', 'record', or a type name. }
    procedure CheckTypeParamConstraint(const AParamName, AArgName, AConstraint,
      AContext: string);
  public
    constructor Create;
    destructor Destroy; override;
    procedure Analyse(AProg: TProgram);
    procedure AnalyseUnit(AUnit: TUnit);
    { Like AnalyseUnit but promotes interface-section symbols to the global
      scope so that subsequent Analyse(Prog) or AnalyseUnitForExport calls
      can resolve them.  Use this when compiling a unit as a dependency. }
    procedure AnalyseUnitForExport(AUnit: TUnit);
  end;

implementation

constructor TSemanticAnalyser.Create;
begin
  inherited Create;
  FTable                := TSymbolTable.Create;
  FMethodIndex          := TStringList.Create;
  FMethodIndex.CaseSensitive := False;
  FProcIndex            := TStringList.Create;
  FProcIndex.CaseSensitive := False;
  FGenericFuncTemplates := TStringList.Create;
  FGenericFuncTemplates.CaseSensitive := False;
  FLoopDepth            := 0;
end;

destructor TSemanticAnalyser.Destroy;
begin
  FGenericFuncTemplates.Free;
  FProcIndex.Free;
  FMethodIndex.Free;
  FTable.Free;
  inherited Destroy;
end;

procedure TSemanticAnalyser.SemanticError(const AMsg: string; ALine, ACol: Integer);
begin
  raise ESemanticError.Create(Format('%s at line %d col %d', [AMsg, ALine, ACol]));
end;

function TSemanticAnalyser.AttrMatches(const AAttrName, ACanonical: string): Boolean;
{ An attribute name matches a canonical form if it equals the canonical
  name case-insensitively, or if it equals <canonical>Attribute (the
  Delphi suffix convention).  This lets [Weak] and [WeakAttribute]
  resolve to the same compiler-recognised attribute. }
var
  Suffix: string;
begin
  if SameText(AAttrName, ACanonical) then
  begin
    Result := True;
    Exit;
  end;
  Suffix := ACanonical + 'Attribute';
  Result := SameText(AAttrName, Suffix);
end;

function TSemanticAnalyser.HasWeakAttribute(AAttrs: TStringList): Boolean;
var
  I: Integer;
begin
  if AAttrs = nil then
  begin
    Result := False;
    Exit;
  end;
  for I := 0 to AAttrs.Count - 1 do
    if AttrMatches(AAttrs.Strings[I], 'Weak') then
    begin
      Result := True;
      Exit;
    end;
  Result := False;
end;

procedure TSemanticAnalyser.CheckTypeParamConstraint(
  const AParamName, AArgName, AConstraint, AContext: string);
var
  ArgType:     TTypeDesc;
  ConstrType:  TTypeDesc;
  RT:          TRecordTypeDesc;
  I:           Integer;
  Implements:  Boolean;
begin
  if AConstraint = '' then Exit;

  ArgType := FTable.FindType(AArgName);
  if ArgType = nil then
    raise ESemanticError.Create(Format(
      'Unknown type ''%s'' for type parameter ''%s'' in %s',
      [AArgName, AParamName, AContext]));

  if SameText(AConstraint, 'class') then
  begin
    if ArgType.Kind <> tyClass then
      raise ESemanticError.Create(Format(
        'Type ''%s'' does not satisfy constraint ''%s: class'' in %s',
        [AArgName, AParamName, AContext]));
    Exit;
  end;

  if SameText(AConstraint, 'record') then
  begin
    if not (ArgType.Kind in [tyRecord, tyInteger, tyInt64, tyUInt32, tyByte,
                             tyBoolean, tyString, tyPointer]) then
      raise ESemanticError.Create(Format(
        'Type ''%s'' does not satisfy constraint ''%s: record'' in %s',
        [AArgName, AParamName, AContext]));
    Exit;
  end;

  { Named constraint: T : SomeType.  Concrete type must BE that type or —
    for classes/interfaces — inherit from / implement it. }
  ConstrType := FTable.FindType(AConstraint);
  if ConstrType = nil then
    raise ESemanticError.Create(Format(
      'Unknown constraint type ''%s'' for type parameter ''%s'' in %s',
      [AConstraint, AParamName, AContext]));

  if ArgType = ConstrType then Exit;

  if (ConstrType.Kind = tyClass) and (ArgType.Kind = tyClass) then
  begin
    if IsSubtypeOf(ArgType, ConstrType) then Exit;
    raise ESemanticError.Create(Format(
      'Type ''%s'' does not inherit from ''%s'' (constraint ''%s: %s'') in %s',
      [AArgName, AConstraint, AParamName, AConstraint, AContext]));
  end;

  if (ConstrType.Kind = tyInterface) and (ArgType.Kind = tyClass) then
  begin
    RT := TRecordTypeDesc(ArgType);
    Implements := False;
    for I := 0 to RT.ImplementsCount - 1 do
      if RT.ImplementsIntfAt(I) = ConstrType then
      begin
        Implements := True;
        Break;
      end;
    if not Implements then
      raise ESemanticError.Create(Format(
        'Type ''%s'' does not implement ''%s'' (constraint ''%s: %s'') in %s',
        [AArgName, AConstraint, AParamName, AConstraint, AContext]));
    Exit;
  end;

  raise ESemanticError.Create(Format(
    'Type ''%s'' does not satisfy constraint ''%s: %s'' in %s',
    [AArgName, AParamName, AConstraint, AContext]));
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
  { nil is compatible with any class, interface, pointer, PChar, or string type }
  if (AActual.Kind = tyNil) and (AExpected.Kind in [tyClass, tyInterface, tyPointer, tyPChar, tyString]) then
    Exit;
  { Two pointer types are compatible when:
      - either is untyped (Pointer), or
      - both are typed pointers to the same base type }
  if (AExpected.Kind = tyPointer) and (AActual.Kind = tyPointer) then
  begin
    if (TPointerTypeDesc(AExpected).BaseType = nil) or
       (TPointerTypeDesc(AActual).BaseType = nil) or
       (TPointerTypeDesc(AExpected).BaseType = TPointerTypeDesc(AActual).BaseType) then
      Exit;
  end;
  { enum ↔ enum (same type) already handled by = check above;
    enum ↔ integer: allow assignment between enum and integer types }
  if (AExpected.Kind = tyEnum) and AActual.IsNumeric then Exit;
  if (AActual.Kind  = tyEnum) and AExpected.IsNumeric then Exit;
  { Numeric widening/narrowing: allow between the integer family members }
  if AExpected.IsNumeric and AActual.IsNumeric then Exit;
  { subtype assignment: TDerived → TBase is allowed }
  if IsSubtypeOf(AActual, AExpected) then
    Exit;
  { TObject accepts any class — universal base class }
  if (AExpected.Kind = tyClass) and (AExpected.Name = 'TObject') and
     (AActual.Kind = tyClass) then
    Exit;
  { class → interface: allowed when the class implements that interface }
  if (AExpected.Kind = tyInterface) and (AActual.Kind = tyClass) then
  begin
    RT := TRecordTypeDesc(AActual);
    for I := 0 to RT.ImplementsCount - 1 do
      if RT.ImplementsIntfAt(I) = AExpected then
        Exit;
  end;
  { Untyped pointer accepts any class/interface/string/PChar reference and vice-versa }
  if (AExpected.Kind = tyPointer) and
     (TPointerTypeDesc(AExpected).BaseType = nil) and
     (AActual.Kind in [tyClass, tyInterface, tyString, tyPointer, tyPChar]) then
    Exit;
  if (AActual.Kind = tyPointer) and
     (TPointerTypeDesc(AActual).BaseType = nil) and
     (AExpected.Kind in [tyClass, tyInterface, tyString, tyPointer, tyPChar]) then
    Exit;
  { PChar is compatible with PChar }
  if (AExpected.Kind = tyPChar) and (AActual.Kind = tyPChar) then Exit;
  { Open-array forwarding: both must be tyOpenArray with the same element type }
  if (AExpected.Kind = tyOpenArray) and (AActual.Kind = tyOpenArray) then
  begin
    if TOpenArrayTypeDesc(AExpected).ElementType =
       TOpenArrayTypeDesc(AActual).ElementType then
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
      MDecl := TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]);

      for J := 0 to MDecl.Params.Count - 1 do
      begin
        Par              := TMethodParam(MDecl.Params.Items[J]);
        Par.ResolvedType := ResolveParamType(Par, MDecl.Line, MDecl.Col);
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

    { Process implementation declarations — skip generic class method impls
      (OwnerTypeName + OwnerTypeParams set); they are handled below. }
    for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
    begin
      ImplDecl := TMethodDecl(AUnit.ImplBlock.ProcDecls.Items[I]);
      if (ImplDecl.OwnerTypeName <> '') and (ImplDecl.OwnerTypeParams <> nil) then
        Continue;

      for J := 0 to ImplDecl.Params.Count - 1 do
      begin
        Par              := TMethodParam(ImplDecl.Params.Items[J]);
        Par.ResolvedType := ResolveParamType(Par, ImplDecl.Line, ImplDecl.Col);
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

    { Link generic class method implementations to their template methods }
    LinkGenericClassMethodImpls(AUnit.ImplBlock);

    { Verify every interface declaration has a matching implementation }
    for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
    begin
      MDecl   := TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]);
      ImplIdx := FProcIndex.IndexOf(MDecl.Name);
      if MDecl.IsExternal then Continue;
      if (ImplIdx < 0) or
         (TMethodDecl(FProcIndex.Objects[ImplIdx]).Body = nil) then
        SemanticError(
          Format('Interface function ''%s'' has no implementation', [MDecl.Name]),
          MDecl.Line, MDecl.Col);
    end;

    { Analyse standalone implementation bodies (skip generic class method impls) }
    for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
    begin
      ImplDecl := TMethodDecl(AUnit.ImplBlock.ProcDecls.Items[I]);
      if (ImplDecl.OwnerTypeName <> '') and (ImplDecl.OwnerTypeParams <> nil) then
        Continue;
      AnalyseStandaloneDecl(ImplDecl);
    end;
  finally
    FTable.PopScope;
  end;
end;

procedure TSemanticAnalyser.AnalyseUnitForExport(AUnit: TUnit);
var
  I, J:     Integer;
  MDecl:    TMethodDecl;
  ImplDecl: TMethodDecl;
  ImplIdx:  Integer;
  Par:      TMethodParam;
  ParType:  TTypeDesc;
  Sym:      TSymbol;
  VDecl:    TVarDecl;
begin
  { --- Interface section ------------------------------------------------
    No scope is pushed here: all FTable.Define calls go to the global scope,
    making these symbols visible to callers of this unit. }

  AnalyseConstDecls(AUnit.IntfBlock);
  AnalyseTypeDecls(AUnit.IntfBlock);

  { Register interface forward declarations for standalone procs/funcs.
    Must happen before AnalyseMethodBodies so class method bodies can call
    them (e.g. TStringList.SetText calls SplitIntoList). }
  for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
  begin
    MDecl := TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]);

    for J := 0 to MDecl.Params.Count - 1 do
    begin
      Par              := TMethodParam(MDecl.Params.Items[J]);
      Par.ResolvedType := ResolveParamType(Par, MDecl.Line, MDecl.Col);
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

  { Link class method bodies from ImplBlock to the class type method decls
    registered by AnalyseTypeDecls. }
  LinkClassMethodImpls(AUnit.ImplBlock);
  LinkGenericClassMethodImpls(AUnit.ImplBlock);

  { --- Implementation section -------------------------------------------
    Push a scope so impl-only standalone symbols don't leak globally.
    Class method bodies are analysed inside this scope so they can call
    impl-only helpers (e.g. TStringList.SetText -> SplitIntoList). }
  FTable.PushScope;
  try
    { Register impl-section global variables — marked IsGlobal so codegen
      emits them as data-segment slots rather than stack allocations. }
    AnalyseConstDecls(AUnit.ImplBlock);
    for I := 0 to AUnit.ImplBlock.Decls.Count - 1 do
    begin
      VDecl := TVarDecl(AUnit.ImplBlock.Decls.Items[I]);
      ParType := FTable.FindType(VDecl.TypeName);
      if ParType = nil then
        SemanticError(Format('Unknown type ''%s''', [VDecl.TypeName]), VDecl.Line, VDecl.Col);
      VDecl.ResolvedType := ParType;
      VDecl.IsGlobal := True;
      for J := 0 to VDecl.Names.Count - 1 do
      begin
        Sym := TSymbol.Create(VDecl.Names.Strings[J], skVariable, ParType);
        Sym.IsGlobal := True;
        if not FTable.Define(Sym) then
        begin
          Sym.Free;
          SemanticError(Format('Duplicate identifier ''%s''', [VDecl.Names.Strings[J]]), VDecl.Line, VDecl.Col);
        end;
      end;
    end;

    { Register impl decls, skipping class method impls (already linked above) }
    for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
    begin
      ImplDecl := TMethodDecl(AUnit.ImplBlock.ProcDecls.Items[I]);
      if ImplDecl.OwnerTypeName <> '' then Continue;  { class method — already handled }

      for J := 0 to ImplDecl.Params.Count - 1 do
      begin
        Par              := TMethodParam(ImplDecl.Params.Items[J]);
        Par.ResolvedType := ResolveParamType(Par, ImplDecl.Line, ImplDecl.Col);
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
        { Matches an interface forward decl — verify param count and update index }
        MDecl := TMethodDecl(FProcIndex.Objects[ImplIdx]);
        if MDecl.Params.Count <> ImplDecl.Params.Count then
          SemanticError(
            Format('Signature mismatch for ''%s'': interface has %d params, implementation has %d',
              [ImplDecl.Name, MDecl.Params.Count, ImplDecl.Params.Count]),
            ImplDecl.Line, ImplDecl.Col);
        FProcIndex.Objects[ImplIdx] := ImplDecl;
      end
      else
      begin
        { Impl-only declaration — register in impl scope (does not persist) }
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

    { Analyse class method bodies — impl-only helpers now visible above }
    AnalyseMethodBodies(AUnit.IntfBlock);

    { Verify every interface declaration has a matching implementation }
    for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
    begin
      MDecl   := TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]);
      ImplIdx := FProcIndex.IndexOf(MDecl.Name);
      if MDecl.IsExternal then Continue;
      if (ImplIdx < 0) or
         (TMethodDecl(FProcIndex.Objects[ImplIdx]).Body = nil) then
        SemanticError(
          Format('Interface function ''%s'' has no implementation', [MDecl.Name]),
          MDecl.Line, MDecl.Col);
    end;

    { Analyse standalone implementation bodies (skip class method impls) }
    for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
    begin
      ImplDecl := TMethodDecl(AUnit.ImplBlock.ProcDecls.Items[I]);
      if ImplDecl.OwnerTypeName <> '' then Continue;
      AnalyseStandaloneDecl(ImplDecl);
    end;
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
    Decl := TMethodDecl(ABlock.ProcDecls.Items[I]);
    if Decl.OwnerTypeName = '' then Continue;
    if Decl.OwnerTypeParams <> nil then Continue;  { generic owner — handled by LinkGenericClassMethodImpls }
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

procedure TSemanticAnalyser.LinkGenericClassMethodImpls(ABlock: TBlock);
var
  I, J: Integer;
  Decl: TMethodDecl;
  Templ: TGenericTypeDef;
  MDecl: TMethodDecl;
begin
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(ABlock.ProcDecls.Items[I]);
    if (Decl.OwnerTypeName = '') or (Decl.OwnerTypeParams = nil) then
      Continue;
    { Locate the generic template by base class name }
    if not (FTable.FindGeneric(Decl.OwnerTypeName) is TGenericTypeDef) then
      SemanticError(
        Format('Generic type ''%s'' not found for method ''%s''',
          [Decl.OwnerTypeName, Decl.Name]),
        Decl.Line, Decl.Col);
    Templ := TGenericTypeDef(FTable.FindGeneric(Decl.OwnerTypeName));
    { Find the matching forward declaration in the template }
    MDecl := nil;
    for J := 0 to Templ.ClassDef.Methods.Count - 1 do
      if SameText(TMethodDecl(Templ.ClassDef.Methods.Items[J]).Name, Decl.Name) then
      begin
        MDecl := TMethodDecl(Templ.ClassDef.Methods.Items[J]);
        Break;
      end;
    if MDecl = nil then
      SemanticError(
        Format('Method ''%s'' is not declared in generic class ''%s''',
          [Decl.Name, Decl.OwnerTypeName]),
        Decl.Line, Decl.Col);
    if MDecl.Body <> nil then
      SemanticError(
        Format('Method ''%s.%s'' already has a body',
          [Decl.OwnerTypeName, Decl.Name]),
        Decl.Line, Decl.Col);
    MDecl.Body := Decl.Body;
    Decl.Body  := nil;
  end;
end;

function TSemanticAnalyser.ResolveScopeBoundTypeParams(const ATypeName: string): string;
var
  BrOpen, BrClose, I: Integer;
  BasePart, ArgsPart, OutArgs, Arg: string;
  ArgList: TStringList;
  Sym: TSymbol;
begin
  Result  := ATypeName;
  BrOpen  := Pos('<', ATypeName);
  if BrOpen = 0 then Exit;
  BrClose  := Length(ATypeName);
  BasePart := Copy(ATypeName, 1, BrOpen - 1);
  ArgsPart := Copy(ATypeName, BrOpen + 1, BrClose - BrOpen - 1);
  ArgList  := TStringList.Create;
  try
    while ArgsPart <> '' do
    begin
      I := Pos(',', ArgsPart);
      if I > 0 then
      begin
        ArgList.Add(Trim(Copy(ArgsPart, 1, I - 1)));
        ArgsPart := Trim(Copy(ArgsPart, I + 1, MaxInt));
      end
      else
      begin
        ArgList.Add(Trim(ArgsPart));
        ArgsPart := '';
      end;
    end;
    OutArgs := '';
    for I := 0 to ArgList.Count - 1 do
    begin
      Arg := ArgList.Strings[I];
      { If this arg is a bare ident bound as skType in the current scope,
        replace it with the concrete type name. }
      Sym := FTable.Lookup(Arg);
      if (Sym <> nil) and (Sym.Kind = skType) and (Sym.TypeDesc <> nil) then
        Arg := Sym.TypeDesc.Name;
      if OutArgs = '' then
        OutArgs := Arg
      else
        OutArgs := OutArgs + ',' + Arg;
    end;
  finally
    ArgList.Free;
  end;
  Result := BasePart + '<' + OutArgs + '>';
end;

function TSemanticAnalyser.FindTypeOrInstantiate(const AName: string): TTypeDesc;
var
  BaseName: string;
  BaseType: TTypeDesc;
  PT:       TPointerTypeDesc;
  Sym:      TSymbol;
  DDotPos, RBrPos, OfPos: Integer;
  LStr, HStr, ElemName: string;
  SAT: TStaticArrayTypeDesc;
begin
  Result := FTable.FindType(AName);
  if Result <> nil then Exit;
  { Static array: 'array[L..H] of TypeName' — create on demand }
  if (Length(AName) > 6) and (Copy(AName, 1, 6) = 'array[') then
  begin
    DDotPos  := Pos('..', AName);
    RBrPos   := Pos(']', AName);
    OfPos    := Pos(' of ', AName);
    LStr     := Copy(AName, 7, DDotPos - 7);
    HStr     := Copy(AName, DDotPos + 2, RBrPos - DDotPos - 2);
    ElemName := Copy(AName, OfPos + 4, MaxInt);
    BaseType := FindTypeOrInstantiate(ElemName);
    if BaseType <> nil then
    begin
      SAT := FTable.NewStaticArrayType(BaseType, StrToInt(LStr), StrToInt(HStr));
      Sym := TSymbol.Create(AName, skType, SAT);
      FTable.DefineGlobal(Sym);
      Result := SAT;
    end;
    Exit;
  end;
  { Typed pointer: '^TypeName' — create on demand }
  if (Length(AName) > 1) and (AName[1] = '^') then
  begin
    BaseName := Copy(AName, 2, MaxInt);
    BaseType := FindTypeOrInstantiate(BaseName);
    if BaseType <> nil then
    begin
      PT := FTable.NewPointerType(AName, BaseType);
      Sym := TSymbol.Create(AName, skType, PT);
      FTable.DefineGlobal(Sym);
      Result := PT;
    end;
    Exit;
  end;
  if Pos('<', AName) > 0 then
  begin
    Result := InstantiateGeneric(AName);
    if Result = nil then
      Result := InstantiateGenericInterface(AName);
  end;
end;

function TSemanticAnalyser.ResolveParamType(APar: TMethodParam;
  ALoc: Integer; ACol: Integer): TTypeDesc;
var
  ElemType: TTypeDesc;
begin
  if APar.IsOpenArray then
  begin
    ElemType := FindTypeOrInstantiate(APar.TypeName);
    if ElemType = nil then
      SemanticError(
        Format('Unknown element type ''%s'' in open-array parameter ''%s''',
          [APar.TypeName, APar.ParamName]),
        ALoc, ACol);
    Result := FTable.NewOpenArrayType(ElemType);
  end
  else
  begin
    Result := FindTypeOrInstantiate(APar.TypeName);
    if Result = nil then
      SemanticError(
        Format('Unknown type ''%s'' for parameter ''%s''',
          [APar.TypeName, APar.ParamName]),
        ALoc, ACol);
  end;
end;

function TSemanticAnalyser.SubstTypeParam(const ATypeName: string;
  AParamNames, AArgs: TStringList): string;
var
  I, BrOpen, BrClose: Integer;
  BasePart, ArgsPart, OutArgs, Arg: string;
  ArgList: TStringList;
begin
  Result := ATypeName;
  { Direct match: T → Integer }
  for I := 0 to AParamNames.Count - 1 do
    if SameText(Result, AParamNames.Strings[I]) then
    begin
      Result := AArgs.Strings[I];
      Exit;
    end;
  { Prefix caret: ^T → ^Integer, ^^T → ^^Integer, etc. }
  if (Length(Result) > 0) and (Result[1] = '^') then
  begin
    Result := '^' + Self.SubstTypeParam(Copy(Result, 2, MaxInt), AParamNames, AArgs);
    Exit;
  end;
  { Generic instantiation: SomeName<T,...> — substitute each type argument }
  BrOpen := Pos('<', Result);
  if BrOpen > 0 then
  begin
    BrClose  := Length(Result);  { closing '>' is always the last char }
    BasePart := Copy(Result, 1, BrOpen - 1);
    ArgsPart := Copy(Result, BrOpen + 1, BrClose - BrOpen - 1);
    ArgList  := TStringList.Create;
    try
      while ArgsPart <> '' do
      begin
        I := Pos(',', ArgsPart);
        if I > 0 then
        begin
          ArgList.Add(Trim(Copy(ArgsPart, 1, I - 1)));
          ArgsPart := Trim(Copy(ArgsPart, I + 1, MaxInt));
        end
        else
        begin
          ArgList.Add(Trim(ArgsPart));
          ArgsPart := '';
        end;
      end;
      OutArgs := '';
      for I := 0 to ArgList.Count - 1 do
      begin
        Arg := Self.SubstTypeParam(ArgList.Strings[I], AParamNames, AArgs);
        if OutArgs = '' then
          OutArgs := Arg
        else
          OutArgs := OutArgs + ',' + Arg;
      end;
    finally
      ArgList.Free;
    end;
    Result := BasePart + '<' + OutArgs + '>';
  end;
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
  PDecl:    TPropertyDecl;
  NewPDecl: TPropertyDecl;
  Sym:      TSymbol;
  Key:      string;
  FldType:  TTypeDesc;
  FldName:  string;
  ParType:  TTypeDesc;
  PropType: TTypeDesc;
  PropInfo: TPropertyInfo;
  RT:       TRecordTypeDesc;
  GI:        TGenericInstance;
  Subst:     string;
  ConcrType: TTypeDesc;
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

    { Bail if the template exists but is a generic interface, not a class }
    if not (FTable.FindGeneric(BaseName) is TGenericTypeDef) then Exit;
    Templ := TGenericTypeDef(FTable.FindGeneric(BaseName));
    if Templ = nil then Exit;
    if Args.Count <> Templ.ParamNames.Count then Exit;

    { Validate each type argument against its declared constraint. }
    for I := 0 to Args.Count - 1 do
      if (Templ.ParamConstraints <> nil) and (I < Templ.ParamConstraints.Count) then
        CheckTypeParamConstraint(Templ.ParamNames.Strings[I], Args.Strings[I],
          Templ.ParamConstraints.Strings[I],
          Format('instantiation ''%s''', [ATypeName]));

    { Create the concrete class type descriptor — defined globally so the
      symbol survives scope pops and is visible after analysis completes. }
    RT  := FTable.NewClassType(ATypeName);
    Sym := TSymbol.Create(ATypeName, skType, RT);
    FTable.DefineGlobal(Sym);

    { Build substituted clone of the class definition }
    ClonedCD             := TClassTypeDef.Create;
    ClonedCD.ParentName  := Templ.ClassDef.ParentName;
    for I := 0 to Templ.ClassDef.ImplementsNames.Count - 1 do
      ClonedCD.ImplementsNames.Add(Templ.ClassDef.ImplementsNames.Strings[I]);

    { Clone fields with type-param substitution (handles ^T → ^Integer etc.) }
    for I := 0 to Templ.ClassDef.Fields.Count - 1 do
    begin
      FDecl    := TFieldDecl(Templ.ClassDef.Fields.Items[I]);
      NewFDecl := TFieldDecl.Create;
      for J := 0 to FDecl.Names.Count - 1 do
        NewFDecl.Names.Add(FDecl.Names.Strings[J]);
      NewFDecl.TypeName := SubstTypeParam(FDecl.TypeName, Templ.ParamNames, Args);
      ClonedCD.Fields.Add(NewFDecl);
    end;

    { Clone method declarations (shared body — OwnBody = False) }
    for I := 0 to Templ.ClassDef.Methods.Count - 1 do
    begin
      MDecl            := TMethodDecl(Templ.ClassDef.Methods.Items[I]);
      NewMDecl         := TMethodDecl.Create;
      NewMDecl.Name          := MDecl.Name;
      NewMDecl.OwnerTypeName := ATypeName;
      NewMDecl.IsVirtual     := MDecl.IsVirtual;
      NewMDecl.IsOverride    := MDecl.IsOverride;
      NewMDecl.Body          := MDecl.Body;
      NewMDecl.OwnBody       := False;

      for J := 0 to MDecl.Params.Count - 1 do
      begin
        Par    := TMethodParam(MDecl.Params.Items[J]);
        NewPar := TMethodParam.Create;
        NewPar.ParamName  := Par.ParamName;
        NewPar.IsVarParam := Par.IsVarParam;
        NewPar.TypeName   := SubstTypeParam(Par.TypeName, Templ.ParamNames, Args);
        NewMDecl.Params.Add(NewPar);
      end;

      NewMDecl.ReturnTypeName :=
        SubstTypeParam(MDecl.ReturnTypeName, Templ.ParamNames, Args);

      ClonedCD.Methods.Add(NewMDecl);
    end;

    { Clone property declarations with type-param substitution }
    for I := 0 to Templ.ClassDef.Properties.Count - 1 do
    begin
      PDecl    := TPropertyDecl(Templ.ClassDef.Properties.Items[I]);
      NewPDecl := TPropertyDecl.Create;
      NewPDecl.Name           := PDecl.Name;
      NewPDecl.TypeName       := SubstTypeParam(PDecl.TypeName, Templ.ParamNames, Args);
      NewPDecl.ReadName       := PDecl.ReadName;
      NewPDecl.WriteName      := PDecl.WriteName;
      NewPDecl.IndexParamName := PDecl.IndexParamName;
      NewPDecl.IndexTypeName  := SubstTypeParam(PDecl.IndexTypeName, Templ.ParamNames, Args);
      ClonedCD.Properties.Add(NewPDecl);
    end;

    { Pre-pass: vtable slots (before fields so vptr is counted in offsets) }
    for J := 0 to ClonedCD.Methods.Count - 1 do
    begin
      NewMDecl := TMethodDecl(ClonedCD.Methods.Items[J]);
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
      NewFDecl := TFieldDecl(ClonedCD.Fields.Items[J]);
      FldType  := FindTypeOrInstantiate(NewFDecl.TypeName);
      if FldType = nil then
        SemanticError(
          Format('Unknown type ''%s'' for field in ''%s''', [NewFDecl.TypeName, ATypeName]),
          0, 0);
      NewFDecl.ResolvedType := FldType;
      for K := 0 to NewFDecl.Names.Count - 1 do
      begin
        FldName := NewFDecl.Names.Strings[K];
        RT.AddField(FldName, FldType);
      end;
    end;

    { Resolve method signatures and index them }
    for J := 0 to ClonedCD.Methods.Count - 1 do
    begin
      NewMDecl := TMethodDecl(ClonedCD.Methods.Items[J]);
      Key      := ATypeName + '.' + NewMDecl.Name;
      FMethodIndex.AddObject(Key, NewMDecl);
      if SameText(NewMDecl.Name, 'Destroy') then
        RT.HasDestroyMethod := True;

      if NewMDecl.IsVirtual or NewMDecl.IsOverride then
        NewMDecl.VTableSlot := RT.FindVTableSlot(NewMDecl.Name);

      for K := 0 to NewMDecl.Params.Count - 1 do
      begin
        Par     := TMethodParam(NewMDecl.Params.Items[K]);
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

    { Resolve property declarations — type-param already substituted in clone pass }
    for J := 0 to ClonedCD.Properties.Count - 1 do
    begin
      NewPDecl := TPropertyDecl(ClonedCD.Properties.Items[J]);
      PropType := FindTypeOrInstantiate(NewPDecl.TypeName);
      if PropType = nil then
        SemanticError(
          Format('Unknown type ''%s'' for property ''%s'' in ''%s''',
            [NewPDecl.TypeName, NewPDecl.Name, ATypeName]),
          0, 0);
      PropInfo := TPropertyInfo.Create;
      PropInfo.Name := NewPDecl.Name;
      PropInfo.TypeDesc := PropType;
      if NewPDecl.ReadName <> '' then
      begin
        if RT.FindField(NewPDecl.ReadName) <> nil then
          PropInfo.ReadField := NewPDecl.ReadName
        else
          PropInfo.ReadMethod := NewPDecl.ReadName;
      end;
      if NewPDecl.WriteName <> '' then
      begin
        if RT.FindField(NewPDecl.WriteName) <> nil then
          PropInfo.WriteField := NewPDecl.WriteName
        else
          PropInfo.WriteMethod := NewPDecl.WriteName;
      end;
      PropInfo.IndexParamName := NewPDecl.IndexParamName;
      if NewPDecl.IndexTypeName <> '' then
        PropInfo.IndexTypeDesc := FindTypeOrInstantiate(NewPDecl.IndexTypeName);
      RT.AddProperty(PropInfo);
    end;

    { Analyse method bodies with concrete types in scope.
      Push type-param bindings (T=Integer etc.) so that SizeOf(T) and
      local var declarations like 'var P: ^T' resolve to concrete types. }
    FTable.PushScope;
    try
      for K := 0 to Templ.ParamNames.Count - 1 do
      begin
        ConcrType := FindTypeOrInstantiate(Args.Strings[K]);
        if ConcrType <> nil then
        begin
          Sym := TSymbol.Create(Templ.ParamNames.Strings[K], skType, ConcrType);
          FTable.Define(Sym);
        end;
      end;
      for J := 0 to ClonedCD.Methods.Count - 1 do
      begin
        NewMDecl := TMethodDecl(ClonedCD.Methods.Items[J]);
        if NewMDecl.Body <> nil then
          AnalyseMethodDecl(NewMDecl, RT);
      end;
    finally
      FTable.PopScope;
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

function TSemanticAnalyser.InstantiateGenericInterface(const ATypeName: string): TInterfaceTypeDesc;
var
  BracPos:     Integer;
  BaseName:    string;
  ArgsStr:     string;
  Args:        TStringList;
  Templ:       TGenericInterfaceDef;
  TemplObj:    TObject;
  I:           Integer;
  MDecl:       TMethodDecl;
  Sym:         TSymbol;
  GII:         TGenericInterfaceInstance;
  MangledName: string;
begin
  Result := nil;

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

    TemplObj := FTable.FindGeneric(BaseName);
    if (TemplObj = nil) or not (TemplObj is TGenericInterfaceDef) then Exit;
    Templ := TGenericInterfaceDef(TemplObj);
    if Args.Count <> Templ.ParamNames.Count then Exit;

    for I := 0 to Args.Count - 1 do
      if (Templ.ParamConstraints <> nil) and (I < Templ.ParamConstraints.Count) then
        CheckTypeParamConstraint(Templ.ParamNames.Strings[I], Args.Strings[I],
          Templ.ParamConstraints.Strings[I],
          Format('interface instantiation ''%s''', [ATypeName]));

    { Check if already instantiated }
    Sym := FTable.Lookup(ATypeName);
    if (Sym <> nil) and (Sym.TypeDesc is TInterfaceTypeDesc) then
    begin
      Result := TInterfaceTypeDesc(Sym.TypeDesc);
      Exit;
    end;

    { Build mangled name: IEqualityComparer<Integer> → IEqualityComparer_Integer }
    MangledName := BaseName;
    for I := 0 to Args.Count - 1 do
      MangledName := MangledName + '_' + Args.Strings[I];

    { Create the concrete interface type descriptor }
    Result := FTable.NewInterfaceType(ATypeName);
    Sym    := TSymbol.Create(ATypeName, skType, Result);
    FTable.DefineGlobal(Sym);

    { Register interface method names with substituted return types }
    for I := 0 to Templ.IntfDef.Methods.Count - 1 do
    begin
      MDecl := TMethodDecl(Templ.IntfDef.Methods.Items[I]);
      Result.AddMethod(MDecl.Name,
        SubstTypeParam(MDecl.ReturnTypeName, Templ.ParamNames, Args));
    end;

    { Register the instantiation for codegen }
    GII          := TGenericInterfaceInstance.Create;
    GII.InstName := MangledName;
    GII.IntfDef.Free;
    GII.IntfDef  := nil;
    GII.TypeDesc := Result;
    FProg.GenericIntfInstances.Add(GII);
  finally
    Args.Free;
  end;
end;

function TSemanticAnalyser.InstantiateGenericFunc(const AInstName: string): TMethodDecl;
var
  BracPos:     Integer;
  BaseName:    string;
  ArgsStr:     string;
  Args:        TStringList;
  Templ:       TMethodDecl;
  TemplIdx:    Integer;
  NewMDecl:    TMethodDecl;
  NewPar:      TMethodParam;
  OldPar:      TMethodParam;
  ParTypeName: string;
  RetTypeName: string;
  SubstType:   TTypeDesc;
  I, J:        Integer;
  Sym:         TSymbol;
  GFI:         TGenericFuncInstance;
begin
  Result := nil;

  { Parse 'Identity<Integer>' → BaseName='Identity', ArgsStr='Integer' }
  BracPos := Pos('<', AInstName);
  if BracPos = 0 then Exit;

  BaseName := Copy(AInstName, 1, BracPos - 1);
  ArgsStr  := Copy(AInstName, BracPos + 1, Length(AInstName) - BracPos - 1);

  TemplIdx := FGenericFuncTemplates.IndexOf(BaseName);
  if TemplIdx < 0 then Exit;  { not a known generic function template }

  Templ := TMethodDecl(FGenericFuncTemplates.Objects[TemplIdx]);

  Args := TStringList.Create;
  try
    while Length(ArgsStr) > 0 do
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

    if Args.Count <> Templ.TypeParams.Count then
      SemanticError(
        Format('Generic function ''%s'' expects %d type parameter(s) but got %d',
          [BaseName, Templ.TypeParams.Count, Args.Count]),
        0, 0);

    { Validate each type argument against the template's declared constraints. }
    for I := 0 to Args.Count - 1 do
      if (Templ.TypeParamConstraints <> nil) and
         (I < Templ.TypeParamConstraints.Count) then
        CheckTypeParamConstraint(Templ.TypeParams.Strings[I], Args.Strings[I],
          Templ.TypeParamConstraints.Strings[I],
          Format('generic function ''%s''', [AInstName]));

    NewMDecl         := TMethodDecl.Create;
    NewMDecl.Name    := AInstName;
    NewMDecl.OwnBody := False;   { share the template body }
    NewMDecl.Body    := Templ.Body;

    { Substitute return type }
    RetTypeName := Templ.ReturnTypeName;
    for I := 0 to Templ.TypeParams.Count - 1 do
      if SameText(RetTypeName, Templ.TypeParams.Strings[I]) then
        RetTypeName := Args.Strings[I];
    NewMDecl.ReturnTypeName := RetTypeName;
    if RetTypeName <> '' then
    begin
      SubstType := FindTypeOrInstantiate(RetTypeName);
      if SubstType = nil then
        SemanticError(Format('Unknown type ''%s'' in generic function instance ''%s''',
          [RetTypeName, AInstName]), 0, 0);
      NewMDecl.ResolvedReturnType := SubstType;
    end;

    { Clone params with substituted types }
    for I := 0 to Templ.Params.Count - 1 do
    begin
      OldPar           := TMethodParam(Templ.Params.Items[I]);
      NewPar           := TMethodParam.Create;
      NewPar.ParamName  := OldPar.ParamName;
      NewPar.IsVarParam := OldPar.IsVarParam;
      ParTypeName       := OldPar.TypeName;
      for J := 0 to Templ.TypeParams.Count - 1 do
        if SameText(ParTypeName, Templ.TypeParams.Strings[J]) then
          ParTypeName := Args.Strings[J];
      NewPar.TypeName := ParTypeName;
      SubstType := FindTypeOrInstantiate(ParTypeName);
      if SubstType = nil then
        SemanticError(Format('Unknown type ''%s'' for parameter ''%s'' in ''%s''',
          [ParTypeName, NewPar.ParamName, AInstName]), 0, 0);
      NewPar.ResolvedType := SubstType;
      NewMDecl.Params.Add(NewPar);
    end;

    { Analyse the shared body with concrete types in scope }
    AnalyseStandaloneDecl(NewMDecl);

    { Register in proc index and global symbol table }
    FProcIndex.AddObject(AInstName, NewMDecl);
    if NewMDecl.ReturnTypeName <> '' then
      Sym := TSymbol.Create(AInstName, skFunction, NewMDecl.ResolvedReturnType)
    else
      Sym := TSymbol.Create(AInstName, skProcedure, nil);
    FTable.DefineGlobal(Sym);

    { Store for codegen }
    GFI            := TGenericFuncInstance.Create;
    GFI.InstName   := AInstName;
    GFI.MethodDecl := NewMDecl;
    FProg.GenericFuncInstances.Add(GFI);

    Result := NewMDecl;
  finally
    Args.Free;
  end;
end;

procedure TSemanticAnalyser.AnalyseBlock(ABlock: TBlock);
begin
  { Type declarations are registered in the outer scope so they remain visible
    after the block scope is popped — needed for var declarations and the
    transferred symbol table used by codegen. }
  AnalyseConstDecls(ABlock);
  AnalyseTypeDecls(ABlock);
  { Link standalone TTypeName.MethodName implementations to their class method
    declarations, transferring the body so AnalyseMethodBodies can process it. }
  LinkClassMethodImpls(ABlock);
  LinkGenericClassMethodImpls(ABlock);
  { Register standalone proc/func signatures before class method bodies so that
    methods can call free functions declared in the same block. }
  AnalyseStandaloneDecls(ABlock);
  AnalyseMethodBodies(ABlock);
  FTable.PushScope;
  Inc(FScopeDepth);
  try
    AnalyseVarDecls(ABlock);
    AnalyseStandaloneBodies(ABlock);
    AnalyseStmts(ABlock);
  finally
    Dec(FScopeDepth);
    FTable.PopScope;
  end;
end;

procedure TSemanticAnalyser.AnalyseConstDecls(ABlock: TBlock);
var
  I:    Integer;
  CD:   TConstDecl;
  Sym:  TSymbol;
  TD:   TTypeDesc;
begin
  for I := 0 to ABlock.ConstDecls.Count - 1 do
  begin
    CD := TConstDecl(ABlock.ConstDecls.Items[I]);
    if CD.IsString then
      TD := FTable.TypeString
    else
      TD := FTable.TypeInteger;
    Sym              := TSymbol.Create(CD.Name, skConstant, TD);
    Sym.ConstValue   := CD.IntVal;
    Sym.ConstString  := CD.StrVal;
    if not FTable.Define(Sym) then
      Sym.Free;  { duplicate const — silently ignore }
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
  PropDecl:   TPropertyDecl;
  PropInfo:   TPropertyInfo;
  PropType:   TTypeDesc;
  EnumDesc:   TEnumTypeDesc;
  EnumDef:    TEnumTypeDef;
  SetDesc:    TSetTypeDesc;
  SetDef:     TSetTypeDef;
  BaseSym:    TSymbol;
  MName:      string;
  MSym:       TSymbol;
  Slot:       Integer;
  CD:         TConstDecl;
begin
  { Pass 1 — register all type symbols with empty descriptors.
    This allows self-referential field types to resolve in pass 2. }
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
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
    else if TD.Def is TGenericInterfaceDef then
    begin
      { Register as template — instantiated on demand when used as type name }
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
    else if TD.Def is TEnumTypeDef then
    begin
      { Enum type: register the type AND each member as a skConstant }
      EnumDef  := TEnumTypeDef(TD.Def);
      EnumDesc := FTable.NewEnumType(TD.Name);
      for K := 0 to EnumDef.Members.Count - 1 do
      begin
        MName           := EnumDef.Members.Strings[K];
        EnumDesc.Members.Add(MName);
        MSym            := TSymbol.Create(MName, skConstant, EnumDesc);
        MSym.ConstValue := K;
        if not FTable.Define(MSym) then
          MSym.Free;
      end;
      Sym := TSymbol.Create(TD.Name, skType, EnumDesc);
      if not FTable.Define(Sym) then
      begin
        Sym.Free;
        SemanticError(Format('Duplicate type name ''%s''', [TD.Name]), TD.Line, TD.Col);
      end;
      Continue;
    end
    else if TD.Def is TSetTypeDef then
    begin
      { Set type: base type must be a previously-defined enum }
      SetDef   := TSetTypeDef(TD.Def);
      BaseSym  := FTable.Lookup(SetDef.BaseTypeName);
      if (BaseSym = nil) or (BaseSym.Kind <> skType) or
         not (BaseSym.TypeDesc is TEnumTypeDesc) then
        SemanticError(
          Format('Set base type ''%s'' must be an enumeration type', [SetDef.BaseTypeName]),
          TD.Line, TD.Col);
      SetDesc := FTable.NewSetType(TD.Name, TEnumTypeDesc(BaseSym.TypeDesc));
      Sym := TSymbol.Create(TD.Name, skType, SetDesc);
      if not FTable.Define(Sym) then
      begin
        Sym.Free;
        SemanticError(Format('Duplicate type name ''%s''', [TD.Name]), TD.Line, TD.Col);
      end;
      Continue;
    end
    else
    begin
      SemanticError('Only record, class, interface, enum, or set type definitions are supported',
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
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);

    { Generic templates, enum, and set types need no pass-2 processing — skip }
    if TD.Def is TGenericTypeDef then Continue;
    if TD.Def is TGenericInterfaceDef then Continue;
    if TD.Def is TEnumTypeDef then Continue;
    if TD.Def is TSetTypeDef then Continue;

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
          IntfDesc.AddMethod(IntfDesc.Parent.MethodName(J),
            IntfDesc.Parent.MethodReturnTypeName(J));
      end;
      for J := 0 to ITD.Methods.Count - 1 do
        IntfDesc.AddMethod(TMethodDecl(ITD.Methods.Items[J]).Name,
          TMethodDecl(ITD.Methods.Items[J]).ReturnTypeName);
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

      { Copy inherited fields and vtable from parent class first.
        The parser may store a generic interface name (e.g. IFoo<T>) as ParentName
        when no explicit class parent was specified — detect this and treat it as
        an implements entry instead. }
      if TClassTypeDef(TD.Def).ParentName <> '' then
      begin
        ParentSym := nil;
        { If name looks generic, try instantiating as interface first }
        if Pos('<', TClassTypeDef(TD.Def).ParentName) > 0 then
        begin
          IntfDesc := TInterfaceTypeDesc(
            FindTypeOrInstantiate(TClassTypeDef(TD.Def).ParentName));
          if IntfDesc <> nil then
          begin
            { Treat it as an interface to implement — move to implements list }
            TClassTypeDef(TD.Def).ImplementsNames.Insert(
              0, TClassTypeDef(TD.Def).ParentName);
            TClassTypeDef(TD.Def).ParentName := '';
          end;
        end;
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
            FldInfo := TFieldInfo(ParentRT.Fields.Items[K]);
            RT.AddField(FldInfo.Name, FldInfo.TypeDesc);
          end;
        end;
      end;

      { If no explicit parent was specified (and this class is not TObject itself),
        implicitly inherit TObject's vtable so that all class types carry a vptr.
        This ensures field offsets start after the 8-byte vtable pointer.
        We do NOT set RT.Parent here — root classes have null parent in typeinfo. }
      if (TClassTypeDef(TD.Def).ParentName = '') and (TD.Name <> 'TObject') then
      begin
        ParentSym := FTable.Lookup('TObject');
        if (ParentSym <> nil) and (ParentSym.TypeDesc is TRecordTypeDesc) then
        begin
          ParentRT := TRecordTypeDesc(ParentSym.TypeDesc);
          RT.CopyVTableFrom(ParentRT);
        end;
      end;

      { Pre-pass: register vtable slots for virtual/override methods BEFORE
        adding own fields, so that field offsets correctly account for the vptr. }
      if MethodList <> nil then
        for J := 0 to MethodList.Count - 1 do
        begin
          MDecl := TMethodDecl(MethodList.Items[J]);
          if MDecl.IsVirtual then
            RT.AddVTableSlot(MDecl.Name, '$' + TD.Name + '_' + MDecl.Name)
          else if MDecl.IsOverride then
          begin
            Slot := RT.FindVTableSlot(MDecl.Name);
            if Slot < 0 then
            begin
              { No inherited vtable slot — check if TObject provides the virtual
                base (handles both parentless classes and deep hierarchies where
                an intermediate class doesn't declare the method as virtual). }
              ParentSym := FTable.Lookup('TObject');
              if (ParentSym <> nil) and (ParentSym.TypeDesc is TRecordTypeDesc) then
              begin
                ParentRT := TRecordTypeDesc(ParentSym.TypeDesc);
                if ParentRT.FindVTableSlot(MDecl.Name) >= 0 then
                begin
                  RT.CopyVTableFrom(ParentRT);
                  if RT.Parent = nil then
                    RT.Parent := ParentRT;
                  Slot := RT.FindVTableSlot(MDecl.Name);
                end;
              end;
            end;
            RT.OverrideVTableSlot(Slot, '$' + TD.Name + '_' + MDecl.Name);
          end;
        end;
    end;

    { Resolve own field declarations (offsets now include vptr if HasVTable) }
    for J := 0 to FieldList.Count - 1 do
    begin
      FDecl   := TFieldDecl(FieldList.Items[J]);
      FldType := FindTypeOrInstantiate(FDecl.TypeName);
      if FldType = nil then
        SemanticError(
          Format('Unknown type ''%s'' for field', [FDecl.TypeName]),
          FDecl.Line, FDecl.Col);
      FDecl.ResolvedType := FldType;
      { Resolve [Weak] on fields.  Same type constraint as local vars. }
      if HasWeakAttribute(FDecl.Attributes) then
      begin
        if not ((FldType.Kind = tyClass) or (FldType.Kind = tyInterface)) then
          SemanticError(
            Format('[Weak] can only be applied to class or interface ' +
                   'fields, not ''%s''', [FDecl.TypeName]),
            FDecl.Line, FDecl.Col);
        FDecl.IsWeak := True;
      end;
      for K := 0 to FDecl.Names.Count - 1 do
      begin
        FldName := FDecl.Names.Strings[K];
        RT.AddField(FldName, FldType);
        { Propagate the weak flag to the just-added field info so codegen
          and the field cleanup emitter can consult it without walking
          back to the AST. }
        if FDecl.IsWeak then
          RT.FindField(FldName).IsWeak := True;
      end;
    end;

    { Index class methods, record VTableSlot on MDecl, resolve param/return types }
    if MethodList <> nil then
      for J := 0 to MethodList.Count - 1 do
      begin
        MDecl               := TMethodDecl(MethodList.Items[J]);
        MDecl.OwnerTypeName := TD.Name;
        Key                 := TD.Name + '.' + MDecl.Name;
        FMethodIndex.AddObject(Key, MDecl);
        if SameText(MDecl.Name, 'Destroy') then
          RT.HasDestroyMethod := True;

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
          Par              := TMethodParam(MDecl.Params.Items[K]);
          Par.ResolvedType := ResolveParamType(Par, MDecl.Line, MDecl.Col);
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

    { Resolve property declarations }
    if TD.Def is TClassTypeDef then
      for J := 0 to TClassTypeDef(TD.Def).Properties.Count - 1 do
      begin
        PropDecl := TPropertyDecl(TClassTypeDef(TD.Def).Properties.Items[J]);
        PropType := FTable.FindType(PropDecl.TypeName);
        if PropType = nil then
          SemanticError(
            Format('Unknown type ''%s'' for property ''%s''',
              [PropDecl.TypeName, PropDecl.Name]),
            PropDecl.Line, PropDecl.Col);
        PropInfo := TPropertyInfo.Create;
        PropInfo.Name := PropDecl.Name;
        PropInfo.TypeDesc := PropType;
        if PropDecl.ReadName <> '' then
        begin
          if RT.FindField(PropDecl.ReadName) <> nil then
            PropInfo.ReadField := PropDecl.ReadName
          else
            PropInfo.ReadMethod := PropDecl.ReadName;
        end;
        if PropDecl.WriteName <> '' then
        begin
          if RT.FindField(PropDecl.WriteName) <> nil then
            PropInfo.WriteField := PropDecl.WriteName
          else
            PropInfo.WriteMethod := PropDecl.WriteName;
        end;
        PropInfo.IndexParamName := PropDecl.IndexParamName;
        if PropDecl.IndexTypeName <> '' then
          PropInfo.IndexTypeDesc := FTable.FindType(PropDecl.IndexTypeName);
        RT.AddProperty(PropInfo);
      end;

    { Register class-level constants in the global scope — accessible both
      unqualified (MaxItems) and qualified (TFoo.MaxItems) }
    if TD.Def is TClassTypeDef then
      for J := 0 to TClassTypeDef(TD.Def).ConstDecls.Count - 1 do
      begin
        CD := TConstDecl(TClassTypeDef(TD.Def).ConstDecls.Items[J]);
        if CD.IsString then
          ParType := FTable.TypeString
        else
          ParType := FTable.TypeInteger;
        { Unqualified name — usable inside class methods without prefix }
        Sym := TSymbol.Create(CD.Name, skConstant, ParType);
        Sym.ConstValue  := CD.IntVal;
        Sym.ConstString := CD.StrVal;
        if not FTable.Define(Sym) then
          Sym.Free;
        { Qualified name — usable as TFoo.MaxItems from anywhere }
        Sym := TSymbol.Create(TD.Name + '.' + CD.Name, skConstant, ParType);
        Sym.ConstValue  := CD.IntVal;
        Sym.ConstString := CD.StrVal;
        if not FTable.Define(Sym) then
          Sym.Free;
      end;

    { Verify class implements all methods of each declared interface }
    if TD.Def is TClassTypeDef then
      for L := 0 to TClassTypeDef(TD.Def).ImplementsNames.Count - 1 do
      begin
        IntfName := TClassTypeDef(TD.Def).ImplementsNames.Strings[L];
        IntfSym  := FTable.Lookup(IntfName);
        if IntfSym = nil then
        begin
          { May be a generic interface — try instantiation }
          IntfDesc := TInterfaceTypeDesc(FindTypeOrInstantiate(IntfName));
          if IntfDesc = nil then
            SemanticError(
              Format('Unknown interface ''%s'' in implements list of ''%s''',
                [IntfName, TD.Name]),
              TD.Line, TD.Col);
          IntfSym := FTable.Lookup(IntfName);
        end;
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
                if SameText(TMethodDecl(TClassTypeDef(TD.Def).Methods.Items[K]).Name, Key) then
                begin
                  MDecl := TMethodDecl(TClassTypeDef(TD.Def).Methods.Items[K]);
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
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
    if not (TD.Def is TClassTypeDef) then
      Continue;
    CD  := TClassTypeDef(TD.Def);
    Sym := FTable.Lookup(TD.Name);
    if (Sym = nil) or not (Sym.TypeDesc is TRecordTypeDesc) then
      Continue;
    RT := TRecordTypeDesc(Sym.TypeDesc);
    for J := 0 to CD.Methods.Count - 1 do
      AnalyseMethodDecl(TMethodDecl(CD.Methods.Items[J]), RT);
  end;
end;

procedure TSemanticAnalyser.AnalyseMethodDecl(
  AMethod: TMethodDecl; AClassType: TRecordTypeDesc);
var
  I:          Integer;
  Par:        TMethodParam;
  Sym:        TSymbol;
  SavedClass: TRecordTypeDesc;
begin
  SavedClass    := FCurrentClass;
  FCurrentClass := AClassType;
  FTable.PushScope;
  Inc(FScopeDepth);
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
      Par := TMethodParam(AMethod.Params.Items[I]);
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
    if AMethod.Body <> nil then
      AnalyseBlock(AMethod.Body);
  finally
    Dec(FScopeDepth);
    FTable.PopScope;
    FCurrentClass := SavedClass;
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
    ADecl := TMethodDecl(ABlock.ProcDecls.Items[I]);
    { Class method implementations have their body transferred; skip them here }
    if ADecl.OwnerTypeName <> '' then Continue;
    { Generic function templates — registered for on-demand instantiation }
    if ADecl.TypeParams <> nil then
    begin
      FGenericFuncTemplates.AddObject(ADecl.Name, ADecl);
      Continue;
    end;

    { Resolve parameter types }
    for J := 0 to ADecl.Params.Count - 1 do
    begin
      Par              := TMethodParam(ADecl.Params.Items[J]);
      Par.ResolvedType := ResolveParamType(Par, ADecl.Line, ADecl.Col);
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

    { If an earlier forward declaration exists, update the index to point to
      this implementation and skip re-registering the symbol. }
    J := FProcIndex.IndexOf(ADecl.Name);
    if (J >= 0) and (TMethodDecl(FProcIndex.Objects[J]).Body = nil) then
    begin
      FProcIndex.Objects[J] := ADecl;
      Continue;
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
  Inc(FScopeDepth);
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
      Par := TMethodParam(ADecl.Params.Items[I]);
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

    if not ADecl.IsExternal then
      AnalyseBlock(ADecl.Body);
  finally
    Dec(FScopeDepth);
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
    ADecl := TMethodDecl(ABlock.ProcDecls.Items[I]);
    { Class method implementations have their body transferred; skip them here }
    if ADecl.OwnerTypeName <> '' then Continue;
    { Generic templates are instantiated on demand — skip until first call }
    if ADecl.TypeParams <> nil then Continue;
    { Forward declarations have no body; the later impl handles analysis }
    if ADecl.Body = nil then Continue;
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
    Decl := TVarDecl(ABlock.Decls.Items[I]);

    Typ := FindTypeOrInstantiate(Decl.TypeName);
    if Typ = nil then
      SemanticError(
        Format('Unknown type ''%s''', [Decl.TypeName]),
        Decl.Line, Decl.Col);

    Decl.ResolvedType := Typ;

    { Resolve [Weak].  Only reference types carry strong refcounts, so
      weakness is meaningful only on classes and interfaces.  Rejecting
      it elsewhere catches misuse at the declaration site rather than
      later when the user wonders why the attribute had no effect. }
    if HasWeakAttribute(Decl.Attributes) then
    begin
      if not ((Typ.Kind = tyClass) or (Typ.Kind = tyInterface)) then
        SemanticError(
          Format('[Weak] can only be applied to class or interface types, ' +
                 'not ''%s''', [Decl.TypeName]),
          Decl.Line, Decl.Col);
      Decl.IsWeak := True;
    end;

    { Depth 2 = inside the top-level program block — these are global variables. }
    Decl.IsGlobal := (FScopeDepth = 1);  { depth 1 = main program block (global scope) }
    for J := 0 to Decl.Names.Count - 1 do
    begin
      VarName := Decl.Names.Strings[J];
      Sym := TSymbol.Create(VarName, skVariable, Typ);
      Sym.IsWeak   := Decl.IsWeak;
      Sym.IsGlobal := Decl.IsGlobal;
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
    AnalyseStmt(TASTStmt(ABody.Stmts.Items[I]));
end;

procedure TSemanticAnalyser.AnalyseStmts(ABlock: TBlock);
var
  I:         Integer;
  PrevBlock: TBlock;
begin
  PrevBlock := FCurrentLocalBlock;
  FCurrentLocalBlock := ABlock;
  try
    for I := 0 to ABlock.Stmts.Count - 1 do
      AnalyseStmt(TASTStmt(ABlock.Stmts.Items[I]));
  finally
    FCurrentLocalBlock := PrevBlock;
  end;
end;

procedure TSemanticAnalyser.AnalyseStmt(AStmt: TASTStmt);
var
  IfS:    TIfStmt;
  CmpS:   TCompoundStmt;
  ForS:   TForStmt;
  ForInS: TForInStmt;
  WS:     TWhileStmt;
  RS:     TRepeatStmt;
  TFS:    TTryFinallyStmt;
  TES:    TTryExceptStmt;
  H:      TExceptHandlerClause;
  RaiseS: TRaiseStmt;
  I:         Integer;
  CondType:  TTypeDesc;
  VarSym:    TSymbol;
  StartType: TTypeDesc;
  EndType:   TTypeDesc;
  CollType:     TTypeDesc;
  CollRT:       TRecordTypeDesc;
  GetEnumDecl:  TMethodDecl;
  EnumType:     TTypeDesc;
  EnumRT:       TRecordTypeDesc;
  MNDecl:       TMethodDecl;
  CurProp:      TPropertyInfo;
  CurDecl:      TMethodDecl;
  ElemType:     TTypeDesc;
  SynthDecl:    TVarDecl;
  WalkRT:       TRecordTypeDesc;
begin
  if AStmt is TForStmt then
  begin
    ForS := TForStmt(AStmt);
    VarSym := FTable.Lookup(ForS.VarName);
    if VarSym = nil then
      SemanticError(
        Format('Undeclared loop variable ''%s''', [ForS.VarName]),
        ForS.Line, ForS.Col);
    ForS.IsGlobal := (VarSym <> nil) and VarSym.IsGlobal;
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
    Inc(FLoopDepth);
    try
      AnalyseStmt(ForS.Body);
    finally
      Dec(FLoopDepth);
    end;
  end
  else if AStmt is TForInStmt then
  begin
    ForInS := TForInStmt(AStmt);

    { 1. Analyse the collection expression }
    CollType := AnalyseExpr(ForInS.CollExpr);
    if CollType = nil then
      SemanticError('for-in collection has unknown type',
        ForInS.Line, ForInS.Col);

    if CollType.Kind = tyStaticArray then
    begin
      { ---- Static array iteration path ---- }
      ElemType := TStaticArrayTypeDesc(CollType).ElementType;

      VarSym := FTable.Lookup(ForInS.VarName);
      if VarSym = nil then
        SemanticError(
          Format('Undeclared loop variable ''%s''', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      if VarSym.Kind <> skVariable then
        SemanticError(
          Format('''%s'' is not a variable', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      CheckTypesMatch(VarSym.TypeDesc, ElemType,
        'for-in loop variable', ForInS.Line, ForInS.Col);
      ForInS.VarIsGlobal    := VarSym.IsGlobal;
      ForInS.IsArrayIter    := True;
      ForInS.ResolvedVarType := ElemType;
      ForInS.ArrayLow  := TStaticArrayTypeDesc(CollType).LowBound;
      ForInS.ArrayHigh := TStaticArrayTypeDesc(CollType).HighBound;

      { Inject synthetic index slot __idx_N (Integer) }
      ForInS.IdxVarName := '__idx_' + IntToStr(FForInCounter);
      Inc(FForInCounter);
      if FCurrentLocalBlock <> nil then
      begin
        SynthDecl := TVarDecl.Create;
        SynthDecl.Names.Add(ForInS.IdxVarName);
        SynthDecl.TypeName    := 'Integer';
        SynthDecl.ResolvedType := FTable.TypeInteger;
        SynthDecl.IsGlobal    := False;
        FCurrentLocalBlock.Decls.Add(SynthDecl);
      end;
    end
    else if CollType.Kind = tyClass then
    begin
      { ---- Class enumerator protocol path ---- }
      CollRT := TRecordTypeDesc(CollType);

      GetEnumDecl := FindMethodDecl(CollRT.Name, 'GetEnumerator');
      if GetEnumDecl = nil then
        SemanticError(
          Format('class ''%s'' does not have a GetEnumerator method',
            [CollRT.Name]),
          ForInS.Line, ForInS.Col);

      EnumType := GetEnumDecl.ResolvedReturnType;
      if (EnumType = nil) or (EnumType.Kind <> tyClass) then
        SemanticError(
          Format('GetEnumerator on ''%s'' must return a class type',
            [CollRT.Name]),
          ForInS.Line, ForInS.Col);
      EnumRT := TRecordTypeDesc(EnumType);

      MNDecl := FindMethodDecl(EnumRT.Name, 'MoveNext');
      if MNDecl = nil then
        SemanticError(
          Format('enumerator class ''%s'' does not have a MoveNext method',
            [EnumRT.Name]),
          ForInS.Line, ForInS.Col);
      if (MNDecl.ResolvedReturnType = nil) or
         (MNDecl.ResolvedReturnType.Kind <> tyBoolean) then
        SemanticError(
          Format('MoveNext on enumerator ''%s'' must return Boolean',
            [EnumRT.Name]),
          ForInS.Line, ForInS.Col);

      CurProp := nil;
      WalkRT  := EnumRT;
      while (WalkRT <> nil) and (CurProp = nil) do
      begin
        CurProp := WalkRT.FindProperty('Current');
        WalkRT  := WalkRT.Parent;
      end;
      if CurProp = nil then
        SemanticError(
          Format('enumerator class ''%s'' does not have a Current property',
            [EnumRT.Name]),
          ForInS.Line, ForInS.Col);
      if CurProp.ReadMethod = '' then
        SemanticError(
          Format('Current property on ''%s'' must have a method-backed getter',
            [EnumRT.Name]),
          ForInS.Line, ForInS.Col);

      CurDecl := FindMethodDecl(EnumRT.Name, CurProp.ReadMethod);
      if CurDecl = nil then
        SemanticError(
          Format('getter ''%s'' for Current on ''%s'' not found',
            [CurProp.ReadMethod, EnumRT.Name]),
          ForInS.Line, ForInS.Col);
      ElemType := CurDecl.ResolvedReturnType;

      VarSym := FTable.Lookup(ForInS.VarName);
      if VarSym = nil then
        SemanticError(
          Format('Undeclared loop variable ''%s''', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      if VarSym.Kind <> skVariable then
        SemanticError(
          Format('''%s'' is not a variable', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      CheckTypesMatch(VarSym.TypeDesc, ElemType,
        'for-in loop variable', ForInS.Line, ForInS.Col);
      ForInS.VarIsGlobal := VarSym.IsGlobal;

      ForInS.ResolvedVarType      := ElemType;
      ForInS.ResolvedEnumTypeName := EnumRT.Name;
      ForInS.GetEnumDecl          := GetEnumDecl;
      ForInS.MoveNextDecl         := MNDecl;
      ForInS.CurrentDecl          := CurDecl;

      ForInS.EnumVarName := '__forin_' + IntToStr(FForInCounter);
      Inc(FForInCounter);
      if FCurrentLocalBlock <> nil then
      begin
        SynthDecl := TVarDecl.Create;
        SynthDecl.Names.Add(ForInS.EnumVarName);
        SynthDecl.TypeName    := EnumRT.Name;
        SynthDecl.ResolvedType := EnumType;
        SynthDecl.IsGlobal    := False;
        FCurrentLocalBlock.Decls.Add(SynthDecl);
      end;
    end
    else if CollType.Kind = tyString then
    begin
      { ---- String byte-iteration path ---- }
      VarSym := FTable.Lookup(ForInS.VarName);
      if VarSym = nil then
        SemanticError(
          Format('Undeclared loop variable ''%s''', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      if VarSym.Kind <> skVariable then
        SemanticError(
          Format('''%s'' is not a variable', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      if not VarSym.TypeDesc.IsOrdinal then
        SemanticError(
          Format('for-in over string: loop variable ''%s'' must be an ordinal type',
            [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      ForInS.VarIsGlobal    := VarSym.IsGlobal;
      ForInS.IsStringIter   := True;
      ForInS.ResolvedVarType := FTable.TypeByte;

      ForInS.IdxVarName := '__idx_' + IntToStr(FForInCounter);
      Inc(FForInCounter);
      if FCurrentLocalBlock <> nil then
      begin
        SynthDecl := TVarDecl.Create;
        SynthDecl.Names.Add(ForInS.IdxVarName);
        SynthDecl.TypeName    := 'Integer';
        SynthDecl.ResolvedType := FTable.TypeInteger;
        SynthDecl.IsGlobal    := False;
        FCurrentLocalBlock.Decls.Add(SynthDecl);
      end;
    end
    else
      SemanticError(
        'for-in collection must be a class instance, static array, or string',
        ForInS.Line, ForInS.Col);

    Inc(FLoopDepth);
    try
      AnalyseStmt(ForInS.Body);
    finally
      Dec(FLoopDepth);
    end;
  end
  else if AStmt is TWhileStmt then
  begin
    WS := TWhileStmt(AStmt);
    CondType := AnalyseExpr(WS.Condition);
    if CondType.Kind <> tyBoolean then
      SemanticError(
        Format('while condition must be Boolean, got ''%s''', [CondType.Name]),
        AStmt.Line, AStmt.Col);
    Inc(FLoopDepth);
    try
      AnalyseStmt(WS.Body);
    finally
      Dec(FLoopDepth);
    end;
  end
  else if AStmt is TRepeatStmt then
  begin
    RS := TRepeatStmt(AStmt);
    Inc(FLoopDepth);
    try
      AnalyseCompoundBody(RS.Body);
    finally
      Dec(FLoopDepth);
    end;
    CondType := AnalyseExpr(RS.Condition);
    if CondType.Kind <> tyBoolean then
      SemanticError(
        Format('repeat condition must be Boolean, got ''%s''', [CondType.Name]),
        AStmt.Line, AStmt.Col);
  end
  else if AStmt is TExitStmt then
  begin
    { No semantic checks needed — a bare 'exit' is valid in any method or
      the main program block. }
  end
  else if AStmt is TBreakStmt then
  begin
    if FLoopDepth = 0 then
      SemanticError('''break'' is not inside a loop', AStmt.Line, AStmt.Col);
  end
  else if AStmt is TContinueStmt then
  begin
    if FLoopDepth = 0 then
      SemanticError('''continue'' is not inside a loop', AStmt.Line, AStmt.Col);
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
      AnalyseStmt(TASTStmt(CmpS.Stmts.Items[I]));
  end
  else if AStmt is TTryFinallyStmt then
  begin
    TFS := TTryFinallyStmt(AStmt);
    AnalyseCompoundBody(TFS.TryBody);
    AnalyseCompoundBody(TFS.FinallyBody);
  end
  else if AStmt is TTryExceptStmt then
  begin
    TES := TTryExceptStmt(AStmt);
    AnalyseCompoundBody(TES.TryBody);
    if TES.Handlers.Count > 0 then
    begin
      for I := 0 to TES.Handlers.Count - 1 do
      begin
        H := TExceptHandlerClause(TES.Handlers[I]);
        CondType := FindTypeOrInstantiate(H.TypeName);
        if CondType = nil then
          SemanticError(
            Format('Unknown exception type ''%s''', [H.TypeName]),
            AStmt.Line, AStmt.Col);
        if CondType.Kind <> tyClass then
          SemanticError(
            Format('Exception handler type must be a class, got ''%s''', [H.TypeName]),
            AStmt.Line, AStmt.Col);
        if H.VarName <> '' then
        begin
          { Inject a synthetic local so EmitVarAllocs allocates a stack slot. }
          if FCurrentLocalBlock <> nil then
          begin
            SynthDecl := TVarDecl.Create;
            SynthDecl.Names.Add(H.VarName);
            SynthDecl.TypeName    := H.TypeName;
            SynthDecl.ResolvedType := CondType;
            SynthDecl.IsGlobal    := False;
            FCurrentLocalBlock.Decls.Add(SynthDecl);
          end;
          FTable.PushScope;
          try
            VarSym := TSymbol.Create(H.VarName, skVariable, CondType);
            if not FTable.Define(VarSym) then
              VarSym.Free;
            AnalyseCompoundBody(H.Body);
          finally
            FTable.PopScope;
          end;
        end
        else
          AnalyseCompoundBody(H.Body);
      end;
      if TES.ElseBody <> nil then
        AnalyseCompoundBody(TES.ElseBody);
    end
    else
      AnalyseCompoundBody(TES.ExceptBody);
  end
  else if AStmt is TRaiseStmt then
  begin
    RaiseS := TRaiseStmt(AStmt);
    if RaiseS.Expr <> nil then
    begin
      CondType := AnalyseExpr(RaiseS.Expr);
      if CondType.Kind <> tyClass then
        SemanticError(
          Format('raise expression must be a class instance, got ''%s''',
            [CondType.Name]),
          AStmt.Line, AStmt.Col);
    end;
  end
  else if AStmt is TFieldAssignment then
    AnalyseFieldAssignment(TFieldAssignment(AStmt))
  else if AStmt is TAssignment then
    AnalyseAssignment(TAssignment(AStmt))
  else if AStmt is TMethodCallStmt then
    AnalyseMethodCall(TMethodCallStmt(AStmt))
  else if AStmt is TInheritedCallStmt then
    AnalyseInheritedCall(TInheritedCallStmt(AStmt))
  else if AStmt is TPointerWriteStmt then
    AnalysePointerWriteStmt(TPointerWriteStmt(AStmt))
  else if AStmt is TStaticSubscriptAssign then
    AnalyseStaticSubscriptAssign(TStaticSubscriptAssign(AStmt))
  else if AStmt is TProcCall then
    AnalyseProcCall(TProcCall(AStmt))
  else if AStmt is TCaseStmt then
    AnalyseCaseStmt(TCaseStmt(AStmt));
end;

procedure TSemanticAnalyser.AnalyseMethodCall(ACall: TMethodCallStmt);
var
  ObjSym:  TSymbol;
  RT:      TRecordTypeDesc;
  MDecl:   TMethodDecl;
  Par:     TMethodParam;
  ArgType: TTypeDesc;
  I:       Integer;
  ObjType: TTypeDesc;
begin
  { Call on a receiver expression: AProg.UsedUnits.Add(UName) }
  if ACall.ObjExpr <> nil then
  begin
    ObjType := AnalyseExpr(ACall.ObjExpr);
    if not (ObjType.Kind in [tyClass, tyInterface]) then
      SemanticError(
        Format('Receiver of ''.%s'' must be a class or interface', [ACall.Name]),
        ACall.Line, ACall.Col);
    RT := TRecordTypeDesc(ObjType);
    MDecl := FindMethodDecl(RT.Name, ACall.Name);
    if (MDecl = nil) and SameText(ACall.Name, 'Free') and (ACall.Args.Count = 0) then
    begin
      ACall.ResolvedClassType := RT;
      ACall.ResolvedMethod    := nil;
      Exit;
    end;
    if MDecl = nil then
      SemanticError(
        Format('Class ''%s'' has no method ''%s''', [RT.Name, ACall.Name]),
        ACall.Line, ACall.Col);
    if ACall.Args.Count <> MDecl.Params.Count then
      SemanticError(
        Format('Method ''%s.%s'' expects %d argument(s) but got %d',
          [RT.Name, ACall.Name, MDecl.Params.Count, ACall.Args.Count]),
        ACall.Line, ACall.Col);
    for I := 0 to ACall.Args.Count - 1 do
    begin
      ArgType := AnalyseExpr(TASTExpr(ACall.Args.Items[I]));
      Par     := TMethodParam(MDecl.Params.Items[I]);
      CheckTypesMatch(Par.ResolvedType, ArgType,
        Format('argument %d of ''%s''', [I + 1, ACall.Name]),
        ACall.Line, ACall.Col);
    end;
    ACall.ResolvedClassType := RT;
    ACall.ResolvedMethod    := MDecl;
    Exit;
  end;

  ObjSym := FTable.Lookup(ACall.ObjectName);
  if ObjSym = nil then
  begin
    { Implicit Self.Field.Method — ObjectName is a field of current class }
    if FCurrentClass <> nil then
    begin
      ACall.ImplicitBaseInfo :=
        FCurrentClass.FindField(ACall.ObjectName);
      if (ACall.ImplicitBaseInfo <> nil) and
         (ACall.ImplicitBaseInfo.TypeDesc.Kind in [tyClass, tyInterface]) then
      begin
        ACall.IsImplicitSelf := True;
        RT := TRecordTypeDesc(ACall.ImplicitBaseInfo.TypeDesc);
        MDecl := FindMethodDecl(RT.Name, ACall.Name);
        if (MDecl = nil) and SameText(ACall.Name, 'Free') and (ACall.Args.Count = 0) then
        begin
          ACall.ResolvedClassType := RT;
          ACall.ResolvedMethod    := nil;
          Exit;
        end;
        if MDecl = nil then
          SemanticError(
            Format('Class ''%s'' has no method ''%s''', [RT.Name, ACall.Name]),
            ACall.Line, ACall.Col);
        if ACall.Args.Count <> MDecl.Params.Count then
          SemanticError(
            Format('Method ''%s.%s'' expects %d argument(s) but got %d',
              [RT.Name, ACall.Name, MDecl.Params.Count, ACall.Args.Count]),
            ACall.Line, ACall.Col);
        for I := 0 to ACall.Args.Count - 1 do
        begin
          ArgType := AnalyseExpr(TASTExpr(ACall.Args.Items[I]));
          Par     := TMethodParam(MDecl.Params.Items[I]);
          CheckTypesMatch(Par.ResolvedType, ArgType,
            Format('argument %d of ''%s''', [I + 1, ACall.Name]),
            ACall.Line, ACall.Col);
        end;
        ACall.ResolvedClassType := RT;
        ACall.ResolvedMethod    := MDecl;
        Exit;
      end;
    end;
    SemanticError(
      Format('Undeclared variable ''%s''', [ACall.ObjectName]),
      ACall.Line, ACall.Col);
  end;
  if not (ObjSym.Kind in [skVariable, skParameter, skVarParameter]) then
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
    ACall.IsGlobal          := ObjSym.IsGlobal;
    ACall.IsVarParam        := (ObjSym.Kind = skVarParameter);
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
      ACall.IsGlobal          := ObjSym.IsGlobal;
      ACall.IsVarParam        := (ObjSym.Kind = skVarParameter);
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
    ArgType := AnalyseExpr(TASTExpr(ACall.Args.Items[I]));
    Par     := TMethodParam(MDecl.Params.Items[I]);
    CheckTypesMatch(Par.ResolvedType, ArgType,
      Format('argument %d of ''%s''', [I + 1, ACall.Name]),
      ACall.Line, ACall.Col);
  end;

  ACall.ResolvedClassType := RT;
  ACall.ResolvedMethod    := MDecl;
  ACall.IsGlobal          := ObjSym.IsGlobal;
  ACall.IsVarParam        := (ObjSym.Kind = skVarParameter);
end;

procedure TSemanticAnalyser.AnalyseAssignment(AAssign: TAssignment);
var
  VarSym:  TSymbol;
  FldInfo: TFieldInfo;
  ExprType: TTypeDesc;
begin
  VarSym := FTable.Lookup(AAssign.Name);
  if VarSym = nil then
  begin
    { Try implicit Self.Field }
    if FCurrentClass <> nil then
    begin
      FldInfo := FCurrentClass.FindField(AAssign.Name);
      if FldInfo <> nil then
      begin
        AAssign.ImplicitSelfField := FldInfo;
        AAssign.ResolvedLhsType   := FldInfo.TypeDesc;
        ExprType := AnalyseExpr(AAssign.Expr);
        CheckTypesMatch(FldInfo.TypeDesc, ExprType, 'assignment', AAssign.Line, AAssign.Col);
        Exit;
      end;
    end;
    SemanticError(
      Format('Undeclared variable ''%s''', [AAssign.Name]),
      AAssign.Line, AAssign.Col);
  end;
  if not (VarSym.Kind in [skVariable, skVarParameter, skParameter]) then
    SemanticError(
      Format('''%s'' is not a variable', [AAssign.Name]),
      AAssign.Line, AAssign.Col);

  AAssign.IsVarParam      := (VarSym.Kind = skVarParameter);
  AAssign.ResolvedLhsType := VarSym.TypeDesc;
  AAssign.IsWeakLhs       := VarSym.IsWeak;
  AAssign.IsGlobal        := VarSym.IsGlobal;

  { Set-literal assignment: [elem, ...] on RHS when LHS is a set type }
  if (VarSym.TypeDesc.Kind = tySet) and (AAssign.Expr is TArrayLiteralExpr) then
  begin
    AnalyseSetLiteralExpr(TArrayLiteralExpr(AAssign.Expr),
      TSetTypeDesc(VarSym.TypeDesc));
    Exit;
  end;

  ExprType := AnalyseExpr(AAssign.Expr);
  CheckTypesMatch(VarSym.TypeDesc, ExprType, 'assignment', AAssign.Line, AAssign.Col);
end;

procedure TSemanticAnalyser.AnalyseInheritedCall(ACall: TInheritedCallStmt);
var
  ParentType: TRecordTypeDesc;
  MDecl:      TMethodDecl;
  ArgType:    TTypeDesc;
  Par:        TMethodParam;
  I:          Integer;
begin
  if FCurrentClass = nil then
    SemanticError('''inherited'' used outside a method body',
      ACall.Line, ACall.Col);

  if FCurrentClass.Parent = nil then
  begin
    { No explicit parent — implicit TObject. inherited Create/Destroy are no-ops. }
    if SameText(ACall.Name, 'Create') or SameText(ACall.Name, 'Destroy') then
    begin
      ACall.ResolvedParentType := nil;
      ACall.ResolvedMethod     := nil;
      Exit;
    end;
    SemanticError(
      Format('Class ''%s'' has no parent; ''inherited'' is not valid',
        [FCurrentClass.Name]),
      ACall.Line, ACall.Col);
  end;

  ParentType := FCurrentClass.Parent;

  { TObject is the builtin root class — inherited Create/Destroy are no-ops }
  if SameText(ParentType.Name, 'TObject') then
  begin
    ACall.ResolvedParentType := ParentType;
    ACall.ResolvedMethod     := nil;
    Exit;
  end;

  MDecl := FindMethodDecl(ParentType.Name, ACall.Name);
  if MDecl = nil then
  begin
    { Constructor/destructor chaining: if the parent doesn't explicitly declare
      Create or Destroy, the call chains up to TObject (a no-op in ARC). }
    if SameText(ACall.Name, 'Create') or SameText(ACall.Name, 'Destroy') then
    begin
      ACall.ResolvedParentType := ParentType;
      ACall.ResolvedMethod     := nil;
      Exit;
    end;
    SemanticError(
      Format('Parent class ''%s'' has no method ''%s''',
        [ParentType.Name, ACall.Name]),
      ACall.Line, ACall.Col);
  end;

  if ACall.Args.Count <> MDecl.Params.Count then
    SemanticError(
      Format('Method ''%s.%s'' expects %d argument(s) but got %d',
        [ParentType.Name, ACall.Name, MDecl.Params.Count, ACall.Args.Count]),
      ACall.Line, ACall.Col);

  for I := 0 to ACall.Args.Count - 1 do
  begin
    ArgType := AnalyseExpr(TASTExpr(ACall.Args.Items[I]));
    Par     := TMethodParam(MDecl.Params.Items[I]);
    CheckTypesMatch(Par.ResolvedType, ArgType,
      Format('argument %d of inherited ''%s''', [I + 1, ACall.Name]),
      ACall.Line, ACall.Col);
  end;

  ACall.ResolvedParentType := ParentType;
  ACall.ResolvedMethod     := MDecl;
end;

procedure TSemanticAnalyser.AnalyseFieldAssignment(AAssign: TFieldAssignment);
var
  RecSym:   TSymbol;
  RT:       TRecordTypeDesc;
  FldInfo:  TFieldInfo;
  BaseInfo: TFieldInfo;
  BaseType: TTypeDesc;
  PropInfo: TPropertyInfo;
  ExprType: TTypeDesc;
  ObjType:  TTypeDesc;
begin
  { ObjExpr path: receiver is an arbitrary expression (e.g. typecast result) }
  if AAssign.ObjExpr <> nil then
  begin
    ObjType := AnalyseExpr(AAssign.ObjExpr);
    if not (ObjType.Kind in [tyRecord, tyClass]) then
      SemanticError(
        Format('Field assignment: expression is not a record or class (got %s)',
          [ObjType.Name]),
        AAssign.Line, AAssign.Col);
    RT      := TRecordTypeDesc(ObjType);
    FldInfo := RT.FindField(AAssign.FieldName);
    if FldInfo = nil then
    begin
      PropInfo := RT.FindProperty(AAssign.FieldName);
      if (PropInfo <> nil) and (PropInfo.WriteField <> '') then
      begin
        AAssign.FieldName := PropInfo.WriteField;
        FldInfo           := RT.FindField(PropInfo.WriteField);
      end
      else
        SemanticError(
          Format('Type ''%s'' has no field ''%s''', [ObjType.Name, AAssign.FieldName]),
          AAssign.Line, AAssign.Col);
    end;
    AAssign.IsClassAccess := ObjType.Kind = tyClass;
    AAssign.FieldInfo     := FldInfo;
    ExprType := AnalyseExpr(AAssign.Expr);
    CheckTypesMatch(FldInfo.TypeDesc, ExprType, 'field assignment',
      AAssign.Line, AAssign.Col);
    Exit;
  end;
  RecSym := FTable.Lookup(AAssign.RecordName);
  if RecSym = nil then
  begin
    { Implicit Self.Field.Subfield — RecordName is a field of current class }
    if FCurrentClass <> nil then
    begin
      BaseInfo := FCurrentClass.FindField(AAssign.RecordName);
      if (BaseInfo <> nil) and
         (BaseInfo.TypeDesc.Kind in [tyRecord, tyClass]) then
      begin
        AAssign.IsImplicitSelf   := True;
        AAssign.ImplicitBaseInfo := BaseInfo;
        AAssign.IsClassAccess    := BaseInfo.TypeDesc.Kind = tyClass;
        BaseType := BaseInfo.TypeDesc;
        RT       := TRecordTypeDesc(BaseType);
        FldInfo  := RT.FindField(AAssign.FieldName);
        if FldInfo = nil then
        begin
          PropInfo := RT.FindProperty(AAssign.FieldName);
          if (PropInfo <> nil) and (PropInfo.WriteField <> '') then
          begin
            AAssign.FieldName := PropInfo.WriteField;
            FldInfo           := RT.FindField(PropInfo.WriteField);
          end
          else if (PropInfo <> nil) and (PropInfo.WriteMethod <> '') then
          begin
            { Method-backed write (includes indexed properties) }
            if PropInfo.IndexParamName <> '' then
            begin
              if AAssign.PropIndexExpr = nil then
                SemanticError(
                  Format('Indexed property ''%s'' requires an index expression',
                    [AAssign.FieldName]),
                  AAssign.Line, AAssign.Col);
              AnalyseExpr(AAssign.PropIndexExpr);
            end;
            AAssign.PropWriteInfo := PropInfo;
            AAssign.PropOwnerType := RT.Name;
            ExprType := AnalyseExpr(AAssign.Expr);
            CheckTypesMatch(PropInfo.TypeDesc, ExprType, 'property assignment',
              AAssign.Line, AAssign.Col);
            Exit;
          end
          else
            SemanticError(
              Format('Type ''%s'' has no field ''%s''',
                [AAssign.RecordName, AAssign.FieldName]),
              AAssign.Line, AAssign.Col);
        end;
        AAssign.FieldInfo := FldInfo;
        ExprType := AnalyseExpr(AAssign.Expr);
        CheckTypesMatch(FldInfo.TypeDesc, ExprType, 'field assignment',
          AAssign.Line, AAssign.Col);
        Exit;
      end;
    end;
    SemanticError(
      Format('Undeclared variable ''%s''', [AAssign.RecordName]),
      AAssign.Line, AAssign.Col);
  end;
  if not ((RecSym.Kind = skVariable) or (RecSym.Kind = skParameter)) then
    SemanticError(
      Format('''%s'' is not a variable', [AAssign.RecordName]),
      AAssign.Line, AAssign.Col);
  if not (RecSym.TypeDesc.Kind in [tyRecord, tyClass]) then
    SemanticError(
      Format('''%s'' is not a record or class variable', [AAssign.RecordName]),
      AAssign.Line, AAssign.Col);

  AAssign.IsClassAccess := RecSym.TypeDesc.Kind = tyClass;
  AAssign.IsGlobal      := RecSym.IsGlobal;

  RT      := TRecordTypeDesc(RecSym.TypeDesc);
  FldInfo := RT.FindField(AAssign.FieldName);
  if FldInfo = nil then
  begin
    { Check if this is a property write }
    PropInfo := RT.FindProperty(AAssign.FieldName);
    if PropInfo <> nil then
    begin
      if PropInfo.WriteField <> '' then
      begin
        { Field-backed write: redirect to the backing field }
        AAssign.FieldName := PropInfo.WriteField;
        FldInfo           := RT.FindField(PropInfo.WriteField);
      end
      else if PropInfo.WriteMethod <> '' then
      begin
        { Method-backed write (includes indexed properties) }
        if PropInfo.IndexParamName <> '' then
        begin
          if AAssign.PropIndexExpr = nil then
            SemanticError(
              Format('Indexed property ''%s'' requires an index expression',
                [AAssign.FieldName]),
              AAssign.Line, AAssign.Col);
          AnalyseExpr(AAssign.PropIndexExpr);
        end;
        AAssign.PropWriteInfo := PropInfo;
        AAssign.PropOwnerType := RT.Name;
        ExprType := AnalyseExpr(AAssign.Expr);
        CheckTypesMatch(PropInfo.TypeDesc, ExprType, 'property assignment',
          AAssign.Line, AAssign.Col);
        Exit;
      end
      else
        SemanticError(
          Format('Property ''%s'' is read-only', [AAssign.FieldName]),
          AAssign.Line, AAssign.Col);
    end
    else
      SemanticError(
        Format('Type ''%s'' has no field ''%s''',
          [AAssign.RecordName, AAssign.FieldName]),
        AAssign.Line, AAssign.Col);
  end;

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
  begin
    { Implicit Self.Method() — name is a method of the current class }
    if FCurrentClass <> nil then
    begin
      MDecl := FindMethodDecl(FCurrentClass.Name, ACall.Name);
      if MDecl <> nil then
      begin
        if ACall.Args.Count <> MDecl.Params.Count then
          SemanticError(
            Format('Method ''%s.%s'' expects %d argument(s) but got %d',
              [FCurrentClass.Name, ACall.Name, MDecl.Params.Count, ACall.Args.Count]),
            ACall.Line, ACall.Col);
        for I := 0 to ACall.Args.Count - 1 do
        begin
          Par     := TMethodParam(MDecl.Params.Items[I]);
          ArgType := AnalyseExpr(TASTExpr(ACall.Args.Items[I]));
          CheckTypesMatch(Par.ResolvedType, ArgType,
            Format('argument %d of ''%s''', [I + 1, ACall.Name]),
            ACall.Line, ACall.Col);
        end;
        ACall.ResolvedDecl         := MDecl;
        ACall.IsImplicitSelfMethod := True;
        Exit;
      end;
    end;
    { Try on-demand instantiation of a generic function }
    if Pos('<', ACall.Name) > 0 then
      InstantiateGenericFunc(ACall.Name);
    Sym := FTable.Lookup(ACall.Name);
    if Sym = nil then
      SemanticError(
        Format('Undeclared procedure ''%s''', [ACall.Name]),
        ACall.Line, ACall.Col);
  end;
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
      Par := TMethodParam(MDecl.Params.Items[I]);
      if Par.IsVarParam then
      begin
        { var parameter: argument must be a simple variable }
        if not (TASTExpr(ACall.Args.Items[I]) is TIdentExpr) then
          SemanticError(
            Format('var argument %d of ''%s'' must be a variable',
              [I + 1, ACall.Name]),
            ACall.Line, ACall.Col);
        ArgType := AnalyseExpr(TASTExpr(ACall.Args.Items[I]));
        CheckTypesMatch(Par.ResolvedType, ArgType,
          Format('var argument %d of ''%s''', [I + 1, ACall.Name]),
          ACall.Line, ACall.Col);
      end
      else
      begin
        ArgType := AnalyseExpr(TASTExpr(ACall.Args.Items[I]));
        CheckTypesMatch(Par.ResolvedType, ArgType,
          Format('argument %d of ''%s''', [I + 1, ACall.Name]),
          ACall.Line, ACall.Col);
      end;
    end;
    ACall.ResolvedDecl := MDecl;
  end
  else
  begin
    { Inc(x) / Inc(x, n) / Dec(x) / Dec(x, n) — in-place add/sub }
    if SameText(ACall.Name, 'Inc') or SameText(ACall.Name, 'Dec') then
    begin
      if (ACall.Args.Count < 1) or (ACall.Args.Count > 2) then
        SemanticError(
          Format('''%s'' requires 1 or 2 arguments', [ACall.Name]),
          ACall.Line, ACall.Col);
      AnalyseExpr(TASTExpr(ACall.Args.Items[0]));
      if ACall.Args.Count = 2 then
        AnalyseExpr(TASTExpr(ACall.Args.Items[1]));
    end
    else
    { Include(S, elem) / Exclude(S, elem): validate arg count and types }
    if SameText(ACall.Name, 'Include') or SameText(ACall.Name, 'Exclude') then
    begin
      if ACall.Args.Count <> 2 then
        SemanticError(
          Format('''%s'' requires exactly 2 arguments', [ACall.Name]),
          ACall.Line, ACall.Col);
      ArgType := AnalyseExpr(TASTExpr(ACall.Args.Items[0]));
      if ArgType.Kind <> tySet then
        SemanticError(
          Format('First argument of ''%s'' must be a set variable, got ''%s''',
            [ACall.Name, ArgType.Name]),
          ACall.Line, ACall.Col);
      { Validate the second arg is the correct enum element type }
      if ACall.Args.Count >= 2 then
      begin
        ArgType := AnalyseExpr(TASTExpr(ACall.Args.Items[1]));
        { The set type arg was the first; recover it }
        if (TASTExpr(ACall.Args.Items[0]).ResolvedType.Kind = tySet) and
           (ArgType <> TSetTypeDesc(TASTExpr(ACall.Args.Items[0]).ResolvedType).BaseType) then
          SemanticError(
            Format('Second argument of ''%s'' must be type ''%s'', got ''%s''',
              [ACall.Name,
               TSetTypeDesc(TASTExpr(ACall.Args.Items[0]).ResolvedType).BaseType.Name,
               ArgType.Name]),
            ACall.Line, ACall.Col);
      end;
    end
    else
    begin
      { Other built-ins (WriteLn/Write/etc.) — just analyse arg expressions }
      for I := 0 to ACall.Args.Count - 1 do
        AnalyseExpr(TASTExpr(ACall.Args.Items[I]));
    end;
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
  { SizeOf(TypeName) — compile-time type size, returns Integer }
  if SameText(AExpr.Name, 'SizeOf') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('SizeOf requires exactly one argument', AExpr.Line, AExpr.Col);
    if AExpr.Args.Items[0] is TIdentExpr then
    begin
      Sym := FTable.Lookup(TIdentExpr(AExpr.Args.Items[0]).Name);
      if (Sym <> nil) and (Sym.Kind = skType) then
        TIdentExpr(AExpr.Args.Items[0]).ResolvedType := Sym.TypeDesc;
    end;
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'PChar') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('PChar requires exactly one argument', AExpr.Line, AExpr.Col);
    ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    if not (ArgType.Kind in [tyString, tyPChar, tyPointer]) then
      SemanticError(
        Format('PChar cast requires a string, PChar, or Pointer expression, got ''%s''',
          [ArgType.Name]),
        AExpr.Line, AExpr.Col);
    Result := FTable.TypePChar;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'string') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('string() requires exactly one argument', AExpr.Line, AExpr.Col);
    ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    if ArgType.Kind <> tyPChar then
      SemanticError(
        Format('string() cast requires a PChar expression, got ''%s''',
          [ArgType.Name]),
        AExpr.Line, AExpr.Col);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'High') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('High requires exactly one argument', AExpr.Line, AExpr.Col);
    ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    if not (ArgType.Kind in [tyOpenArray, tyStaticArray]) then
      SemanticError('High argument must be an array', AExpr.Line, AExpr.Col);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Low') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Low requires exactly one argument', AExpr.Line, AExpr.Col);
    ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    if not (ArgType.Kind in [tyOpenArray, tyStaticArray]) then
      SemanticError('Low argument must be an array', AExpr.Line, AExpr.Col);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  Sym := FTable.Lookup(AExpr.Name);
  if Sym = nil then
  begin
    { Implicit Self.Method() on a function method of the current class }
    if FCurrentClass <> nil then
    begin
      MDecl := FindMethodDecl(FCurrentClass.Name, AExpr.Name);
      if MDecl <> nil then
      begin
        if AExpr.Args.Count <> MDecl.Params.Count then
          SemanticError(
            Format('Method ''%s.%s'' expects %d argument(s) but got %d',
              [FCurrentClass.Name, AExpr.Name, MDecl.Params.Count, AExpr.Args.Count]),
            AExpr.Line, AExpr.Col);
        for I := 0 to AExpr.Args.Count - 1 do
        begin
          Par     := TMethodParam(MDecl.Params.Items[I]);
          ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));
          CheckTypesMatch(Par.ResolvedType, ArgType,
            Format('argument %d of ''%s''', [I + 1, AExpr.Name]),
            AExpr.Line, AExpr.Col);
        end;
        AExpr.ResolvedDecl         := MDecl;
        AExpr.IsImplicitSelfMethod := True;
        Result := MDecl.ResolvedReturnType;
        AExpr.ResolvedType := Result;
        Exit;
      end;
    end;
    { Try on-demand instantiation of a generic function }
    if Pos('<', AExpr.Name) > 0 then
      InstantiateGenericFunc(AExpr.Name);
    Sym := FTable.Lookup(AExpr.Name);
    if Sym = nil then
      SemanticError(
        Format('Undeclared function ''%s''', [AExpr.Name]),
        AExpr.Line, AExpr.Col);
  end;
  { Type cast: TypeName(Expr) — single-argument call to a type name }
  if Sym.Kind = skType then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(
        Format('Type cast ''%s'' expects exactly one argument', [AExpr.Name]),
        AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := Sym.TypeDesc;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if Sym.Kind <> skFunction then
    SemanticError(
      Format('''%s'' is not a function', [AExpr.Name]),
      AExpr.Line, AExpr.Col);

  { Built-in memory functions: GetMem / ReallocMem }
  if SameText(AExpr.Name, 'GetMem') or SameText(AExpr.Name, 'ReallocMem') then
  begin
    for I := 0 to AExpr.Args.Count - 1 do
      AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));
    Result := FTable.TypePointer;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { Built-in string functions — validate arg count and first-arg type,
    then set return type.  These call RTL functions at runtime. }
  if SameText(AExpr.Name, 'Length') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Length requires exactly one argument', AExpr.Line, AExpr.Col);
    ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    if ArgType.Kind <> tyString then
      SemanticError('Length argument must be a string', AExpr.Line, AExpr.Col);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Pos') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('Pos requires exactly two arguments', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    AnalyseExpr(TASTExpr(AExpr.Args.Items[1]));
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Copy') then
  begin
    if AExpr.Args.Count <> 3 then
      SemanticError('Copy requires exactly three arguments', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    AnalyseExpr(TASTExpr(AExpr.Args.Items[1]));
    AnalyseExpr(TASTExpr(AExpr.Args.Items[2]));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'UpperCase') or SameText(AExpr.Name, 'LowerCase')
     or SameText(AExpr.Name, 'Trim') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(AExpr.Name + ' requires exactly one argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'SameText') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('SameText requires exactly two arguments', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    AnalyseExpr(TASTExpr(AExpr.Args.Items[1]));
    Result := FTable.TypeBoolean;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'IntToStr') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('IntToStr requires exactly one argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Int64ToStr') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Int64ToStr requires exactly one argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'StrToInt') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('StrToInt requires exactly one argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'StrToInt64') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('StrToInt64 requires exactly one argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeInt64;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Format') then
  begin
    if AExpr.Args.Count < 1 then
      SemanticError('Format requires at least one argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    { When the second arg is an array literal (Pascal 'array of const' notation),
      analyse each element individually — types need not be homogeneous. }
    if (AExpr.Args.Count = 2) and (AExpr.Args.Items[1] is TArrayLiteralExpr) then
    begin
      for I := 0 to TArrayLiteralExpr(AExpr.Args.Items[1]).Elements.Count - 1 do
        AnalyseExpr(TASTExpr(TArrayLiteralExpr(AExpr.Args.Items[1]).Elements.Items[I]));
      TArrayLiteralExpr(AExpr.Args.Items[1]).ResolvedType := FTable.TypeString;
    end
    else
      for I := 1 to AExpr.Args.Count - 1 do
        AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'OrdAt') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('OrdAt requires exactly 2 arguments', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    AnalyseExpr(TASTExpr(AExpr.Args.Items[1]));
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Ord') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Ord requires exactly 1 argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Chr') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Chr requires exactly 1 argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'UpCase') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('UpCase requires exactly 1 argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'CompareStr') or SameText(AExpr.Name, 'CompareText') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError(AExpr.Name + ' requires exactly 2 arguments', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    AnalyseExpr(TASTExpr(AExpr.Args.Items[1]));
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { CLI arguments }
  if SameText(AExpr.Name, 'ParamCount') then
  begin
    if AExpr.Args.Count <> 0 then
      SemanticError('ParamCount takes no arguments', AExpr.Line, AExpr.Col);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'ParamStr') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('ParamStr requires exactly 1 argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { File I/O functions }
  if SameText(AExpr.Name, 'ReadFile') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('ReadFile requires exactly 1 argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'FileExists') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('FileExists requires exactly 1 argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeBoolean;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { Environment and process functions }
  if SameText(AExpr.Name, 'GetEnvVar') or
     SameText(AExpr.Name, 'GetEnvironmentVariable') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(Format('''%s'' requires exactly 1 argument', [AExpr.Name]),
                    AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Exec') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Exec requires exactly 1 argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { File path manipulation }
  if SameText(AExpr.Name, 'ChangeFileExt') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('ChangeFileExt requires exactly 2 arguments', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    AnalyseExpr(TASTExpr(AExpr.Args.Items[1]));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'ExtractFileName') or
     SameText(AExpr.Name, 'ExtractFilePath') or
     SameText(AExpr.Name, 'IncludeTrailingPathDelimiter') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(Format('''%s'' requires exactly 1 argument', [AExpr.Name]),
                    AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  { Process management built-ins }
  if SameText(AExpr.Name, 'ProcessCreate') then
  begin
    if AExpr.Args.Count <> 0 then
      SemanticError('ProcessCreate takes no arguments', AExpr.Line, AExpr.Col);
    Result := FTable.TypePointer;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'ProcessRunning') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('ProcessRunning requires exactly 1 argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeBoolean;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'ProcessReadOutput') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('ProcessReadOutput requires exactly 1 argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'ProcessExitCode') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('ProcessExitCode requires exactly 1 argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

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
    ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));
    Par     := TMethodParam(MDecl.Params.Items[I]);
    CheckTypesMatch(Par.ResolvedType, ArgType,
      Format('argument %d of ''%s''', [I + 1, AExpr.Name]),
      AExpr.Line, AExpr.Col);
  end;

  AExpr.ResolvedDecl := MDecl;
  Result := MDecl.ResolvedReturnType;
end;

function TSemanticAnalyser.AnalyseMethodCallExpr(AExpr: TMethodCallExpr): TTypeDesc;
var
  ObjSym:   TSymbol;
  RT:       TRecordTypeDesc;
  MDecl:    TMethodDecl;
  Par:      TMethodParam;
  ArgType:  TTypeDesc;
  I:        Integer;
  IntfDesc: TInterfaceTypeDesc;
  ObjType:  TTypeDesc;
begin
  { Call on an arbitrary expression (e.g. TCast(x).Method(y)) }
  if AExpr.ObjExpr <> nil then
  begin
    ObjType := AnalyseExpr(AExpr.ObjExpr);
    if not (ObjType.Kind in [tyClass, tyInterface]) then
      SemanticError(
        Format('Receiver of ''.%s'' must be a class or interface', [AExpr.Name]),
        AExpr.Line, AExpr.Col);
    if ObjType.Kind = tyInterface then
    begin
      IntfDesc := TInterfaceTypeDesc(ObjType);
      if not IntfDesc.HasMethod(AExpr.Name) then
        SemanticError(
          Format('Interface ''%s'' has no method ''%s''',
            [ObjType.Name, AExpr.Name]),
          AExpr.Line, AExpr.Col);
      for I := 0 to AExpr.Args.Count - 1 do
        AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));
      AExpr.ResolvedClassType := ObjType;
      AExpr.ResolvedMethod    := nil;
      Result := FindTypeOrInstantiate(
        IntfDesc.MethodReturnTypeName(IntfDesc.MethodIndex(AExpr.Name)));
      if Result = nil then Result := FTable.TypeInteger;
      AExpr.ResolvedType := Result;
      Exit;
    end;
    RT    := TRecordTypeDesc(ObjType);
    MDecl := FindMethodDecl(RT.Name, AExpr.Name);
    if MDecl = nil then
      SemanticError(
        Format('Class ''%s'' has no method ''%s''', [RT.Name, AExpr.Name]),
        AExpr.Line, AExpr.Col);
    if AExpr.Args.Count <> MDecl.Params.Count then
      SemanticError(
        Format('Method ''%s.%s'' expects %d argument(s) but got %d',
          [RT.Name, AExpr.Name, MDecl.Params.Count, AExpr.Args.Count]),
        AExpr.Line, AExpr.Col);
    for I := 0 to AExpr.Args.Count - 1 do
    begin
      ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));
      Par     := TMethodParam(MDecl.Params.Items[I]);
      CheckTypesMatch(Par.ResolvedType, ArgType,
        Format('argument %d of ''%s''', [I + 1, AExpr.Name]),
        AExpr.Line, AExpr.Col);
    end;
    AExpr.ResolvedClassType := RT;
    AExpr.ResolvedMethod    := MDecl;
    Result := MDecl.ResolvedReturnType;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  ObjSym := FTable.Lookup(AExpr.ObjectName);
  if ObjSym = nil then
  begin
    { Implicit Self.Field.Method — ObjectName is a field of current class.
      Synthesise a receiver expression that reads the field. }
    if FCurrentClass <> nil then
    begin
      ObjType := nil;
      ObjSym  := nil;
      begin
        { Attempt field lookup and rewrite AExpr.ObjExpr to read Self.Field }
        AExpr.ObjExpr := TIdentExpr.Create;
        TIdentExpr(AExpr.ObjExpr).Name := AExpr.ObjectName;
        TIdentExpr(AExpr.ObjExpr).Line := AExpr.Line;
        TIdentExpr(AExpr.ObjExpr).Col  := AExpr.Col;
        try
          ObjType := AnalyseExpr(AExpr.ObjExpr);
        except
          AExpr.ObjExpr.Free;
          AExpr.ObjExpr := nil;
          SemanticError(
            Format('Undeclared identifier ''%s''', [AExpr.ObjectName]),
            AExpr.Line, AExpr.Col);
        end;
      end;
      if (ObjType = nil) or not (ObjType.Kind in [tyClass, tyInterface]) then
      begin
        AExpr.ObjExpr.Free;
        AExpr.ObjExpr := nil;
        SemanticError(
          Format('Undeclared identifier ''%s''', [AExpr.ObjectName]),
          AExpr.Line, AExpr.Col);
      end;
      AExpr.ObjectName := '';
      if ObjType.Kind = tyInterface then
      begin
        IntfDesc := TInterfaceTypeDesc(ObjType);
        if not IntfDesc.HasMethod(AExpr.Name) then
          SemanticError(
            Format('Interface ''%s'' has no method ''%s''',
              [ObjType.Name, AExpr.Name]),
            AExpr.Line, AExpr.Col);
        for I := 0 to AExpr.Args.Count - 1 do
          AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));
        AExpr.ResolvedClassType := ObjType;
        AExpr.ResolvedMethod    := nil;
        Result := FindTypeOrInstantiate(
          IntfDesc.MethodReturnTypeName(IntfDesc.MethodIndex(AExpr.Name)));
        if Result = nil then Result := FTable.TypeInteger;
        AExpr.ResolvedType := Result;
        Exit;
      end;
      RT    := TRecordTypeDesc(ObjType);
      MDecl := FindMethodDecl(RT.Name, AExpr.Name);
      if MDecl = nil then
        SemanticError(
          Format('Class ''%s'' has no method ''%s''', [RT.Name, AExpr.Name]),
          AExpr.Line, AExpr.Col);
      if AExpr.Args.Count <> MDecl.Params.Count then
        SemanticError(
          Format('Method ''%s.%s'' expects %d argument(s) but got %d',
            [RT.Name, AExpr.Name, MDecl.Params.Count, AExpr.Args.Count]),
          AExpr.Line, AExpr.Col);
      for I := 0 to AExpr.Args.Count - 1 do
      begin
        ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));
        Par     := TMethodParam(MDecl.Params.Items[I]);
        CheckTypesMatch(Par.ResolvedType, ArgType,
          Format('argument %d of ''%s''', [I + 1, AExpr.Name]),
          AExpr.Line, AExpr.Col);
      end;
      AExpr.ResolvedClassType := RT;
      AExpr.ResolvedMethod    := MDecl;
      Result := MDecl.ResolvedReturnType;
      AExpr.ResolvedType := Result;
      Exit;
    end;
    SemanticError(
      Format('Undeclared identifier ''%s''', [AExpr.ObjectName]),
      AExpr.Line, AExpr.Col);
  end;

  { Constructor call with args: TypeName.Create(arg1, arg2, ...) or any
    method on a class type starting with Create (e.g. CreateFmt). }
  if (ObjSym.Kind = skType) and
     (SameText(AExpr.Name, 'Create') or
      (Pos('Create', AExpr.Name) = 1)) then
  begin
    if ObjSym.TypeDesc.Kind <> tyClass then
      SemanticError(
        Format('Cannot construct non-class type ''%s''', [AExpr.ObjectName]),
        AExpr.Line, AExpr.Col);
    for I := 0 to AExpr.Args.Count - 1 do
      AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));
    { Try to find a user-defined constructor method for type checking }
    MDecl := FindMethodDecl(AExpr.ObjectName, AExpr.Name);
    AExpr.ResolvedMethod    := MDecl;
    AExpr.ResolvedClassType := ObjSym.TypeDesc;
    AExpr.IsConstructorCall := True;
    Result := ObjSym.TypeDesc;
    Exit;
  end;

  if not (ObjSym.Kind in [skVariable, skParameter, skVarParameter]) then
    SemanticError(
      Format('''%s'' is not a variable', [AExpr.ObjectName]),
      AExpr.Line, AExpr.Col);
  if not (ObjSym.TypeDesc.Kind in [tyClass, tyInterface]) then
    SemanticError(
      Format('''%s'' is not a class or interface variable', [AExpr.ObjectName]),
      AExpr.Line, AExpr.Col);

  { Interface method call expression: dispatch through itab }
  if ObjSym.TypeDesc.Kind = tyInterface then
  begin
    IntfDesc := TInterfaceTypeDesc(ObjSym.TypeDesc);
    if not IntfDesc.HasMethod(AExpr.Name) then
      SemanticError(
        Format('Interface ''%s'' has no method ''%s''',
          [ObjSym.TypeDesc.Name, AExpr.Name]),
        AExpr.Line, AExpr.Col);
    for I := 0 to AExpr.Args.Count - 1 do
      AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));
    AExpr.ResolvedClassType := ObjSym.TypeDesc;
    AExpr.ResolvedMethod    := nil;  { nil = interface dispatch }
    AExpr.IsGlobal          := ObjSym.IsGlobal;
    AExpr.IsVarParam        := (ObjSym.Kind = skVarParameter);
    { Look up return type from interface method descriptor }
    Result := FindTypeOrInstantiate(
      IntfDesc.MethodReturnTypeName(IntfDesc.MethodIndex(AExpr.Name)));
    if Result = nil then
      Result := FTable.TypeInteger;  { fallback for void/unknown }
    Exit;
  end;

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
    ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));
    Par     := TMethodParam(MDecl.Params.Items[I]);
    CheckTypesMatch(Par.ResolvedType, ArgType,
      Format('argument %d of ''%s''', [I + 1, AExpr.Name]),
      AExpr.Line, AExpr.Col);
  end;

  AExpr.ResolvedClassType := RT;
  AExpr.ResolvedMethod    := MDecl;
  AExpr.IsGlobal          := ObjSym.IsGlobal;
  AExpr.IsVarParam        := (ObjSym.Kind = skVarParameter);
  Result := MDecl.ResolvedReturnType;
end;

function TSemanticAnalyser.AnalyseExpr(AExpr: TASTExpr): TTypeDesc;
var
  Sym:       TSymbol;
  FldInfo:   TFieldInfo;
  PropInfo:  TPropertyInfo;
  NoArgIdx:  Integer;
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
    begin
      { Not in scope — try implicit Self.Field when inside a method }
      if FCurrentClass <> nil then
      begin
        FldInfo := FCurrentClass.FindField(TIdentExpr(AExpr).Name);
        if FldInfo <> nil then
        begin
          TIdentExpr(AExpr).IsImplicitSelf   := True;
          TIdentExpr(AExpr).ImplicitFieldInfo := FldInfo;
          Result := FldInfo.TypeDesc;
          AExpr.ResolvedType := Result;
          Exit;
        end;
        { Bare zero-arg method call: e.g. TokenText inside a method }
        TIdentExpr(AExpr).ImplicitMethodDecl :=
          FindMethodDecl(FCurrentClass.Name, TIdentExpr(AExpr).Name);
        if TIdentExpr(AExpr).ImplicitMethodDecl <> nil then
        begin
          TIdentExpr(AExpr).IsImplicitSelfMethod := True;
          Result :=
            TMethodDecl(TIdentExpr(AExpr).ImplicitMethodDecl).ResolvedReturnType;
          AExpr.ResolvedType := Result;
          Exit;
        end;
        { Property of current class, method-backed: rewrite to the read method }
        FldInfo := nil;  { reuse PropInfo via local }
        begin
          PropInfo := FCurrentClass.FindProperty(TIdentExpr(AExpr).Name);
          if PropInfo <> nil then
          begin
            if PropInfo.ReadMethod <> '' then
            begin
              TIdentExpr(AExpr).ImplicitMethodDecl :=
                FindMethodDecl(FCurrentClass.Name, PropInfo.ReadMethod);
              if TIdentExpr(AExpr).ImplicitMethodDecl <> nil then
              begin
                TIdentExpr(AExpr).IsImplicitSelfMethod := True;
                TIdentExpr(AExpr).Name := PropInfo.ReadMethod;
                Result := PropInfo.TypeDesc;
                AExpr.ResolvedType := Result;
                Exit;
              end;
            end
            else if PropInfo.ReadField <> '' then
            begin
              FldInfo := FCurrentClass.FindField(PropInfo.ReadField);
              if FldInfo <> nil then
              begin
                TIdentExpr(AExpr).IsImplicitSelf := True;
                TIdentExpr(AExpr).ImplicitFieldInfo := FldInfo;
                Result := FldInfo.TypeDesc;
                AExpr.ResolvedType := Result;
                Exit;
              end;
            end;
          end;
        end;
      end;
      SemanticError(
        Format('Undeclared identifier ''%s''', [TIdentExpr(AExpr).Name]),
        AExpr.Line, AExpr.Col);
    end;
    TIdentExpr(AExpr).IsVarParam := (Sym.Kind = skVarParameter);
    TIdentExpr(AExpr).IsGlobal  := Sym.IsGlobal;
    if Sym.Kind = skConstant then
    begin
      TIdentExpr(AExpr).IsConstant  := True;
      TIdentExpr(AExpr).ConstValue  := Sym.ConstValue;
      TIdentExpr(AExpr).ConstString := Sym.ConstString;
    end;
    { Bare function reference without parens — mark as no-arg call for codegen.
      Covers both builtins (not in FProcIndex) and user-defined standalone functions. }
    if (Sym.Kind = skFunction) and (Sym.TypeDesc <> nil) then
    begin
      TIdentExpr(AExpr).IsNoArgFuncCall := True;
      { Propagate TMethodDecl for user-defined functions so codegen can emit the call }
      NoArgIdx := FProcIndex.IndexOf(TIdentExpr(AExpr).Name);
      if NoArgIdx >= 0 then
        TIdentExpr(AExpr).NoArgFuncDecl := FProcIndex.Objects[NoArgIdx];
    end;
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
  else if AExpr is TDerefExpr then
    Result := AnalyseDerefExpr(TDerefExpr(AExpr))
  else if AExpr is TAddrOfExpr then
    Result := AnalyseAddrOfExpr(TAddrOfExpr(AExpr))
  else if AExpr is TStringSubscriptExpr then
    Result := AnalyseStringSubscriptExpr(TStringSubscriptExpr(AExpr))
  else if AExpr is TArrayLiteralExpr then
    Result := AnalyseArrayLiteralExpr(TArrayLiteralExpr(AExpr))
  else if AExpr is TNotExpr then
  begin
    Result := AnalyseExpr(TNotExpr(AExpr).Expr);
    if Result.Kind <> tyBoolean then
      SemanticError(
        Format('''not'' requires a Boolean operand, got ''%s''', [Result.Name]),
        AExpr.Line, AExpr.Col);
    Result := FTable.TypeBoolean;
  end
  else
    SemanticError('Unknown expression node', AExpr.Line, AExpr.Col);

  AExpr.ResolvedType := Result;
end;

function TSemanticAnalyser.AnalyseFieldAccess(AAccess: TFieldAccessExpr): TTypeDesc;
var
  RecSym:   TSymbol;
  Sym:      TSymbol;
  RT:       TRecordTypeDesc;
  FldInfo:  TFieldInfo;
  PropInfo: TPropertyInfo;
  BaseType: TTypeDesc;
begin
  { Chained access: A.B.C — base is another expression whose type must be
    a record or class.  Leaf lookup uses Base.ResolvedType; RecordName path
    (no Base) is used only for the simple IDENT.IDENT form. }
  if AAccess.Base <> nil then
  begin
    BaseType := AnalyseExpr(AAccess.Base);
    if not (BaseType.Kind in [tyRecord, tyClass]) then
      SemanticError(
        Format('Field access ''.%s'' requires a record or class base, got ''%s''',
          [AAccess.FieldName, BaseType.Name]),
        AAccess.Line, AAccess.Col);
    AAccess.IsClassAccess := BaseType.Kind = tyClass;
    RT      := TRecordTypeDesc(BaseType);
    FldInfo := RT.FindField(AAccess.FieldName);
    if FldInfo = nil then
    begin
      PropInfo := RT.FindProperty(AAccess.FieldName);
      if (PropInfo <> nil) and (PropInfo.ReadField <> '') then
      begin
        AAccess.FieldName := PropInfo.ReadField;
        AAccess.FieldInfo := RT.FindField(PropInfo.ReadField);
        Result := PropInfo.TypeDesc;
        Exit;
      end;
      { Method-backed property (including indexed; index attached later by subscript analyser) }
      if (PropInfo <> nil) and (PropInfo.ReadMethod <> '') then
      begin
        AAccess.PropRead := PropInfo;
        AAccess.PropOwnerType := RT.Name;
        Result := PropInfo.TypeDesc;
        Exit;
      end;
      { Zero-arg method call via field access: Obj.Method (no parens) }
      AAccess.ResolvedMethod := FindMethodDecl(RT.Name, AAccess.FieldName);
      if AAccess.ResolvedMethod <> nil then
      begin
        AAccess.IsMethodCall := True;
        Result := TMethodDecl(AAccess.ResolvedMethod).ResolvedReturnType;
        Exit;
      end;
      SemanticError(
        Format('Type ''%s'' has no field ''%s''',
          [BaseType.Name, AAccess.FieldName]),
        AAccess.Line, AAccess.Col);
    end;
    AAccess.FieldInfo := FldInfo;
    Result := FldInfo.TypeDesc;
    Exit;
  end;

  RecSym := FTable.Lookup(AAccess.RecordName);
  { If the name contains '<' and wasn't found, resolve scope-bound type params
    (e.g. 'TGenEnum<T>' → 'TGenEnum<Integer>' when T=Integer is in scope)
    and update AAccess.RecordName so codegen sees the concrete instantiation. }
  if (RecSym = nil) and (Pos('<', AAccess.RecordName) > 0) then
  begin
    AAccess.RecordName := ResolveScopeBoundTypeParams(AAccess.RecordName);
    FindTypeOrInstantiate(AAccess.RecordName);
    RecSym := FTable.Lookup(AAccess.RecordName);
  end;
  if RecSym = nil then
  begin
    { Implicit Self.RecordName.FieldName — RecordName is a field of current class }
    if FCurrentClass <> nil then
    begin
      FldInfo := FCurrentClass.FindField(AAccess.RecordName);
      if (FldInfo <> nil) and
         (FldInfo.TypeDesc.Kind in [tyRecord, tyClass]) then
      begin
        AAccess.IsImplicitSelf   := True;
        AAccess.ImplicitBaseInfo := FldInfo;
        AAccess.IsClassAccess    := FldInfo.TypeDesc.Kind = tyClass;
        RT := TRecordTypeDesc(FldInfo.TypeDesc);
        AAccess.FieldInfo := RT.FindField(AAccess.FieldName);
        if AAccess.FieldInfo = nil then
        begin
          { Field-backed property on the implicit-Self field's type }
          PropInfo := RT.FindProperty(AAccess.FieldName);
          if PropInfo <> nil then
          begin
            if PropInfo.ReadField <> '' then
            begin
              AAccess.FieldName := PropInfo.ReadField;
              AAccess.FieldInfo := RT.FindField(PropInfo.ReadField);
              Result := PropInfo.TypeDesc;
              AAccess.ResolvedType := Result;
              Exit;
            end
            else if PropInfo.ReadMethod <> '' then
            begin
              { Method-backed read (includes indexed properties) }
              if PropInfo.IndexParamName <> '' then
              begin
                if AAccess.PropIndexExpr = nil then
                  SemanticError(
                    Format('Indexed property ''%s'' requires an index expression',
                      [AAccess.FieldName]),
                    AAccess.Line, AAccess.Col);
                AnalyseExpr(AAccess.PropIndexExpr);
              end;
              AAccess.PropRead := PropInfo;
              AAccess.PropOwnerType := RT.Name;
              Result := PropInfo.TypeDesc;
              AAccess.ResolvedType := Result;
              Exit;
            end;
          end;
          { Zero-arg method on the implicit-Self field: FTok.NextToken }
          AAccess.ResolvedMethod := FindMethodDecl(RT.Name, AAccess.FieldName);
          if AAccess.ResolvedMethod <> nil then
          begin
            AAccess.IsMethodCall := True;
            Result := TMethodDecl(AAccess.ResolvedMethod).ResolvedReturnType;
            AAccess.ResolvedType := Result;
            Exit;
          end;
          SemanticError(
            Format('Type ''%s'' has no field ''%s''',
              [AAccess.RecordName, AAccess.FieldName]),
            AAccess.Line, AAccess.Col);
        end;
        Result := AAccess.FieldInfo.TypeDesc;
        Exit;
      end;
    end;
    SemanticError(
      Format('Undeclared identifier ''%s''', [AAccess.RecordName]),
      AAccess.Line, AAccess.Col);
  end;

  { Constructor call: TypeName.Create }
  if RecSym.Kind = skType then
  begin
    if RecSym.TypeDesc.Kind <> tyClass then
      SemanticError(
        Format('Cannot call constructor on non-class type ''%s''',
          [AAccess.RecordName]),
        AAccess.Line, AAccess.Col);
    if not SameText(AAccess.FieldName, 'Create') then
    begin
      { Check for a class-level constant registered as TypeName.ConstName }
      Sym := FTable.Lookup(AAccess.RecordName + '.' + AAccess.FieldName);
      if (Sym <> nil) and (Sym.Kind = skConstant) then
      begin
        AAccess.IsConstant  := True;
        AAccess.ConstValue  := Sym.ConstValue;
        AAccess.ConstString := Sym.ConstString;
        AAccess.ResolvedType := Sym.TypeDesc;
        Result := Sym.TypeDesc;
        Exit;
      end;
      SemanticError(
        Format('Unknown class method ''%s'' on type ''%s''',
          [AAccess.FieldName, AAccess.RecordName]),
        AAccess.Line, AAccess.Col);
    end;
    AAccess.IsConstructorCall := True;
    AAccess.ResolvedMethod    := FindMethodDecl(TRecordTypeDesc(RecSym.TypeDesc).Name, 'Create');
    Result := RecSym.TypeDesc;
    Exit;
  end;

  { Field access on variable or parameter }
  if not (RecSym.Kind in [skVariable, skParameter, skVarParameter]) then
    SemanticError(
      Format('''%s'' is not a variable or type', [AAccess.RecordName]),
      AAccess.Line, AAccess.Col);

  if not (RecSym.TypeDesc.Kind in [tyRecord, tyClass]) then
    SemanticError(
      Format('''%s'' is not a record or class', [AAccess.RecordName]),
      AAccess.Line, AAccess.Col);

  AAccess.IsClassAccess := RecSym.TypeDesc.Kind = tyClass;
  AAccess.IsGlobal      := RecSym.IsGlobal;

  RT      := TRecordTypeDesc(RecSym.TypeDesc);
  FldInfo := RT.FindField(AAccess.FieldName);
  if FldInfo = nil then
  begin
    { Zero-arg method call via field access: Obj.Method (no parens) }
    AAccess.ResolvedMethod := FindMethodDecl(RT.Name, AAccess.FieldName);
    if AAccess.ResolvedMethod <> nil then
    begin
      AAccess.IsMethodCall := True;
      Result := TMethodDecl(AAccess.ResolvedMethod).ResolvedReturnType;
      AAccess.ResolvedType := Result;
      Exit;
    end;
    { Check if this is a property access }
    PropInfo := RT.FindProperty(AAccess.FieldName);
    if PropInfo <> nil then
    begin
      if PropInfo.ReadField <> '' then
      begin
        { Field-backed read: redirect to the backing field }
        AAccess.FieldName := PropInfo.ReadField;
        AAccess.FieldInfo := RT.FindField(PropInfo.ReadField);
        Result := PropInfo.TypeDesc;
        AAccess.ResolvedType := Result;
        Exit;
      end
      else if PropInfo.ReadMethod <> '' then
      begin
        { Method-backed read (includes indexed properties) }
        if PropInfo.IndexParamName <> '' then
        begin
          if AAccess.PropIndexExpr = nil then
            SemanticError(
              Format('Indexed property ''%s'' requires an index expression',
                [AAccess.FieldName]),
              AAccess.Line, AAccess.Col);
          AnalyseExpr(AAccess.PropIndexExpr);
        end;
        AAccess.PropRead := PropInfo;
        AAccess.PropOwnerType := RT.Name;
        Result := PropInfo.TypeDesc;
        AAccess.ResolvedType := Result;
        Exit;
      end;
    end;
    SemanticError(
      Format('Type ''%s'' has no field ''%s''',
        [AAccess.RecordName, AAccess.FieldName]),
      AAccess.Line, AAccess.Col);
  end;

  AAccess.FieldInfo := FldInfo;
  Result := FldInfo.TypeDesc;
end;

function TSemanticAnalyser.AnalyseBinaryExpr(ABin: TBinaryExpr): TTypeDesc;
var
  LType, RType: TTypeDesc;
  TmpSet: TSetTypeDesc;
begin
  LType := AnalyseExpr(ABin.Left);
  RType := AnalyseExpr(ABin.Right);

  { Set membership: elem in SetVar — left is base enum, right is set type }
  if ABin.Op = boIn then
  begin
    { Coerce array literal [a, b, c] to an anonymous set type when the left
      operand is an enum — handles the common 'x in [A, B, C]' idiom. }
    if (ABin.Right is TArrayLiteralExpr) and (LType.Kind = tyEnum) then
    begin
      TmpSet := FTable.NewSetType('', TEnumTypeDesc(LType));
      RType := AnalyseSetLiteralExpr(TArrayLiteralExpr(ABin.Right), TmpSet);
    end;
    if RType.Kind <> tySet then
      SemanticError(
        Format('Right operand of ''in'' must be a set type, got ''%s''', [RType.Name]),
        ABin.Line, ABin.Col);
    if LType <> TSetTypeDesc(RType).BaseType then
      SemanticError(
        Format('Left operand of ''in'' must be type ''%s'', got ''%s''',
          [TSetTypeDesc(RType).BaseType.Name, LType.Name]),
        ABin.Line, ABin.Col);
    Result := FTable.TypeBoolean;
    ABin.ResolvedType := Result;
    Exit;
  end;

  { Set arithmetic and equality when both operands are set types }
  if (LType.Kind = tySet) or (RType.Kind = tySet) then
  begin
    if LType.Kind <> tySet then
      SemanticError(
        Format('Left operand of ''%s'' must be a set type, got ''%s''',
          [BinaryOpName(ABin.Op), LType.Name]),
        ABin.Line, ABin.Col);
    if RType.Kind <> tySet then
      SemanticError(
        Format('Right operand of ''%s'' must be a set type, got ''%s''',
          [BinaryOpName(ABin.Op), RType.Name]),
        ABin.Line, ABin.Col);
    if LType <> RType then
      SemanticError(
        Format('Incompatible set types in ''%s'': ''%s'' vs ''%s''',
          [BinaryOpName(ABin.Op), LType.Name, RType.Name]),
        ABin.Line, ABin.Col);
    if ABin.Op in [boEQ, boNE] then
      Result := FTable.TypeBoolean
    else if ABin.Op in [boAdd, boSub, boMul] then
      Result := LType
    else
      SemanticError(
        Format('Operator ''%s'' is not defined for set types', [BinaryOpName(ABin.Op)]),
        ABin.Line, ABin.Col);
    ABin.ResolvedType := Result;
    Exit;
  end;

  { Logical AND / OR / XOR — both operands must be Boolean or both numeric. }
  if ABin.Op in [boAnd, boOr, boXor] then
  begin
    { Bitwise or/and for integer types }
    if LType.IsNumeric and RType.IsNumeric then
    begin
      if (LType.Kind = tyInt64) or (RType.Kind = tyInt64) then
        Result := FTable.TypeInt64
      else
        Result := FTable.TypeInteger;
      Exit;
    end;
    if LType.Kind <> tyBoolean then
      SemanticError(
        Format('Left operand of ''%s'' must be Boolean, got ''%s''',
          [BinaryOpName(ABin.Op), LType.Name]),
        ABin.Line, ABin.Col);
    if RType.Kind <> tyBoolean then
      SemanticError(
        Format('Right operand of ''%s'' must be Boolean, got ''%s''',
          [BinaryOpName(ABin.Op), RType.Name]),
        ABin.Line, ABin.Col);
    Result := FTable.TypeBoolean;
    Exit;
  end;

  if IsComparisonOp(ABin.Op) then
  begin
    { Char literal coercion: S[N] = '-' — subscript yields Integer; coerce the literal }
    if (LType.Kind = tyInteger) and (ABin.Right is TStringLiteral) then
    begin
      CoerceToCharOrd(TStringLiteral(ABin.Right));
      RType := ABin.Right.ResolvedType;
    end
    else if (RType.Kind = tyInteger) and (ABin.Left is TStringLiteral) then
    begin
      CoerceToCharOrd(TStringLiteral(ABin.Left));
      LType := ABin.Left.ResolvedType;
    end;
    { nil can be compared with class, interface, pointer, or PChar types }
    if not (
      (LType = RType) or
      ((LType.Kind = tyNil) and (RType.Kind in [tyClass, tyInterface, tyPointer, tyPChar])) or
      ((RType.Kind = tyNil) and (LType.Kind in [tyClass, tyInterface, tyPointer, tyPChar])) or
      ((LType.Kind = tyPointer) and (RType.Kind = tyPointer)) or
      { Class comparisons: allow subtype on either side }
      ((LType.Kind = tyClass) and (RType.Kind = tyClass) and
       (IsSubtypeOf(LType, RType) or IsSubtypeOf(RType, LType))) or
      { TObject is universal base class }
      ((LType.Kind = tyClass) and (RType.Kind = tyClass) and
       ((LType.Name = 'TObject') or (RType.Name = 'TObject')))
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

    { Pointer arithmetic: Pointer/PChar + Integer or Integer + Pointer → same type }
    if (ABin.Op in [boAdd, boSub]) and (LType.Kind in [tyPointer, tyPChar]) and RType.IsNumeric then
    begin
      Result := LType;
      Exit;
    end;
    if (ABin.Op = boAdd) and LType.IsNumeric and (RType.Kind in [tyPointer, tyPChar]) then
    begin
      Result := RType;
      Exit;
    end;

    { Shift operators: result has the left operand's type; right is the shift amount }
    if ABin.Op in [boShl, boShr] then
    begin
      if not LType.IsNumeric then
        SemanticError(
          Format('Left operand of ''%s'' must be numeric, got ''%s''',
            [BinaryOpName(ABin.Op), LType.Name]),
          ABin.Line, ABin.Col);
      if not RType.IsNumeric then
        SemanticError(
          Format('Shift amount of ''%s'' must be numeric, got ''%s''',
            [BinaryOpName(ABin.Op), RType.Name]),
          ABin.Line, ABin.Col);
      Result := LType;
      ABin.ResolvedType := Result;
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
  { Allow untyped Pointer on left — GetObject/Get return Pointer, used with 'is' }
  if not ((ObjType.Kind = tyClass) or (ObjType.Kind = tyPointer) or
          (ObjType.Kind = tyInterface)) then
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

function TSemanticAnalyser.AnalyseDerefExpr(AExpr: TDerefExpr): TTypeDesc;
var
  PtrType: TTypeDesc;
begin
  PtrType := AnalyseExpr(AExpr.Expr);
  if PtrType.Kind <> tyPointer then
    SemanticError(
      Format('Dereference operator ''%s^'' requires a pointer type',
        [PtrType.Name]),
      AExpr.Line, AExpr.Col);
  if TPointerTypeDesc(PtrType).BaseType = nil then
    SemanticError(
      'Cannot dereference untyped ''Pointer'' — use a typed pointer (e.g. ^Integer)',
      AExpr.Line, AExpr.Col);
  Result := TPointerTypeDesc(PtrType).BaseType;
end;

function TSemanticAnalyser.AnalyseAddrOfExpr(AExpr: TAddrOfExpr): TTypeDesc;
var
  InnerType: TTypeDesc;
  PtrName: string;
  PT: TPointerTypeDesc;
  Sym: TSymbol;
begin
  InnerType := AnalyseExpr(AExpr.Expr);
  PtrName := '^' + InnerType.Name;
  Result := FindTypeOrInstantiate(PtrName);
  if Result = nil then
  begin
    PT := FTable.NewPointerType(PtrName, InnerType);
    Sym := TSymbol.Create(PtrName, skType, PT);
    FTable.DefineGlobal(Sym);
    Result := PT;
  end;
  AExpr.ResolvedType := Result;
end;

function TSemanticAnalyser.AnalyseStringSubscriptExpr(AExpr: TStringSubscriptExpr): TTypeDesc;
var
  StrType, IdxType: TTypeDesc;
  FldAccess: TFieldAccessExpr;
begin
  StrType := AnalyseExpr(AExpr.StrExpr);
  { Indexed property read: Obj.Prop[I] where Prop is a method-backed indexed property }
  if AExpr.StrExpr is TFieldAccessExpr then
  begin
    FldAccess := TFieldAccessExpr(AExpr.StrExpr);
    if (FldAccess.PropRead <> nil) and (FldAccess.PropRead.IndexParamName <> '') then
    begin
      IdxType := AnalyseExpr(AExpr.IndexExpr);
      FldAccess.PropIndexExpr := AExpr.IndexExpr;
      AExpr.IndexExpr := nil;
      Result := FldAccess.PropRead.TypeDesc;
      AExpr.ResolvedType := Result;
      Exit;
    end;
  end;
  { Static array element access: A[I] where A is a static array local }
  if StrType.Kind = tyStaticArray then
  begin
    IdxType := AnalyseExpr(AExpr.IndexExpr);
    if not IdxType.IsNumeric then
      SemanticError(
        Format('Static array index must be numeric, got ''%s''', [IdxType.Name]),
        AExpr.Line, AExpr.Col);
    Result := TStaticArrayTypeDesc(StrType).ElementType;
    AExpr.ResolvedType := Result;
    Exit;
  end;
  { Open-array element access: A[I] where A is an open-array parameter }
  if StrType.Kind = tyOpenArray then
  begin
    IdxType := AnalyseExpr(AExpr.IndexExpr);
    if not IdxType.IsNumeric then
      SemanticError(
        Format('Open-array index must be numeric, got ''%s''', [IdxType.Name]),
        AExpr.Line, AExpr.Col);
    Result := TOpenArrayTypeDesc(StrType).ElementType;
    AExpr.ResolvedType := Result;
    Exit;
  end;
  { PChar byte access: P[I] — 0-based, reads one byte as Integer }
  if StrType.Kind = tyPChar then
  begin
    IdxType := AnalyseExpr(AExpr.IndexExpr);
    if not IdxType.IsNumeric then
      SemanticError(
        Format('PChar subscript index must be numeric, got ''%s''', [IdxType.Name]),
        AExpr.Line, AExpr.Col);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;
  if not StrType.IsString then
    SemanticError(
      Format('String subscript ''[]'' requires a string expression, got ''%s''',
        [StrType.Name]),
      AExpr.Line, AExpr.Col);
  IdxType := AnalyseExpr(AExpr.IndexExpr);
  if not IdxType.IsNumeric then
    SemanticError(
      Format('String subscript index must be numeric, got ''%s''', [IdxType.Name]),
      AExpr.Line, AExpr.Col);
  Result := FTable.TypeInteger;
end;

procedure TSemanticAnalyser.CoerceToCharOrd(ALit: TStringLiteral);
begin
  if Length(ALit.Value) <> 1 then
    SemanticError(
      Format('String literal ''%s'' is %d bytes and cannot coerce to Byte; ' +
        'use a single ASCII character (U+0000..U+007F)',
        [ALit.Value, Length(ALit.Value)]),
      ALit.Line, ALit.Col);
  ALit.IsCharCoerce := True;
  ALit.CharOrdValue := Ord(ALit.Value[1]);
  ALit.ResolvedType := FTable.TypeInteger;
end;

procedure TSemanticAnalyser.AnalyseCaseStmt(AStmt: TCaseStmt);
var
  SelType:  TTypeDesc;
  Branch:   TCaseBranch;
  ValType:  TTypeDesc;
  I, J:     Integer;
begin
  SelType := AnalyseExpr(AStmt.Selector);
  if not SelType.IsOrdinal then
    SemanticError(
      Format('case selector must be ordinal type, got ''%s''', [SelType.Name]),
      AStmt.Line, AStmt.Col);
  for I := 0 to AStmt.Branches.Count - 1 do
  begin
    Branch := TCaseBranch(AStmt.Branches.Items[I]);
    for J := 0 to Branch.Values.Count - 1 do
    begin
      ValType := AnalyseExpr(TASTExpr(Branch.Values.Items[J]));
      CheckTypesMatch(SelType, ValType, 'case value', AStmt.Line, AStmt.Col);
    end;
    AnalyseStmt(Branch.Stmt);
  end;
  if AStmt.ElseStmt <> nil then
    AnalyseStmt(AStmt.ElseStmt);
end;

procedure TSemanticAnalyser.AnalysePointerWriteStmt(AStmt: TPointerWriteStmt);
var
  PtrType: TTypeDesc;
  ValType: TTypeDesc;
begin
  PtrType := AnalyseExpr(AStmt.PtrExpr);
  if PtrType.Kind <> tyPointer then
    SemanticError(
      Format('Pointer write requires a pointer type, got ''%s''', [PtrType.Name]),
      AStmt.Line, AStmt.Col);
  if TPointerTypeDesc(PtrType).BaseType = nil then
    SemanticError(
      'Cannot write through untyped ''Pointer'' — use a typed pointer (e.g. ^Integer)',
      AStmt.Line, AStmt.Col);
  AStmt.BaseTy := TPointerTypeDesc(PtrType).BaseType;
  ValType := AnalyseExpr(AStmt.ValExpr);
  CheckTypesMatch(AStmt.BaseTy, ValType, 'pointer write', AStmt.Line, AStmt.Col);
end;

procedure TSemanticAnalyser.AnalyseStaticSubscriptAssign(AStmt: TStaticSubscriptAssign);
var
  Sym:     TSymbol;
  ArrType: TStaticArrayTypeDesc;
  IdxType: TTypeDesc;
  ValType: TTypeDesc;
begin
  Sym := FTable.Lookup(AStmt.ArrayName);
  if Sym = nil then
    SemanticError(
      Format('Undeclared variable ''%s''', [AStmt.ArrayName]),
      AStmt.Line, AStmt.Col);
  { PChar subscript write: P[I] := Integer — storeb at ptr + I }
  if Sym.TypeDesc.Kind = tyPChar then
  begin
    AStmt.IsGlobal := Sym.IsGlobal;
    AStmt.ResolvedArrayType := FTable.TypePChar;
    IdxType := AnalyseExpr(AStmt.IndexExpr);
    if not IdxType.IsNumeric then
      SemanticError('PChar subscript index must be numeric', AStmt.Line, AStmt.Col);
    AnalyseExpr(AStmt.ValueExpr);
    Exit;
  end;
  if Sym.TypeDesc.Kind <> tyStaticArray then
    SemanticError(
      Format('''%s'' is not a static array', [AStmt.ArrayName]),
      AStmt.Line, AStmt.Col);
  ArrType := TStaticArrayTypeDesc(Sym.TypeDesc);
  AStmt.IsGlobal := Sym.IsGlobal;
  AStmt.ResolvedArrayType := ArrType;
  IdxType := AnalyseExpr(AStmt.IndexExpr);
  if not IdxType.IsNumeric then
    SemanticError('Array index must be numeric', AStmt.Line, AStmt.Col);
  ValType := AnalyseExpr(AStmt.ValueExpr);
  CheckTypesMatch(ArrType.ElementType, ValType,
    Format('''%s'' element', [AStmt.ArrayName]), AStmt.Line, AStmt.Col);
end;

function TSemanticAnalyser.AnalyseArrayLiteralExpr(AExpr: TArrayLiteralExpr): TTypeDesc;
var
  ElemType: TTypeDesc;
  ActType:  TTypeDesc;
  I:        Integer;
begin
  if AExpr.Elements.Count = 0 then
    SemanticError('Array literal must contain at least one element',
      AExpr.Line, AExpr.Col);
  ElemType := AnalyseExpr(TASTExpr(AExpr.Elements.Items[0]));
  for I := 1 to AExpr.Elements.Count - 1 do
  begin
    ActType := AnalyseExpr(TASTExpr(AExpr.Elements.Items[I]));
    if ActType <> ElemType then
      SemanticError(
        Format('Array literal element %d has type ''%s''; expected ''%s''',
          [I + 1, ActType.Name, ElemType.Name]),
        AExpr.Line, AExpr.Col);
  end;
  Result := FTable.NewOpenArrayType(ElemType);
  AExpr.ResolvedType := Result;
end;

function TSemanticAnalyser.AnalyseSetLiteralExpr(AExpr: TArrayLiteralExpr;
  ASetType: TSetTypeDesc): TTypeDesc;
{ Validates a set literal [elem, ...] against ASetType.
  Elements must be constants or variables of the set's base enum type.
  An empty literal [] is valid and yields the set type with bitmask 0. }
var
  ElemType: TTypeDesc;
  I:        Integer;
begin
  for I := 0 to AExpr.Elements.Count - 1 do
  begin
    ElemType := AnalyseExpr(TASTExpr(AExpr.Elements.Items[I]));
    if ElemType <> ASetType.BaseType then
      SemanticError(
        Format('Set literal element %d has type ''%s''; expected ''%s''',
          [I + 1, ElemType.Name, ASetType.BaseType.Name]),
        AExpr.Line, AExpr.Col);
  end;
  AExpr.ResolvedType := ASetType;
  Result := ASetType;
end;

end.
