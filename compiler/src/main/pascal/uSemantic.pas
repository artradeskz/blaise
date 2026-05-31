{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uSemantic;

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
  SysUtils, Classes, contnrs, uAST, uSymbolTable, uStrCompat;

type
  ESemanticError = class(Exception);

  TSemanticAnalyser = class
  private
    FTable:                TSymbolTable;
    FProg:                 TProgram;      { current program being analysed; set in Analyse }
    FCurrentUnit:          TUnit;        { current unit being analysed; nil during program analysis }
    FMethodIndex:          TStringList;  { 'TypeName.MethodName' → TMethodDecl (not owned) }
    FProcIndex:            TStringList;  { 'ProcName' → TMethodDecl (not owned) }
    FGenericFuncTemplates: TStringList;  { base name → TMethodDecl template (not owned) }
    FLoopDepth:            Integer;      { depth of enclosing while/for — Break only legal if > 0 }
    FScopeDepth:           Integer;      { mirrors FTable scope depth; used to detect main-level globals }
    FCurrentClass:         TRecordTypeDesc;  { class being analysed (set in AnalyseMethodDecl) }
    FCurrentLocalBlock:    TBlock;       { block currently being stmt-analysed; for-in injects synthetic TVarDecl here }
    FForInCounter:         Integer;      { counter for generating unique __forin_N variable names }
    FCurrentUnitName:      string;       { name of the unit/program currently being analysed }
    FCurrentEnclosingDecl: TMethodDecl;  { the innermost standalone proc/func currently being analysed;
                                           nil at program level.  Used to set EnclosingDecl on nested procs. }

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
    procedure AnalyseArrayConstDecls(ABlock: TBlock);
    procedure AnalyseTypeDecls(ABlock: TBlock);
    procedure LinkClassMethodImpls(ABlock: TBlock);
    procedure LinkGenericClassMethodImpls(ABlock: TBlock);
    procedure AnalyseMethodBodies(ABlock: TBlock);
    procedure AnalyseMethodDecl(AMethod: TMethodDecl; AClassType: TRecordTypeDesc);
    procedure AnalyseStandaloneDecls(ABlock: TBlock);
    procedure AnalyseStandaloneBodies(ABlock: TBlock);
    procedure AnalyseStandaloneDecl(ADecl: TMethodDecl);
    procedure CollectCaptures(ADecl: TMethodDecl; AOuterBlock: TBlock);
    { Inlining: after bodies are analysed, mark each TMethodDecl whose body
      qualifies for codegen-side inlining.  Conservative: primitive params
      + return + locals only; no try/loops/raise/nested defs; small body.
      See docs/inlining-design.adoc. }
    procedure MarkInlineCandidates(ABlock: TBlock);
    function  IsInlineEligible(ADecl: TMethodDecl): Boolean;
    function  StmtRejectsInline(AStmt: TASTStmt;
                                 const ASelfDecl: TMethodDecl;
                                 var AStmtCount: Integer): Boolean;
    function  ExprRejectsInline(AExpr: TASTExpr;
                                 const ASelfDecl: TMethodDecl): Boolean;
    function  AssignmentTargetsParameter(const AName: string;
                                          const ADecl: TMethodDecl): Boolean;
    procedure AnalyseVarDecls(ABlock: TBlock);
    procedure AnalyseStmts(ABlock: TBlock);
    procedure AnalyseStmt(AStmt: TASTStmt);
    procedure AnalyseAssignment(AAssign: TAssignment);
    procedure AnalyseFieldAssignment(AAssign: TFieldAssignment);
    procedure AnalyseProcCall(ACall: TProcCall);
    { Phase A/B overload resolution.  Walks FProcIndex collecting all
      decls whose name matches AName (case-insensitive); filters by
      arity; for the survivors, scores per-argument compatibility
      using AArgs (each TASTExpr already analysed, ResolvedType set);
      returns the highest-scoring candidate.  Raises ESemanticError on
      "no matching overload" or ambiguous ties.  AArgs may be nil for
      a pure arity probe (used when args are not yet analysed). }
    function  ResolveStandaloneOverload(const AName: string;
      AArity: Integer; AArgs: TObjectList;
      ALine, ACol: Integer): TMethodDecl;
    { Class-method overload resolution.  Walks the inheritance chain
      starting at ATypeName, collecting candidates whose method name
      matches AMethodName.  Filters by arity, scores by argument type
      (Phase B rules), returns the best match.  Raises ESemanticError
      on no-match or ambiguity.  AArgs may be nil to fall back to
      first-name-match (used by paths that need the decl before args
      are analysed, e.g. zero-arg lookups). }
    function  ResolveMethodOverload(const ATypeName, AMethodName: string;
      AArgs: TObjectList; ALine, ACol: Integer): TMethodDecl;
    { Type-code suffix for a single parameter.  Phase B mangling. }
    function  MangleTypeCode(AType: TTypeDesc; AVarParam: Boolean): string;
    { Full mangled signature for a TMethodDecl: '$<code1><code2>…'.
      Empty parameter list yields '$' (lone dollar). }
    function  MangleParamSig(ADecl: TMethodDecl): string;
    { Per-arg compatibility: 2 = exact, 1 = widening, 0 = no match. }
    function  ArgMatchScore(AParam: TTypeDesc; AArg: TTypeDesc;
                AArgExpr: TASTExpr = nil): Integer;
    procedure AnalyseMethodCall(ACall: TMethodCallStmt);
    procedure AnalyseInheritedCall(ACall: TInheritedCallStmt);
    procedure AnalyseCaseStmt(AStmt: TCaseStmt);
    function  AnalyseMethodCallExpr(AExpr: TMethodCallExpr): TTypeDesc;
    function  AnalyseFuncCallExpr(AExpr: TFuncCallExpr): TTypeDesc;
    function  AnalyseIndirectFuncCallExpr(AExpr: TIndirectFuncCallExpr): TTypeDesc;
    function  AnalyseExpr(AExpr: TASTExpr): TTypeDesc;
    function  AnalyseBinaryExpr(ABin: TBinaryExpr): TTypeDesc;
    function  AnalyseFieldAccess(AAccess: TFieldAccessExpr): TTypeDesc;
    function  AnalyseIsExpr(AExpr: TIsExpr): TTypeDesc;
    function  AnalyseAsExpr(AExpr: TAsExpr): TTypeDesc;
    function  AnalyseSupportsExpr(AExpr: TSupportsExpr): TTypeDesc;
    function  AnalyseDerefExpr(AExpr: TDerefExpr): TTypeDesc;
    function  AnalyseAddrOfExpr(AExpr: TAddrOfExpr): TTypeDesc;
    procedure ResolveProceduralTypeDef(ATD: TTypeDecl);
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
      any form of the Weak marker.  IsCustomAttributeClass walks the parent
      chain of a class to verify it descends from TCustomAttribute. }
    function  AttrMatches(const AAttrName, ACanonical: string): Boolean;
    function  HasWeakAttribute(AAttrs: TStringList): Boolean;
    function  IsCustomAttributeClass(const ATypeName: string): Boolean;
    function  ResolveCustomAttrName(const ARawName: string): string;

    { Default-argument support.  MinArity returns the minimum number of
      arguments a call must supply: params before the first one carrying a
      DefaultValue.  TransferDefaultValues moves DefaultValue ownership from
      AFrom's params into AInto's matching params (used to forward defaults
      from an interface forward decl to its implementation).
      AnalyseDefaultValueExpr type-checks an already-attached default
      expression against the param's resolved type.
      CloneDefaultExprNode produces a fresh AST copy of a default-value
      literal/identifier so a call site can own its own argument node.
      AppendDefaultArgs fills a call's Args list from MDecl.Params for any
      missing trailing slots (Args.Count < Params.Count). }
    function  MinArity(ADecl: TMethodDecl): Integer;
    procedure TransferDefaultValues(AFrom, AInto: TMethodDecl);
    procedure AnalyseDefaultValueExpr(APar: TMethodParam;
      const AContext: string; ALine, ACol: Integer);
    function  CloneDefaultExprNode(ASrc: TASTExpr): TASTExpr;
    procedure AppendDefaultArgs(AArgs: TObjectList; ADecl: TMethodDecl;
      const AContext: string; ALine, ACol: Integer);

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
  if FCurrentUnitName <> '' then
    raise ESemanticError.Create(Format('%s at line %d col %d in %s', [AMsg, ALine, ACol, FCurrentUnitName]))
  else
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

function TSemanticAnalyser.IsCustomAttributeClass(const ATypeName: string): Boolean;
var
  Sym:  TSymbol;
  RT:   TRecordTypeDesc;
  Walk: TRecordTypeDesc;
begin
  Result := False;
  Sym := FTable.Lookup(ATypeName);
  if (Sym = nil) or not (Sym.TypeDesc is TRecordTypeDesc) then Exit;
  RT := TRecordTypeDesc(Sym.TypeDesc);
  if RT.Kind <> tyClass then Exit;
  Walk := RT;
  while Walk <> nil do
  begin
    if SameText(Walk.Name, 'TCustomAttribute') then
    begin
      Result := True;
      Exit;
    end;
    Walk := Walk.Parent;
  end;
end;

function TSemanticAnalyser.ResolveCustomAttrName(const ARawName: string): string;
{ Apply Delphi suffix convention: try 'Name' then 'NameAttribute'. Returns the
  resolved class name that descends from TCustomAttribute, or '' if not found. }
var
  Sym: TSymbol;
begin
  Result := '';
  Sym := FTable.Lookup(ARawName);
  if (Sym <> nil) and (Sym.TypeDesc is TRecordTypeDesc) and
     IsCustomAttributeClass(ARawName) then
  begin
    Result := ARawName;
    Exit;
  end;
  Sym := FTable.Lookup(ARawName + 'Attribute');
  if (Sym <> nil) and (Sym.TypeDesc is TRecordTypeDesc) and
     IsCustomAttributeClass(ARawName + 'Attribute') then
    Result := ARawName + 'Attribute';
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
    if not (ArgType.Kind in [tyRecord, tyInteger, tyInt64, tyUInt32, tyUInt64,
                             tySmallInt, tyWord, tyByte, tyBoolean, tyString,
                             tyPointer]) then
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
  if (AActual.Kind = tyNil) and (AExpected.Kind in [tyClass, tyInterface, tyPointer, tyPChar, tyString, tyProcedural]) then
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
  { Metaclass-of-TBase accepts metaclass-of-TDerived (TDerived is-a TBase). }
  if (AExpected.Kind = tyMetaClass) and (AActual.Kind = tyMetaClass) then
  begin
    if (TMetaClassTypeDesc(AExpected).BaseClass = TMetaClassTypeDesc(AActual).BaseClass) or
       IsSubtypeOf(TMetaClassTypeDesc(AActual).BaseClass,
                   TMetaClassTypeDesc(AExpected).BaseClass) then
      Exit;
  end;
  { Untyped Pointer ↔ metaclass: a class identifier passes through any
    'Pointer' parameter (used heavily by punit.AssertEquals(Pointer)). }
  if (AExpected.Kind = tyPointer) and (AActual.Kind = tyMetaClass) and
     (TPointerTypeDesc(AExpected).BaseType = nil) then
    Exit;
  if (AActual.Kind = tyPointer) and (AExpected.Kind = tyMetaClass) and
     (TPointerTypeDesc(AActual).BaseType = nil) then
    Exit;
  { enum ↔ enum (same type) already handled by = check above;
    enum ↔ integer: allow assignment between enum and integer types }
  if (AExpected.Kind = tyEnum) and AActual.IsNumeric then Exit;
  if (AActual.Kind  = tyEnum) and AExpected.IsNumeric then Exit;
  { Numeric widening: allow within the integer family, within the float family
    (Single ↔ Double), and integer → float (implicit widening, same as
    Delphi/FPC).  Float → integer still requires explicit Trunc/Round.
    Exception: Int64 ↔ UInt64 requires an explicit cast since the same
    bit pattern means different values across the sign boundary. }
  if AExpected.IsFloat and AActual.IsFloat then Exit;
  if AExpected.IsFloat and AActual.IsNumeric and (not AActual.IsFloat) then Exit;
  if AExpected.IsNumeric and AActual.IsNumeric
     and (not AExpected.IsFloat) and (not AActual.IsFloat) then
  begin
    if not (((AExpected.Kind = tyInt64)  and (AActual.Kind = tyUInt64)) or
            ((AExpected.Kind = tyUInt64) and (AActual.Kind = tyInt64))) then
      Exit;
  end;
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
  { Static array coerced to open-array: element types must match }
  if (AExpected.Kind = tyOpenArray) and (AActual.Kind = tyStaticArray) then
  begin
    if TOpenArrayTypeDesc(AExpected).ElementType =
       TStaticArrayTypeDesc(AActual).ElementType then
      Exit;
  end;
  { Procedural-type assignability: signatures must match (return type,
    parameter count, parameter types, parameter modes). }
  if (AExpected.Kind = tyProcedural) and (AActual.Kind = tyProcedural) then
  begin
    if TProceduralTypeDesc(AExpected).IsCompatibleWith(
         TProceduralTypeDesc(AActual)) then
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
  FCurrentUnitName := AProg.Name;
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
  FCurrentUnitName := AUnit.Name;
  FCurrentUnit := AUnit;
  FTable.PushScope;
  try
    { Resolve interface type and constant declarations. }
    AnalyseConstDecls(AUnit.IntfBlock);
    AnalyseTypeDecls(AUnit.IntfBlock);
    AnalyseArrayConstDecls(AUnit.IntfBlock);

    { Generic class templates must receive their impl-section method bodies
      *before* any FindTypeOrInstantiate call can clone an instance, or the
      instance is born with nil bodies and codegen emits no function for it. }
    LinkGenericClassMethodImpls(AUnit.ImplBlock);

    { Register interface-section global variables — visible to impl bodies. }
    for I := 0 to AUnit.IntfBlock.Decls.Count - 1 do
    begin
      MDecl := nil;  { reuse var below }
      ParType := FindTypeOrInstantiate(TVarDecl(AUnit.IntfBlock.Decls.Items[I]).TypeName);
      if ParType = nil then
        SemanticError(
          Format('Unknown type ''%s''',
            [TVarDecl(AUnit.IntfBlock.Decls.Items[I]).TypeName]),
          TVarDecl(AUnit.IntfBlock.Decls.Items[I]).Line,
          TVarDecl(AUnit.IntfBlock.Decls.Items[I]).Col);
      TVarDecl(AUnit.IntfBlock.Decls.Items[I]).ResolvedType := ParType;
      TVarDecl(AUnit.IntfBlock.Decls.Items[I]).IsGlobal := True;
      for J := 0 to TVarDecl(AUnit.IntfBlock.Decls.Items[I]).Names.Count - 1 do
      begin
        Sym := TSymbol.Create(
          TVarDecl(AUnit.IntfBlock.Decls.Items[I]).Names.Strings[J],
          skVariable, ParType);
        Sym.IsGlobal := True;
        if not FTable.Define(Sym) then
        begin
          Sym.Free;
          SemanticError(Format('Duplicate identifier ''%s''',
            [TVarDecl(AUnit.IntfBlock.Decls.Items[I]).Names.Strings[J]]),
            TVarDecl(AUnit.IntfBlock.Decls.Items[I]).Line,
            TVarDecl(AUnit.IntfBlock.Decls.Items[I]).Col);
        end;
      end;
    end;

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

      { Compute mangled QBE name for overloaded forward decls. }
      if MDecl.IsOverload then
        MDecl.ResolvedQbeName := MDecl.Name + '$' + MangleParamSig(MDecl)
      else
        MDecl.ResolvedQbeName := MDecl.Name;

      FProcIndex.AddObject(MDecl.Name, MDecl);

      if MDecl.ReturnTypeName <> '' then
        Sym := TSymbol.Create(MDecl.Name, skFunction, MDecl.ResolvedReturnType)
      else
        Sym := TSymbol.Create(MDecl.Name, skProcedure, nil);
      Sym.IsOverload := MDecl.IsOverload;
      Sym.Decl       := MDecl;
      if not FTable.Define(Sym) then
      begin
        Sym.Free;
        SemanticError(Format('Duplicate identifier ''%s''', [MDecl.Name]),
          MDecl.Line, MDecl.Col);
      end;
    end;

    { Process implementation-section const + type declarations before
      walking proc bodies, so that impl-only types and consts are in
      scope when their referencing routines are analysed. }
    AnalyseConstDecls(AUnit.ImplBlock);
    AnalyseTypeDecls(AUnit.ImplBlock);
    AnalyseArrayConstDecls(AUnit.ImplBlock);

    { Register impl-section global variables. }
    for I := 0 to AUnit.ImplBlock.Decls.Count - 1 do
    begin
      ParType := FindTypeOrInstantiate(TVarDecl(AUnit.ImplBlock.Decls.Items[I]).TypeName);
      if ParType = nil then
        SemanticError(
          Format('Unknown type ''%s''',
            [TVarDecl(AUnit.ImplBlock.Decls.Items[I]).TypeName]),
          TVarDecl(AUnit.ImplBlock.Decls.Items[I]).Line,
          TVarDecl(AUnit.ImplBlock.Decls.Items[I]).Col);
      TVarDecl(AUnit.ImplBlock.Decls.Items[I]).ResolvedType := ParType;
      TVarDecl(AUnit.ImplBlock.Decls.Items[I]).IsGlobal := True;
      for J := 0 to TVarDecl(AUnit.ImplBlock.Decls.Items[I]).Names.Count - 1 do
      begin
        Sym := TSymbol.Create(
          TVarDecl(AUnit.ImplBlock.Decls.Items[I]).Names.Strings[J],
          skVariable, ParType);
        Sym.IsGlobal := True;
        if not FTable.Define(Sym) then
        begin
          Sym.Free;
          SemanticError(Format('Duplicate identifier ''%s''',
            [TVarDecl(AUnit.ImplBlock.Decls.Items[I]).Names.Strings[J]]),
            TVarDecl(AUnit.ImplBlock.Decls.Items[I]).Line,
            TVarDecl(AUnit.ImplBlock.Decls.Items[I]).Col);
        end;
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

      { Match impl to forward by signature.
        When any forward decl with this name is overloaded (or when the impl
        itself is marked overload), use mangled-signature matching so that each
        overload variant pairs with the correct forward decl.  This handles the
        common pattern where the interface marks each overload but the
        implementation body omits the 'overload' keyword. }
      ImplIdx := -1;
      if ImplDecl.IsOverload then
      begin
        for J := 0 to FProcIndex.Count - 1 do
          if SameText(FProcIndex.Strings[J], ImplDecl.Name) and
             (TMethodDecl(FProcIndex.Objects[J]).IsOverload) and
             (MangleParamSig(TMethodDecl(FProcIndex.Objects[J])) =
              MangleParamSig(ImplDecl)) then
          begin
            ImplIdx := J;
            Break;
          end;
      end
      else
      begin
        { Check if any forward decl with this name is overloaded.
          If so, use signature matching even without 'overload' on the impl. }
        for J := 0 to FProcIndex.Count - 1 do
          if SameText(FProcIndex.Strings[J], ImplDecl.Name) and
             (TMethodDecl(FProcIndex.Objects[J]).IsOverload) and
             (MangleParamSig(TMethodDecl(FProcIndex.Objects[J])) =
              MangleParamSig(ImplDecl)) then
          begin
            ImplIdx := J;
            Break;
          end;
        if ImplIdx < 0 then
          ImplIdx := FProcIndex.IndexOf(ImplDecl.Name);
      end;

      if ImplIdx >= 0 then
      begin
        { Matched an interface forward decl — verify param count }
        MDecl := TMethodDecl(FProcIndex.Objects[ImplIdx]);
        if MDecl.Params.Count <> ImplDecl.Params.Count then
          SemanticError(
            Format('Signature mismatch for ''%s'': interface has %d params, implementation has %d',
              [ImplDecl.Name, MDecl.Params.Count, ImplDecl.Params.Count]),
            ImplDecl.Line, ImplDecl.Col);
        { Carry mangling forward, then update the index entry. }
        ImplDecl.ResolvedQbeName := MDecl.ResolvedQbeName;
        ImplDecl.IsOverload      := MDecl.IsOverload;
        TransferDefaultValues(MDecl, ImplDecl);
        FProcIndex.Objects[ImplIdx] := ImplDecl;
      end
      else
      begin
        { Impl-only declaration — register symbol and index it }
        if ImplDecl.IsOverload then
          ImplDecl.ResolvedQbeName := ImplDecl.Name + '$' + MangleParamSig(ImplDecl)
        else
          ImplDecl.ResolvedQbeName := ImplDecl.Name;
        FProcIndex.AddObject(ImplDecl.Name, ImplDecl);
        if ImplDecl.ReturnTypeName <> '' then
          Sym := TSymbol.Create(ImplDecl.Name, skFunction, ImplDecl.ResolvedReturnType)
        else
          Sym := TSymbol.Create(ImplDecl.Name, skProcedure, nil);
        Sym.IsOverload := ImplDecl.IsOverload;
        Sym.Decl       := ImplDecl;
        if not FTable.Define(Sym) then
        begin
          Sym.Free;
          SemanticError(Format('Duplicate identifier ''%s''', [ImplDecl.Name]),
            ImplDecl.Line, ImplDecl.Col);
        end;
      end;
    end;

    { Generic class method body linking already happened above, before any
      potential instantiation. }

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

    { After all unit-impl bodies are analysed, mark inline candidates. }
    MarkInlineCandidates(AUnit.ImplBlock);

    { Analyse initialization/finalization section statements at unit scope. }
    if AUnit.InitStmts <> nil then
      for I := 0 to AUnit.InitStmts.Count - 1 do
        AnalyseStmt(TASTStmt(AUnit.InitStmts.Items[I]));
    if AUnit.FinalStmts <> nil then
      for I := 0 to AUnit.FinalStmts.Count - 1 do
        AnalyseStmt(TASTStmt(AUnit.FinalStmts.Items[I]));
  finally
    FTable.PopScope;
  end;
  AUnit.SymbolTable := FTable;
  FTable := nil;
  FCurrentUnit := nil;
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
  FCurrentUnitName := AUnit.Name;
  FCurrentUnit := AUnit;
  { --- Interface section ------------------------------------------------
    No scope is pushed here: all FTable.Define calls go to the global scope,
    making these symbols visible to callers of this unit. }

  AnalyseConstDecls(AUnit.IntfBlock);
  AnalyseTypeDecls(AUnit.IntfBlock);
  AnalyseArrayConstDecls(AUnit.IntfBlock);

  { Transfer impl-section bodies to generic class templates *before* any
    instantiation can happen.  Generic instances clone the template's
    Methods.Body at instantiation time (uSemantic.pas ~line 1524), so if
    the body is still nil when an interface-section global variable or
    parameter triggers FindTypeOrInstantiate, the cloned instance method
    is born without a body and codegen emits no function — leaving call
    sites referencing an undefined symbol. }
  LinkGenericClassMethodImpls(AUnit.ImplBlock);

  { Register interface-section global variables.  Marked IsGlobal so
    codegen emits them as data-segment slots rather than stack allocs;
    visible to callers of this unit. }
  for I := 0 to AUnit.IntfBlock.Decls.Count - 1 do
  begin
    VDecl := TVarDecl(AUnit.IntfBlock.Decls.Items[I]);
    ParType := FindTypeOrInstantiate(VDecl.TypeName);
    if ParType = nil then
      SemanticError(Format('Unknown type ''%s''', [VDecl.TypeName]),
        VDecl.Line, VDecl.Col);
    VDecl.ResolvedType := ParType;
    VDecl.IsGlobal := True;
    for J := 0 to VDecl.Names.Count - 1 do
    begin
      Sym := TSymbol.Create(VDecl.Names.Strings[J], skVariable, ParType);
      Sym.IsGlobal := True;
      if not FTable.Define(Sym) then
      begin
        Sym.Free;
        SemanticError(Format('Duplicate identifier ''%s''',
          [VDecl.Names.Strings[J]]), VDecl.Line, VDecl.Col);
      end;
    end;
  end;

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

    if MDecl.IsOverload then
      MDecl.ResolvedQbeName := MDecl.Name + '$' + MangleParamSig(MDecl)
    else
      MDecl.ResolvedQbeName := MDecl.Name;

    FProcIndex.AddObject(MDecl.Name, MDecl);

    if MDecl.ReturnTypeName <> '' then
      Sym := TSymbol.Create(MDecl.Name, skFunction, MDecl.ResolvedReturnType)
    else
      Sym := TSymbol.Create(MDecl.Name, skProcedure, nil);
    Sym.IsOverload := MDecl.IsOverload;
    Sym.Decl       := MDecl;
    if not FTable.Define(Sym) then
    begin
      Sym.Free;
      SemanticError(Format('Duplicate identifier ''%s''', [MDecl.Name]),
        MDecl.Line, MDecl.Col);
    end;
  end;

  { Link class method bodies from ImplBlock to the class type method decls
    registered by AnalyseTypeDecls.  Generic-class linking happened earlier
    so instances can clone bodies at instantiation time. }
  LinkClassMethodImpls(AUnit.ImplBlock);

  { --- Implementation section -------------------------------------------
    Push a scope so impl-only standalone symbols don't leak globally.
    Class method bodies are analysed inside this scope so they can call
    impl-only helpers (e.g. TStringList.SetText -> SplitIntoList). }
  FTable.PushScope;
  try
    { Register impl-section global variables — marked IsGlobal so codegen
      emits them as data-segment slots rather than stack allocations. }
    AnalyseConstDecls(AUnit.ImplBlock);
    AnalyseTypeDecls(AUnit.ImplBlock);
    AnalyseArrayConstDecls(AUnit.ImplBlock);
    for I := 0 to AUnit.ImplBlock.Decls.Count - 1 do
    begin
      VDecl := TVarDecl(AUnit.ImplBlock.Decls.Items[I]);
      ParType := FindTypeOrInstantiate(VDecl.TypeName);
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

      { Match impl to forward by signature.
        When any forward decl with this name is overloaded (or when the impl
        itself is marked overload), use mangled-signature matching so that
        each overload variant pairs with the correct forward decl.
        This covers the common Pascal pattern where the interface marks each
        overload with the 'overload' keyword but the implementation section
        repeats the body without re-stating 'overload'. }
      ImplIdx := -1;
      if ImplDecl.IsOverload then
      begin
        for J := 0 to FProcIndex.Count - 1 do
          if SameText(FProcIndex.Strings[J], ImplDecl.Name) and
             (TMethodDecl(FProcIndex.Objects[J]).IsOverload) and
             (MangleParamSig(TMethodDecl(FProcIndex.Objects[J])) =
              MangleParamSig(ImplDecl)) then
          begin
            ImplIdx := J;
            Break;
          end;
      end
      else
      begin
        { Check if any forward decl with this name is overloaded.
          If so, use signature matching even though the impl lacks 'overload'. }
        for J := 0 to FProcIndex.Count - 1 do
          if SameText(FProcIndex.Strings[J], ImplDecl.Name) and
             (TMethodDecl(FProcIndex.Objects[J]).IsOverload) and
             (MangleParamSig(TMethodDecl(FProcIndex.Objects[J])) =
              MangleParamSig(ImplDecl)) then
          begin
            ImplIdx := J;
            Break;
          end;
        if ImplIdx < 0 then
          ImplIdx := FProcIndex.IndexOf(ImplDecl.Name);
      end;

      if ImplIdx >= 0 then
      begin
        { Matches an interface forward decl — verify param count and update index }
        MDecl := TMethodDecl(FProcIndex.Objects[ImplIdx]);
        if MDecl.Params.Count <> ImplDecl.Params.Count then
          SemanticError(
            Format('Signature mismatch for ''%s'': interface has %d params, implementation has %d',
              [ImplDecl.Name, MDecl.Params.Count, ImplDecl.Params.Count]),
            ImplDecl.Line, ImplDecl.Col);
        ImplDecl.ResolvedQbeName := MDecl.ResolvedQbeName;
        ImplDecl.IsOverload      := MDecl.IsOverload;
        TransferDefaultValues(MDecl, ImplDecl);
        FProcIndex.Objects[ImplIdx] := ImplDecl;
      end
      else
      begin
        { Impl-only declaration — register in impl scope (does not persist) }
        if ImplDecl.IsOverload then
          ImplDecl.ResolvedQbeName := ImplDecl.Name + '$' + MangleParamSig(ImplDecl)
        else
          ImplDecl.ResolvedQbeName := ImplDecl.Name;
        FProcIndex.AddObject(ImplDecl.Name, ImplDecl);
        if ImplDecl.ReturnTypeName <> '' then
          Sym := TSymbol.Create(ImplDecl.Name, skFunction, ImplDecl.ResolvedReturnType)
        else
          Sym := TSymbol.Create(ImplDecl.Name, skProcedure, nil);
        Sym.IsOverload := ImplDecl.IsOverload;
        Sym.Decl       := ImplDecl;
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

    { After all unit-impl bodies are analysed, mark inline candidates. }
    MarkInlineCandidates(AUnit.ImplBlock);

    { Analyse initialization/finalization section statements at unit scope. }
    if AUnit.InitStmts <> nil then
      for I := 0 to AUnit.InitStmts.Count - 1 do
        AnalyseStmt(TASTStmt(AUnit.InitStmts.Items[I]));
    if AUnit.FinalStmts <> nil then
      for I := 0 to AUnit.FinalStmts.Count - 1 do
        AnalyseStmt(TASTStmt(AUnit.FinalStmts.Items[I]));
  finally
    FTable.PopScope;
  end;
  FCurrentUnit := nil;
end;

procedure TSemanticAnalyser.LinkClassMethodImpls(ABlock: TBlock);
var
  I, J, K:  Integer;
  Decl:     TMethodDecl;
  Key:      string;
  CD:       TMethodDecl;
  Match:    TMethodDecl;
  ImplSig:  string;
  Par:      TMethodParam;
begin
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(ABlock.ProcDecls.Items[I]);
    if Decl.OwnerTypeName = '' then Continue;
    if Decl.OwnerTypeParams <> nil then Continue;  { generic owner — handled by LinkGenericClassMethodImpls }

    { Resolve impl param types so we can compute its signature for matching. }
    for J := 0 to Decl.Params.Count - 1 do
    begin
      Par              := TMethodParam(Decl.Params.Items[J]);
      Par.ResolvedType := ResolveParamType(Par, Decl.Line, Decl.Col);
    end;
    ImplSig := MangleParamSig(Decl);

    Key   := Decl.OwnerTypeName + '.' + Decl.Name;
    Match := nil;
    for K := 0 to FMethodIndex.Count - 1 do
      if SameText(FMethodIndex.Strings[K], Key) then
      begin
        CD := TMethodDecl(FMethodIndex.Objects[K]);
        if CD.IsOverload then
        begin
          if MangleParamSig(CD) = ImplSig then
          begin
            Match := CD;
            Break;
          end;
        end
        else
        begin
          { Non-overloaded: first (and only) match wins }
          Match := CD;
          Break;
        end;
      end;
    if Match = nil then
      SemanticError(
        Format('Method ''%s'' is not declared in class ''%s''',
          [Decl.Name, Decl.OwnerTypeName]),
        Decl.Line, Decl.Col);
    if Match.Body <> nil then
      SemanticError(
        Format('Method ''%s.%s'' already has an inline body',
          [Decl.OwnerTypeName, Decl.Name]),
        Decl.Line, Decl.Col);
    { Transfer the body; after this, AnalyseMethodBodies will find and analyse it }
    Match.Body := Decl.Body;
    Decl.Body  := nil;
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
  BrOpen  := StrPos('<', ATypeName);
  if BrOpen < 0 then Exit;
  BrClose  := Length(ATypeName);
  BasePart := StrHead(ATypeName, BrOpen);
  ArgsPart := StrCopyFrom(ATypeName, BrOpen + 1, BrClose - BrOpen - 2);
  ArgList  := TStringList.Create;
  try
    while ArgsPart <> '' do
    begin
      I := StrPos(',', ArgsPart);
      if I >= 0 then
      begin
        ArgList.Add(Trim(StrHead(ArgsPart, I)));
        ArgsPart := Trim(StrCopyTail(ArgsPart, I + 1));
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
  CanonName: string;
  SAT: TStaticArrayTypeDesc;
  DAT: TDynArrayTypeDesc;
begin
  Result := FTable.FindType(AName);
  if Result <> nil then Exit;
  { Dynamic array: 'array of TypeName' — create on demand.  Key cache by
    the canonical element-type name so 'array of T' under T=String and
    T=TObject do not collide. }
  if (Length(AName) > 9) and (StrHead(AName, 9) = 'array of ') then
  begin
    ElemName := StrCopyTail(AName, 9);
    BaseType := FindTypeOrInstantiate(ElemName);
    if BaseType <> nil then
    begin
      CanonName := 'array of ' + BaseType.Name;
      Result    := FTable.FindType(CanonName);
      if Result = nil then
      begin
        DAT := FTable.NewDynArrayType(BaseType);
        Sym := TSymbol.Create(CanonName, skType, DAT);
        FTable.DefineGlobal(Sym);
        Result := DAT;
      end;
    end;
    Exit;
  end;
  { Static array: 'array[L..H] of TypeName' — create on demand. }
  if (Length(AName) > 6) and (StrHead(AName, 6) = 'array[') then
  begin
    DDotPos  := StrPos('..', AName);
    RBrPos   := StrPos(']', AName);
    OfPos    := StrPos(' of ', AName);
    LStr     := StrCopyFrom(AName, 6, DDotPos - 6);
    HStr     := StrCopyFrom(AName, DDotPos + 2, RBrPos - DDotPos - 2);
    ElemName := StrCopyTail(AName, OfPos + 4);
    BaseType := FindTypeOrInstantiate(ElemName);
    if BaseType <> nil then
    begin
      CanonName := 'array[' + LStr + '..' + HStr + '] of ' + BaseType.Name;
      Result    := FTable.FindType(CanonName);
      if Result = nil then
      begin
        SAT := FTable.NewStaticArrayType(BaseType, StrToInt(LStr), StrToInt(HStr));
        Sym := TSymbol.Create(CanonName, skType, SAT);
        FTable.DefineGlobal(Sym);
        Result := SAT;
      end;
    end;
    Exit;
  end;
  { Typed pointer: '^TypeName' — create on demand.  When TypeName resolves
    to a concrete type (e.g. T → String inside a generic method body), key
    the cache by the canonical '^String' rather than the unsubstituted
    '^T' — otherwise a second instantiation that binds T to a different
    concrete type re-uses the stale '^T' → '^String' entry. }
  if (Length(AName) > 1) and (StrAt(AName, 0) = Ord('^')) then
  begin
    BaseName := StrCopyTail(AName, 1);
    BaseType := FindTypeOrInstantiate(BaseName);
    if BaseType <> nil then
    begin
      CanonName := '^' + BaseType.Name;
      Result    := FTable.FindType(CanonName);
      if Result = nil then
      begin
        PT  := FTable.NewPointerType(CanonName, BaseType);
        Sym := TSymbol.Create(CanonName, skType, PT);
        FTable.DefineGlobal(Sym);
        Result := PT;
      end;
    end;
    Exit;
  end;
  { Metaclass: 'class of TypeName' — create on demand. }
  if (Length(AName) > 9) and (StrHead(AName, 9) = 'class of ') then
  begin
    BaseName := StrCopyTail(AName, 9);
    BaseType := FindTypeOrInstantiate(BaseName);
    if (BaseType <> nil) and (BaseType.Kind = tyClass) then
    begin
      CanonName := 'class of ' + BaseType.Name;
      Result    := FTable.FindType(CanonName);
      if Result = nil then
      begin
        Sym := TSymbol.Create(CanonName, skType,
          FTable.NewMetaClassType(CanonName, BaseType));
        FTable.DefineGlobal(Sym);
        Result := Sym.TypeDesc;
      end;
    end;
    Exit;
  end;
  if StrPos('<', AName) >= 0 then
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
  if (Length(Result) > 0) and (StrAt(Result, 0) = Ord('^')) then
  begin
    Result := '^' + Self.SubstTypeParam(StrCopyTail(Result, 1), AParamNames, AArgs);
    Exit;
  end;
  { Generic instantiation: SomeName<T,...> — substitute each type argument }
  BrOpen := StrPos('<', Result);
  if BrOpen >= 0 then
  begin
    BrClose  := Length(Result);  { closing '>' is always the last char }
    BasePart := StrHead(Result, BrOpen);
    ArgsPart := StrCopyFrom(Result, BrOpen + 1, BrClose - BrOpen - 2);
    ArgList  := TStringList.Create;
    try
      while ArgsPart <> '' do
      begin
        I := StrPos(',', ArgsPart);
        if I >= 0 then
        begin
          ArgList.Add(Trim(StrHead(ArgsPart, I)));
          ArgsPart := Trim(StrCopyTail(ArgsPart, I + 1));
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
  IntfDesc:  TInterfaceTypeDesc;
  ParentSym: TSymbol;
  ParentRT:  TRecordTypeDesc;
begin
  Result := nil;

  { Parse 'BaseName<Arg1,Arg2>' }
  BracPos := StrPos('<', ATypeName);
  if BracPos < 0 then Exit;
  BaseName := StrHead(ATypeName, BracPos);
  ArgsStr  := StrCopyFrom(ATypeName, BracPos + 1, Length(ATypeName) - BracPos - 2);

  Args := TStringList.Create;
  try
    while ArgsStr <> '' do
    begin
      BracPos := StrPos(',', ArgsStr);
      if BracPos >= 0 then
      begin
        Args.Add(Trim(StrHead(ArgsStr, BracPos)));
        ArgsStr := Trim(StrCopyTail(ArgsStr, BracPos + 1));
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
    ClonedCD            := TClassTypeDef.Create;
    ClonedCD.ParentName := SubstTypeParam(Templ.ClassDef.ParentName, Templ.ParamNames, Args);
    { If the substituted parent name looks like a generic interface (contains '<'),
      try to resolve it. If it resolves to an interface, move it to ImplementsNames
      so the implements-wiring pass can call AddImplements on RT. }
    if StrPos('<', ClonedCD.ParentName) >= 0 then
    begin
      FldType := FindTypeOrInstantiate(ClonedCD.ParentName);
      if (FldType <> nil) and (FldType.Kind = tyInterface) then
      begin
        ClonedCD.ImplementsNames.Insert(0, ClonedCD.ParentName);
        ClonedCD.ParentName := '';
      end;
    end;
    for I := 0 to Templ.ClassDef.ImplementsNames.Count - 1 do
      ClonedCD.ImplementsNames.Add(
        SubstTypeParam(Templ.ClassDef.ImplementsNames.Strings[I], Templ.ParamNames, Args));

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

    { Clone method declarations.  Body is deep-cloned so each generic
      instance has its own AST nodes for semantic re-analysis; without this
      the Resolved* annotations on the shared body would carry whichever
      instance was analysed last, causing call targets in instance N's
      method body to resolve against instance M's class. }
    for I := 0 to Templ.ClassDef.Methods.Count - 1 do
    begin
      MDecl            := TMethodDecl(Templ.ClassDef.Methods.Items[I]);
      NewMDecl         := TMethodDecl.Create;
      NewMDecl.Name          := MDecl.Name;
      NewMDecl.OwnerTypeName := ATypeName;
      NewMDecl.IsVirtual     := MDecl.IsVirtual;
      NewMDecl.IsOverride    := MDecl.IsOverride;
      if MDecl.Body <> nil then
      begin
        NewMDecl.Body    := CloneBlock(MDecl.Body);
        NewMDecl.OwnBody := True;
      end
      else
      begin
        NewMDecl.Body    := nil;
        NewMDecl.OwnBody := False;
      end;

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

    { Wire up parent class so the generic instance is a first-class class:
      - inherits parent fields (FindField walks them after AddField copies)
      - inherits parent vtable slots (Destroy/ToString from TObject, etc.)
      - has a valid RT.Parent chain (FindProperty/FindMethodDecl walk it)
      Mirrors the regular class resolution path in AnalyseProgramTypes.
      If no explicit parent name, implicitly inherit from TObject. }
    if ClonedCD.ParentName <> '' then
    begin
      ParentSym := FTable.Lookup(ClonedCD.ParentName);
      if (ParentSym <> nil) and (ParentSym.TypeDesc is TRecordTypeDesc) then
      begin
        ParentRT  := TRecordTypeDesc(ParentSym.TypeDesc);
        RT.Parent := ParentRT;
        RT.CopyVTableFrom(ParentRT);
        for K := 0 to ParentRT.Fields.Count - 1 do
          RT.AddField(
            TFieldInfo(ParentRT.Fields.Items[K]).Name,
            TFieldInfo(ParentRT.Fields.Items[K]).TypeDesc);
      end;
    end
    else if not SameText(ATypeName, 'TObject') then
    begin
      ParentSym := FTable.Lookup('TObject');
      if (ParentSym <> nil) and (ParentSym.TypeDesc is TRecordTypeDesc) then
      begin
        ParentRT  := TRecordTypeDesc(ParentSym.TypeDesc);
        RT.Parent := ParentRT;
        RT.CopyVTableFrom(ParentRT);
      end;
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

    { Wire up implements: for each interface name in the cloned definition,
      find or instantiate the interface and call AddImplements on RT so that
      type-compatibility checks (class → interface assignment) work. }
    for J := 0 to ClonedCD.ImplementsNames.Count - 1 do
    begin
      Key      := ClonedCD.ImplementsNames.Strings[J];
      IntfDesc := TInterfaceTypeDesc(FindTypeOrInstantiate(Key));
      if IntfDesc <> nil then
        RT.AddImplements(IntfDesc);
    end;

    GI          := TGenericInstance.Create;
    GI.TypeName := ATypeName;
    GI.ClassDef := ClonedCD;
    GI.TypeDesc := RT;
    if FCurrentUnit <> nil then
      FCurrentUnit.GenericInstances.Add(GI)
    else
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
  I, K:        Integer;
  MDecl:       TMethodDecl;
  Par:         TMethodParam;
  Sym:         TSymbol;
  GII:         TGenericInterfaceInstance;
  MangledName: string;
  VarFlags:    string;
begin
  Result := nil;

  BracPos := StrPos('<', ATypeName);
  if BracPos < 0 then Exit;
  BaseName := StrHead(ATypeName, BracPos);
  ArgsStr  := StrCopyFrom(ATypeName, BracPos + 1, Length(ATypeName) - BracPos - 2);

  Args := TStringList.Create;
  try
    while ArgsStr <> '' do
    begin
      BracPos := StrPos(',', ArgsStr);
      if BracPos >= 0 then
      begin
        Args.Add(Trim(StrHead(ArgsStr, BracPos)));
        ArgsStr := Trim(StrCopyTail(ArgsStr, BracPos + 1));
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

    { Register interface method names with substituted return types + var-param flags }
    for I := 0 to Templ.IntfDef.Methods.Count - 1 do
    begin
      MDecl    := TMethodDecl(Templ.IntfDef.Methods.Items[I]);
      VarFlags := '';
      for K := 0 to MDecl.Params.Count - 1 do
      begin
        Par := TMethodParam(MDecl.Params.Items[K]);
        if K > 0 then VarFlags := VarFlags + ',';
        if Par.IsVarParam then VarFlags := VarFlags + '1'
                          else VarFlags := VarFlags + '0';
      end;
      Result.AddMethod(MDecl.Name,
        SubstTypeParam(MDecl.ReturnTypeName, Templ.ParamNames, Args),
        VarFlags);
    end;

    { Register the instantiation for codegen }
    GII          := TGenericInterfaceInstance.Create;
    GII.InstName := MangledName;
    {$IFDEF FPC}GII.IntfDef.Free;{$ENDIF}
    GII.IntfDef  := nil;
    GII.TypeDesc := Result;
    if FCurrentUnit <> nil then
      FCurrentUnit.GenericIntfInstances.Add(GII)
    else
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
  BracPos := StrPos('<', AInstName);
  if BracPos < 0 then Exit;

  BaseName := StrHead(AInstName, BracPos);
  ArgsStr  := StrCopyFrom(AInstName, BracPos + 1, Length(AInstName) - BracPos - 2);

  TemplIdx := FGenericFuncTemplates.IndexOf(BaseName);
  if TemplIdx < 0 then Exit;  { not a known generic function template }

  Templ := TMethodDecl(FGenericFuncTemplates.Objects[TemplIdx]);

  Args := TStringList.Create;
  try
    while Length(ArgsStr) > 0 do
    begin
      BracPos := StrPos(',', ArgsStr);
      if BracPos >= 0 then
      begin
        Args.Add(Trim(StrHead(ArgsStr, BracPos)));
        ArgsStr := Trim(StrCopyTail(ArgsStr, BracPos + 1));
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
    { Deep-clone the template body so each instance has its own analysed
      AST.  Sharing would leave Resolved* annotations from the last
      instance on the body, miscompiling earlier instances. }
    if Templ.Body <> nil then
    begin
      NewMDecl.Body    := CloneBlock(Templ.Body);
      NewMDecl.OwnBody := True;
    end
    else
    begin
      NewMDecl.Body    := nil;
      NewMDecl.OwnBody := False;
    end;

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
    if FCurrentUnit <> nil then
      FCurrentUnit.GenericFuncInstances.Add(GFI)
    else
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
  AnalyseArrayConstDecls(ABlock);
  { Link standalone TTypeName.MethodName implementations to their class method
    declarations, transferring the body so AnalyseMethodBodies can process it. }
  LinkClassMethodImpls(ABlock);
  LinkGenericClassMethodImpls(ABlock);
  { Register standalone proc/func signatures before class method bodies so that
    methods can call free functions declared in the same block. }
  AnalyseStandaloneDecls(ABlock);
  FTable.PushScope;
  Inc(FScopeDepth);
  try
    { Register var declarations before method bodies so that class methods can
      resolve identifiers that refer to program-level globals (issue #43).
      The same applies inside nested function/procedure blocks: locals must be
      in scope before any method body declared in this block is analysed. }
    AnalyseVarDecls(ABlock);
    AnalyseMethodBodies(ABlock);
    AnalyseStandaloneBodies(ABlock);
    AnalyseStmts(ABlock);
    { After all bodies are analysed, mark inline candidates so codegen can
      decide whether to emit a call or inline the body at each call site. }
    MarkInlineCandidates(ABlock);
  finally
    Dec(FScopeDepth);
    FTable.PopScope;
  end;
end;

procedure TSemanticAnalyser.AnalyseConstDecls(ABlock: TBlock);
var
  I, J:   Integer;
  CD:     TConstDecl;
  Sym:    TSymbol;
  RefSym: TSymbol;
  TD:     TTypeDesc;
  Resolved: string;
  IsSameBlockDup: Boolean;
begin
  for I := 0 to ABlock.ConstDecls.Count - 1 do
  begin
    CD := TConstDecl(ABlock.ConstDecls.Items[I]);
    if CD.IsArrayConst then Continue;  { handled by AnalyseArrayConstDecls }

    if CD.IsString and (CD.ConstParts <> nil) then
    begin
      Resolved := '';
      for J := 0 to CD.ConstParts.Count - 1 do
      begin
        if CD.ConstParts.Objects[J] <> nil then
        begin
          RefSym := FTable.Lookup(CD.ConstParts[J]);
          if (RefSym <> nil) and (RefSym.Kind = skConstant) then
            Resolved := Resolved + RefSym.ConstString
          else
            SemanticError(Format('Undeclared constant ''%s''', [CD.ConstParts[J]]),
                          CD.Line, CD.Col);
        end
        else
          Resolved := Resolved + CD.ConstParts[J];
      end;
      CD.StrVal := Resolved;
    end;
    if CD.TypeName <> '' then
    begin
      { Typed constant: use the declared type.  The value kind (IsFloat,
        IsString, IntVal) is still set by the parser from the RHS literal,
        which is all the codegen needs.  We only override the symbol's type
        descriptor so that type-checking against the declared type is exact. }
      TD := FTable.FindType(CD.TypeName);
      if TD = nil then
        SemanticError(Format('Unknown type ''%s'' in typed constant ''%s''',
          [CD.TypeName, CD.Name]), CD.Line, CD.Col);
    end
    else if CD.IsString then
      TD := FTable.TypeString
    else if CD.IsFloat then
      TD := FTable.TypeDouble
    else
      TD := FTable.TypeInteger;
    Sym              := TSymbol.Create(CD.Name, skConstant, TD);
    Sym.ConstValue   := CD.IntVal;
    Sym.ConstString  := CD.StrVal;
    if not FTable.Define(Sym) then
    begin
      Sym.Free;
      { Only error for same-block duplicates.  Cross-unit const shadowing
        (e.g. a unit redefining a system.pas constant) is silently accepted,
        matching FPC behaviour and preserving the existing test coverage. }
      IsSameBlockDup := False;
      for J := 0 to I - 1 do
        if SameText(TConstDecl(ABlock.ConstDecls.Items[J]).Name, CD.Name) then
        begin
          IsSameBlockDup := True;
          Break;
        end;
      if IsSameBlockDup then
        SemanticError(Format('Duplicate identifier ''%s''', [CD.Name]), CD.Line, CD.Col);
    end;
  end;
end;

procedure TSemanticAnalyser.AnalyseArrayConstDecls(ABlock: TBlock);
{ Second-pass constant analysis for array-typed constants.
  Called after AnalyseTypeDecls so that enum index types are in scope. }
var
  I, J:     Integer;
  CD:       TConstDecl;
  Sym:      TSymbol;
  ElemTD:   TTypeDesc;
  IdxTD:    TTypeDesc;
  ArrTD:    TStaticArrayTypeDesc;
  EnumDesc: TEnumTypeDesc;
  Expected: Integer;
begin
  for I := 0 to ABlock.ConstDecls.Count - 1 do
  begin
    CD := TConstDecl(ABlock.ConstDecls.Items[I]);
    if not CD.IsArrayConst then Continue;
    ElemTD := FTable.FindType(CD.ArrayElemType);
    if ElemTD = nil then
      SemanticError(Format('Unknown element type ''%s'' in array const ''%s''',
        [CD.ArrayElemType, CD.Name]), CD.Line, CD.Col);
    if CD.ArrayIsRangeIndexed then
    begin
      Expected := CD.ArrayHighBound - CD.ArrayLowBound + 1;
      if CD.ArrayElements.Count <> Expected then
        SemanticError(Format(
          'Array const ''%s'' has %d element(s) but range [%d..%d] needs %d',
          [CD.Name, CD.ArrayElements.Count, CD.ArrayLowBound,
           CD.ArrayHighBound, Expected]),
          CD.Line, CD.Col);
      ArrTD := FTable.NewStaticArrayType(ElemTD, CD.ArrayLowBound, CD.ArrayHighBound);
    end
    else
    begin
      IdxTD := FTable.FindType(CD.ArrayIndexType);
      if IdxTD = nil then
        SemanticError(Format('Unknown index type ''%s'' in array const ''%s''',
          [CD.ArrayIndexType, CD.Name]), CD.Line, CD.Col);
      if IdxTD.Kind <> tyEnum then
        SemanticError(Format('Array const index type must be an enum, got ''%s''',
          [IdxTD.Name]), CD.Line, CD.Col);
      EnumDesc := TEnumTypeDesc(IdxTD);
      Expected := EnumDesc.Members.Count;
      if CD.ArrayElements.Count <> Expected then
        SemanticError(Format(
          'Array const ''%s'' has %d element(s) but index type ''%s'' has %d member(s)',
          [CD.Name, CD.ArrayElements.Count, CD.ArrayIndexType, Expected]),
          CD.Line, CD.Col);
      ArrTD := FTable.NewStaticArrayType(ElemTD, 0, Expected - 1);
    end;
    Sym := TSymbol.Create(CD.Name, skConstant, ArrTD);
    Sym.IsGlobal := True;
    Sym.ConstArray := TStringList.Create;
    for J := 0 to CD.ArrayElements.Count - 1 do
      Sym.ConstArray.Add(CD.ArrayElements[J]);
    if not FTable.Define(Sym) then
      Sym.Free;
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
  AttrIdx:    Integer;
  RawAttr:    string;
  Resolved:   string;
  BaseSym:    TSymbol;
  MName:      string;
  MSym:       TSymbol;
  Slot:       Integer;
  CD:         TConstDecl;
  AliasDef:   TTypeAliasDef;
  AliasName:  string;
  AliasDesc:  TTypeDesc;
  BaseName:   string;
  BaseType:   TTypeDesc;
  MangledKey: string;
  VarFlags:   string;
  ElemTD:     TTypeDesc;
  IdxTD:      TTypeDesc;
  ArrTD:      TStaticArrayTypeDesc;
  Expected:   Integer;
begin
  { Pass 1 — register all type symbols with empty descriptors.
    This allows self-referential field types to resolve in pass 2. }
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
    if TD.Def is TRecordTypeDef then
    begin
      RT := FTable.NewRecordType(TD.Name);
      RT.IsPacked := TRecordTypeDef(TD.Def).IsPacked;
    end
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
        MSym.ConstValue := EnumDef.OrdinalAt(K);
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
    else if TD.Def is TProceduralTypeDef then
    begin
      { Procedural type: register an empty TProceduralTypeDesc; param/return
        resolution happens in pass 2. }
      Sym := TSymbol.Create(TD.Name, skType,
                            FTable.NewProceduralType(TD.Name));
      if not FTable.Define(Sym) then
      begin
        Sym.Free;
        SemanticError(Format('Duplicate type name ''%s''', [TD.Name]), TD.Line, TD.Col);
      end;
      Continue;
    end
    else if TD.Def is TTypeAliasDef then
    begin
      { Type alias or pointer alias: resolve the named type and register
        a new symbol pointing at either the base type (simple alias) or
        a fresh TPointerTypeDesc (pointer alias '^T'). }
      AliasDef  := TTypeAliasDef(TD.Def);
      AliasName := AliasDef.TypeName;
      if (Length(AliasName) > 0) and (StrAt(AliasName, 0) = Ord('^')) then
      begin
        { Pointer alias: ^BaseName — base may not be registered yet
          (forward reference); leave BaseType nil for now (untyped
          pointer semantics — safe for punit's usage pattern). }
        BaseName := StrCopyTail(AliasName, 1);
        BaseSym  := FTable.Lookup(BaseName);
        BaseType := nil;
        if (BaseSym <> nil) and (BaseSym.Kind = skType) then
          BaseType := BaseSym.TypeDesc;
        AliasDesc := FTable.NewPointerType(TD.Name, BaseType);
      end
      else if (Length(AliasName) > 9) and (StrHead(AliasName, 9) = 'class of ') then
      begin
        { Metaclass alias: 'class of TFoo'.  Route through the standard
          on-demand instantiation path so the underlying class type is
          resolved consistently with other 'class of TFoo' references. }
        AliasDesc := FindTypeOrInstantiate(AliasName);
        if AliasDesc = nil then
        begin
          SemanticError(
            Format('Unknown class type in metaclass alias ''%s''', [AliasName]),
            TD.Line, TD.Col);
          Continue;
        end;
      end
      else
      begin
        { Simple alias or constructed alias (array[L..H] of T, etc.).
          Try direct lookup first; fall through to FindTypeOrInstantiate
          for names the symbol table doesn't hold yet (e.g. array types
          that are created on demand). }
        BaseSym := FTable.Lookup(AliasName);
        if (BaseSym <> nil) and (BaseSym.Kind = skType) then
          AliasDesc := BaseSym.TypeDesc
        else
        begin
          AliasDesc := FindTypeOrInstantiate(AliasName);
          if AliasDesc = nil then
          begin
            SemanticError(Format('Unknown type ''%s'' in type alias', [AliasName]),
              TD.Line, TD.Col);
            Continue;
          end;
        end;
      end;
      Sym := TSymbol.Create(TD.Name, skType, AliasDesc);
      if not FTable.Define(Sym) then
      begin
        Sym.Free;
        SemanticError(Format('Duplicate type name ''%s''', [TD.Name]), TD.Line, TD.Col);
      end;
      Continue;
    end
    else
    begin
      SemanticError('Only record, class, interface, enum, set, procedural, or type alias definitions are supported',
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

    { Generic templates, enum, set, and type alias need no pass-2 processing }
    if TD.Def is TGenericTypeDef then Continue;
    if TD.Def is TGenericInterfaceDef then Continue;
    if TD.Def is TEnumTypeDef then Continue;
    if TD.Def is TSetTypeDef then Continue;
    if TD.Def is TTypeAliasDef then Continue;

    { Procedural types: resolve param + return types now that all
      type names are registered. }
    if TD.Def is TProceduralTypeDef then
    begin
      ResolveProceduralTypeDef(TD);
      Continue;
    end;

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
        { Inherit parent methods (propagate var-param flags too) }
        for J := 0 to IntfDesc.Parent.MethodCount - 1 do
          IntfDesc.AddMethod(IntfDesc.Parent.MethodName(J),
            IntfDesc.Parent.MethodReturnTypeName(J),
            IntfDesc.Parent.MethodParamVarFlagsStr(J));
      end;
      for J := 0 to ITD.Methods.Count - 1 do
      begin
        MDecl    := TMethodDecl(ITD.Methods.Items[J]);
        VarFlags := '';
        for K := 0 to MDecl.Params.Count - 1 do
        begin
          Par := TMethodParam(MDecl.Params.Items[K]);
          if K > 0 then VarFlags := VarFlags + ',';
          if Par.IsVarParam then VarFlags := VarFlags + '1'
                            else VarFlags := VarFlags + '0';
        end;
        IntfDesc.AddMethod(MDecl.Name, MDecl.ReturnTypeName, VarFlags);
      end;
      Continue;
    end;

    Sym := FTable.Lookup(TD.Name);
    RT  := TRecordTypeDesc(Sym.TypeDesc);

    if TD.Def is TRecordTypeDef then
    begin
      FieldList  := TRecordTypeDef(TD.Def).Fields;
      MethodList := TRecordTypeDef(TD.Def).Methods;
      { Resolve param and return types for record methods. }
      if MethodList <> nil then
        for J := 0 to MethodList.Count - 1 do
        begin
          MDecl := TMethodDecl(MethodList.Items[J]);
          MDecl.IsRecordMethod := True;
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
    end
    else
    begin
      FieldList  := TClassTypeDef(TD.Def).Fields;
      MethodList := TClassTypeDef(TD.Def).Methods;

      { Resolve class-level custom attributes.  Each raw name is matched
        using the Delphi suffix convention: [Threaded] resolves to
        ThreadedAttribute if that class descends from TCustomAttribute.
        [Weak] is a compiler intrinsic and is skipped here. }
      for AttrIdx := 0 to TClassTypeDef(TD.Def).Attributes.Count - 1 do
      begin
        RawAttr := TClassTypeDef(TD.Def).Attributes.Strings[AttrIdx];
        if AttrMatches(RawAttr, 'Weak') then Continue;
        Resolved := ResolveCustomAttrName(RawAttr);
        if Resolved = '' then
          SemanticError(
            Format('Unknown attribute ''%s'': no class ''%s'' or ''%sAttribute'' ' +
                   'descending from TCustomAttribute found',
                   [RawAttr, RawAttr, RawAttr]),
            TD.Line, TD.Col)
        else
          RT.AddClassAttribute(Resolved);
      end;

      { Copy inherited fields and vtable from parent class first.
        The parser may store a generic interface name (e.g. IFoo<T>) as ParentName
        when no explicit class parent was specified — detect this and treat it as
        an implements entry instead. }
      if TClassTypeDef(TD.Def).ParentName <> '' then
      begin
        ParentSym := nil;
        { If name looks generic, try instantiating as interface first }
        if StrPos('<', TClassTypeDef(TD.Def).ParentName) >= 0 then
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
          { If the first name in class(...) is an interface, not a class,
            treat it as an implements entry — TObject becomes the implicit parent. }
          if (ParentSym <> nil) and (ParentSym.TypeDesc is TInterfaceTypeDesc) then
          begin
            TClassTypeDef(TD.Def).ImplementsNames.Insert(
              0, TClassTypeDef(TD.Def).ParentName);
            TClassTypeDef(TD.Def).ParentName := '';
          end
          else
          begin
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
      end;

      { If no explicit parent was specified (and this class is not TObject itself),
        implicitly inherit from TObject: copy its vtable so the vptr slot is
        present and field offsets start after the 8-byte pointer, and set
        RT.Parent so that typeinfo carries the correct parent chain for
        is/as/InheritsFrom checks. }
      if (TClassTypeDef(TD.Def).ParentName = '') and (TD.Name <> 'TObject') then
      begin
        ParentSym := FTable.Lookup('TObject');
        if (ParentSym <> nil) and (ParentSym.TypeDesc is TRecordTypeDesc) then
        begin
          ParentRT := TRecordTypeDesc(ParentSym.TypeDesc);
          RT.CopyVTableFrom(ParentRT);
          RT.Parent := ParentRT;
        end;
      end;

      { Pre-resolve param and return types for class methods so that MangleParamSig
        can compute overloaded keys correctly in the vtable pre-pass below. }
      if MethodList <> nil then
        for J := 0 to MethodList.Count - 1 do
        begin
          MDecl := TMethodDecl(MethodList.Items[J]);
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

      { Pre-pass: register vtable slots for virtual/override methods BEFORE
        adding own fields, so that field offsets correctly account for the vptr.
        Each (name, parameter-signature) pair gets its own slot — overloaded
        virtual methods are independently dispatched. }
      if MethodList <> nil then
        for J := 0 to MethodList.Count - 1 do
        begin
          MDecl := TMethodDecl(MethodList.Items[J]);
          MangledKey := MDecl.Name;
          if MDecl.IsOverload then
            MangledKey := MangledKey + '$' + MangleParamSig(MDecl);
          if MDecl.IsVirtual then
          begin
            Slot := RT.AddVTableSlot(MangledKey, '$' + TD.Name + '_' + MangledKey);
            if MDecl.IsAbstract then
            begin
              RT.VTableEntryAt(Slot).IsAbstract := True;
              RT.HasAbstractMethods := True;
            end;
          end
          else if MDecl.IsOverride then
          begin
            Slot := RT.FindVTableSlot(MangledKey);
            if Slot < 0 then
            begin
              ParentSym := FTable.Lookup('TObject');
              if (ParentSym <> nil) and (ParentSym.TypeDesc is TRecordTypeDesc) then
              begin
                ParentRT := TRecordTypeDesc(ParentSym.TypeDesc);
                if ParentRT.FindVTableSlot(MangledKey) >= 0 then
                begin
                  RT.CopyVTableFrom(ParentRT);
                  if RT.Parent = nil then
                    RT.Parent := ParentRT;
                  Slot := RT.FindVTableSlot(MangledKey);
                end;
              end;
            end;
            RT.OverrideVTableSlot(Slot, '$' + TD.Name + '_' + MangledKey);
            { Override clears the abstract flag on the inherited slot }
            if Slot >= 0 then
              RT.VTableEntryAt(Slot).IsAbstract := False;
          end;
        end;
    end;

    { After building this class's vtable, check if any abstract slots remain
      (inherited but not overridden). If so, mark the class as abstract. }
    if RT <> nil then
    begin
      for J := 0 to RT.VTableCount - 1 do
        if RT.VTableEntryAt(J).IsAbstract then
        begin
          RT.HasAbstractMethods := True;
          Break;
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

        { Compute mangled key and ResolvedQbeName for overloaded methods.
          Non-overloaded methods keep their plain name throughout. }
        MangledKey := MDecl.Name;
        if MDecl.IsOverload then
          MangledKey := MangledKey + '$' + MangleParamSig(MDecl);
        MDecl.ResolvedQbeName := TD.Name + '_' + MangledKey;

        { Reject duplicate-without-overload at registration time.  Walk
          existing FMethodIndex entries for this (TypeName.Name) — if
          any sibling has IsOverload=False or the new MDecl lacks
          IsOverload, this is a duplicate-identifier error. }
        Key := TD.Name + '.' + MDecl.Name;
        for K := 0 to FMethodIndex.Count - 1 do
          if SameText(FMethodIndex.Strings[K], Key) then
          begin
            if (not MDecl.IsOverload) or
               (not TMethodDecl(FMethodIndex.Objects[K]).IsOverload) then
              SemanticError(
                Format('Duplicate method ''%s.%s'' (missing ''overload'' directive?)',
                  [TD.Name, MDecl.Name]),
                MDecl.Line, MDecl.Col);
          end;
        FMethodIndex.AddObject(Key, MDecl);
        if SameText(MDecl.Name, 'Destroy') then
          RT.HasDestroyMethod := True;

        { Retrieve the vtable slot assigned in the pre-pass above. }
        if MDecl.IsVirtual or MDecl.IsOverride then
        begin
          MDecl.VTableSlot := RT.FindVTableSlot(MangledKey);
          if MDecl.IsOverride and (MDecl.VTableSlot < 0) then
            SemanticError(
              Format('Method ''%s'' marked override but no matching virtual base method found',
                [MDecl.Name]),
              MDecl.Line, MDecl.Col);
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
        if CD.IsArrayConst then
        begin
          ElemTD := FTable.FindType(CD.ArrayElemType);
          if ElemTD = nil then
            SemanticError(Format('Unknown element type ''%s'' in class array const ''%s''',
              [CD.ArrayElemType, CD.Name]), CD.Line, CD.Col);
          if CD.ArrayIsRangeIndexed then
          begin
            Expected := CD.ArrayHighBound - CD.ArrayLowBound + 1;
            if CD.ArrayElements.Count <> Expected then
              SemanticError(Format(
                'Class array const ''%s'' has %d element(s) but range [%d..%d] needs %d',
                [CD.Name, CD.ArrayElements.Count, CD.ArrayLowBound,
                 CD.ArrayHighBound, Expected]),
                CD.Line, CD.Col);
            ArrTD := FTable.NewStaticArrayType(ElemTD, CD.ArrayLowBound, CD.ArrayHighBound);
          end
          else
          begin
            IdxTD := FTable.FindType(CD.ArrayIndexType);
            if IdxTD = nil then
              SemanticError(Format('Unknown index type ''%s'' in class array const ''%s''',
                [CD.ArrayIndexType, CD.Name]), CD.Line, CD.Col);
            if IdxTD.Kind <> tyEnum then
              SemanticError(Format('Class array const index must be an enum, got ''%s''',
                [IdxTD.Name]), CD.Line, CD.Col);
            EnumDesc := TEnumTypeDesc(IdxTD);
            Expected := EnumDesc.Members.Count;
            if CD.ArrayElements.Count <> Expected then
              SemanticError(Format(
                'Class array const ''%s'' has %d element(s) but index type ''%s'' has %d member(s)',
                [CD.Name, CD.ArrayElements.Count, CD.ArrayIndexType, Expected]),
                CD.Line, CD.Col);
            ArrTD := FTable.NewStaticArrayType(ElemTD, 0, Expected - 1);
          end;
          Sym := TSymbol.Create(CD.Name, skConstant, ArrTD);
          Sym.IsGlobal := True;
          Sym.ConstArray := TStringList.Create;
          for K := 0 to CD.ArrayElements.Count - 1 do
            Sym.ConstArray.Add(CD.ArrayElements[K]);
          if not FTable.Define(Sym) then
            Sym.Free;
          Sym := TSymbol.Create(TD.Name + '.' + CD.Name, skConstant, ArrTD);
          Sym.IsGlobal := True;
          Sym.ConstArray := TStringList.Create;
          for K := 0 to CD.ArrayElements.Count - 1 do
            Sym.ConstArray.Add(CD.ArrayElements[K]);
          if not FTable.Define(Sym) then
            Sym.Free;
        end
        else
        begin
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

  { Pass 3 — resolve forward-referenced pointer aliases.
    A pointer type 'PFoo = ^TFoo' may have been processed before TFoo was
    registered; its TPointerTypeDesc.BaseType is nil.  Now that all types
    are in the symbol table, fill in the missing base types. }
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
    if not (TD.Def is TTypeAliasDef) then Continue;
    AliasDef  := TTypeAliasDef(TD.Def);
    AliasName := AliasDef.TypeName;
    if (Length(AliasName) = 0) or (StrAt(AliasName, 0) <> Ord('^')) then Continue;
    BaseName := StrCopyTail(AliasName, 1);
    BaseSym  := FTable.Lookup(TD.Name);
    if (BaseSym = nil) or not (BaseSym.TypeDesc is TPointerTypeDesc) then Continue;
    if TPointerTypeDesc(BaseSym.TypeDesc).BaseType <> nil then Continue;
    { Base was unresolved in Pass 1 — try again now }
    Sym := FTable.Lookup(BaseName);
    if (Sym <> nil) and (Sym.Kind = skType) then
      TPointerTypeDesc(BaseSym.TypeDesc).BaseType := Sym.TypeDesc;
  end;
end;

procedure TSemanticAnalyser.AnalyseMethodBodies(ABlock: TBlock);
var
  I, J:    Integer;
  TD:      TTypeDecl;
  CD:      TClassTypeDef;
  RD:      TRecordTypeDef;
  RT:      TRecordTypeDesc;
  Sym:     TSymbol;
  Methods: TObjectList;
begin
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
    if TD.Def is TClassTypeDef then
    begin
      CD  := TClassTypeDef(TD.Def);
      Sym := FTable.Lookup(TD.Name);
      if (Sym = nil) or not (Sym.TypeDesc is TRecordTypeDesc) then
        Continue;
      RT      := TRecordTypeDesc(Sym.TypeDesc);
      Methods := CD.Methods;
    end
    else if TD.Def is TRecordTypeDef then
    begin
      RD  := TRecordTypeDef(TD.Def);
      Sym := FTable.Lookup(TD.Name);
      if (Sym = nil) or not (Sym.TypeDesc is TRecordTypeDesc) then
        Continue;
      RT      := TRecordTypeDesc(Sym.TypeDesc);
      Methods := RD.Methods;
    end
    else
      Continue;
    for J := 0 to Methods.Count - 1 do
      AnalyseMethodDecl(TMethodDecl(Methods.Items[J]), RT);
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
    { Record methods receive the record by pointer (like a var param); class
      methods receive the object pointer as a value.  Declaring Self as
      skVarParameter for records makes the codegen dereference it correctly. }
    if AMethod.IsRecordMethod then
      Sym := TSymbol.Create('Self', skVarParameter, AClassType)
    else
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

    { Abstract methods must not have a body }
    if AMethod.IsAbstract and (AMethod.Body <> nil) then
      SemanticError(
        Format('Abstract method ''%s'' must not have an implementation',
          [AMethod.Name]),
        AMethod.Line, AMethod.Col);

    { Analyse the method body block (pushes its own inner scope) }
    if (AMethod.Body <> nil) and not AMethod.IsAbstract then
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

function TSemanticAnalyser.ResolveMethodOverload(
  const ATypeName, AMethodName: string;
  AArgs: TObjectList; ALine, ACol: Integer): TMethodDecl;
var
  CurrName:    string;
  Sym:         TSymbol;
  RT:          TRecordTypeDesc;
  Key:         string;
  Cand:        TMethodDecl;
  ArityMatch:  TObjectList;
  J, K, Score: Integer;
  ArgScore:    Integer;
  Par:         TMethodParam;
  Arg:         TASTExpr;
  BestScore:   Integer;
  BestCount:   Integer;
  Best:        TMethodDecl;
  TotalCnt:    Integer;
  Arity:       Integer;
  ExactNew:    Integer;
  ExactBest:   Integer;
  S1, S2:      Integer;
begin
  Result    := nil;
  if AArgs <> nil then Arity := AArgs.Count else Arity := -1;
  TotalCnt  := 0;
  ArityMatch := TObjectList.Create(False);
  try
    CurrName := ATypeName;
    while CurrName <> '' do
    begin
      Key := CurrName + '.' + AMethodName;
      for K := 0 to FMethodIndex.Count - 1 do
        if SameText(FMethodIndex.Strings[K], Key) then
        begin
          Inc(TotalCnt);
          Cand := TMethodDecl(FMethodIndex.Objects[K]);
          if (Arity < 0) or
             ((Arity >= MinArity(Cand)) and (Arity <= Cand.Params.Count)) then
            ArityMatch.Add(Cand);
        end;
      if ArityMatch.Count > 0 then Break;
      { Walk parent — only if no candidates yet (Delphi: derived overloads
        do not mix with inherited ones unless the descendant explicitly
        repeats the directive, which our model treats as a fresh slot). }
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

    if TotalCnt = 0 then Exit;  { caller treats nil as "no method on class" }

    if ArityMatch.Count = 0 then
      SemanticError(
        Format('No matching overload for ''%s.%s'' with %d argument(s)',
          [ATypeName, AMethodName, Arity]),
        ALine, ACol);

    if (AArgs = nil) or (Arity = 0) then
    begin
      if ArityMatch.Count = 1 then
      begin
        Result := TMethodDecl(ArityMatch.Items[0]);
        Exit;
      end;
      Exit;  { ambiguous-by-arity-only — caller must score with args }
    end;

    BestScore := -1;
    BestCount := 0;
    Best      := nil;
    for K := 0 to ArityMatch.Count - 1 do
    begin
      Cand  := TMethodDecl(ArityMatch.Items[K]);
      Score := 0;
      for J := 0 to Arity - 1 do
      begin
        Par      := TMethodParam(Cand.Params.Items[J]);
        Arg      := TASTExpr(AArgs.Items[J]);
        ArgScore := ArgMatchScore(Par.ResolvedType, Arg.ResolvedType, Arg);
        if ArgScore = 0 then
        begin
          Score := -1;
          Break;
        end;
        Score := Score + ArgScore;
      end;
      if Score < 0 then Continue;
      { Primary tie-break: prefer fewer defaulted slots. }
      Score := (Score * 16) - (Cand.Params.Count - Arity);
      if Score > BestScore then
      begin
        BestScore := Score;
        BestCount := 1;
        Best      := Cand;
      end
      else if Score = BestScore then
      begin
        { Secondary tie-break: count exact matches (score=2) per argument.
          More exact matches = better candidate. }
        ExactNew  := 0;
        ExactBest := 0;
        for J := 0 to Arity - 1 do
        begin
          S1 := ArgMatchScore(TMethodParam(Cand.Params.Items[J]).ResolvedType,
                              TASTExpr(AArgs.Items[J]).ResolvedType,
                              TASTExpr(AArgs.Items[J]));
          S2 := ArgMatchScore(TMethodParam(Best.Params.Items[J]).ResolvedType,
                              TASTExpr(AArgs.Items[J]).ResolvedType,
                              TASTExpr(AArgs.Items[J]));
          if S1 = 2 then Inc(ExactNew);
          if S2 = 2 then Inc(ExactBest);
        end;
        if ExactNew > ExactBest then
        begin
          Best      := Cand;
          BestCount := 1;
        end
        else if ExactNew = ExactBest then
          Inc(BestCount);
        { ExactNew < ExactBest: keep current Best, don't increment BestCount }
      end;
    end;

    if BestScore < 0 then
      SemanticError(
        Format('No matching overload for ''%s.%s'' with %d argument(s)',
          [ATypeName, AMethodName, Arity]),
        ALine, ACol);
    if BestCount > 1 then
      SemanticError(
        Format('Ambiguous overload of ''%s.%s'' — multiple candidates match equally',
          [ATypeName, AMethodName]),
        ALine, ACol);
    Result := Best;
  finally
    ArityMatch.Free;
  end;
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
      this implementation and skip re-registering the symbol.  Overloaded
      decls bypass this — each overload is independent. }
    if not ADecl.IsOverload then
    begin
      J := FProcIndex.IndexOf(ADecl.Name);
      if (J >= 0) and (TMethodDecl(FProcIndex.Objects[J]).Body = nil) and
         (not TMethodDecl(FProcIndex.Objects[J]).IsOverload) then
      begin
        FProcIndex.Objects[J] := ADecl;
        Continue;
      end;
    end;

    { Compute the QBE-emit name.  Phase B: overloads get a type-code
      suffix ('$<codes>'); non-overloaded decls keep their plain name. }
    if ADecl.IsOverload then
      ADecl.ResolvedQbeName := ADecl.Name + '$' + MangleParamSig(ADecl)
    else
      ADecl.ResolvedQbeName := ADecl.Name;

    { Index for call resolution — overloaded names appear multiple times.
      Nested procs (those inside another proc's body) are resolved via the
      scoped symbol table only; adding them to the global FProcIndex would
      make same-named nested procs in different outer procs appear as
      ambiguous overloads of each other. }
    if FCurrentEnclosingDecl = nil then
      FProcIndex.AddObject(ADecl.Name, ADecl);

    { Register in symbol table }
    if ADecl.ReturnTypeName <> '' then
      Sym := TSymbol.Create(ADecl.Name, skFunction, ADecl.ResolvedReturnType)
    else
      Sym := TSymbol.Create(ADecl.Name, skProcedure, nil);
    Sym.IsOverload := ADecl.IsOverload;
    Sym.Decl       := ADecl;

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
  I:           Integer;
  Par:         TMethodParam;
  Sym:         TSymbol;
  SavedEncl:   TMethodDecl;
begin
  ADecl.EnclosingDecl := FCurrentEnclosingDecl;
  SavedEncl := FCurrentEnclosingDecl;
  FCurrentEnclosingDecl := ADecl;
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

    if (not ADecl.IsExternal) and (ADecl.Body <> nil) then
    begin
      AnalyseBlock(ADecl.Body);
      { After analysing the body, determine which outer-scope variables are
        captured by any nested proc declared inside this one. }
      if ADecl.EnclosingDecl <> nil then
        CollectCaptures(ADecl, ADecl.EnclosingDecl.Body);
    end;
  finally
    Dec(FScopeDepth);
    FTable.PopScope;
    FCurrentEnclosingDecl := SavedEncl;
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

procedure TSemanticAnalyser.CollectCaptures(ADecl: TMethodDecl; AOuterBlock: TBlock);
{ Walk ADecl's body statements/expressions to find all TIdentExpr nodes whose
  name matches a variable declared in AOuterBlock (the enclosing proc's locals).
  Each such variable is "captured": ADecl will receive an implicit hidden
  var-by-pointer parameter, and the call site will pass the variable's address. }
var
  OuterVars: TStringList;
  I, J:      Integer;
  VDecl:     TVarDecl;
  VName:     string;
  TodoExprs: TObjectList;
  TodoStmts: TObjectList;
  CurExpr:   TASTExpr;
  CurStmt:   TASTStmt;
begin
  if ADecl.Body = nil then Exit;

  OuterVars := TStringList.Create;
  TodoExprs := TObjectList.Create(False);
  TodoStmts := TObjectList.Create(False);
  try
    { Build set of outer-block local variable names }
    for I := 0 to AOuterBlock.Decls.Count - 1 do
    begin
      VDecl := TVarDecl(AOuterBlock.Decls.Items[I]);
      for J := 0 to VDecl.Names.Count - 1 do
      begin
        VName := VDecl.Names.Strings[J];
        if OuterVars.IndexOf(VName) < 0 then
          OuterVars.Add(VName);
      end;
    end;
    if OuterVars.Count = 0 then Exit;

    { Seed work-list with all statements in the inner body }
    for I := 0 to ADecl.Body.Stmts.Count - 1 do
      TodoStmts.Add(ADecl.Body.Stmts.Items[I]);

    { Iterative BFS over stmts, pushing child exprs/stmts onto the work-lists }
    while (TodoStmts.Count > 0) or (TodoExprs.Count > 0) do
    begin
      { Process one stmt }
      while TodoStmts.Count > 0 do
      begin
        CurStmt := TASTStmt(TodoStmts.Items[TodoStmts.Count - 1]);
        TodoStmts.Delete(TodoStmts.Count - 1);
        if CurStmt = nil then Continue;

        if CurStmt is TAssignment then
        begin
          { LHS name — check if it's an outer var (direct assign) }
          if TAssignment(CurStmt).ImplicitSelfField = nil then
          begin
            VName := TAssignment(CurStmt).Name;
            if (OuterVars.IndexOf(VName) >= 0) and
               ((ADecl.CapturedVars = nil) or
                (ADecl.CapturedVars.IndexOf(VName) < 0)) then
            begin
              if ADecl.CapturedVars = nil then
                ADecl.CapturedVars := TStringList.Create;
              ADecl.CapturedVars.Add(VName);
            end;
          end;
          TodoExprs.Add(TAssignment(CurStmt).Expr);
        end
        else if CurStmt is TProcCall then
        begin
          for J := 0 to TProcCall(CurStmt).Args.Count - 1 do
            TodoExprs.Add(TProcCall(CurStmt).Args.Items[J]);
        end
        else if CurStmt is TMethodCallStmt then
        begin
          for J := 0 to TMethodCallStmt(CurStmt).Args.Count - 1 do
            TodoExprs.Add(TMethodCallStmt(CurStmt).Args.Items[J]);
        end
        else if CurStmt is TIfStmt then
        begin
          TodoExprs.Add(TIfStmt(CurStmt).Condition);
          TodoStmts.Add(TIfStmt(CurStmt).ThenStmt);
          TodoStmts.Add(TIfStmt(CurStmt).ElseStmt);
        end
        else if CurStmt is TWhileStmt then
        begin
          TodoExprs.Add(TWhileStmt(CurStmt).Condition);
          TodoStmts.Add(TWhileStmt(CurStmt).Body);
        end
        else if CurStmt is TRepeatStmt then
        begin
          for J := 0 to TRepeatStmt(CurStmt).Body.Stmts.Count - 1 do
            TodoStmts.Add(TRepeatStmt(CurStmt).Body.Stmts.Items[J]);
          TodoExprs.Add(TRepeatStmt(CurStmt).Condition);
        end
        else if CurStmt is TForStmt then
        begin
          TodoExprs.Add(TForStmt(CurStmt).StartExpr);
          TodoExprs.Add(TForStmt(CurStmt).EndExpr);
          TodoStmts.Add(TForStmt(CurStmt).Body);
        end
        else if CurStmt is TCompoundStmt then
        begin
          for J := 0 to TCompoundStmt(CurStmt).Stmts.Count - 1 do
            TodoStmts.Add(TCompoundStmt(CurStmt).Stmts.Items[J]);
        end
      end;

      { Process one expr }
      if TodoExprs.Count > 0 then
      begin
        CurExpr := TASTExpr(TodoExprs.Items[TodoExprs.Count - 1]);
        TodoExprs.Delete(TodoExprs.Count - 1);
        if CurExpr = nil then Continue;

        if CurExpr is TIdentExpr then
        begin
          VName := TIdentExpr(CurExpr).Name;
          if (OuterVars.IndexOf(VName) >= 0) and
             ((ADecl.CapturedVars = nil) or
              (ADecl.CapturedVars.IndexOf(VName) < 0)) then
          begin
            if ADecl.CapturedVars = nil then
              ADecl.CapturedVars := TStringList.Create;
            ADecl.CapturedVars.Add(VName);
          end;
        end
        else if CurExpr is TBinaryExpr then
        begin
          TodoExprs.Add(TBinaryExpr(CurExpr).Left);
          TodoExprs.Add(TBinaryExpr(CurExpr).Right);
        end
        else if CurExpr is TNotExpr then
          TodoExprs.Add(TNotExpr(CurExpr).Expr)
        else if CurExpr is TFuncCallExpr then
        begin
          for J := 0 to TFuncCallExpr(CurExpr).Args.Count - 1 do
            TodoExprs.Add(TFuncCallExpr(CurExpr).Args.Items[J]);
        end
        else if CurExpr is TMethodCallExpr then
        begin
          for J := 0 to TMethodCallExpr(CurExpr).Args.Count - 1 do
            TodoExprs.Add(TMethodCallExpr(CurExpr).Args.Items[J]);
        end;
      end;
    end;
  finally
    OuterVars.Free;
    TodoExprs.Free;
    TodoStmts.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Inlining: eligibility analyser                                       }
{ ------------------------------------------------------------------ }
{ A function is inlinable when all of:                                 }
{   - has a body (not external, not forward)                           }
{   - not a method on a class or record                                }
{   - not generic (TypeParams = nil)                                   }
{   - has no var-params, open-array params, interface params, or       }
{     record-by-value params                                           }
{   - return type is nil (procedure) or a primitive scalar fitting     }
{     in a register (no record/string/class returns)                   }
{   - body has no try/except/finally, no raise, no loops, no nested    }
{     function/method calls that are themselves recursive, and no      }
{     references to the function itself (no self-recursion)            }
{   - body has at most a small number of statements                    }
{                                                                      }
{ Implementation: walks Body.Stmts and the parameter/return type list. }
{ Used by codegen — see docs/inlining-design.adoc.                     }

function TSemanticAnalyser.AssignmentTargetsParameter(const AName: string;
                                                       const ADecl: TMethodDecl): Boolean;
var
  I: Integer;
begin
  Result := False;
  if ADecl = nil then Exit;
  for I := 0 to ADecl.Params.Count - 1 do
    if SameText(TMethodParam(ADecl.Params.Items[I]).ParamName, AName) then
    begin
      Result := True;
      Exit;
    end;
end;

function TSemanticAnalyser.ExprRejectsInline(AExpr: TASTExpr;
                                              const ASelfDecl: TMethodDecl): Boolean;
var
  FC:  TFuncCallExpr;
  Bin: TBinaryExpr;
  I:   Integer;
begin
  Result := False;
  if AExpr = nil then Exit;
  if AExpr is TFuncCallExpr then
  begin
    FC := TFuncCallExpr(AExpr);
    { Self-recursion makes inlining unbounded. }
    if FC.ResolvedDecl = ASelfDecl then begin Result := True; Exit; end;
    for I := 0 to FC.Args.Count - 1 do
      if ExprRejectsInline(TASTExpr(FC.Args.Items[I]), ASelfDecl) then
        begin Result := True; Exit; end;
    Exit;
  end;
  if AExpr is TMethodCallExpr then begin Result := True; Exit; end;
  if AExpr is TBinaryExpr then
  begin
    Bin := TBinaryExpr(AExpr);
    if ExprRejectsInline(Bin.Left, ASelfDecl) then begin Result := True; Exit; end;
    if ExprRejectsInline(Bin.Right, ASelfDecl) then begin Result := True; Exit; end;
    Exit;
  end;
  if AExpr is TNotExpr then
  begin
    Result := ExprRejectsInline(TNotExpr(AExpr).Expr, ASelfDecl);
    Exit;
  end;
end;

function TSemanticAnalyser.StmtRejectsInline(AStmt: TASTStmt;
                                              const ASelfDecl: TMethodDecl;
                                              var AStmtCount: Integer): Boolean;
var
  I, J: Integer;
  Cmp:  TCompoundStmt;
  Asg:  TAssignment;
  Ifs:  TIfStmt;
  Cs:   TCaseStmt;
  Br:   TCaseBranch;
begin
  Result := True;
  if AStmt = nil then begin Result := False; Exit; end;

  { Hard rejects: loops, try, raise, method calls, nested calls we can't trace. }
  if (AStmt is TWhileStmt) or
     (AStmt is TRepeatStmt) or
     (AStmt is TForStmt) or
     (AStmt is TForInStmt) or
     (AStmt is TTryFinallyStmt) or
     (AStmt is TTryExceptStmt) or
     (AStmt is TRaiseStmt) or
     (AStmt is TBreakStmt) or
     (AStmt is TContinueStmt) or
     (AStmt is TMethodCallStmt) or
     (AStmt is TInheritedCallStmt) or
     (AStmt is TPointerWriteStmt) or
     (AStmt is TFieldAssignment) or
     (AStmt is TStaticSubscriptAssign) then
    Exit;

  if AStmt is TCompoundStmt then
  begin
    Cmp := TCompoundStmt(AStmt);
    for I := 0 to Cmp.Stmts.Count - 1 do
      if StmtRejectsInline(TASTStmt(Cmp.Stmts.Items[I]), ASelfDecl, AStmtCount) then
        Exit;
    Result := False;
    Exit;
  end;

  if AStmt is TExitStmt then
  begin
    Inc(AStmtCount);
    Result := False;
    Exit;
  end;

  if AStmt is TIfStmt then
  begin
    Ifs := TIfStmt(AStmt);
    Inc(AStmtCount);
    if ExprRejectsInline(Ifs.Condition, ASelfDecl) then Exit;
    if StmtRejectsInline(Ifs.ThenStmt, ASelfDecl, AStmtCount) then Exit;
    if (Ifs.ElseStmt <> nil) and
       StmtRejectsInline(Ifs.ElseStmt, ASelfDecl, AStmtCount) then Exit;
    Result := False;
    Exit;
  end;

  if AStmt is TAssignment then
  begin
    Asg := TAssignment(AStmt);
    Inc(AStmtCount);
    if ExprRejectsInline(Asg.Expr, ASelfDecl) then Exit;
    { Assignment to a parameter requires updating the caller-side temp,
      which the simple inliner does not support.  Reject. }
    if AssignmentTargetsParameter(Asg.Name, ASelfDecl) then Exit;
    Result := False;
    Exit;
  end;

  if AStmt is TProcCall then
  begin
    Inc(AStmtCount);
    { Calls to other functions inside an inline candidate are allowed as long
      as they are not the function itself.  The codegen will emit them as
      regular calls or inline them in turn. }
    if TProcCall(AStmt).ResolvedDecl = ASelfDecl then Exit;
    for I := 0 to TProcCall(AStmt).Args.Count - 1 do
      if ExprRejectsInline(TASTExpr(TProcCall(AStmt).Args.Items[I]), ASelfDecl) then
        Exit;
    Result := False;
    Exit;
  end;

  if AStmt is TCaseStmt then
  begin
    Cs := TCaseStmt(AStmt);
    Inc(AStmtCount);
    if ExprRejectsInline(Cs.Selector, ASelfDecl) then Exit;
    for I := 0 to Cs.Branches.Count - 1 do
    begin
      Br := TCaseBranch(Cs.Branches.Items[I]);
      for J := 0 to Br.Values.Count - 1 do
        if ExprRejectsInline(TASTExpr(Br.Values.Items[J]), ASelfDecl) then Exit;
      if StmtRejectsInline(Br.Stmt, ASelfDecl, AStmtCount) then Exit;
    end;
    if (Cs.ElseStmt <> nil) and
       StmtRejectsInline(Cs.ElseStmt, ASelfDecl, AStmtCount) then Exit;
    Result := False;
    Exit;
  end;

  { Unknown statement form: reject conservatively. }
end;

function TSemanticAnalyser.IsInlineEligible(ADecl: TMethodDecl): Boolean;
const
  MAX_STMTS = 24;
var
  I:   Integer;
  Par: TMethodParam;
  K:   TTypeKind;
  Cnt: Integer;
begin
  Result := False;
  if ADecl = nil then Exit;
  if ADecl.IsExternal then Exit;
  if ADecl.Body = nil then Exit;
  if ADecl.OwnerTypeName <> '' then Exit;       { class/record method — phase 2 }
  if ADecl.TypeParams <> nil then Exit;         { generic template }
  if ADecl.VTableSlot >= 0 then Exit;           { virtual dispatch }
  if ADecl.IsVirtual or ADecl.IsAbstract then Exit;

  { Return type: nil (procedure) or primitive scalar only. }
  if ADecl.ResolvedReturnType <> nil then
  begin
    K := ADecl.ResolvedReturnType.Kind;
    if not (K in [tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum,
                  tyInt64, tyUInt64, tySmallInt, tyWord,
                  tyDouble, tySingle, tyPointer, tyPChar]) then
      Exit;
  end;

  { Parameters: only primitive by-value. }
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Items[I]);
    if Par.IsVarParam or Par.IsOpenArray then Exit;
    if Par.ResolvedType = nil then Exit;
    K := Par.ResolvedType.Kind;
    if not (K in [tyInteger, tyUInt32, tyBoolean, tyByte, tyEnum,
                  tyInt64, tyUInt64, tySmallInt, tyWord,
                  tyDouble, tySingle, tyPointer, tyPChar]) then
      Exit;
  end;

  { No local variables (phase 1 keeps it simple — only the implicit Result). }
  if (ADecl.Body.Decls <> nil) and (ADecl.Body.Decls.Count > 0) then Exit;
  if (ADecl.Body.TypeDecls <> nil) and (ADecl.Body.TypeDecls.Count > 0) then Exit;
  if (ADecl.Body.ConstDecls <> nil) and (ADecl.Body.ConstDecls.Count > 0) then Exit;
  if (ADecl.Body.ProcDecls <> nil) and (ADecl.Body.ProcDecls.Count > 0) then Exit;

  { Walk body statements, counting and checking. }
  Cnt := 0;
  for I := 0 to ADecl.Body.Stmts.Count - 1 do
  begin
    if StmtRejectsInline(TASTStmt(ADecl.Body.Stmts.Items[I]), ADecl, Cnt) then Exit;
    if Cnt > MAX_STMTS then Exit;
  end;

  Result := True;
end;

procedure TSemanticAnalyser.MarkInlineCandidates(ABlock: TBlock);
var
  I:     Integer;
  ADecl: TMethodDecl;
begin
  for I := 0 to ABlock.ProcDecls.Count - 1 do
  begin
    ADecl := TMethodDecl(ABlock.ProcDecls.Items[I]);
    ADecl.IsInlineCandidate := IsInlineEligible(ADecl);
  end;
end;

procedure TSemanticAnalyser.AnalyseVarDecls(ABlock: TBlock);
var
  I, J, K: Integer;
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
      { Consts from the same block live in the immediately enclosing scope
        (AnalyseBlock pushes a new scope before calling AnalyseVarDecls, so
        FTable.Define cannot see same-block consts).  Scan the block's own
        ConstDecls list so we catch only same-block clashes, not legitimate
        shadowing of outer-scope or unit-imported consts. }
      for K := 0 to ABlock.ConstDecls.Count - 1 do
        if SameText(TConstDecl(ABlock.ConstDecls.Items[K]).Name, VarName) then
          SemanticError(
            Format('Duplicate identifier ''%s''', [VarName]),
            Decl.Line, Decl.Col);
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
    ForS.VarName  := VarSym.Name;  { normalise to declared casing }
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
      ForInS.VarName := VarSym.Name;  { normalise to declared casing }
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
      ForInS.VarName := VarSym.Name;  { normalise to declared casing }
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
    else if CollType.Kind = tySet then
    begin
      { ---- Set iteration path ---- }
      VarSym := FTable.Lookup(ForInS.VarName);
      if VarSym = nil then
        SemanticError(
          Format('Undeclared loop variable ''%s''', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      if VarSym.Kind <> skVariable then
        SemanticError(
          Format('''%s'' is not a variable', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      ElemType := TSetTypeDesc(CollType).BaseType;
      { Loop variable must be the same enum type as the set's base type,
        or any numeric type (ordinal compatibility). Reject non-ordinal types. }
      if not VarSym.TypeDesc.IsOrdinal then
        SemanticError(
          Format('for-in over set: loop variable ''%s'' must be an ordinal type',
            [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      ForInS.VarIsGlobal    := VarSym.IsGlobal;
      ForInS.IsSetIter      := True;
      ForInS.ResolvedVarType := ElemType;
      ForInS.SetBitCount    := TSetTypeDesc(CollType).BitCount;

      { Inject synthetic mask slot (Integer) for the evaluated set value }
      ForInS.SetMaskVarName := '__setmask_' + IntToStr(FForInCounter);
      { Inject synthetic index slot (Integer) for the bit position }
      ForInS.IdxVarName := '__idx_' + IntToStr(FForInCounter);
      Inc(FForInCounter);
      if FCurrentLocalBlock <> nil then
      begin
        SynthDecl := TVarDecl.Create;
        SynthDecl.Names.Add(ForInS.SetMaskVarName);
        SynthDecl.TypeName    := 'Integer';
        SynthDecl.ResolvedType := FTable.TypeInteger;
        SynthDecl.IsGlobal    := False;
        FCurrentLocalBlock.Decls.Add(SynthDecl);

        SynthDecl := TVarDecl.Create;
        SynthDecl.Names.Add(ForInS.IdxVarName);
        SynthDecl.TypeName    := 'Integer';
        SynthDecl.ResolvedType := FTable.TypeInteger;
        SynthDecl.IsGlobal    := False;
        FCurrentLocalBlock.Decls.Add(SynthDecl);
      end;
    end
    else if CollType.Kind = tyDynArray then
    begin
      { ---- Dynamic array iteration path ---- }
      ElemType := TDynArrayTypeDesc(CollType).ElementType;

      VarSym := FTable.Lookup(ForInS.VarName);
      if VarSym = nil then
        SemanticError(
          Format('Undeclared loop variable ''%s''', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      ForInS.VarName := VarSym.Name;
      if VarSym.Kind <> skVariable then
        SemanticError(
          Format('''%s'' is not a variable', [ForInS.VarName]),
          ForInS.Line, ForInS.Col);
      CheckTypesMatch(VarSym.TypeDesc, ElemType,
        'for-in loop variable', ForInS.Line, ForInS.Col);
      ForInS.VarIsGlobal    := VarSym.IsGlobal;
      ForInS.IsDynArrayIter := True;
      ForInS.ResolvedVarType := ElemType;

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
    else
      SemanticError(
        'for-in collection must be a class instance, static array, dynamic array, string, or set',
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
  FldInfo: TFieldInfo;
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
    if SameText(ACall.Name, 'Free') and (ACall.Args.Count = 0) and
       (FindMethodDecl(RT.Name, 'Free') = nil) then
    begin
      ACall.ResolvedClassType := RT;
      ACall.ResolvedMethod    := nil;
      Exit;
    end;
    for I := 0 to ACall.Args.Count - 1 do
      AnalyseExpr(TASTExpr(ACall.Args.Items[I]));
    MDecl := ResolveMethodOverload(RT.Name, ACall.Name, ACall.Args,
      ACall.Line, ACall.Col);
    if MDecl = nil then
      SemanticError(
        Format('Class ''%s'' has no method ''%s''', [RT.Name, ACall.Name]),
        ACall.Line, ACall.Col);
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
        if SameText(ACall.Name, 'Free') and (ACall.Args.Count = 0) and
           (FindMethodDecl(RT.Name, 'Free') = nil) then
        begin
          ACall.ResolvedClassType := RT;
          ACall.ResolvedMethod    := nil;
          Exit;
        end;
        for I := 0 to ACall.Args.Count - 1 do
          AnalyseExpr(TASTExpr(ACall.Args.Items[I]));
        MDecl := ResolveMethodOverload(RT.Name, ACall.Name, ACall.Args,
          ACall.Line, ACall.Col);
        if MDecl = nil then
          SemanticError(
            Format('Class ''%s'' has no method ''%s''', [RT.Name, ACall.Name]),
            ACall.Line, ACall.Col);
        ACall.ResolvedClassType := RT;
        ACall.ResolvedMethod    := MDecl;
        Exit;
      end;
    end;
    SemanticError(
      Format('Undeclared variable ''%s''', [ACall.ObjectName]),
      ACall.Line, ACall.Col);
  end;
  ACall.ObjectName := ObjSym.Name;  { normalise to declared casing }
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
    { Resolve arg expressions so codegen has ResolvedType on every node.
      We don't have concrete param signatures at interface-dispatch sites
      (Phase 3 limitation), so we can't validate types — but expressions
      still need to be analysed so e.g. `@Buf[0]` annotates the
      TStringSubscriptExpr's StrExpr.ResolvedType.  Without this,
      EmitAddrOfExpr crashes on a nil ResolvedType when emitting the
      argument. }
    for I := 0 to ACall.Args.Count - 1 do
      AnalyseExpr(TASTExpr(ACall.Args.Items[I]));
    ACall.ResolvedClassType := ObjSym.TypeDesc;
    ACall.ResolvedMethod    := nil;  { nil = interface dispatch, not class dispatch }
    ACall.IsGlobal          := ObjSym.IsGlobal;
    ACall.IsVarParam        := (ObjSym.Kind = skVarParameter);
    Exit;
  end;

  RT := TRecordTypeDesc(ObjSym.TypeDesc);
  { Free is a built-in: if Self <> nil then free(Self). No user-defined method needed. }
  if SameText(ACall.Name, 'Free') and (ACall.Args.Count = 0) and
     (FindMethodDecl(RT.Name, 'Free') = nil) then
  begin
    ACall.ResolvedClassType := RT;
    ACall.ResolvedMethod    := nil;
    ACall.IsGlobal          := ObjSym.IsGlobal;
    ACall.IsVarParam        := (ObjSym.Kind = skVarParameter);
    Exit;
  end;

  for I := 0 to ACall.Args.Count - 1 do
    AnalyseExpr(TASTExpr(ACall.Args.Items[I]));

  { Direct invocation of a procedural-typed field (e.g. an event-handler
    field): F.Handler; or F.Handler();.  Resolve this before reporting a
    missing method so the call dispatches through the (Code, Data) pair
    stored in the field, mirroring the indirect-call path used for a
    procedural-typed local variable. }
  FldInfo := RT.FindField(ACall.Name);
  if (FldInfo <> nil) and (FldInfo.TypeDesc <> nil) and
     (FldInfo.TypeDesc.Kind = tyProcedural) and
     (FindMethodDecl(RT.Name, ACall.Name) = nil) then
  begin
    ACall.IsProcFieldCall   := True;
    ACall.ProcFieldInfo     := FldInfo;
    ACall.ResolvedProcType  := FldInfo.TypeDesc;
    ACall.ResolvedClassType := RT;
    ACall.ResolvedMethod    := nil;
    ACall.IsGlobal          := ObjSym.IsGlobal;
    ACall.IsVarParam        := (ObjSym.Kind = skVarParameter);
    Exit;
  end;

  MDecl := ResolveMethodOverload(RT.Name, ACall.Name, ACall.Args,
    ACall.Line, ACall.Col);
  if MDecl = nil then
    SemanticError(
      Format('Class ''%s'' has no method ''%s''', [RT.Name, ACall.Name]),
      ACall.Line, ACall.Col);

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

  AAssign.Name            := VarSym.Name;  { normalise to declared casing }
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
    { Set-literal RHS into a tySet field — analyse with set context. }
    if (FldInfo.TypeDesc.Kind = tySet) and (AAssign.Expr is TArrayLiteralExpr) then
    begin
      AnalyseSetLiteralExpr(TArrayLiteralExpr(AAssign.Expr),
        TSetTypeDesc(FldInfo.TypeDesc));
      Exit;
    end;
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
  if not (RecSym.Kind in [skVariable, skParameter, skVarParameter]) then
    SemanticError(
      Format('''%s'' is not a variable', [AAssign.RecordName]),
      AAssign.Line, AAssign.Col);
  if not (RecSym.TypeDesc.Kind in [tyRecord, tyClass]) then
    SemanticError(
      Format('''%s'' is not a record or class variable', [AAssign.RecordName]),
      AAssign.Line, AAssign.Col);

  AAssign.RecordName    := RecSym.Name;  { normalise to declared casing }
  AAssign.IsClassAccess := RecSym.TypeDesc.Kind = tyClass;
  AAssign.IsGlobal      := RecSym.IsGlobal;
  { Treat value record/array params as by-reference at QBE ABI level. }
  AAssign.IsVarParam    :=
    (RecSym.Kind = skVarParameter) or
    ((RecSym.Kind = skParameter) and (RecSym.TypeDesc <> nil) and
     (RecSym.TypeDesc.Kind in [tyRecord, tyStaticArray]));

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
  { Set-literal RHS into a tySet field — analyse with set context. }
  if (FldInfo.TypeDesc.Kind = tySet) and (AAssign.Expr is TArrayLiteralExpr) then
  begin
    AnalyseSetLiteralExpr(TArrayLiteralExpr(AAssign.Expr),
      TSetTypeDesc(FldInfo.TypeDesc));
    Exit;
  end;
  ExprType := AnalyseExpr(AAssign.Expr);
  CheckTypesMatch(FldInfo.TypeDesc, ExprType, 'field assignment',
    AAssign.Line, AAssign.Col);
end;

function TSemanticAnalyser.MangleTypeCode(AType: TTypeDesc;
  AVarParam: Boolean): string;
var
  Base: string;
  PT:   TPointerTypeDesc;
begin
  if AType = nil then
  begin
    Result := '?';
    Exit;
  end;
  case AType.Kind of
    tyInteger:  Base := 'i';
    tyInt64:    Base := 'l';
    tyUInt32:   Base := 'u';
    tyUInt64:   Base := 'Q';
    tySmallInt: Base := 'h';
    tyWord:     Base := 'H';
    tyByte:     Base := 'y';
    tyBoolean:  Base := 'b';
    tyDouble:   Base := 'd';
    tySingle:   Base := 's';
    tyString:   Base := 'S';
    tyPChar:    Base := 'C';
    tyEnum:     Base := 'E' + AType.Name;
    tyRecord:   Base := 'R' + AType.Name;
    tyClass:    Base := 'K' + AType.Name;
    tyInterface:Base := 'I' + AType.Name;
    tyPointer:
      begin
        PT := TPointerTypeDesc(AType);
        if (PT.BaseType = nil) then
          Base := 'p'
        else
          Base := '^' + MangleTypeCode(PT.BaseType, False);
      end;
    tyOpenArray: Base := 'A' + MangleTypeCode(
                          TOpenArrayTypeDesc(AType).ElementType, False);
    tySet:       Base := 'T' + AType.Name;
    tyProcedural:Base := 'F' + AType.Name;
  else
    Base := '?';
  end;
  if AVarParam then
    Result := '@' + Base
  else
    Result := Base;
end;

function TSemanticAnalyser.MangleParamSig(ADecl: TMethodDecl): string;
var
  I:   Integer;
  Par: TMethodParam;
begin
  Result := '';
  for I := 0 to ADecl.Params.Count - 1 do
  begin
    Par    := TMethodParam(ADecl.Params.Items[I]);
    Result := Result + MangleTypeCode(Par.ResolvedType, Par.IsVarParam);
  end;
end;

function TSemanticAnalyser.MinArity(ADecl: TMethodDecl): Integer;
var
  I: Integer;
begin
  for I := 0 to ADecl.Params.Count - 1 do
    if TMethodParam(ADecl.Params.Items[I]).DefaultValue <> nil then
    begin
      Result := I;
      Exit;
    end;
  Result := ADecl.Params.Count;
end;

procedure TSemanticAnalyser.TransferDefaultValues(AFrom, AInto: TMethodDecl);
var
  I:    Integer;
  PSrc: TMethodParam;
  PDst: TMethodParam;
begin
  if (AFrom = nil) or (AInto = nil) then Exit;
  if AFrom.Params.Count <> AInto.Params.Count then Exit;
  for I := 0 to AFrom.Params.Count - 1 do
  begin
    PSrc := TMethodParam(AFrom.Params.Items[I]);
    PDst := TMethodParam(AInto.Params.Items[I]);
    if (PSrc.DefaultValue <> nil) and (PDst.DefaultValue = nil) then
    begin
      PDst.DefaultValue := PSrc.DefaultValue;
      PSrc.DefaultValue := nil;  { ownership transferred }
    end;
  end;
end;

procedure TSemanticAnalyser.AnalyseDefaultValueExpr(APar: TMethodParam;
  const AContext: string; ALine, ACol: Integer);
var
  T: TTypeDesc;
begin
  if APar.DefaultValue = nil then Exit;
  if APar.DefaultValue.ResolvedType <> nil then Exit;  { already analysed }
  if not ((APar.DefaultValue is TIntLiteral)    or
          (APar.DefaultValue is TFloatLiteral)  or
          (APar.DefaultValue is TStringLiteral) or
          (APar.DefaultValue is TNilLiteral)    or
          (APar.DefaultValue is TIdentExpr)) then
    SemanticError(
      Format('Default value for parameter ''%s'' must be a literal or named constant',
        [APar.ParamName]),
      ALine, ACol);
  T := AnalyseExpr(APar.DefaultValue);
  if APar.DefaultValue is TIdentExpr then
    if not TIdentExpr(APar.DefaultValue).IsConstant then
      SemanticError(
        Format('Default value for parameter ''%s'' must be a constant expression',
          [APar.ParamName]),
        ALine, ACol);
  CheckTypesMatch(APar.ResolvedType, T,
    Format('default value of parameter ''%s'' (%s)', [APar.ParamName, AContext]),
    ALine, ACol);
end;

function TSemanticAnalyser.CloneDefaultExprNode(ASrc: TASTExpr): TASTExpr;
var
  ILit: TIntLiteral;
  FLit: TFloatLiteral;
  SLit: TStringLiteral;
  Ident: TIdentExpr;
  SrcId: TIdentExpr;
begin
  Result := nil;
  if ASrc = nil then Exit;
  if ASrc is TIntLiteral then
  begin
    ILit       := TIntLiteral.Create;
    ILit.Value := TIntLiteral(ASrc).Value;
    ILit.Line  := ASrc.Line;
    ILit.Col   := ASrc.Col;
    ILit.ResolvedType := ASrc.ResolvedType;
    Result := ILit;
  end
  else if ASrc is TFloatLiteral then
  begin
    FLit       := TFloatLiteral.Create;
    FLit.Value := TFloatLiteral(ASrc).Value;
    FLit.Line  := ASrc.Line;
    FLit.Col   := ASrc.Col;
    FLit.ResolvedType := ASrc.ResolvedType;
    Result := FLit;
  end
  else if ASrc is TStringLiteral then
  begin
    SLit       := TStringLiteral.Create;
    SLit.Value := TStringLiteral(ASrc).Value;
    SLit.IsCharCoerce := TStringLiteral(ASrc).IsCharCoerce;
    SLit.CharOrdValue := TStringLiteral(ASrc).CharOrdValue;
    SLit.Line  := ASrc.Line;
    SLit.Col   := ASrc.Col;
    SLit.ResolvedType := ASrc.ResolvedType;
    Result := SLit;
  end
  else if ASrc is TNilLiteral then
  begin
    Result      := TNilLiteral.Create;
    Result.Line := ASrc.Line;
    Result.Col  := ASrc.Col;
    Result.ResolvedType := ASrc.ResolvedType;
  end
  else if ASrc is TIdentExpr then
  begin
    SrcId  := TIdentExpr(ASrc);
    Ident  := TIdentExpr.Create;
    Ident.Name        := SrcId.Name;
    Ident.IsConstant  := SrcId.IsConstant;
    Ident.ConstValue  := SrcId.ConstValue;
    Ident.ConstString := SrcId.ConstString;
    Ident.Line        := SrcId.Line;
    Ident.Col         := SrcId.Col;
    Ident.ResolvedType := SrcId.ResolvedType;
    Result := Ident;
  end
  else
    SemanticError(
      'Internal: unsupported default-value AST node — only literals and named constants allowed',
      ASrc.Line, ASrc.Col);
end;

procedure TSemanticAnalyser.AppendDefaultArgs(AArgs: TObjectList;
  ADecl: TMethodDecl; const AContext: string; ALine, ACol: Integer);
var
  I:        Integer;
  Par:      TMethodParam;
  CloneEx:  TASTExpr;
begin
  if ADecl = nil then Exit;
  for I := AArgs.Count to ADecl.Params.Count - 1 do
  begin
    Par := TMethodParam(ADecl.Params.Items[I]);
    if Par.DefaultValue = nil then
      SemanticError(
        Format('No default value for parameter ''%s'' of ''%s''',
          [Par.ParamName, AContext]),
        ALine, ACol);
    AnalyseDefaultValueExpr(Par, AContext, ALine, ACol);
    CloneEx := CloneDefaultExprNode(Par.DefaultValue);
    AArgs.Add(CloneEx);
  end;
end;

function TSemanticAnalyser.ArgMatchScore(AParam: TTypeDesc;
  AArg: TTypeDesc; AArgExpr: TASTExpr): Integer;
begin
  Result := 0;
  if (AParam = nil) or (AArg = nil) then Exit;
  { Integer literal (untyped constant) matches any integer type exactly —
    mirrors Pascal's treatment of untyped integer constants.  Floating-point
    params score 1 (widening) so an Integer overload beats a Double overload
    when both are candidates. }
  if (AArgExpr is TIntLiteral) and AParam.IsNumeric then
  begin
    if AParam.Kind in [tyInteger, tyInt64, tyUInt32, tyUInt64,
                       tySmallInt, tyWord, tyByte] then
      Result := 2
    else
      Result := 1;  { Double, Single — widening }
    Exit;
  end;
  if AParam = AArg then
  begin
    Result := 2;  { exact match — same descriptor instance }
    Exit;
  end;
  { Same-kind, same-name, structurally identical types count as exact —
    catches multiple TOpenArrayTypeDesc instances over the same element. }
  if (AParam.Kind = tyOpenArray) and (AArg.Kind = tyOpenArray) and
     (TOpenArrayTypeDesc(AParam).ElementType =
      TOpenArrayTypeDesc(AArg).ElementType) then
  begin
    Result := 2;
    Exit;
  end;
  { Static array coerced to open-array: widening match (score 1) }
  if (AParam.Kind = tyOpenArray) and (AArg.Kind = tyStaticArray) and
     (TOpenArrayTypeDesc(AParam).ElementType =
      TStaticArrayTypeDesc(AArg).ElementType) then
  begin
    Result := 1;
    Exit;
  end;
  { Same numeric kind = exact match (same kind, just possibly different
    descriptor instance). }
  if AParam.IsNumeric and AArg.IsNumeric and (AParam.Kind = AArg.Kind) then
  begin
    Result := 2;
    Exit;
  end;
  { Numeric widening: both numerics, kinds differ.  Captures
    Integer→Int64, Integer→Double, Single→Double, Byte→Integer, etc. }
  if AParam.IsNumeric and AArg.IsNumeric then
  begin
    Result := 1;
    Exit;
  end;
  { Fall-through: probe full assignability via CheckTypesMatch.  This
    covers nil-literal, class subtypes, untyped-Pointer compatibility,
    enum/integer crossover, procedural-type signature compatibility,
    and similar.  Cost 1 (widening). }
  try
    CheckTypesMatch(AParam, AArg, '', 0, 0);
    Result := 1;
  except
    on E: ESemanticError do
      Result := 0;
  end;
end;

function TSemanticAnalyser.ResolveStandaloneOverload(const AName: string;
  AArity: Integer; AArgs: TObjectList; ALine, ACol: Integer): TMethodDecl;
var
  I, J:        Integer;
  Cand:        TMethodDecl;
  ArityMatch:  TObjectList;
  Score:       Integer;
  ArgScore:    Integer;
  Par:         TMethodParam;
  Arg:         TASTExpr;
  BestScore:   Integer;
  BestCount:   Integer;
  Best:        TMethodDecl;
  TotalCnt:    Integer;
  ExactNew:    Integer;
  ExactBest:   Integer;
  S1, S2:      Integer;
begin
  Result    := nil;
  TotalCnt  := 0;
  ArityMatch := TObjectList.Create(False);
  try
    for I := 0 to FProcIndex.Count - 1 do
      if SameText(FProcIndex.Strings[I], AName) then
      begin
        Inc(TotalCnt);
        Cand := TMethodDecl(FProcIndex.Objects[I]);
        if (AArity >= MinArity(Cand)) and (AArity <= Cand.Params.Count) then
          ArityMatch.Add(Cand);
      end;

    if TotalCnt = 0 then Exit;  { caller treats as "no decl found" }

    if ArityMatch.Count = 0 then
      SemanticError(
        Format('No matching overload for ''%s'' with %d argument(s)',
          [AName, AArity]),
        ALine, ACol);

    { With no args supplied, accept the unique arity match — used by
      callers that haven't analysed their args yet.  Ambiguity is then
      caught when the caller re-resolves with arg types. }
    if (AArgs = nil) or (AArity = 0) then
    begin
      if ArityMatch.Count = 1 then
      begin
        Result := TMethodDecl(ArityMatch.Items[0]);
        Exit;
      end;
      { zero-arg ambiguity is impossible — same name + zero params would
        have been rejected by the symbol-table chain, but be defensive. }
      if AArity = 0 then
        SemanticError(
          Format('Ambiguous overload of ''%s''', [AName]),
          ALine, ACol);
      { Multiple arity matches but no args to score with — keep nil. }
      Exit;
    end;

    BestScore := -1;
    BestCount := 0;
    Best      := nil;
    for I := 0 to ArityMatch.Count - 1 do
    begin
      Cand  := TMethodDecl(ArityMatch.Items[I]);
      Score := 0;
      for J := 0 to AArity - 1 do
      begin
        Par      := TMethodParam(Cand.Params.Items[J]);
        Arg      := TASTExpr(AArgs.Items[J]);
        ArgScore := ArgMatchScore(Par.ResolvedType, Arg.ResolvedType, Arg);
        if ArgScore = 0 then
        begin
          Score := -1;  { drop this candidate }
          Break;
        end;
        Score := Score + ArgScore;
      end;
      if Score < 0 then Continue;
      { Tie-break: prefer the candidate that needs the fewest defaulted
        parameters — i.e. Params.Count closest to AArity.  Score in the
        high bits, defaulting penalty in the low bits.  Each defaulted
        slot subtracts 1 from the composite score. }
      Score := (Score * 16) - (Cand.Params.Count - AArity);
      if Score > BestScore then
      begin
        BestScore := Score;
        BestCount := 1;
        Best      := Cand;
      end
      else if Score = BestScore then
      begin
        { Secondary tie-break: count exact matches (ArgMatchScore=2).
          More exact matches = better candidate. }
        ExactNew  := 0;
        ExactBest := 0;
        for J := 0 to AArity - 1 do
        begin
          S1 := ArgMatchScore(TMethodParam(Cand.Params.Items[J]).ResolvedType,
                              TASTExpr(AArgs.Items[J]).ResolvedType,
                              TASTExpr(AArgs.Items[J]));
          S2 := ArgMatchScore(TMethodParam(Best.Params.Items[J]).ResolvedType,
                              TASTExpr(AArgs.Items[J]).ResolvedType,
                              TASTExpr(AArgs.Items[J]));
          if S1 = 2 then Inc(ExactNew);
          if S2 = 2 then Inc(ExactBest);
        end;
        if ExactNew > ExactBest then
        begin
          Best      := Cand;
          BestCount := 1;
        end
        else if ExactNew = ExactBest then
          Inc(BestCount);
      end;
    end;

    if BestScore < 0 then
      SemanticError(
        Format('No matching overload for ''%s'' with %d argument(s)',
          [AName, AArity]),
        ALine, ACol);
    if BestCount > 1 then
      SemanticError(
        Format('Ambiguous overload of ''%s'' — multiple candidates match equally',
          [AName]),
        ALine, ACol);
    Result := Best;
  finally
    ArityMatch.Free;
  end;
end;

procedure TSemanticAnalyser.AnalyseProcCall(ACall: TProcCall);
var
  Sym:     TSymbol;
  MDecl:   TMethodDecl;
  Par:     TMethodParam;
  ArgType: TTypeDesc;
  Idx:     Integer;
  I:       Integer;
  PT:      TProceduralTypeDesc;
  PPar:    TProcParamInfo;
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
        { Analyse args first so overload resolution can score by type. }
        for I := 0 to ACall.Args.Count - 1 do
          AnalyseExpr(TASTExpr(ACall.Args.Items[I]));
        { Use overload resolution so the correct variant is chosen when
          multiple overloads exist (e.g. AssertEquals(string,string,string)
          vs AssertEquals(string,Integer,Integer)). }
        MDecl := ResolveMethodOverload(FCurrentClass.Name, ACall.Name,
          ACall.Args, ACall.Line, ACall.Col);
        if MDecl = nil then
          SemanticError(
            Format('No matching overload for ''%s.%s'' with %d argument(s)',
              [FCurrentClass.Name, ACall.Name, ACall.Args.Count]),
            ACall.Line, ACall.Col);
        { Validate only var-param arguments (non-var compatibility was
          verified by the overload scorer). }
        for I := 0 to ACall.Args.Count - 1 do
        begin
          Par := TMethodParam(MDecl.Params.Items[I]);
          if Par.IsVarParam then
          begin
            ArgType := TASTExpr(ACall.Args.Items[I]).ResolvedType;
            CheckTypesMatch(Par.ResolvedType, ArgType,
              Format('var argument %d of ''%s''', [I + 1, ACall.Name]),
              ACall.Line, ACall.Col);
          end;
        end;
        AppendDefaultArgs(ACall.Args, MDecl, ACall.Name, ACall.Line, ACall.Col);
        ACall.ResolvedDecl         := MDecl;
        ACall.IsImplicitSelfMethod := True;
        Exit;
      end;
    end;
    { Try on-demand instantiation of a generic function }
    if StrPos('<', ACall.Name) >= 0 then
      InstantiateGenericFunc(ACall.Name);
    Sym := FTable.Lookup(ACall.Name);
    if Sym = nil then
      SemanticError(
        Format('Undeclared procedure ''%s''', [ACall.Name]),
        ACall.Line, ACall.Col);
  end;
  ACall.Name := Sym.Name;  { normalise to declared casing }
  { Indirect call through a procedural-typed variable used as a statement:
    e.g. 'MyHandler(Arg1, Arg2)' where MyHandler is 'var MyHandler: TMyProc'. }
  if (Sym.Kind in [skVariable, skParameter, skVarParameter]) and
     (Sym.TypeDesc <> nil) and (Sym.TypeDesc.Kind = tyProcedural) then
  begin
    ACall.IsIndirectCall       := True;
    ACall.IndirectCallIsGlobal := Sym.IsGlobal;
    ACall.ResolvedProcType     := Sym.TypeDesc;
    PT := TProceduralTypeDesc(Sym.TypeDesc);
    if ACall.Args.Count <> PT.Params.Count then
      SemanticError(Format(
        'Indirect call ''%s'' expects %d argument(s), got %d',
        [ACall.Name, PT.Params.Count, ACall.Args.Count]),
        ACall.Line, ACall.Col);
    for I := 0 to ACall.Args.Count - 1 do
    begin
      ArgType := AnalyseExpr(TASTExpr(ACall.Args.Items[I]));
      PPar    := TProcParamInfo(PT.Params.Items[I]);
      { Var-param actual must be an L-value; check before the type match
        so the diagnostic matches the regular-call path. }
      if PPar.IsVarParam and
         not ((TASTExpr(ACall.Args.Items[I]) is TIdentExpr) or
              (TASTExpr(ACall.Args.Items[I]) is TFieldAccessExpr) or
              (TASTExpr(ACall.Args.Items[I]) is TDerefExpr)) then
        SemanticError(
          Format('var argument %d of ''%s'' must be a variable',
            [I + 1, ACall.Name]),
          ACall.Line, ACall.Col);
      CheckTypesMatch(PPar.TypeDesc, ArgType,
        Format('argument %d of ''%s''', [I + 1, ACall.Name]),
        ACall.Line, ACall.Col);
    end;
    Exit;
  end;

  if not (Sym.Kind in [skProcedure, skFunction]) then
    SemanticError(
      Format('''%s'' is not a procedure or function', [ACall.Name]),
      ACall.Line, ACall.Col);

  { Nested proc: found in scope but not in FProcIndex (nested procs are
    excluded from the global index to prevent same-name clashes across
    different outer procs).  Resolve directly from the symbol's Decl. }
  if (Sym.Kind in [skProcedure, skFunction]) and
     (Sym.Decl <> nil) and
     (TMethodDecl(Sym.Decl).EnclosingDecl <> nil) then
  begin
    MDecl := TMethodDecl(Sym.Decl);
    if ACall.Args.Count <> MDecl.Params.Count then
      SemanticError(
        Format('Nested procedure ''%s'' expects %d argument(s), got %d',
          [ACall.Name, MDecl.Params.Count, ACall.Args.Count]),
        ACall.Line, ACall.Col);
    for I := 0 to ACall.Args.Count - 1 do
      AnalyseExpr(TASTExpr(ACall.Args.Items[I]));
    ACall.ResolvedDecl := MDecl;
    Exit;
  end;

  { For user-defined procs/funcs, validate arg count and types.
    Phase B: analyse all args FIRST so overload resolution can score
    them by type, then re-validate the chosen overload's parameter
    modes (var/out arguments). }
  Idx := FProcIndex.IndexOf(ACall.Name);
  if Idx >= 0 then
  begin
    for I := 0 to ACall.Args.Count - 1 do
      AnalyseExpr(TASTExpr(ACall.Args.Items[I]));

    MDecl := ResolveStandaloneOverload(ACall.Name, ACall.Args.Count,
      ACall.Args, ACall.Line, ACall.Col);
    if MDecl = nil then
      SemanticError(
        Format('No matching overload for ''%s'' with %d argument(s)',
          [ACall.Name, ACall.Args.Count]),
        ACall.Line, ACall.Col);

    for I := 0 to ACall.Args.Count - 1 do
    begin
      Par := TMethodParam(MDecl.Params.Items[I]);
      if Par.IsVarParam then
      begin
        { Var argument must be an L-value: simple ident, field access,
          pointer-deref-then-field (P^.F), or pointer deref (P^). }
        if not ((TASTExpr(ACall.Args.Items[I]) is TIdentExpr) or
                (TASTExpr(ACall.Args.Items[I]) is TFieldAccessExpr) or
                (TASTExpr(ACall.Args.Items[I]) is TDerefExpr)) then
          SemanticError(
            Format('var argument %d of ''%s'' must be a variable',
              [I + 1, ACall.Name]),
            ACall.Line, ACall.Col);
        ArgType := TASTExpr(ACall.Args.Items[I]).ResolvedType;
        CheckTypesMatch(Par.ResolvedType, ArgType,
          Format('var argument %d of ''%s''', [I + 1, ACall.Name]),
          ACall.Line, ACall.Col);
      end;
      { Non-var argument compatibility was verified by overload scoring;
        no second CheckTypesMatch needed here. }
    end;
    AppendDefaultArgs(ACall.Args, MDecl, ACall.Name, ACall.Line, ACall.Col);
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
    if SameText(ACall.Name, 'Delete') then
    begin
      { Delete(var S: string; Idx, Count: Integer) — string mutator. }
      if ACall.Args.Count <> 3 then
        SemanticError('Delete requires exactly 3 arguments',
          ACall.Line, ACall.Col);
      ArgType := AnalyseExpr(TASTExpr(ACall.Args.Items[0]));
      if (ArgType = nil) or (ArgType.Kind <> tyString) then
        SemanticError('First argument of ''Delete'' must be a string variable',
          ACall.Line, ACall.Col);
      if not ((TASTExpr(ACall.Args.Items[0]) is TIdentExpr) or
              (TASTExpr(ACall.Args.Items[0]) is TFieldAccessExpr)) then
        SemanticError('First argument of ''Delete'' must be an assignable string',
          ACall.Line, ACall.Col);
      AnalyseExpr(TASTExpr(ACall.Args.Items[1]));
      AnalyseExpr(TASTExpr(ACall.Args.Items[2]));
    end
    else
    if SameText(ACall.Name, 'SetLength') then
    begin
      { SetLength(var S: string; N: Integer) — string truncate/grow.
        SetLength(var A: array of T; N: Integer) — dynamic array resize. }
      if ACall.Args.Count <> 2 then
        SemanticError('SetLength requires exactly 2 arguments',
          ACall.Line, ACall.Col);
      ArgType := AnalyseExpr(TASTExpr(ACall.Args.Items[0]));
      if (ArgType = nil) or not (ArgType.Kind in [tyString, tyDynArray]) then
        SemanticError('First argument of ''SetLength'' must be a string or dynamic array variable',
          ACall.Line, ACall.Col);
      if not ((TASTExpr(ACall.Args.Items[0]) is TIdentExpr) or
              (TASTExpr(ACall.Args.Items[0]) is TFieldAccessExpr)) then
        SemanticError('First argument of ''SetLength'' must be an assignable variable',
          ACall.Line, ACall.Col);
      AnalyseExpr(TASTExpr(ACall.Args.Items[1]));
    end
    else
    if SameText(ACall.Name, 'Sleep') then
    begin
      if ACall.Args.Count <> 1 then
        SemanticError('Sleep requires exactly 1 argument', ACall.Line, ACall.Col);
      AnalyseExpr(TASTExpr(ACall.Args.Items[0]));
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
  PT:      TProceduralTypeDesc;
  PPar:    TProcParamInfo;
begin
  { HasClassAttribute(AClass, AAttrClass): Boolean — runtime query of the custom
    attribute RTTI stored in slot 7 of the class's typeinfo.  Both arguments
    must be metaclass expressions (bare class names).  Lowers to a call to
    $_HasClassAttribute(l typeinfo_class, l typeinfo_attr). }
  if SameText(AExpr.Name, 'HasClassAttribute') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('HasClassAttribute requires exactly 2 arguments', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    AnalyseExpr(TASTExpr(AExpr.Args.Items[1]));
    if (TASTExpr(AExpr.Args.Items[0]).ResolvedType = nil) or
       not (TASTExpr(AExpr.Args.Items[0]).ResolvedType.Kind in [tyClass, tyMetaClass]) then
      SemanticError('HasClassAttribute: first argument must be a class type reference',
        AExpr.Line, AExpr.Col);
    if (TASTExpr(AExpr.Args.Items[1]).ResolvedType = nil) or
       not (TASTExpr(AExpr.Args.Items[1]).ResolvedType.Kind in [tyClass, tyMetaClass]) then
      SemanticError('HasClassAttribute: second argument must be an attribute class reference',
        AExpr.Line, AExpr.Col);
    AExpr.IsBuiltinHasClassAttr := True;
    AExpr.ResolvedType := FTable.TypeBoolean;
    Result := AExpr.ResolvedType;
    Exit;
  end;

  { SizeOf(TypeName) or SizeOf(expression) — compile-time byte size,
    returns Integer.  The codegen reads Args[0].ResolvedType.ByteSize and
    emits a literal, so the argument is never evaluated at runtime. }
  if SameText(AExpr.Name, 'SizeOf') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('SizeOf requires exactly one argument', AExpr.Line, AExpr.Col);
    Sym := nil;
    if AExpr.Args.Items[0] is TIdentExpr then
      Sym := FTable.Lookup(TIdentExpr(AExpr.Args.Items[0]).Name);
    if (Sym <> nil) and (Sym.Kind = skType) then
      TIdentExpr(AExpr.Args.Items[0]).ResolvedType := Sym.TypeDesc
    else
      AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    if TASTExpr(AExpr.Args.Items[0]).ResolvedType = nil then
      SemanticError('SizeOf argument must be a type or typed expression',
        AExpr.Line, AExpr.Col);
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

  if SameText(AExpr.Name, 'High') or SameText(AExpr.Name, 'Low') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(AExpr.Name + ' requires exactly one argument',
        AExpr.Line, AExpr.Col);
    { Accept either a type-name identifier (e.g. High(Integer)) or a typed
      expression (e.g. High(SomeVar)).  For type-name form, record the type
      on the argument node so codegen can read ResolvedType directly. }
    Sym := nil;
    if AExpr.Args.Items[0] is TIdentExpr then
      Sym := FTable.Lookup(TIdentExpr(AExpr.Args.Items[0]).Name);
    if (Sym <> nil) and (Sym.Kind = skType) then
    begin
      ArgType := Sym.TypeDesc;
      TIdentExpr(AExpr.Args.Items[0]).ResolvedType := ArgType;
    end
    else
      ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    if ArgType = nil then
      SemanticError(AExpr.Name + ' argument has no resolved type',
        AExpr.Line, AExpr.Col);
    if ArgType.IsFloat then
      SemanticError(AExpr.Name +
        ' is not defined for floating-point types; use MaxDouble/MinDouble or Math.Infinity',
        AExpr.Line, AExpr.Col);
    if ArgType.Kind in [tyOpenArray, tyStaticArray, tyDynArray, tyString] then
    begin
      { Index-bound form: result is Integer (existing behaviour). }
      Result := FTable.TypeInteger;
      AExpr.ResolvedType := Result;
      Exit;
    end;
    if ArgType.IsOrdinal then
    begin
      { Ordinal-bound form: result type is the argument's own type. }
      Result := ArgType;
      AExpr.ResolvedType := Result;
      Exit;
    end;
    SemanticError(AExpr.Name +
      ' argument must be an ordinal type, array, or string',
      AExpr.Line, AExpr.Col);
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
        { Analyse args first so overload resolution can score by type. }
        for I := 0 to AExpr.Args.Count - 1 do
          AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));
        MDecl := ResolveMethodOverload(FCurrentClass.Name, AExpr.Name,
          AExpr.Args, AExpr.Line, AExpr.Col);
        if MDecl = nil then
          SemanticError(
            Format('No matching overload for ''%s.%s'' with %d argument(s)',
              [FCurrentClass.Name, AExpr.Name, AExpr.Args.Count]),
            AExpr.Line, AExpr.Col);
        for I := 0 to AExpr.Args.Count - 1 do
        begin
          Par := TMethodParam(MDecl.Params.Items[I]);
          if Par.IsVarParam then
          begin
            ArgType := TASTExpr(AExpr.Args.Items[I]).ResolvedType;
            CheckTypesMatch(Par.ResolvedType, ArgType,
              Format('var argument %d of ''%s''', [I + 1, AExpr.Name]),
              AExpr.Line, AExpr.Col);
          end;
        end;
        AppendDefaultArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
        AExpr.ResolvedDecl         := MDecl;
        AExpr.IsImplicitSelfMethod := True;
        Result := MDecl.ResolvedReturnType;
        AExpr.ResolvedType := Result;
        Exit;
      end;
    end;
    { Try on-demand instantiation of a generic function }
    if StrPos('<', AExpr.Name) >= 0 then
      InstantiateGenericFunc(AExpr.Name);
    Sym := FTable.Lookup(AExpr.Name);
    if Sym = nil then
      SemanticError(
        Format('Undeclared function ''%s''', [AExpr.Name]),
        AExpr.Line, AExpr.Col);
  end;
  AExpr.Name := Sym.Name;  { normalise to declared casing }
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

  { Indirect call through a procedural-typed variable: F() where F is
    declared 'var F: TIntFn'.  The call dispatches through the function
    pointer stored in F. }
  if (Sym.Kind in [skVariable, skParameter, skVarParameter]) and
     (Sym.TypeDesc <> nil) and (Sym.TypeDesc.Kind = tyProcedural) then
  begin
    AExpr.IsIndirectCall       := True;
    AExpr.IndirectCallIsGlobal := Sym.IsGlobal;
    AExpr.ResolvedProcType     := Sym.TypeDesc;
    { Validate arg count + types against the signature. }
    PT := TProceduralTypeDesc(Sym.TypeDesc);
    if AExpr.Args.Count <> PT.Params.Count then
      SemanticError(Format(
        'Indirect call ''%s'' expects %d argument(s), got %d',
        [AExpr.Name, PT.Params.Count, AExpr.Args.Count]),
        AExpr.Line, AExpr.Col);
    for I := 0 to AExpr.Args.Count - 1 do
    begin
      ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));
      PPar    := TProcParamInfo(PT.Params.Items[I]);
      if PPar.IsVarParam and
         not ((TASTExpr(AExpr.Args.Items[I]) is TIdentExpr) or
              (TASTExpr(AExpr.Args.Items[I]) is TFieldAccessExpr) or
              (TASTExpr(AExpr.Args.Items[I]) is TDerefExpr)) then
        SemanticError(
          Format('var argument %d of ''%s'' must be a variable',
            [I + 1, AExpr.Name]),
          AExpr.Line, AExpr.Col);
      CheckTypesMatch(PPar.TypeDesc, ArgType,
        Format('argument %d of ''%s''', [I + 1, AExpr.Name]),
        AExpr.Line, AExpr.Col);
    end;
    Result := PT.ReturnType;
    if Result = nil then
      Result := FTable.TypeVoid;
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
    if not (ArgType.Kind in [tyString, tyOpenArray, tyStaticArray, tyDynArray]) then
      SemanticError('Length argument must be a string or array', AExpr.Line, AExpr.Col);
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

  if SameText(AExpr.Name, 'PosEx') then
  begin
    if AExpr.Args.Count <> 3 then
      SemanticError('PosEx requires exactly three arguments', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    AnalyseExpr(TASTExpr(AExpr.Args.Items[1]));
    AnalyseExpr(TASTExpr(AExpr.Args.Items[2]));
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

  if SameText(AExpr.Name, 'Assigned') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Assigned requires exactly one argument',
        AExpr.Line, AExpr.Col);
    ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    if (ArgType = nil) or
       not (ArgType.Kind in [tyPointer, tyPChar, tyClass, tyInterface,
                             tyString, tyProcedural]) then
      SemanticError(
        Format('Assigned requires a pointer/class/interface/proc argument, got ''%s''',
          [ArgType.Name]),
        AExpr.Line, AExpr.Col);
    Result := FTable.TypeBoolean;
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

  if SameText(AExpr.Name, 'UInt64ToStr') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('UInt64ToStr requires exactly one argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'DoubleToStr') or SameText(AExpr.Name, 'SingleToStr') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(AExpr.Name + ' requires exactly one argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'StrToDouble') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('StrToDouble requires exactly one argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeDouble;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Abs') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Abs requires exactly one argument', AExpr.Line, AExpr.Col);
    Result := AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    if not Result.IsNumeric then
      SemanticError(Format('Abs requires a numeric argument, got ''%s''', [Result.Name]),
        AExpr.Line, AExpr.Col);
    AExpr.ResolvedType := Result;  { return type matches argument type }
    Exit;
  end;

  { Math builtins — Sqrt, Ceil, Floor, Round, Trunc, Ln, Log2, Log10,
    Power, Sin, Cos, Tan, ArcTan, ArcTan2, IsNaN, IsInfinite.
    These are implemented as compiler builtins rather than RTL functions
    so that the codegen can emit dtosi/stosi for the float→integer
    conversions (Ceil/Floor/Round/Trunc) and can dispatch to the *f
    variants for Single arguments on the trig functions.
    Min and Max are implemented in pure Pascal in math.pas because they
    are handled correctly by normal overload resolution. }

  if SameText(AExpr.Name, 'Sqrt') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('Sqrt requires exactly one argument', AExpr.Line, AExpr.Col);
    Result := AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    if not Result.IsFloat then
      SemanticError(Format('Sqrt requires a float argument, got ''%s''', [Result.Name]),
        AExpr.Line, AExpr.Col);
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Ceil') or SameText(AExpr.Name, 'Floor') or
     SameText(AExpr.Name, 'Round') or SameText(AExpr.Name, 'Trunc') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(AExpr.Name + ' requires exactly one argument', AExpr.Line, AExpr.Col);
    ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    if not ArgType.IsFloat then
      SemanticError(Format('%s requires a float argument, got ''%s''', [AExpr.Name, ArgType.Name]),
        AExpr.Line, AExpr.Col);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Ln') or SameText(AExpr.Name, 'Log2') or
     SameText(AExpr.Name, 'Log10') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(AExpr.Name + ' requires exactly one argument', AExpr.Line, AExpr.Col);
    ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    if not ArgType.IsFloat then
      SemanticError(Format('%s requires a float argument, got ''%s''', [AExpr.Name, ArgType.Name]),
        AExpr.Line, AExpr.Col);
    Result := FTable.TypeDouble;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Power') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('Power requires exactly two arguments', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    AnalyseExpr(TASTExpr(AExpr.Args.Items[1]));
    Result := FTable.TypeDouble;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'Sin') or SameText(AExpr.Name, 'Cos') or
     SameText(AExpr.Name, 'Tan') or SameText(AExpr.Name, 'ArcTan') or
     SameText(AExpr.Name, 'ArcSin') or SameText(AExpr.Name, 'ArcCos') or
     SameText(AExpr.Name, 'Sinh') or SameText(AExpr.Name, 'Cosh') or
     SameText(AExpr.Name, 'Tanh') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(AExpr.Name + ' requires exactly one argument', AExpr.Line, AExpr.Col);
    Result := AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    if not Result.IsFloat then
      SemanticError(Format('%s requires a float argument, got ''%s''', [AExpr.Name, Result.Name]),
        AExpr.Line, AExpr.Col);
    AExpr.ResolvedType := Result;  { return type matches argument type — Single→Single, Double→Double }
    Exit;
  end;

  if SameText(AExpr.Name, 'ArcTan2') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('ArcTan2 requires exactly two arguments', AExpr.Line, AExpr.Col);
    Result := AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    AnalyseExpr(TASTExpr(AExpr.Args.Items[1]));
    if not Result.IsFloat then
      SemanticError('ArcTan2 requires float arguments', AExpr.Line, AExpr.Col);
    AExpr.ResolvedType := Result;  { return type matches first argument type }
    Exit;
  end;

  if SameText(AExpr.Name, 'IsNaN') or SameText(AExpr.Name, 'IsInfinite') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(AExpr.Name + ' requires exactly one argument', AExpr.Line, AExpr.Col);
    ArgType := AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    if not ArgType.IsFloat then
      SemanticError(Format('%s requires a float argument, got ''%s''', [AExpr.Name, ArgType.Name]),
        AExpr.Line, AExpr.Col);
    Result := FTable.TypeBoolean;
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

  { MethodAddress(Obj, Name): walks the object's typeinfo chain looking for
    a published method named 'Name'.  Returns nil when not found.  Used by
    blaise.testing's RegisterTest path to dispatch test methods by name. }
  if SameText(AExpr.Name, 'MethodAddress') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('MethodAddress requires exactly two arguments (Obj, Name)',
        AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    AnalyseExpr(TASTExpr(AExpr.Args.Items[1]));
    if (TASTExpr(AExpr.Args.Items[0]).ResolvedType = nil) or
       (TASTExpr(AExpr.Args.Items[0]).ResolvedType.Kind <> tyClass) then
      SemanticError('MethodAddress: first argument must be a class instance',
        AExpr.Line, AExpr.Col);
    if (TASTExpr(AExpr.Args.Items[1]).ResolvedType = nil) or
       (TASTExpr(AExpr.Args.Items[1]).ResolvedType.Kind <> tyString) then
      SemanticError('MethodAddress: second argument must be a string',
        AExpr.Line, AExpr.Col);
    Result := FTable.TypePointer;
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

  { ClassCreate(Cls, ...args): runtime construction from a metaclass.
    Resolves the constructor on Cls.BaseClass with the supplied args
    and stores the TMethodDecl on AExpr.ResolvedDecl.  Codegen lowers
    this to '%p = call $_ClassCreate(l <classvalue>); call $T_Create(l %p, args...)'.
    Result type is the BaseClass — assigning to a 'var T: TFoo' is
    well-typed when Cls: class of TFoo. }
  if SameText(AExpr.Name, 'ClassCreate') then
  begin
    if AExpr.Args.Count < 1 then
      SemanticError('ClassCreate requires a metaclass as the first argument',
        AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    if (TASTExpr(AExpr.Args.Items[0]).ResolvedType = nil) or
       (TASTExpr(AExpr.Args.Items[0]).ResolvedType.Kind <> tyMetaClass) then
      SemanticError('ClassCreate: first argument must be a metaclass (class of T) value',
        AExpr.Line, AExpr.Col);
    { Analyse remaining args before resolving the constructor — argument
      types feed FindMethodDecl when we add overload resolution; for v0
      we look up 'Create' by name and trust uniqueness. }
    for I := 1 to AExpr.Args.Count - 1 do
      AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));
    Result := TMetaClassTypeDesc(TASTExpr(AExpr.Args.Items[0]).ResolvedType).BaseClass;
    AExpr.ResolvedType := Result;
    AExpr.ResolvedDecl := FindMethodDecl(Result.Name, 'Create');
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
  if SameText(AExpr.Name, 'ParamCount') or
     SameText(AExpr.Name, 'GetProcessID') then
  begin
    if AExpr.Args.Count <> 0 then
      SemanticError(Format('''%s'' takes no arguments', [AExpr.Name]),
                    AExpr.Line, AExpr.Col);
    Result := FTable.TypeInteger;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'GetTempDir') then
  begin
    if AExpr.Args.Count <> 0 then
      SemanticError('GetTempDir takes no arguments', AExpr.Line, AExpr.Col);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'GetCurrentDir') then
  begin
    if AExpr.Args.Count <> 0 then
      SemanticError('GetCurrentDir takes no arguments', AExpr.Line, AExpr.Col);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'GetTempFileName') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('GetTempFileName requires exactly 2 arguments', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    AnalyseExpr(TASTExpr(AExpr.Args.Items[1]));
    Result := FTable.TypeString;
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

  if SameText(AExpr.Name, 'FileExists') or
     SameText(AExpr.Name, 'DirectoryExists') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(Format('''%s'' requires exactly 1 argument', [AExpr.Name]),
                    AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeBoolean;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'ForceDirectories') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('ForceDirectories requires exactly 1 argument', AExpr.Line, AExpr.Col);
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
     SameText(AExpr.Name, 'ExtractFileDir') or
     SameText(AExpr.Name, 'ExtractFileExt') or
     SameText(AExpr.Name, 'IncludeTrailingPathDelimiter') or
     SameText(AExpr.Name, 'ExcludeTrailingPathDelimiter') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError(Format('''%s'' requires exactly 1 argument', [AExpr.Name]),
                    AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'RenameFile') then
  begin
    if AExpr.Args.Count <> 2 then
      SemanticError('RenameFile requires exactly 2 arguments', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    AnalyseExpr(TASTExpr(AExpr.Args.Items[1]));
    Result := FTable.TypeBoolean;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if SameText(AExpr.Name, 'SetCurrentDir') then
  begin
    if AExpr.Args.Count <> 1 then
      SemanticError('SetCurrentDir requires exactly 1 argument', AExpr.Line, AExpr.Col);
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    Result := FTable.TypeBoolean;
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

  { Phase B: analyse args first, then score overloads by argument type. }
  for I := 0 to AExpr.Args.Count - 1 do
    AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));

  MDecl := ResolveStandaloneOverload(AExpr.Name, AExpr.Args.Count,
    AExpr.Args, AExpr.Line, AExpr.Col);
  if MDecl = nil then
    SemanticError(
      Format('No matching overload for ''%s'' with %d argument(s)',
        [AExpr.Name, AExpr.Args.Count]),
      AExpr.Line, AExpr.Col);

  AppendDefaultArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
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
  ResolvedObjName: string;
begin
  { Call on an arbitrary expression (e.g. TCast(x).Method(y)) }
  if AExpr.ObjExpr <> nil then
  begin
    ObjType := AnalyseExpr(AExpr.ObjExpr);

    { Built-in InheritsFrom on a Pointer/metaclass/class ObjExpr receiver. }
    if SameText(AExpr.Name, 'InheritsFrom') and (AExpr.Args.Count = 1) and
       (ObjType.Kind in [tyPointer, tyMetaClass, tyClass]) then
    begin
      AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
      AExpr.IsBuiltinInheritsFrom := True;
      Result := FTable.TypeBoolean;
      AExpr.ResolvedType := Result;
      Exit;
    end;

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
    RT := TRecordTypeDesc(ObjType);
    { Analyse args first so overload resolution can score by type. }
    for I := 0 to AExpr.Args.Count - 1 do
      AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));
    { Built-in TObject.ToString: virtual dispatch via vtable slot 1. }
    if SameText(AExpr.Name, 'ToString') and (AExpr.Args.Count = 0) then
    begin
      AExpr.ResolvedClassType := RT;
      AExpr.ResolvedMethod    := nil;
      AExpr.IsBuiltinToString := True;
      Result := FTable.TypeString;
      AExpr.ResolvedType := Result;
      Exit;
    end;
    MDecl := ResolveMethodOverload(RT.Name, AExpr.Name, AExpr.Args,
      AExpr.Line, AExpr.Col);
    if MDecl = nil then
      SemanticError(
        Format('Class ''%s'' has no method ''%s''', [RT.Name, AExpr.Name]),
        AExpr.Line, AExpr.Col);
    AppendDefaultArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
    AExpr.ResolvedClassType := RT;
    AExpr.ResolvedMethod    := MDecl;
    Result := MDecl.ResolvedReturnType;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  ObjSym := FTable.Lookup(AExpr.ObjectName);
  { If the name contains '<' and wasn't found, resolve scope-bound type params
    (e.g. 'TListEnumerator<T>' → 'TListEnumerator<Integer>' when T=Integer is
    in scope) and trigger on-demand instantiation.  Mirrors the field-access
    path so that 'TGen<T>.Create(args)' resolves inside a generic method body.

    The shared method body means we must NOT mutate AExpr.ObjectName — a
    second instantiation with a different concrete arg would then see the
    first instance's resolved name and skip its own substitution. }
  if (ObjSym = nil) and (StrPos('<', AExpr.ObjectName) >= 0) then
  begin
    ResolvedObjName := ResolveScopeBoundTypeParams(AExpr.ObjectName);
    FindTypeOrInstantiate(ResolvedObjName);
    ObjSym := FTable.Lookup(ResolvedObjName);
  end;
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
          {$IFDEF FPC}AExpr.ObjExpr.Free;{$ENDIF}
          AExpr.ObjExpr := nil;
          SemanticError(
            Format('Undeclared identifier ''%s''', [AExpr.ObjectName]),
            AExpr.Line, AExpr.Col);
        end;
      end;
      if (ObjType = nil) or not (ObjType.Kind in [tyClass, tyInterface]) then
      begin
        {$IFDEF FPC}AExpr.ObjExpr.Free;{$ENDIF}
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
      RT := TRecordTypeDesc(ObjType);
      { Analyse args first so overload resolution can score by type. }
      for I := 0 to AExpr.Args.Count - 1 do
        AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));
      MDecl := ResolveMethodOverload(RT.Name, AExpr.Name, AExpr.Args,
        AExpr.Line, AExpr.Col);
      if MDecl = nil then
        SemanticError(
          Format('Class ''%s'' has no method ''%s''', [RT.Name, AExpr.Name]),
          AExpr.Line, AExpr.Col);
      AppendDefaultArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
      { Validate var/out-param arguments (type compatibility scored by
        overload resolver; only lvalue constraint needs rechecking). }
      for I := 0 to AExpr.Args.Count - 1 do
      begin
        Par := TMethodParam(MDecl.Params.Items[I]);
        if Par.IsVarParam then
        begin
          ArgType := TASTExpr(AExpr.Args.Items[I]).ResolvedType;
          CheckTypesMatch(Par.ResolvedType, ArgType,
            Format('var argument %d of ''%s''', [I + 1, AExpr.Name]),
            AExpr.Line, AExpr.Col);
        end;
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

  { Normalise casing on the AST node ONLY when the lookup matched the
    original name case-insensitively.  When the symbol came in via
    scope-bound type-param substitution (e.g. AExpr.ObjectName was
    'TFoo<T>' and we resolved it to 'TFoo<String>'), keep the AST
    name as the template form so a second instantiation that binds T
    to a different concrete type re-runs the same substitution.  The
    resolved name is captured in ResolvedClassType for codegen. }
  if SameText(ObjSym.Name, AExpr.ObjectName) then
    AExpr.ObjectName := ObjSym.Name;

  { Constructor call with args: TypeName.Create(arg1, arg2, ...) or any
    method on a class type starting with Create (e.g. CreateFmt). }
  if (ObjSym.Kind = skType) and
     (SameText(AExpr.Name, 'Create') or
      (StrPos('Create', AExpr.Name) = 0)) then
  begin
    if ObjSym.TypeDesc.Kind <> tyClass then
      SemanticError(
        Format('Cannot construct non-class type ''%s''', [ObjSym.Name]),
        AExpr.Line, AExpr.Col);
    if TRecordTypeDesc(ObjSym.TypeDesc).HasAbstractMethods then
      SemanticError(
        Format('Cannot instantiate abstract class ''%s''', [ObjSym.Name]),
        AExpr.Line, AExpr.Col);
    for I := 0 to AExpr.Args.Count - 1 do
      AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));
    { Try to find a user-defined constructor method for type checking.
      Use overload resolution so the correct variant is chosen when multiple
      constructors with the same name (e.g. Create) are declared.  Look up
      on the resolved class name (ObjSym.Name) so generic instances pick
      the right concrete method set. }
    MDecl := ResolveMethodOverload(ObjSym.Name, AExpr.Name,
      AExpr.Args, AExpr.Line, AExpr.Col);
    if MDecl = nil then
      MDecl := FindMethodDecl(ObjSym.Name, AExpr.Name);
    if MDecl <> nil then
      AppendDefaultArgs(AExpr.Args, MDecl, AExpr.Name, AExpr.Line, AExpr.Col);
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

  { Built-in InheritsFrom on a Pointer/metaclass receiver.
    Called as AClass.InheritsFrom(BClass) where both sides are typeinfo
    pointers (i.e. TClass = Pointer, or class-of-T metaclass).
    Also handles a tyClass receiver (instance) for uniform usage. }
  if SameText(AExpr.Name, 'InheritsFrom') and (AExpr.Args.Count = 1) and
     (ObjSym.TypeDesc.Kind in [tyPointer, tyMetaClass, tyClass]) then
  begin
    AnalyseExpr(TASTExpr(AExpr.Args.Items[0]));
    AExpr.IsBuiltinInheritsFrom := True;
    AExpr.IsGlobal  := ObjSym.IsGlobal;
    AExpr.IsVarParam := (ObjSym.Kind = skVarParameter);
    Result := FTable.TypeBoolean;
    AExpr.ResolvedType := Result;
    Exit;
  end;

  if not (ObjSym.TypeDesc.Kind in [tyClass, tyInterface, tyRecord]) then
    SemanticError(
      Format('''%s'' is not a class, interface, or record variable', [AExpr.ObjectName]),
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
    AExpr.ResolvedType := Result;
    Exit;
  end;

  RT    := TRecordTypeDesc(ObjSym.TypeDesc);
  MDecl := FindMethodDecl(RT.Name, AExpr.Name);
  { Built-in TObject.ToString: virtual dispatch yielding string.
    Every class inherits this from TObject (vtable slot 1). }
  if (MDecl = nil) and SameText(AExpr.Name, 'ToString') and (AExpr.Args.Count = 0) then
  begin
    AExpr.ResolvedClassType := RT;
    AExpr.ResolvedMethod    := nil;
    AExpr.IsBuiltinToString := True;
    AExpr.IsGlobal          := ObjSym.IsGlobal;
    AExpr.IsVarParam        := (ObjSym.Kind = skVarParameter);
    Result := FTable.TypeString;
    AExpr.ResolvedType := Result;
    Exit;
  end;
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
    if TIntLiteral(AExpr).IsUInt64 then
      Result := FTable.TypeUInt64
    else if (TIntLiteral(AExpr).Value < -2147483648) or
            (TIntLiteral(AExpr).Value > 2147483647) then
      Result := FTable.TypeInt64
    else
      Result := FTable.TypeInteger
  else if AExpr is TFloatLiteral then
    Result := FTable.TypeDouble   { float literals default to Double }
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
    { Var-params and value-record/array params are both passed by reference at
      the QBE ABI level: the local slot holds a pointer, not the aggregate
      bytes.  Codegen must dereference the slot before reading fields. }
    TIdentExpr(AExpr).Name      := Sym.Name;  { normalise to declared casing }
    TIdentExpr(AExpr).IsVarParam :=
      (Sym.Kind = skVarParameter) or
      ((Sym.Kind = skParameter) and (Sym.TypeDesc <> nil) and
       (Sym.TypeDesc.Kind in [tyRecord, tyStaticArray]));
    TIdentExpr(AExpr).IsGlobal  := Sym.IsGlobal;
    if Sym.Kind = skConstant then
    begin
      TIdentExpr(AExpr).IsConstant  := True;
      TIdentExpr(AExpr).ConstValue  := Sym.ConstValue;
      TIdentExpr(AExpr).ConstString := Sym.ConstString;
    end;
    { Bare class type identifier used as a value: metaclass reference.
      The result type is 'class of TFoo'; codegen emits the typeinfo
      address.  Compatibility with untyped Pointer (so 'Pointer(EError)'
      casts and 'AClass: Pointer' parameters keep working) is handled
      in CheckTypesMatch. }
    if (Sym.Kind = skType) and (Sym.TypeDesc <> nil) and
       (Sym.TypeDesc.Kind = tyClass) then
    begin
      TIdentExpr(AExpr).IsMetaclassRef := True;
      Result := FindTypeOrInstantiate('class of ' + Sym.TypeDesc.Name);
      if Result = nil then Result := FTable.TypePointer;
      AExpr.ResolvedType := Result;
      Exit;
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
  else if AExpr is TIndirectFuncCallExpr then
    Result := AnalyseIndirectFuncCallExpr(TIndirectFuncCallExpr(AExpr))
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
  else if AExpr is TSupportsExpr then
    Result := AnalyseSupportsExpr(TSupportsExpr(AExpr))
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
  IntfDesc: TInterfaceTypeDesc;
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
    { Built-in class intrinsics available on any class instance }
    if SameText(AAccess.FieldName, 'ClassName') and (BaseType.Kind = tyClass) then
    begin
      AAccess.IsClassNameAccess := True;
      AAccess.ResolvedType := FTable.TypeString;
      Result := FTable.TypeString;
      Exit;
    end;
    if SameText(AAccess.FieldName, 'ClassType') and (BaseType.Kind = tyClass) then
    begin
      AAccess.IsClassTypeAccess := True;
      AAccess.ResolvedType := FTable.TypePointer;  { TClass = Pointer for now }
      Result := FTable.TypePointer;
      Exit;
    end;
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
      { Method-backed property (including indexed: the parser attaches the
        '[idx]' to AAccess.PropIndexExpr when it parses 'Base.Prop[idx]'). }
      if (PropInfo <> nil) and (PropInfo.ReadMethod <> '') then
      begin
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
      { Zero-arg method call via field access: Obj.Method (no parens) }
      AAccess.ResolvedMethod := FindMethodDecl(RT.Name, AAccess.FieldName);
      if AAccess.ResolvedMethod <> nil then
      begin
        AAccess.IsMethodCall := True;
        Result := TMethodDecl(AAccess.ResolvedMethod).ResolvedReturnType;
        Exit;
      end;
      { Built-in TObject.ToString: virtual dispatch yielding string.
        Every class inherits this via vtable slot 1. }
      if SameText(AAccess.FieldName, 'ToString') then
      begin
        AAccess.IsMethodCall      := True;
        AAccess.IsBuiltinToString := True;
        AAccess.ResolvedMethod    := nil;
        Result := FTable.TypeString;
        AAccess.ResolvedType := Result;
        Exit;
      end;
      { Class-level constant (scalar or array): look up ClassName.ConstName }
      Sym := FTable.Lookup(BaseType.Name + '.' + AAccess.FieldName);
      if (Sym <> nil) and (Sym.Kind = skConstant) then
      begin
        AAccess.IsConstant := True;
        AAccess.ConstValue := Sym.ConstValue;
        AAccess.ConstString := Sym.ConstString;
        if Sym.ConstArray <> nil then
        begin
          AAccess.ConstArraySymbol := BaseType.Name + '_' + AAccess.FieldName;
          AAccess.ConstArrayType := Sym.TypeDesc;
        end;
        AAccess.ResolvedType := Sym.TypeDesc;
        Result := Sym.TypeDesc;
        Exit;
      end;
      SemanticError(
        Format('Type ''%s'' has no field ''%s''',
          [BaseType.Name, AAccess.FieldName]),
        AAccess.Line, AAccess.Col);
    end;
    AAccess.FieldInfo := FldInfo;
    Result := FldInfo.TypeDesc;
    if AAccess.PropIndexExpr <> nil then
    begin
      { Subscript on a string field: Rec.Field[N] — emit char access. }
      if FldInfo.TypeDesc.IsString then
      begin
        AnalyseExpr(AAccess.PropIndexExpr);
        AAccess.IsCharAccess := True;
        Result := FTable.TypeInteger;
        AAccess.ResolvedType := Result;
      end
      { Subscript on a class field: Rec.Field[I] — use the field type's indexed property. }
      else if FldInfo.TypeDesc.Kind in [tyRecord, tyClass] then
      begin
        PropInfo := TRecordTypeDesc(FldInfo.TypeDesc).FindIndexedProperty;
        if PropInfo <> nil then
        begin
          AnalyseExpr(AAccess.PropIndexExpr);
          AAccess.PropRead      := PropInfo;
          AAccess.PropOwnerType := TRecordTypeDesc(FldInfo.TypeDesc).Name;
          Result := PropInfo.TypeDesc;
          AAccess.ResolvedType := Result;
        end;
      end;
    end;
    Exit;
  end;

  RecSym := FTable.Lookup(AAccess.RecordName);
  { If the name contains '<' and wasn't found, resolve scope-bound type params
    (e.g. 'TGenEnum<T>' → 'TGenEnum<Integer>' when T=Integer is in scope)
    and update AAccess.RecordName so codegen sees the concrete instantiation. }
  if (RecSym = nil) and (StrPos('<', AAccess.RecordName) >= 0) then
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
        if AAccess.PropIndexExpr <> nil then
        begin
          if AAccess.FieldInfo.TypeDesc.IsString then
          begin
            AnalyseExpr(AAccess.PropIndexExpr);
            AAccess.IsCharAccess := True;
            Result := FTable.TypeInteger;
            AAccess.ResolvedType := Result;
          end
          else if AAccess.FieldInfo.TypeDesc.Kind in [tyRecord, tyClass] then
          begin
            PropInfo := TRecordTypeDesc(AAccess.FieldInfo.TypeDesc).FindIndexedProperty;
            if PropInfo <> nil then
            begin
              AnalyseExpr(AAccess.PropIndexExpr);
              AAccess.PropRead      := PropInfo;
              AAccess.PropOwnerType := TRecordTypeDesc(AAccess.FieldInfo.TypeDesc).Name;
              Result := PropInfo.TypeDesc;
              AAccess.ResolvedType := Result;
            end;
          end;
        end;
        Exit;
      end;
    end;
    SemanticError(
      Format('Undeclared identifier ''%s''', [AAccess.RecordName]),
      AAccess.Line, AAccess.Col);
  end;

  AAccess.RecordName := RecSym.Name;  { normalise to declared casing }

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
        if Sym.ConstArray <> nil then
        begin
          AAccess.ConstArraySymbol := AAccess.RecordName + '_' + AAccess.FieldName;
          AAccess.ConstArrayType := Sym.TypeDesc;
          if AAccess.PropIndexExpr <> nil then
          begin
            AnalyseExpr(AAccess.PropIndexExpr);
            AAccess.ResolvedType := TStaticArrayTypeDesc(Sym.TypeDesc).ElementType;
            Result := AAccess.ResolvedType;
            Exit;
          end;
        end;
        AAccess.ResolvedType := Sym.TypeDesc;
        Result := Sym.TypeDesc;
        Exit;
      end;
      SemanticError(
        Format('Unknown class method ''%s'' on type ''%s''',
          [AAccess.FieldName, AAccess.RecordName]),
        AAccess.Line, AAccess.Col);
    end;
    if TRecordTypeDesc(RecSym.TypeDesc).HasAbstractMethods then
      SemanticError(
        Format('Cannot instantiate abstract class ''%s''', [AAccess.RecordName]),
        AAccess.Line, AAccess.Col);
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

  { Interface variable: method call through itab (expression context) }
  if RecSym.TypeDesc.Kind = tyInterface then
  begin
    IntfDesc := TInterfaceTypeDesc(RecSym.TypeDesc);
    if not IntfDesc.HasMethod(AAccess.FieldName) then
      SemanticError(
        Format('Interface ''%s'' has no method ''%s''',
          [IntfDesc.Name, AAccess.FieldName]),
        AAccess.Line, AAccess.Col);
    AAccess.IsInterfaceCall  := True;
    AAccess.ResolvedClassType := IntfDesc;
    AAccess.IsGlobal         := RecSym.IsGlobal;
    AAccess.IsVarParam       := (RecSym.Kind = skVarParameter);
    Result := FindTypeOrInstantiate(
      IntfDesc.MethodReturnTypeName(IntfDesc.MethodIndex(AAccess.FieldName)));
    if Result = nil then
      Result := FTable.TypeInteger;
    AAccess.ResolvedType := Result;
    Exit;
  end;

  if not (RecSym.TypeDesc.Kind in [tyRecord, tyClass]) then
    SemanticError(
      Format('''%s'' is not a record or class', [AAccess.RecordName]),
      AAccess.Line, AAccess.Col);

  AAccess.IsClassAccess := RecSym.TypeDesc.Kind = tyClass;
  AAccess.IsGlobal      := RecSym.IsGlobal;
  { Records and static arrays are always passed by reference at the QBE ABI
    level — the param slot holds a pointer.  Mark both var-params and value
    aggregate params so codegen dereferences the slot. }
  AAccess.IsVarParam    :=
    (RecSym.Kind = skVarParameter) or
    ((RecSym.Kind = skParameter) and (RecSym.TypeDesc <> nil) and
     (RecSym.TypeDesc.Kind in [tyRecord, tyStaticArray]));

  { Built-in class intrinsics }
  if SameText(AAccess.FieldName, 'ClassName') and (RecSym.TypeDesc.Kind = tyClass) then
  begin
    AAccess.IsClassNameAccess := True;
    AAccess.ResolvedType := FTable.TypeString;
    Result := FTable.TypeString;
    Exit;
  end;
  if SameText(AAccess.FieldName, 'ClassType') and (RecSym.TypeDesc.Kind = tyClass) then
  begin
    AAccess.IsClassTypeAccess := True;
    AAccess.ResolvedType := FTable.TypePointer;
    Result := FTable.TypePointer;
    Exit;
  end;

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
    { Built-in TObject.ToString: virtual dispatch yielding string. }
    if SameText(AAccess.FieldName, 'ToString') then
    begin
      AAccess.IsMethodCall      := True;
      AAccess.IsBuiltinToString := True;
      AAccess.ResolvedMethod    := nil;
      Result := FTable.TypeString;
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
    { Class-level constant (scalar or array) via instance: T.Const }
    Sym := FTable.Lookup(RT.Name + '.' + AAccess.FieldName);
    if (Sym <> nil) and (Sym.Kind = skConstant) then
    begin
      AAccess.IsConstant := True;
      AAccess.ConstValue := Sym.ConstValue;
      AAccess.ConstString := Sym.ConstString;
      if Sym.ConstArray <> nil then
      begin
        AAccess.ConstArraySymbol := RT.Name + '_' + AAccess.FieldName;
        AAccess.ConstArrayType := Sym.TypeDesc;
        if AAccess.PropIndexExpr <> nil then
        begin
          AnalyseExpr(AAccess.PropIndexExpr);
          AAccess.ResolvedType := TStaticArrayTypeDesc(Sym.TypeDesc).ElementType;
          Result := AAccess.ResolvedType;
          Exit;
        end;
      end;
      AAccess.ResolvedType := Sym.TypeDesc;
      Result := Sym.TypeDesc;
      Exit;
    end;
    SemanticError(
      Format('Type ''%s'' has no field ''%s''',
        [AAccess.RecordName, AAccess.FieldName]),
      AAccess.Line, AAccess.Col);
  end;

  AAccess.FieldInfo := FldInfo;
  Result := FldInfo.TypeDesc;
  if AAccess.PropIndexExpr <> nil then
  begin
    if FldInfo.TypeDesc.IsString then
    begin
      AnalyseExpr(AAccess.PropIndexExpr);
      AAccess.IsCharAccess := True;
      Result := FTable.TypeInteger;
      AAccess.ResolvedType := Result;
    end
    else if FldInfo.TypeDesc.Kind in [tyRecord, tyClass] then
    begin
      PropInfo := TRecordTypeDesc(FldInfo.TypeDesc).FindIndexedProperty;
      if PropInfo <> nil then
      begin
        AnalyseExpr(AAccess.PropIndexExpr);
        AAccess.PropRead      := PropInfo;
        AAccess.PropOwnerType := TRecordTypeDesc(FldInfo.TypeDesc).Name;
        Result := PropInfo.TypeDesc;
        AAccess.ResolvedType := Result;
      end;
    end;
  end;
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
      if ((LType.Kind = tyInt64) and (RType.Kind = tyUInt64)) or
         ((LType.Kind = tyUInt64) and (RType.Kind = tyInt64)) then
        SemanticError(
          Format('Cannot mix signed Int64 and UInt64 in ''%s'' '
                 + 'without an explicit cast', [BinaryOpName(ABin.Op)]),
          ABin.Line, ABin.Col);
      if (LType.Kind = tyUInt64) or (RType.Kind = tyUInt64) then
        Result := FTable.TypeUInt64
      else if (LType.Kind = tyInt64) or (RType.Kind = tyInt64) then
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
      { Float comparisons: Single/Double are compatible with each other }
      (LType.IsFloat and RType.IsFloat) or
      { Integer/float mixing in comparisons is allowed (integer promotes) }
      (LType.IsFloat and RType.IsNumeric) or
      (RType.IsFloat and LType.IsNumeric) or
      ((LType.Kind = tyNil) and (RType.Kind in [tyClass, tyInterface, tyPointer, tyPChar])) or
      ((RType.Kind = tyNil) and (LType.Kind in [tyClass, tyInterface, tyPointer, tyPChar])) or
      ((LType.Kind = tyPointer) and (RType.Kind = tyPointer)) or
      { Class comparisons: allow subtype on either side }
      ((LType.Kind = tyClass) and (RType.Kind = tyClass) and
       (IsSubtypeOf(LType, RType) or IsSubtypeOf(RType, LType))) or
      { TObject is universal base class }
      ((LType.Kind = tyClass) and (RType.Kind = tyClass) and
       ((LType.Name = 'TObject') or (RType.Name = 'TObject'))) or
      { Metaclass comparisons: any two metaclass-typed values compare
        as pointer identity. }
      ((LType.Kind = tyMetaClass) and (RType.Kind = tyMetaClass)) or
      ((LType.Kind = tyMetaClass) and (RType.Kind in [tyPointer, tyNil])) or
      ((RType.Kind = tyMetaClass) and (LType.Kind in [tyPointer, tyNil]))
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
    if ABin.Op in [boShl, boShr, boSar] then
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
    { `div` is integer division; reject float operands. }
    if (ABin.Op = boDiv) and (LType.IsFloat or RType.IsFloat) then
      SemanticError(
        '''div'' requires integer operands; use ''/'' for real division',
        ABin.Line, ABin.Col);
    { `/` is real division: always yields a float, even with Integer operands.
      Result is Single when both operands are Single, Double otherwise. }
    if ABin.Op = boSlash then
    begin
      if (LType.Kind = tySingle) and (RType.Kind = tySingle) then
        Result := FTable.TypeSingle
      else
        Result := FTable.TypeDouble;
    end
    { Float promotion: if either side is float, result is float.
      Double wins over Single; any integer mixed with float promotes to Double. }
    else if LType.IsFloat or RType.IsFloat then
    begin
      if (LType.Kind = tyDouble) or (RType.Kind = tyDouble) or
         (not LType.IsFloat) or (not RType.IsFloat) then
        Result := FTable.TypeDouble
      else
        Result := FTable.TypeSingle;  { Single op Single → Single }
    end
    else
    begin
      CheckTypesMatch(LType, RType, 'binary expression', ABin.Line, ABin.Col);
      { Int64 / UInt64 wins over narrower integer types so codegen emits
        l-typed instructions and the high bits are preserved.  Signed and
        unsigned 64-bit types cannot be mixed without an explicit cast. }
      if ((LType.Kind = tyInt64) and (RType.Kind = tyUInt64)) or
         ((LType.Kind = tyUInt64) and (RType.Kind = tyInt64)) then
        SemanticError(
          'Cannot mix signed Int64 and UInt64 in arithmetic without '
          + 'an explicit cast', ABin.Line, ABin.Col);
      if (LType.Kind = tyUInt64) or (RType.Kind = tyUInt64) then
        Result := FTable.TypeUInt64
      else if (LType.Kind = tyInt64) or (RType.Kind = tyInt64) then
        Result := FTable.TypeInt64
      else
        Result := LType;
    end;
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

function TSemanticAnalyser.AnalyseSupportsExpr(AExpr: TSupportsExpr): TTypeDesc;
var
  ObjType:   TTypeDesc;
  IntfType:  TTypeDesc;
  OutSym:    TSymbol;
begin
  ObjType := AnalyseExpr(AExpr.Obj);
  if not (ObjType.Kind in [tyClass, tyInterface, tyPointer]) then
    SemanticError(
      Format('Supports() requires a class or interface instance as first argument, got ''%s''',
        [ObjType.Name]),
      AExpr.Line, AExpr.Col);

  IntfType := FTable.FindType(AExpr.IntfTypeName);
  if (IntfType = nil) or (IntfType.Kind <> tyInterface) then
    SemanticError(
      Format('Supports() second argument must be an interface type name, got ''%s''',
        [AExpr.IntfTypeName]),
      AExpr.Line, AExpr.Col);

  AExpr.ResolvedIntfType := IntfType;

  if AExpr.OutVarName <> '' then
  begin
    OutSym := FTable.Lookup(AExpr.OutVarName);
    if (OutSym = nil) or (OutSym.TypeDesc = nil) or
       (OutSym.TypeDesc.Kind <> tyInterface) then
      SemanticError(
        Format('Supports() third argument must be an interface-typed variable, got ''%s''',
          [AExpr.OutVarName]),
        AExpr.Line, AExpr.Col);
    AExpr.OutVarName     := OutSym.Name;  { normalise to declared casing }
    AExpr.OutVarIsGlobal := OutSym.IsGlobal;
  end;

  Result := FTable.TypeBoolean;
  AExpr.ResolvedType := Result;
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
  Sym, FSym: TSymbol;
  IdentExpr: TIdentExpr;
  FldExpr: TFieldAccessExpr;
  ProcDesc: TProceduralTypeDesc;
  ProcParam: TProcParamInfo;
  MD: TMethodDecl;
  MParam: TMethodParam;
  BaseType: TTypeDesc;
  Idx, K: Integer;
begin
  { @FuncName / @ProcName — if the inner is a bare identifier that
    resolves to a standalone function or procedure, build a procedural
    type matching the function's signature and return it.  This must run
    before AnalyseExpr, which would treat a zero-arg function reference
    as an implicit call. }
  if AExpr.Expr is TIdentExpr then
  begin
    IdentExpr := TIdentExpr(AExpr.Expr);
    FSym := FTable.Lookup(IdentExpr.Name);
    if (FSym <> nil) and (FSym.Kind in [skFunction, skProcedure]) then
    begin
      Idx := FProcIndex.IndexOf(IdentExpr.Name);
      if Idx < 0 then
        SemanticError(Format('Internal: function ''%s'' not in proc index',
          [IdentExpr.Name]), AExpr.Line, AExpr.Col);
      MD := TMethodDecl(FProcIndex.Objects[Idx]);
      ProcDesc := FTable.NewProceduralType('');
      for K := 0 to MD.Params.Count - 1 do
      begin
        MParam := TMethodParam(MD.Params.Items[K]);
        ProcParam := TProcParamInfo.Create;
        ProcParam.Name         := MParam.ParamName;
        ProcParam.TypeDesc     := MParam.ResolvedType;
        ProcParam.IsVarParam   := MParam.IsVarParam;
        ProcParam.IsConstParam := MParam.IsConstParam;
        ProcDesc.Params.Add(ProcParam);
      end;
      ProcDesc.ReturnType := MD.ResolvedReturnType;  { nil for procedure }
      Result := ProcDesc;
      IdentExpr.ResolvedType := ProcDesc;
      AExpr.ResolvedType := Result;
      Exit;
    end;
  end;

  { @Obj.MethodName — method pointer construction.  The inner expression is a
    TFieldAccessExpr whose base is a class instance and whose field name
    resolves to a method on that class.  Build a method-pointer type
    (IsMethodPtr = True) that pairs the method code with the object pointer.
    Two forms: Obj.Method (RecordName set, Base=nil) and Expr.Method (Base set). }
  if AExpr.Expr is TFieldAccessExpr then
  begin
    FldExpr  := TFieldAccessExpr(AExpr.Expr);
    { Determine base type from either RecordName or Base expression }
    if FldExpr.Base = nil then
    begin
      { Simple form: @VarName.MethodName — look up VarName }
      Sym := FTable.Lookup(FldExpr.RecordName);
      if (Sym <> nil) and
         (Sym.Kind in [skVariable, skParameter, skVarParameter]) and
         (Sym.TypeDesc <> nil) and (Sym.TypeDesc.Kind = tyClass) then
        BaseType := Sym.TypeDesc
      else
        BaseType := nil;
      if BaseType <> nil then
      begin
        FldExpr.RecordName := Sym.Name;  { normalise to declared casing }
        FldExpr.IsGlobal := Sym.IsGlobal;
      end;
    end
    else
      BaseType := AnalyseExpr(FldExpr.Base);
    if (BaseType <> nil) and (BaseType.Kind = tyClass) then
    begin
      MD := FindMethodDecl(TRecordTypeDesc(BaseType).Name, FldExpr.FieldName);
      if MD <> nil then
      begin
        FldExpr.IsClassAccess  := True;
        FldExpr.IsMethodCall   := False;  { @Obj.M is not a call }
        FldExpr.ResolvedMethod := MD;
        ProcDesc := FTable.NewProceduralType('');
        ProcDesc.IsMethodPtr := True;
        for K := 0 to MD.Params.Count - 1 do
        begin
          MParam := TMethodParam(MD.Params.Items[K]);
          ProcParam := TProcParamInfo.Create;
          ProcParam.Name         := MParam.ParamName;
          ProcParam.TypeDesc     := MParam.ResolvedType;
          ProcParam.IsVarParam   := MParam.IsVarParam;
          ProcParam.IsConstParam := MParam.IsConstParam;
          ProcDesc.Params.Add(ProcParam);
        end;
        ProcDesc.ReturnType := MD.ResolvedReturnType;
        FldExpr.ResolvedType := ProcDesc;
        AExpr.ResolvedType   := ProcDesc;
        Result               := ProcDesc;
        Exit;
      end;
    end;
  end;
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

procedure TSemanticAnalyser.ResolveProceduralTypeDef(ATD: TTypeDecl);
var
  Def: TProceduralTypeDef;
  ProcDesc: TProceduralTypeDesc;
  Sym: TSymbol;
  K: Integer;
  MParam: TMethodParam;
  ProcParam: TProcParamInfo;
  TSym: TSymbol;
begin
  Def := TProceduralTypeDef(ATD.Def);
  Sym := FTable.Lookup(ATD.Name);
  if (Sym = nil) or not (Sym.TypeDesc is TProceduralTypeDesc) then
    SemanticError(Format('Internal: procedural type ''%s'' not registered',
      [ATD.Name]), ATD.Line, ATD.Col);
  ProcDesc := TProceduralTypeDesc(Sym.TypeDesc);
  ProcDesc.IsMethodPtr := Def.IsMethodPtr;
  for K := 0 to Def.Params.Count - 1 do
  begin
    MParam := TMethodParam(Def.Params.Items[K]);
    TSym   := FTable.Lookup(MParam.TypeName);
    if (TSym = nil) or (TSym.Kind <> skType) then
      SemanticError(Format(
        'Unknown parameter type ''%s'' in procedural type ''%s''',
        [MParam.TypeName, ATD.Name]), ATD.Line, ATD.Col);
    MParam.ResolvedType := TSym.TypeDesc;
    ProcParam := TProcParamInfo.Create;
    ProcParam.Name         := MParam.ParamName;
    ProcParam.TypeDesc     := TSym.TypeDesc;
    ProcParam.IsVarParam   := MParam.IsVarParam;
    ProcParam.IsConstParam := MParam.IsConstParam;
    ProcDesc.Params.Add(ProcParam);
  end;
  if Def.IsFunction then
  begin
    TSym := FTable.Lookup(Def.ReturnTypeName);
    if (TSym = nil) or (TSym.Kind <> skType) then
      SemanticError(Format(
        'Unknown return type ''%s'' in procedural type ''%s''',
        [Def.ReturnTypeName, ATD.Name]), ATD.Line, ATD.Col);
    ProcDesc.ReturnType := TSym.TypeDesc;
  end;
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
  { Dynamic array element access: A[I] — 0-based, returns element type }
  if StrType.Kind = tyDynArray then
  begin
    IdxType := AnalyseExpr(AExpr.IndexExpr);
    if not IdxType.IsNumeric then
      SemanticError(
        Format('Dynamic array index must be numeric, got ''%s''', [IdxType.Name]),
        AExpr.Line, AExpr.Col);
    Result := TDynArrayTypeDesc(StrType).ElementType;
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

function TSemanticAnalyser.AnalyseIndirectFuncCallExpr(AExpr: TIndirectFuncCallExpr): TTypeDesc;
var
  CalleeType: TTypeDesc;
  ProcDesc:   TProceduralTypeDesc;
  I:          Integer;
begin
  CalleeType := AnalyseExpr(AExpr.CalleeExpr);
  if (CalleeType = nil) or (CalleeType.Kind <> tyProcedural) then
  begin
    SemanticError(
      'Expression is not callable — expected procedural type',
      AExpr.Line, AExpr.Col);
    Result := FTable.TypeInteger;
    Exit;
  end;
  ProcDesc := TProceduralTypeDesc(CalleeType);
  AExpr.ResolvedProcType := ProcDesc;
  for I := 0 to AExpr.Args.Count - 1 do
    AnalyseExpr(TASTExpr(AExpr.Args.Items[I]));
  if ProcDesc.ReturnType <> nil then
    Result := ProcDesc.ReturnType
  else
    Result := FTable.TypeInteger;
  AExpr.ResolvedType := Result;
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
  ALit.CharOrdValue := StrAt(ALit.Value, 0);
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
  AStmt.IsStringCase := SelType.IsString;
  if not (SelType.IsOrdinal or AStmt.IsStringCase) then
    SemanticError(
      Format('case selector must be ordinal or string type, got ''%s''',
        [SelType.Name]),
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
  AStmt.ArrayName := Sym.Name;  { normalise to declared casing }
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
  { Dynamic array subscript write: A[I] := V }
  if Sym.TypeDesc.Kind = tyDynArray then
  begin
    AStmt.IsGlobal          := Sym.IsGlobal;
    AStmt.ResolvedArrayType := Sym.TypeDesc;
    IdxType := AnalyseExpr(AStmt.IndexExpr);
    if not IdxType.IsNumeric then
      SemanticError('Dynamic array index must be numeric', AStmt.Line, AStmt.Col);
    ValType := AnalyseExpr(AStmt.ValueExpr);
    CheckTypesMatch(TDynArrayTypeDesc(Sym.TypeDesc).ElementType, ValType,
      Format('''%s'' element', [AStmt.ArrayName]), AStmt.Line, AStmt.Col);
    Exit;
  end;
  if Sym.TypeDesc.Kind <> tyStaticArray then
    SemanticError(
      Format('''%s'' is not a static array or dynamic array', [AStmt.ArrayName]),
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
