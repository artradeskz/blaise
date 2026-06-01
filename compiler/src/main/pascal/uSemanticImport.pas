{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ uSemanticImport — registers a previously-exported TUnitInterface into
  a TSymbolTable, mirroring the interface-section side-effects of
  uSemantic.AnalyseUnitForExport without re-running semantic on the
  source unit.

  Pipeline position:
    uSemantic.AnalyseUnitForExport(DepUnit, FTable)   ← legacy path
    uSemanticImport.ImportUnitInterface(Iface, FTable) ← new path

  Both end with the same TSymbolTable state for downstream consumers
  (semantic of the main unit, then codegen).

  Scope of this commit (6c-A):
    * Constants — IntVal/StrVal already evaluated, just register.
    * Variables — interface-section global vars (IsGlobal=True).
    * Enumeration types — and their members as skConstant.
    * Set types over enum bases.
    * Type aliases (simple name → existing type).
    * Free routines — skFunction/skProcedure with resolved params/return.

  Out of scope (deferred to 6c-B/C):
    * Class & record types — vtable, parent, fields, interface impls.
    * Procedural types.
    * Generics.
    * Inline-body wiring (codegen still walks bodies). }

unit uSemanticImport;

interface

uses
  Classes, Contnrs, SysUtils, uAST, uSymbolTable, uUnitInterface,
  uSemantic;

type
  EImportError = class(Exception);

{ Register everything in AIface into ATable.  ATable must already have
  the dependencies of AIface (the units in AIface.UsedUnits) imported,
  so cross-unit type references can be resolved by simple name lookup
  against ATable.  Builtin types must also be present (RegisterBuiltins).

  When ASemantic is non-nil, free routines are *also* pushed into
  the analyser's FProcIndex via RegisterImportedRoutine — needed
  because AnalyseFuncCall looks up callees in that index rather
  than going through the symbol table.  The synthesised
  TMethodDecls are owned by ATable.OwnImportedDecl so the symbol
  table's lifetime covers them. }
procedure ImportUnitInterface(AIface: TUnitInterface;
                              ATable: TSymbolTable;
                              ASemantic: TSemanticAnalyser = nil);

implementation

{ ----- Type-ref resolution -------------------------------------- }

{ Resolve a TQualTypeRef to a TTypeDesc by name lookup.  After topo-
  order import, every referenced symbol is already in ATable. }
function ResolveTypeName(const ATypeName: string; ATable: TSymbolTable): TTypeDesc;
begin
  if ATypeName = '' then begin Result := nil; Exit; end;
  Result := ATable.FindType(ATypeName);
end;

{ ----- Type-entry registration ---------------------------------- }

procedure RegisterEnum(AEntry: TTypeEntry; ATable: TSymbolTable;
                       const AUnitName: string);
var
  EnumDef:  TEnumTypeDef;
  EnumDesc: TEnumTypeDesc;
  Sym, MSym: TSymbol;
  K: Integer;
  MName: string;
begin
  EnumDef  := TEnumTypeDef(AEntry.Def);
  EnumDesc := ATable.NewEnumType(AEntry.Name);
  for K := 0 to EnumDef.Members.Count - 1 do
  begin
    MName := EnumDef.Members.Strings[K];
    EnumDesc.Members.Add(MName);
    MSym  := TSymbol.Create(MName, skConstant, EnumDesc);
    MSym.ConstValue := EnumDef.OrdinalAt(K);
    MSym.OwningUnit := AUnitName;
    if not ATable.Define(MSym) then MSym.Free;
  end;
  Sym := TSymbol.Create(AEntry.Name, skType, EnumDesc);
  Sym.OwningUnit := AUnitName;
  if not ATable.Define(Sym) then Sym.Free;
end;

procedure RegisterSet(AEntry: TTypeEntry; ATable: TSymbolTable;
                      const AUnitName: string);
var
  SetDef:   TSetTypeDef;
  BaseSym:  TSymbol;
  SetDesc:  TSetTypeDesc;
  Sym:      TSymbol;
begin
  SetDef := TSetTypeDef(AEntry.Def);
  BaseSym := ATable.Lookup(SetDef.BaseTypeName);
  if (BaseSym = nil) or (BaseSym.Kind <> skType) or
     not (BaseSym.TypeDesc is TEnumTypeDesc) then
    raise EImportError.CreateFmt(
      'Set %s base ''%s'' is not an enum (import order?)',
      [AEntry.Name, SetDef.BaseTypeName]);
  SetDesc := ATable.NewSetType(AEntry.Name, TEnumTypeDesc(BaseSym.TypeDesc));
  Sym := TSymbol.Create(AEntry.Name, skType, SetDesc);
  Sym.OwningUnit := AUnitName;
  if not ATable.Define(Sym) then Sym.Free;
end;

{ Resolve a class parent reference into the symbol table.  Returns nil
  if AEntry has no parent (root) or if the parent name resolves to
  something that is not a class. }
{ Add or override a single vtable slot on ART for ASig.
  Virtual → AddVTableSlot, Override → OverrideVTableSlot at the
  inherited slot.  Static methods are no-ops on the descriptor side
  (they live as direct-call symbols only). }
procedure RegisterClassMethod(ART: TRecordTypeDesc; ASig: TRoutineSig);
var
  Slot:     Integer;
  ImplName: string;
begin
  if (not ASig.IsVirtual) and (not ASig.IsOverride) then Exit;
  if ASig.ResolvedQbeName = '' then Exit;
  ImplName := '$' + ASig.ResolvedQbeName;

  if ASig.IsVirtual then
    ART.AddVTableSlot(ASig.Name, ImplName)
  else { IsOverride }
  begin
    Slot := ART.FindVTableSlot(ASig.Name);
    if Slot >= 0 then
      ART.OverrideVTableSlot(Slot, ImplName);
    { If the slot wasn't found, the override targets a method only
      reachable through a grand-parent we haven't fully copied —
      treat as a no-op for now; class-level test will catch this. }
  end;
end;

function ResolveParentClassByName(const AParentName: string;
                                  ATable: TSymbolTable): TRecordTypeDesc;
var
  Sym: TSymbol;
begin
  Result := nil;
  if AParentName = '' then Exit;
  Sym := ATable.Lookup(AParentName);
  if (Sym = nil) or (Sym.Kind <> skType) then Exit;
  if Sym.TypeDesc is TRecordTypeDesc then
    Result := TRecordTypeDesc(Sym.TypeDesc);
end;

{ Build the comma-separated '1'/'0' var-flag string AddMethod expects.
  '1' for var params, '0' otherwise.  Matches the semantic-side
  string built in AnalyseTypeDecls pass-2 for interfaces. }
function ParamVarFlags(AMethod: TMethodDecl): string;
var
  K: Integer;
  P: TMethodParam;
begin
  Result := '';
  for K := 0 to AMethod.Params.Count - 1 do
  begin
    P := TMethodParam(AMethod.Params.Items[K]);
    if K > 0 then Result := Result + ',';
    if P.IsVarParam then Result := Result + '1' else Result := Result + '0';
  end;
end;

procedure RegisterInterface(AEntry: TTypeEntry; ATable: TSymbolTable;
                            const AUnitName: string);
var
  IntfDef:  TInterfaceTypeDef;
  IntfDesc: TInterfaceTypeDesc;
  Sym:      TSymbol;
  ParentSym: TSymbol;
  M:        TMethodDecl;
  I:        Integer;
begin
  IntfDef  := TInterfaceTypeDef(AEntry.Def);
  IntfDesc := ATable.NewInterfaceType(AEntry.Name);

  Sym := TSymbol.Create(AEntry.Name, skType, IntfDesc);
  Sym.OwningUnit := AUnitName;
  if not ATable.Define(Sym) then
  begin
    Sym.Free;
    Exit;
  end;

  if IntfDef.ParentName <> '' then
  begin
    ParentSym := ATable.Lookup(IntfDef.ParentName);
    if (ParentSym <> nil) and (ParentSym.TypeDesc is TInterfaceTypeDesc) then
    begin
      IntfDesc.Parent := TInterfaceTypeDesc(ParentSym.TypeDesc);
      { Inherit parent methods so FindMethod walks transparently. }
      for I := 0 to IntfDesc.Parent.MethodCount - 1 do
        IntfDesc.AddMethod(
          IntfDesc.Parent.MethodName(I),
          IntfDesc.Parent.MethodReturnTypeName(I),
          IntfDesc.Parent.MethodParamVarFlagsStr(I));
    end;
  end;

  for I := 0 to IntfDef.Methods.Count - 1 do
  begin
    M := TMethodDecl(IntfDef.Methods.Items[I]);
    IntfDesc.AddMethod(M.Name, M.ReturnTypeName, ParamVarFlags(M));
  end;
end;

procedure RegisterClass(AEntry: TTypeEntry; ATable: TSymbolTable;
                        const AUnitName: string);
var
  ClassDef: TClassTypeDef;
  RT:       TRecordTypeDesc;
  ParentRT: TRecordTypeDesc;
  ParentName: string;
  Sym:      TSymbol;
  FldSym:   TSymbol;
  FldDecl:  TFieldDecl;
  FldInfo:  TFieldInfo;
  I, J:     Integer;
begin
  ClassDef := TClassTypeDef(AEntry.Def);
  RT := ATable.NewClassType(AEntry.Name);

  Sym := TSymbol.Create(AEntry.Name, skType, RT);
  Sym.OwningUnit := AUnitName;
  if not ATable.Define(Sym) then
  begin
    Sym.Free;
    Exit;  { duplicate; skip — caller's responsibility }
  end;

  { Parent resolution mirrors uSemantic.AnalyseTypeDecls pass-2:
    explicit ParentName → look it up; empty + not TObject → implicit
    TObject.  The generic-interface-as-parent special case is not
    handled here; that's a class-import edge case for 6c-C generics. }
  ParentName := ClassDef.ParentName;
  if ParentName <> '' then
    ParentRT := ResolveParentClassByName(ParentName, ATable)
  else if AEntry.Name <> 'TObject' then
  begin
    Sym := ATable.Lookup('TObject');
    if (Sym <> nil) and (Sym.TypeDesc is TRecordTypeDesc) then
      ParentRT := TRecordTypeDesc(Sym.TypeDesc)
    else
      ParentRT := nil;
  end
  else
    ParentRT := nil;

  if ParentRT <> nil then
  begin
    RT.Parent := ParentRT;
    RT.CopyVTableFrom(ParentRT);
    { Inherit parent fields so offsets continue past the parent. }
    for I := 0 to ParentRT.Fields.Count - 1 do
    begin
      FldInfo := TFieldInfo(ParentRT.Fields.Items[I]);
      RT.AddField(FldInfo.Name, FldInfo.TypeDesc);
    end;
  end;

  { Own fields. }
  for I := 0 to ClassDef.Fields.Count - 1 do
  begin
    FldDecl := TFieldDecl(ClassDef.Fields.Items[I]);
    FldSym  := ATable.Lookup(FldDecl.TypeName);
    if (FldSym = nil) or (FldSym.Kind <> skType) then
      raise EImportError.CreateFmt(
        'Class %s field type ''%s'' unresolved',
        [AEntry.Name, FldDecl.TypeName]);
    for J := 0 to FldDecl.Names.Count - 1 do
      RT.AddField(FldDecl.Names.Strings[J], FldSym.TypeDesc);
  end;

  { Methods: walk TRoutineSig list; for virtual/override, register
    vtable slots.  ResolvedQbeName comes pre-mangled from semantic,
    so ImplName is '$' + ResolvedQbeName.  The MethodName used as
    the vtable lookup key is just the unqualified routine name; for
    overloaded methods the mangled suffix is included in
    ResolvedQbeName but the lookup-key dance is left to a follow-up
    (overloaded class methods are not in the 6c-B happy path). }
  for I := 0 to AEntry.Methods.Count - 1 do
    RegisterClassMethod(RT, TRoutineSig(AEntry.Methods.Items[I]));

  { Interface implements list — names are 'Unit.Type' (cross-unit) or
    just 'Type' (local).  We strip any 'Unit.' prefix since the
    flat symbol-table namespace doesn't carry unit qualification. }
  for I := 0 to AEntry.Implements.Count - 1 do
  begin
    ParentName := AEntry.Implements.Strings[I];
    J := Pos('.', ParentName);
    if J > 0 then ParentName := Copy(ParentName, J + 1, Length(ParentName) - J);
    Sym := ATable.Lookup(ParentName);
    if (Sym <> nil) and (Sym.TypeDesc is TInterfaceTypeDesc) then
      RT.AddImplements(TInterfaceTypeDesc(Sym.TypeDesc));
  end;

  { Class attributes.  uSemanticExport currently copies the raw
    attribute names ('Threaded', not 'ThreadedAttribute') — but
    AddClassAttribute downstream wants the resolved-name form.
    For now, append the literal 'Attribute' suffix when missing;
    this works for the common Delphi-style attribute convention
    and matches what the symbol table receives from semantic.
    A cleaner fix is to have uSemanticExport copy resolved names
    out of the source TRecordTypeDesc.ClassAttributes — left as
    an audit item. }
  for I := 0 to AEntry.Attributes.Count - 1 do
  begin
    ParentName := AEntry.Attributes.Strings[I];
    if (Length(ParentName) < 9) or
       (Copy(ParentName, Length(ParentName) - 8, 9) <> 'Attribute') then
      ParentName := ParentName + 'Attribute';
    RT.AddClassAttribute(ParentName);
  end;
end;

procedure RegisterRecord(AEntry: TTypeEntry; ATable: TSymbolTable;
                         const AUnitName: string);
var
  RecDef:   TRecordTypeDef;
  RecDesc:  TRecordTypeDesc;
  Sym, FldSym: TSymbol;
  I, J:     Integer;
  FldDecl:  TFieldDecl;
  FldType:  TTypeDesc;
begin
  RecDef  := TRecordTypeDef(AEntry.Def);
  RecDesc := ATable.NewRecordType(AEntry.Name);
  RecDesc.IsPacked := RecDef.IsPacked;

  { Pre-register so self-referential pointer fields (rare in records,
    common in classes) can resolve against the in-progress type. }
  Sym := TSymbol.Create(AEntry.Name, skType, RecDesc);
  Sym.OwningUnit := AUnitName;
  if not ATable.Define(Sym) then
  begin
    Sym.Free;
    Exit;  { duplicate — caller responsibility }
  end;

  for I := 0 to RecDef.Fields.Count - 1 do
  begin
    FldDecl := TFieldDecl(RecDef.Fields.Items[I]);
    FldSym  := ATable.Lookup(FldDecl.TypeName);
    if (FldSym = nil) or (FldSym.Kind <> skType) then
      raise EImportError.CreateFmt(
        'Record %s field type ''%s'' unresolved',
        [AEntry.Name, FldDecl.TypeName]);
    FldType := FldSym.TypeDesc;
    for J := 0 to FldDecl.Names.Count - 1 do
      RecDesc.AddField(FldDecl.Names.Strings[J], FldType);
  end;
end;

procedure RegisterAlias(AEntry: TTypeEntry; ATable: TSymbolTable;
                        const AUnitName: string);
var
  AliasDef:   TTypeAliasDef;
  AliasName:  string;
  BaseSym:    TSymbol;
  BaseType:   TTypeDesc;
  AliasDesc:  TTypeDesc;
  Sym:        TSymbol;
begin
  AliasDef  := TTypeAliasDef(AEntry.Def);
  AliasName := AliasDef.TypeName;
  if (Length(AliasName) > 0) and (AliasName[1] = '^') then
  begin
    BaseSym  := ATable.Lookup(Copy(AliasName, 2, Length(AliasName) - 1));
    BaseType := nil;
    if (BaseSym <> nil) and (BaseSym.Kind = skType) then
      BaseType := BaseSym.TypeDesc;
    AliasDesc := ATable.NewPointerType(AEntry.Name, BaseType);
  end
  else
  begin
    BaseSym := ATable.Lookup(AliasName);
    if (BaseSym = nil) or (BaseSym.Kind <> skType) then
      raise EImportError.CreateFmt(
        'Type alias %s = %s: base not found', [AEntry.Name, AliasName]);
    AliasDesc := BaseSym.TypeDesc;
  end;
  Sym := TSymbol.Create(AEntry.Name, skType, AliasDesc);
  Sym.OwningUnit := AUnitName;
  if not ATable.Define(Sym) then Sym.Free;
end;

procedure RegisterTypes(AIface: TUnitInterface; ATable: TSymbolTable);
var
  I: Integer;
  Entry: TTypeEntry;
begin
  for I := 0 to AIface.Types.Count - 1 do
  begin
    Entry := TTypeEntry(AIface.Types.Items[I]);

    { Generic type templates — register the AST template so the
      consumer's FindTypeOrInstantiate path can clone-and-substitute
      on demand.  Matches uSemantic.AnalyseTypeDecls pass-1 for
      TGenericTypeDef / TGenericInterfaceDef. }
    if Entry.IsGeneric or (Entry.Def is TGenericInterfaceDef) then
    begin
      ATable.RegisterGeneric(Entry.Name, Entry.Def);
      Continue;
    end;

    if Entry.Def is TEnumTypeDef then
      RegisterEnum(Entry, ATable, AIface.Name)
    else if Entry.Def is TSetTypeDef then
      RegisterSet(Entry, ATable, AIface.Name)
    else if Entry.Def is TTypeAliasDef then
      RegisterAlias(Entry, ATable, AIface.Name)
    else if Entry.Def is TInterfaceTypeDef then
      RegisterInterface(Entry, ATable, AIface.Name)
    else if Entry.Def is TClassTypeDef then
      RegisterClass(Entry, ATable, AIface.Name)
    else if Entry.Def is TRecordTypeDef then
      RegisterRecord(Entry, ATable, AIface.Name)
    else
      raise EImportError.CreateFmt(
        'Type %s.%s: import of %s not yet implemented',
        [AIface.Name, Entry.Name, Entry.Def.ClassName]);
  end;
end;

{ ----- Const registration --------------------------------------- }

procedure RegisterConsts(AIface: TUnitInterface; ATable: TSymbolTable);
var
  I: Integer;
  Entry: TConstEntry;
  Sym: TSymbol;
  TypeDesc: TTypeDesc;
begin
  for I := 0 to AIface.Consts.Count - 1 do
  begin
    Entry := TConstEntry(AIface.Consts.Items[I]);
    TypeDesc := ResolveTypeName(Entry.TypeRef.TypeName, ATable);

    { Untyped const: derive a builtin TTypeDesc from the literal kind.
      Matches the shape AnalyseConstDecls registers — see uSemantic. }
    if TypeDesc = nil then
    begin
      if Entry.Decl.IsString then
        TypeDesc := ATable.FindType('string')
      else if Entry.Decl.IsFloat then
        TypeDesc := ATable.FindType('Double')
      else
        TypeDesc := ATable.FindType('Integer');
    end;

    Sym := TSymbol.Create(Entry.Decl.Name, skConstant, TypeDesc);
    Sym.ConstValue  := Entry.Decl.IntVal;
    Sym.ConstString := Entry.Decl.StrVal;
    Sym.OwningUnit  := AIface.Name;
    if not ATable.Define(Sym) then
      Sym.Free;  { duplicate — silently skip }
  end;
end;

{ ----- Var registration ----------------------------------------- }

procedure RegisterVars(AIface: TUnitInterface; ATable: TSymbolTable);
var
  I: Integer;
  Entry: TVarEntry;
  Sym: TSymbol;
  TypeDesc: TTypeDesc;
begin
  for I := 0 to AIface.Vars.Count - 1 do
  begin
    Entry := TVarEntry(AIface.Vars.Items[I]);
    TypeDesc := ResolveTypeName(Entry.TypeRef.TypeName, ATable);
    if TypeDesc = nil then
      raise EImportError.CreateFmt(
        'Var %s.%s: type %s unresolved',
        [AIface.Name, Entry.Name, Entry.TypeRef.TypeName]);
    Sym := TSymbol.Create(Entry.Name, skVariable, TypeDesc);
    Sym.IsGlobal := True;
    Sym.OwningUnit := AIface.Name;
    if not ATable.Define(Sym) then
      Sym.Free;
  end;
end;

{ ----- Routine registration ------------------------------------- }

{ Build a TParamDesc for the symbol table from a cloned TMethodParam.
  Param types must already be registered in ATable (caller imported
  the dep, or it's a builtin). }
function BuildParamDesc(AParam: TMethodParam; ATable: TSymbolTable): TParamDesc;
var
  Sym: TSymbol;
begin
  Result := TParamDesc.Create;
  Result.Name     := AParam.ParamName;
  Result.IsConst  := AParam.IsConstParam;
  Result.IsVar    := AParam.IsVarParam;
  Sym := ATable.Lookup(AParam.TypeName);
  if (Sym <> nil) and (Sym.Kind = skType) then
    Result.TypeDesc := Sym.TypeDesc;
  { Unresolved param type leaves TypeDesc nil; downstream call-site
    resolution would catch this — but for the cases in 6c-A scope we
    expect all param types to resolve. }
end;

{ Synthesise a TMethodDecl from a TRoutineSig + its return-type
  qual-ref, sufficient for downstream call-site analysis: param
  list with ResolvedType set, ResolvedReturnType, ResolvedQbeName,
  IsOverload.  Body stays nil.  AOwningUnit is the iface's unit name
  — combined with the routine's bare Name through MangleUnitPrefix
  to produce ResolvedQbeName, so the call site emits the same global
  symbol the exporting unit defines. }
function SynthesiseMethodDecl(ASig: TRoutineSig;
                              const AOwningUnit: string;
                              ATable: TSymbolTable): TMethodDecl;
var
  J:     Integer;
  Param: TMethodParam;
  PSyn:  TMethodParam;
  Sym:   TSymbol;
begin
  Result := TMethodDecl.Create;
  Result.Name           := ASig.Name;
  Result.OwningUnit     := AOwningUnit;
  Result.ReturnTypeName := ASig.ReturnType.TypeName;
  Result.ResolvedReturnType :=
    ResolveTypeName(ASig.ReturnType.TypeName, ATable);
  Result.ResolvedQbeName := MangleUnitPrefix(AOwningUnit) + ASig.Name;
  for J := 0 to ASig.Params.Count - 1 do
  begin
    Param := TMethodParam(ASig.Params.Items[J]);
    PSyn := TMethodParam.Create;
    PSyn.ParamName    := Param.ParamName;
    PSyn.TypeName     := Param.TypeName;
    PSyn.IsVarParam   := Param.IsVarParam;
    PSyn.IsConstParam := Param.IsConstParam;
    PSyn.IsOpenArray  := Param.IsOpenArray;
    Sym := ATable.Lookup(Param.TypeName);
    if (Sym <> nil) and (Sym.Kind = skType) then
      PSyn.ResolvedType := Sym.TypeDesc;
    Result.Params.Add(PSyn);
  end;
end;

procedure RegisterRoutines(AIface: TUnitInterface; ATable: TSymbolTable;
                           ASemantic: TSemanticAnalyser);
var
  I, J: Integer;
  Sig: TRoutineSig;
  Sym: TSymbol;
  RetType: TTypeDesc;
  Param: TMethodParam;
  PDesc: TParamDesc;
  MDecl: TMethodDecl;
begin
  for I := 0 to AIface.Routines.Count - 1 do
  begin
    Sig := TRoutineSig(AIface.Routines.Items[I]);

    if Sig.IsFunction then
    begin
      RetType := ResolveTypeName(Sig.ReturnType.TypeName, ATable);
      Sym := TSymbol.Create(Sig.Name, skFunction, RetType);
    end
    else
      Sym := TSymbol.Create(Sig.Name, skProcedure, nil);

    Sym.IsOverload := False;

    for J := 0 to Sig.Params.Count - 1 do
    begin
      Param := TMethodParam(Sig.Params.Items[J]);
      PDesc := BuildParamDesc(Param, ATable);
      Sym.Params.Add(PDesc);
    end;

    { Build a synthetic TMethodDecl so call-site analysis can resolve
      via FProcIndex.  Owned by the symbol table to outlive imports. }
    if ASemantic <> nil then
    begin
      MDecl := SynthesiseMethodDecl(Sig, AIface.Name, ATable);
      ATable.OwnImportedDecl(MDecl);
      Sym.Decl := MDecl;
      ASemantic.RegisterImportedRoutine(Sig.Name, MDecl);
    end;

    Sym.OwningUnit := AIface.Name;
    if not ATable.Define(Sym) then
      Sym.Free;
  end;
end;

{ ----- Top-level ------------------------------------------------ }

procedure RegisterGenericRoutines(AIface: TUnitInterface; ATable: TSymbolTable);
var
  I: Integer;
  G: TGenericBody;
begin
  for I := 0 to AIface.GenericBodies.Count - 1 do
  begin
    G := TGenericBody(AIface.GenericBodies.Items[I]);
    if G.IsType then Continue;
    if G.MethodDecl = nil then Continue;
    ATable.RegisterGenericRoutine(G.Name, G.MethodDecl);
  end;
end;

procedure ImportUnitInterface(AIface: TUnitInterface;
                              ATable: TSymbolTable;
                              ASemantic: TSemanticAnalyser = nil);
var
  Saved: string;
begin
  { Belt-and-braces: even though each Register* now sets OwningUnit
    on its created TSymbols explicitly (task #44 step 1), also set
    the table's auto-tag context so any helper that grows a new
    Define site picks up OwningUnit by default.  Restored on exit. }
  Saved := ATable.DefineOwningUnit;
  ATable.DefineOwningUnit := AIface.Name;
  try
    { Types FIRST — consts, vars, and routine params look up against
      the symbol table by name. }
    RegisterTypes  (AIface, ATable);
    RegisterConsts (AIface, ATable);
    RegisterVars   (AIface, ATable);
    RegisterRoutines(AIface, ATable, ASemantic);
    RegisterGenericRoutines(AIface, ATable);
  finally
    ATable.DefineOwningUnit := Saved;
  end;
end;

end.
