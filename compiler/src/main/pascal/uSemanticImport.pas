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
  uSemantic, uStrCompat;

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

{ Return the bare type name from a possibly unit-qualified name.  The
  unit qualifier may itself be dotted (e.g. 'blaise.codegen.ICodeGen'),
  so everything up to and including the LAST '.' is removed.  Names with
  no '.' are returned unchanged.  Uses StrAt (0-based) per house style. }
function StripUnitQualifier(const AName: string): string;
var
  I, LastDot: Integer;
begin
  LastDot := -1;
  for I := 0 to Length(AName) - 1 do
    if StrAt(AName, I) = Ord('.') then
      LastDot := I;
  if LastDot < 0 then
    Result := AName
  else
    Result := StrCopyTail(AName, LastDot + 1);
end;

{ Resolve a TQualTypeRef to a TTypeDesc by name lookup.  After topo-
  order import, every referenced symbol is already in ATable. }
function ResolveTypeName(const ATypeName: string; ATable: TSymbolTable): TTypeDesc;
begin
  if ATypeName = '' then begin Result := nil; Exit; end;
  Result := ATable.FindType(ATypeName);
end;

{ Resolve an inline type name that is not a registered symbol.
  Handles:
    - '^BaseName'         → pointer to BaseName
    - 'array[L..H] of E' → static array
    - 'array of E'        → dynamic array
    - 'class of X'        → metaclass
  Returns nil if the pattern is not recognised. }
function ResolveInlineTypeName(const ATypeName: string;
                               ATable: TSymbolTable): TTypeDesc;
var
  DotDot, OfPos: Integer;
  LowStr, HighStr, ElemName: string;
  Lo, Hi: Integer;
  ElemSym: TSymbol;
  BaseSym: TSymbol;
begin
  Result := nil;
  if Length(ATypeName) < 2 then Exit;

  if StrAt(ATypeName, 0) = Ord('^') then
  begin
    BaseSym := ATable.Lookup(StrCopyTail(ATypeName, 1));
    if (BaseSym <> nil) and (BaseSym.Kind = skType) then
      Result := ATable.NewPointerType('', BaseSym.TypeDesc)
    else
      Result := ATable.NewPointerType('', nil);
    Exit;
  end;

  if StrHead(ATypeName, 6) = 'array[' then
  begin
    DotDot := StrPos('..', ATypeName);
    OfPos  := StrPos('] of ', ATypeName);
    if (DotDot < 0) or (OfPos < 0) then Exit;
    LowStr   := StrCopyTail(StrHead(ATypeName, DotDot), 6);
    HighStr  := StrCopyTail(StrHead(ATypeName, OfPos), DotDot + 2);
    ElemName := StrCopyTail(ATypeName, OfPos + 5);
    Lo := StrToInt(LowStr);
    Hi := StrToInt(HighStr);
    ElemSym := ATable.Lookup(ElemName);
    if (ElemSym <> nil) and (ElemSym.Kind = skType) then
      Result := ATable.NewStaticArrayType(ElemSym.TypeDesc, Lo, Hi);
    Exit;
  end;

  if (Length(ATypeName) > 9) and (StrHead(ATypeName, 9) = 'array of ') then
  begin
    ElemName := StrCopyTail(ATypeName, 9);
    ElemSym := ATable.Lookup(ElemName);
    if (ElemSym <> nil) and (ElemSym.Kind = skType) then
      Result := ATable.NewDynArrayType(ElemSym.TypeDesc);
    Exit;
  end;

  if (Length(ATypeName) > 9) and (StrHead(ATypeName, 9) = 'class of ') then
  begin
    BaseSym := ATable.Lookup(StrCopyTail(ATypeName, 9));
    if (BaseSym <> nil) and (BaseSym.Kind = skType) then
      Result := ATable.NewMetaClassType('', BaseSym.TypeDesc)
    else
      Result := ATable.NewMetaClassType('', nil);
    Exit;
  end;
end;

{ Resolve a type-name string from a cached iface entry to a TTypeDesc,
  trying every avenue the source-compile path has: a registered symbol,
  an inline type pattern ('^T', 'array of T', etc.), and finally the
  semantic analyser's on-demand resolver, which instantiates generics
  ('TList<TFoo>') and synthesises anonymous array/set types.  The last
  step is only available when ASemantic is non-nil (the Blaise.pas
  prebuilt-iface path always passes it); without it generic-instance
  field types from a .bif cannot be resolved. }
function ResolveImportTypeName(const ATypeName: string;
                               ATable: TSymbolTable;
                               ASemantic: TSemanticAnalyser): TTypeDesc;
var
  Sym: TSymbol;
begin
  Result := nil;
  if ATypeName = '' then Exit;
  Sym := ATable.Lookup(ATypeName);
  if (Sym <> nil) and (Sym.Kind = skType) then
  begin
    Result := Sym.TypeDesc;
    Exit;
  end;
  Result := ResolveInlineTypeName(ATypeName, ATable);
  if Result <> nil then Exit;
  if ASemantic <> nil then
    Result := ASemantic.ResolveImportedTypeName(ATypeName);
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
    if not ATable.Define(MSym) then MSym.Free();
  end;
  Sym := TSymbol.Create(AEntry.Name, skType, EnumDesc);
  Sym.OwningUnit := AUnitName;
  if not ATable.Define(Sym) then Sym.Free();
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
  if not ATable.Define(Sym) then Sym.Free();
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
  ImplName: string;
begin
  { Place every vtable-carrying method at its AUTHORITATIVE slot index,
    taken from the exported .bif (ASig.VTableSlot).  The earlier append-only
    approach assumed the .bif method order matched the source-side slot
    order, which it does not: the exporter lists newly-introduced virtual
    methods first and parent overrides last, and a non-virtual constructor
    named 'Create' takes an implicit slot (metaclass dispatch) that the
    append path skipped entirely.  Skipping it dropped Create's slot and
    shifted every later virtual method down by one, so a Cls.Create call or
    a descendant's virtual dispatch landed on the wrong method.  Honouring
    VTableSlot directly reproduces the exact source-side layout regardless
    of .bif ordering and is robust to import order.

    VTableSlot < 0 means the method does not occupy a vtable slot (static /
    non-dispatch), so there is nothing to place. }
  if ASig.VTableSlot < 0 then Exit;
  if ASig.ResolvedQbeName = '' then Exit;
  ImplName := '$' + ASig.ResolvedQbeName;
  ART.SetVTableSlotAt(ASig.VTableSlot, ASig.Name, ImplName);
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

{ Return AName in the casing of the matching method declaration, or AName
  unchanged when no declaration matches — emitted method symbols are
  case-sensitive at link time. }
function DeclaredMethodCaseOf(AMethods: TObjectList; const AName: string): string;
var
  I: Integer;
begin
  Result := AName;
  if AMethods = nil then Exit;
  for I := 0 to AMethods.Count - 1 do
    if SameText(TMethodDecl(AMethods.Items[I]).Name, AName) then
      Exit(TMethodDecl(AMethods.Items[I]).Name);
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
  PropDecl: TPropertyDecl;
  PropInfo: TPropertyInfo;
  PropSym:  TSymbol;
  PropType: TTypeDesc;
begin
  IntfDef  := TInterfaceTypeDef(AEntry.Def);

  Sym := ATable.Lookup(AEntry.Name);
  if (Sym <> nil) and (Sym.Kind = skType) and (Sym.TypeDesc is TInterfaceTypeDesc) then
    IntfDesc := TInterfaceTypeDesc(Sym.TypeDesc)
  else
  begin
    IntfDesc := ATable.NewInterfaceType(AEntry.Name);
    Sym := TSymbol.Create(AEntry.Name, skType, IntfDesc);
    Sym.OwningUnit := AUnitName;
    if not ATable.Define(Sym) then
    begin
      Sym.Free();
      Exit;
    end;
  end;

  if IntfDef.ParentName <> '' then
  begin
    ParentSym := ATable.Lookup(IntfDef.ParentName);
    if (ParentSym <> nil) and (ParentSym.TypeDesc is TInterfaceTypeDesc) then
    begin
      IntfDesc.Parent := TInterfaceTypeDesc(ParentSym.TypeDesc);
      { Inherit parent methods so FindMethod walks transparently. }
      for I := 0 to IntfDesc.Parent.MethodCount() - 1 do
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

  { Register interface properties.  Accessors are always interface methods
    (interfaces have no fields); the type resolves against the importing
    table like class property types do. }
  for I := 0 to IntfDef.Properties.Count - 1 do
  begin
    PropDecl := TPropertyDecl(IntfDef.Properties.Items[I]);
    if IntfDesc.FindProperty(PropDecl.Name) <> nil then Continue;
    PropInfo := TPropertyInfo.Create();
    PropInfo.Name := PropDecl.Name;
    PropSym := ATable.Lookup(PropDecl.TypeName);
    if (PropSym <> nil) and (PropSym.Kind = skType) then
      PropInfo.TypeDesc := PropSym.TypeDesc
    else
    begin
      PropType := ResolveInlineTypeName(PropDecl.TypeName, ATable);
      if PropType <> nil then
        PropInfo.TypeDesc := PropType;
    end;
    if PropDecl.ReadName <> '' then
    begin
      if IntfDesc.MethodIndex(PropDecl.ReadName) >= 0 then
        PropInfo.ReadMethod :=
          IntfDesc.MethodName(IntfDesc.MethodIndex(PropDecl.ReadName))
      else
        PropInfo.ReadMethod := PropDecl.ReadName;
    end;
    if PropDecl.WriteName <> '' then
    begin
      if IntfDesc.MethodIndex(PropDecl.WriteName) >= 0 then
        PropInfo.WriteMethod :=
          IntfDesc.MethodName(IntfDesc.MethodIndex(PropDecl.WriteName))
      else
        PropInfo.WriteMethod := PropDecl.WriteName;
    end;
    IntfDesc.AddProperty(PropInfo);
  end;
end;

procedure RegisterClass(AEntry: TTypeEntry; ATable: TSymbolTable;
                        const AUnitName: string;
                        ASemantic: TSemanticAnalyser = nil);
var
  ClassDef: TClassTypeDef;
  RT:       TRecordTypeDesc;
  ParentRT: TRecordTypeDesc;
  ParentName: string;
  Sym:      TSymbol;
  FldSym:   TSymbol;
  FldDecl:  TFieldDecl;
  FldType:  TTypeDesc;
  FldInfo:  TFieldInfo;
  MDecl:    TMethodDecl;
  PropDecl: TPropertyDecl;
  PropInfo: TPropertyInfo;
  I, J:     Integer;
begin
  ClassDef := TClassTypeDef(AEntry.Def);

  Sym := ATable.Lookup(AEntry.Name);
  if (Sym <> nil) and (Sym.Kind = skType) and (Sym.TypeDesc is TRecordTypeDesc) then
    RT := TRecordTypeDesc(Sym.TypeDesc)
  else
  begin
    RT := ATable.NewClassType(AEntry.Name);
    Sym := TSymbol.Create(AEntry.Name, skType, RT);
    Sym.OwningUnit := AUnitName;
    if not ATable.Define(Sym) then
    begin
      Sym.Free();
      Exit;
    end;
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
    FldType := ResolveImportTypeName(FldDecl.TypeName, ATable, ASemantic);
    if FldType = nil then
      raise EImportError.CreateFmt(
        'Class %s field type %s unresolved',
        [AEntry.Name, FldDecl.TypeName]);
    for J := 0 to FldDecl.Names.Count - 1 do
      RT.AddField(FldDecl.Names.Strings[J], FldType);
  end;

  { Methods: walk TRoutineSig list; for virtual/override, register
    vtable slots.  ResolvedQbeName comes pre-mangled from semantic,
    so ImplName is '$' + ResolvedQbeName.  The MethodName used as
    the vtable lookup key is just the unqualified routine name; for
    overloaded methods the mangled suffix is included in
    ResolvedQbeName but the lookup-key dance is left to a follow-up
    (overloaded class methods are not in the 6c-B happy path). }
  for I := 0 to AEntry.Methods.Count - 1 do
  begin
    RegisterClassMethod(RT, TRoutineSig(AEntry.Methods.Items[I]));
    if ASemantic <> nil then
    begin
      MDecl := SynthesiseMethodDecl(
        TRoutineSig(AEntry.Methods.Items[I]), AUnitName, ATable, ASemantic);
      ATable.OwnImportedDecl(MDecl);
      ASemantic.RegisterImportedMethod(AEntry.Name, MDecl);
    end;
  end;

  { Interface implements list — names are 'Unit.Type' (cross-unit) or
    just 'Type' (local).  We strip any 'Unit.' prefix since the
    flat symbol-table namespace doesn't carry unit qualification. }
  for I := 0 to AEntry.Implements.Count - 1 do
  begin
    ParentName := AEntry.Implements.Strings[I];
    { Strip any 'Unit.' qualifier — the unit name may itself be dotted
      (e.g. 'blaise.codegen.ICodeGen'), so take the segment after the
      LAST '.' as the type name.  The flat symbol-table namespace carries
      no unit qualification. }
    ParentName := StripUnitQualifier(ParentName);
    Sym := ATable.Lookup(ParentName);
    if (Sym <> nil) and (Sym.TypeDesc is TInterfaceTypeDesc) then
      RT.AddImplements(TInterfaceTypeDesc(Sym.TypeDesc));
  end;

  { Properties. }
  for I := 0 to ClassDef.Properties.Count - 1 do
  begin
    PropDecl := TPropertyDecl(ClassDef.Properties.Items[I]);
    PropInfo := TPropertyInfo.Create();
    PropInfo.Name := PropDecl.Name;
    FldSym := ATable.Lookup(PropDecl.TypeName);
    if (FldSym <> nil) and (FldSym.Kind = skType) then
      PropInfo.TypeDesc := FldSym.TypeDesc
    else
    begin
      FldType := ResolveInlineTypeName(PropDecl.TypeName, ATable);
      if FldType <> nil then
        PropInfo.TypeDesc := FldType;
    end;
    if PropDecl.ReadName <> '' then
    begin
      if RT.FindField(PropDecl.ReadName) <> nil then
        PropInfo.ReadField := PropDecl.ReadName
      else
        PropInfo.ReadMethod :=
          DeclaredMethodCaseOf(ClassDef.Methods, PropDecl.ReadName);
    end;
    if PropDecl.WriteName <> '' then
    begin
      if RT.FindField(PropDecl.WriteName) <> nil then
        PropInfo.WriteField := PropDecl.WriteName
      else
        PropInfo.WriteMethod :=
          DeclaredMethodCaseOf(ClassDef.Methods, PropDecl.WriteName);
    end;
    PropInfo.IndexParamName := PropDecl.IndexParamName;
    if PropDecl.IndexTypeName <> '' then
    begin
      FldSym := ATable.Lookup(PropDecl.IndexTypeName);
      if (FldSym <> nil) and (FldSym.Kind = skType) then
        PropInfo.IndexTypeDesc := FldSym.TypeDesc;
    end;
    RT.AddProperty(PropInfo);
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
                         const AUnitName: string;
                         ASemantic: TSemanticAnalyser = nil);
var
  RecDef:   TRecordTypeDef;
  RecDesc:  TRecordTypeDesc;
  Sym:      TSymbol;
  I, J:     Integer;
  FldDecl:  TFieldDecl;
  FldType:  TTypeDesc;
begin
  RecDef  := TRecordTypeDef(AEntry.Def);

  Sym := ATable.Lookup(AEntry.Name);
  if (Sym <> nil) and (Sym.Kind = skType) and (Sym.TypeDesc is TRecordTypeDesc) then
    RecDesc := TRecordTypeDesc(Sym.TypeDesc)
  else
  begin
    RecDesc := ATable.NewRecordType(AEntry.Name);
    Sym := TSymbol.Create(AEntry.Name, skType, RecDesc);
    Sym.OwningUnit := AUnitName;
    if not ATable.Define(Sym) then
    begin
      Sym.Free();
      Exit;
    end;
  end;
  RecDesc.IsPacked := RecDef.IsPacked;

  for I := 0 to RecDef.Fields.Count - 1 do
  begin
    FldDecl := TFieldDecl(RecDef.Fields.Items[I]);
    FldType := ResolveImportTypeName(FldDecl.TypeName, ATable, ASemantic);
    if FldType = nil then
      raise EImportError.CreateFmt(
        'Record %s field type %s unresolved',
        [AEntry.Name, FldDecl.TypeName]);
    for J := 0 to FldDecl.Names.Count - 1 do
      RecDesc.AddField(FldDecl.Names.Strings[J], FldType);
  end;
end;

procedure RegisterProcType(AEntry: TTypeEntry; ATable: TSymbolTable;
                           const AUnitName: string);
var
  Def:       TProceduralTypeDef;
  ProcDesc:  TProceduralTypeDesc;
  Sym:       TSymbol;
  K:         Integer;
  MParam:    TMethodParam;
  ParamInfo: TProcParamInfo;
  TSym:      TSymbol;
begin
  Def      := TProceduralTypeDef(AEntry.Def);
  ProcDesc := ATable.NewProceduralType(AEntry.Name);
  ProcDesc.IsMethodPtr := Def.IsMethodPtr;
  for K := 0 to Def.Params.Count - 1 do
  begin
    MParam := TMethodParam(Def.Params.Items[K]);
    TSym   := ATable.Lookup(MParam.TypeName);
    if (TSym <> nil) and (TSym.Kind = skType) then
    begin
      ParamInfo := TProcParamInfo.Create();
      ParamInfo.Name         := MParam.ParamName;
      ParamInfo.TypeDesc     := TSym.TypeDesc;
      ParamInfo.IsVarParam   := MParam.IsVarParam;
      ParamInfo.IsConstParam := MParam.IsConstParam;
      ProcDesc.Params.Add(ParamInfo);
    end;
  end;
  if Def.IsFunction then
  begin
    TSym := ATable.Lookup(Def.ReturnTypeName);
    if (TSym <> nil) and (TSym.Kind = skType) then
      ProcDesc.ReturnType := TSym.TypeDesc;
  end;
  Sym := TSymbol.Create(AEntry.Name, skType, ProcDesc);
  Sym.OwningUnit := AUnitName;
  if not ATable.Define(Sym) then Sym.Free();
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
  BaseSym := ATable.Lookup(AliasName);
  if (BaseSym <> nil) and (BaseSym.Kind = skType) then
    AliasDesc := BaseSym.TypeDesc
  else
  begin
    AliasDesc := ResolveInlineTypeName(AliasName, ATable);
    if AliasDesc = nil then
      raise EImportError.CreateFmt(
        'Type alias %s = %s: base not found', [AEntry.Name, AliasName]);
  end;
  Sym := TSymbol.Create(AEntry.Name, skType, AliasDesc);
  Sym.OwningUnit := AUnitName;
  if not ATable.Define(Sym) then Sym.Free();
end;

procedure RegisterTypes(AIface: TUnitInterface; ATable: TSymbolTable;
                        ASemantic: TSemanticAnalyser = nil);
var
  I: Integer;
  Entry: TTypeEntry;
  Sym: TSymbol;
begin
  { Pass 1: pre-register class, record, and interface names so
    forward references (field types pointing at later types in the
    same unit) resolve during pass 2. }
  for I := 0 to AIface.Types.Count - 1 do
  begin
    Entry := TTypeEntry(AIface.Types.Items[I]);
    if Entry.IsGeneric or (Entry.Def is TGenericInterfaceDef) then
      Continue;
    if Entry.Def is TClassTypeDef then
    begin
      Sym := TSymbol.Create(Entry.Name, skType, ATable.NewClassType(Entry.Name));
      Sym.OwningUnit := AIface.Name;
      if not ATable.Define(Sym) then Sym.Free();
    end
    else if Entry.Def is TRecordTypeDef then
    begin
      Sym := TSymbol.Create(Entry.Name, skType, ATable.NewRecordType(Entry.Name));
      Sym.OwningUnit := AIface.Name;
      if not ATable.Define(Sym) then Sym.Free();
    end
    else if Entry.Def is TInterfaceTypeDef then
    begin
      Sym := TSymbol.Create(Entry.Name, skType, ATable.NewInterfaceType(Entry.Name));
      Sym.OwningUnit := AIface.Name;
      if not ATable.Define(Sym) then Sym.Free();
    end;
  end;

  { Pass 2: fill in details — enums, sets, aliases, proc types go
    here in full; class/record/interface fill fields/methods/parents
    using the pre-registered descriptor. }
  for I := 0 to AIface.Types.Count - 1 do
  begin
    Entry := TTypeEntry(AIface.Types.Items[I]);

    if Entry.IsGeneric or (Entry.Def is TGenericInterfaceDef) then
    begin
      { Record the declaring unit on class templates so allocation sites
        inside cloned method bodies are attributed to the template source. }
      if Entry.Def is TGenericTypeDef then
        TGenericTypeDef(Entry.Def).DefUnitName := AIface.Name;
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
      RegisterClass(Entry, ATable, AIface.Name, ASemantic)
    else if Entry.Def is TRecordTypeDef then
      RegisterRecord(Entry, ATable, AIface.Name, ASemantic)
    else if Entry.Def is TProceduralTypeDef then
      RegisterProcType(Entry, ATable, AIface.Name)
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
      Sym.Free();  { duplicate — silently skip }
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
    Sym.IsGlobal    := True;
    Sym.IsThreadVar := Entry.IsThreadVar;
    Sym.OwningUnit  := AIface.Name;
    if not ATable.Define(Sym) then
      Sym.Free();
  end;
end;

{ ----- Routine registration ------------------------------------- }

{ Build a TParamDesc for the symbol table from a cloned TMethodParam.
  Param types must already be registered in ATable (caller imported
  the dep, or it's a builtin). }
function BuildParamDesc(AParam: TMethodParam; ATable: TSymbolTable;
                        ASemantic: TSemanticAnalyser = nil): TParamDesc;
begin
  Result := TParamDesc.Create();
  Result.Name     := AParam.ParamName;
  Result.IsConst  := AParam.IsConstParam;
  Result.IsVar    := AParam.IsVarParam;
  { Generic-aware resolution so an instance param type (e.g.
    'TList<TArchiveMember>') resolves rather than leaving TypeDesc nil. }
  Result.TypeDesc := ResolveImportTypeName(AParam.TypeName, ATable, ASemantic);
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
                              ATable: TSymbolTable;
                              ASemantic: TSemanticAnalyser = nil): TMethodDecl;
var
  J:     Integer;
  Param: TMethodParam;
  PSyn:  TMethodParam;
begin
  Result := TMethodDecl.Create();
  Result.Name           := ASig.Name;
  Result.OwningUnit     := AOwningUnit;
  Result.ReturnTypeName := ASig.ReturnType.TypeName;
  Result.ResolvedReturnType :=
    ResolveImportTypeName(ASig.ReturnType.TypeName, ATable, ASemantic);
  if ASig.ResolvedQbeName <> '' then
    Result.ResolvedQbeName := ASig.ResolvedQbeName
  else
    Result.ResolvedQbeName := MangleUnitPrefix(AOwningUnit) + ASig.Name;
  { Propagate the vtable-dispatch facts.  Without these, a call to a virtual
    method resolved from a cached .bif keeps VTableSlot = -1 (the TMethodDecl
    default) and codegen emits a DIRECT call to the base/abstract symbol
    instead of a vtable dispatch — e.g. an incremental rebuild miscompiles
    Driver.CreateUnitCodeGen into a call to the abstract TBackendDriver stub,
    aborting at run time.  The .bif already carries these (EncodeMethodSig). }
  Result.VTableSlot := ASig.VTableSlot;
  Result.IsVirtual  := ASig.IsVirtual;
  Result.IsOverride := ASig.IsOverride;
  for J := 0 to ASig.Params.Count - 1 do
  begin
    Param := TMethodParam(ASig.Params.Items[J]);
    PSyn := TMethodParam.Create();
    PSyn.ParamName    := Param.ParamName;
    PSyn.TypeName     := Param.TypeName;
    PSyn.IsVarParam   := Param.IsVarParam;
    PSyn.IsConstParam := Param.IsConstParam;
    PSyn.IsOpenArray  := Param.IsOpenArray;
    PSyn.HasDefault   := Param.HasDefault;
    { Carry the default-value expression through so call sites that omit
      the trailing arguments can synthesise them (AppendDefaultArgs).  The
      .bif round-trips the literal/ident default expression; ownership of
      the cloned node passes to PSyn. }
    PSyn.DefaultValue := Param.DefaultValue;
    Param.DefaultValue := nil;
    { Resolve the param type, including generic instances such as
      'TList<TArchiveMember>' — a plain symbol Lookup cannot, so without the
      generic-aware resolver the param's ResolvedType stays nil and the
      call-site overload scorer rejects every candidate. }
    PSyn.ResolvedType := ResolveImportTypeName(Param.TypeName, ATable, ASemantic);
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
      RetType := ResolveImportTypeName(Sig.ReturnType.TypeName, ATable, ASemantic);
      Sym := TSymbol.Create(Sig.Name, skFunction, RetType);
    end
    else
      Sym := TSymbol.Create(Sig.Name, skProcedure, nil);

    Sym.IsOverload := False;

    for J := 0 to Sig.Params.Count - 1 do
    begin
      Param := TMethodParam(Sig.Params.Items[J]);
      PDesc := BuildParamDesc(Param, ATable, ASemantic);
      Sym.Params.Add(PDesc);
    end;

    { Build a synthetic TMethodDecl so call-site analysis can resolve
      via FProcIndex.  Owned by the symbol table to outlive imports. }
    if ASemantic <> nil then
    begin
      MDecl := SynthesiseMethodDecl(Sig, AIface.Name, ATable, ASemantic);
      ATable.OwnImportedDecl(MDecl);
      Sym.Decl := MDecl;
      ASemantic.RegisterImportedRoutine(Sig.Name, MDecl);
    end;

    Sym.OwningUnit := AIface.Name;
    if not ATable.Define(Sym) then
      Sym.Free();
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
    RegisterTypes  (AIface, ATable, ASemantic);
    RegisterConsts (AIface, ATable);
    RegisterVars   (AIface, ATable);
    RegisterRoutines(AIface, ATable, ASemantic);
    RegisterGenericRoutines(AIface, ATable);
  finally
    ATable.DefineOwningUnit := Saved;
  end;
end;

end.
