{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ uSemanticExport — produces a self-contained TUnitInterface from a
  source TUnit that has already had uSemantic.AnalyseUnit run on it.

  Pipeline position:
    uUnitLoader.LoadOne  → parsed TUnit
    uSemantic.AnalyseUnit → TUnit + populated TSymbolTable
    uSemanticExport.Export → TUnitInterface (this unit)

  After Export returns, the caller may free the source TUnit; the
  returned TUnitInterface is self-contained.  See uUnitInterface
  unit header for the full discipline.

  Phase 2 scope (current): structural carry-over.
    - Name / SourceFile / UsedUnits
    - Interface-section type declarations  → TTypeEntry (Def cloned)
    - Interface-section const declarations → TConstEntry
    - Interface-section free routines      → TRoutineSig

  Phase 3+ scope (not yet):
    - InstanceSize / VTableLayout / class-method export
    - Inline-body extraction (impl-side body paired with intf sig)
    - Generic-body extraction
    - Cross-unit type-ref resolution against ADeps
    - Forward-declared class impl-side completion }

unit uSemanticExport;

interface

uses
  Classes, Contnrs, uAST, uUnitInterface;

{ Build a TUnitInterface from AUnit.  AUnit must have been semantically
  analysed already.  ADeps holds the already-exported interfaces of
  every unit listed in AUnit's interface uses clause, in any order. }
function ExportUnitInterface(AUnit: TUnit;
                             ADeps: TObjectList)
                             : TUnitInterface;

implementation

{ ----- Type-reference resolution ---------------------------------

  Given a type name appearing in a declaration, figure out which unit
  owns it.  Search order:
    1. The unit currently being exported (local types take precedence)
    2. The supplied dependencies
    3. Fall back to '$builtin'

  This is intentionally name-based for Phase 2 — no TTypeDesc
  introspection.  Good enough to populate TQualTypeRef correctly for
  the common cases; classes that need full resolution against
  TSymbolTable will revisit this in Phase 3. }

function ResolveTypeRef(const ATypeName: string;
                        AIface:          TUnitInterface;
                        ADeps:           TObjectList)
                        : TQualTypeRef;
var
  I: Integer;
begin
  if ATypeName = '' then
  begin
    Result := MakeQualRef('', '');
    Exit;
  end;

  if AIface.FindType(ATypeName) <> nil then
  begin
    Result := MakeLocalRef(ATypeName);
    Exit;
  end;

  if ADeps <> nil then
    for I := 0 to ADeps.Count - 1 do
      if TUnitInterface(ADeps.Items[I]).FindType(ATypeName) <> nil then
      begin
        Result := MakeQualRef(TUnitInterface(ADeps.Items[I]).Name, ATypeName);
        Exit;
      end;

  Result := MakeBuiltinRef(ATypeName);
end;

{ ----- Per-declaration builders ---------------------------------- }

{ Populate the class-specific fields of a TTypeEntry from its
  TClassTypeDef.  Parent and implements references are resolved
  against ADeps (and the in-progress AIface for forward-references
  inside the same unit).  Methods are exported as TRoutineSig — no
  bodies; downstream consumers re-emit them from the class
  declaration when instantiating the class. }
procedure PopulateClassEntry(AEntry:      TTypeEntry;
                             ASrc:        TClassTypeDef;
                             AIface:      TUnitInterface;
                             ADeps:       TObjectList);
var
  I:    Integer;
  M:    TMethodDecl;
  Sig:  TRoutineSig;
  IRef: TQualTypeRef;
begin
  AEntry.ParentClass := ResolveTypeRef(ASrc.ParentName, AIface, ADeps);

  for I := 0 to ASrc.ImplementsNames.Count - 1 do
  begin
    IRef := ResolveTypeRef(ASrc.ImplementsNames.Strings[I], AIface, ADeps);
    if IRef.UnitName = '' then
      AEntry.Implements.Add(IRef.TypeName)
    else
      AEntry.Implements.Add(IRef.UnitName + '.' + IRef.TypeName);
  end;

  for I := 0 to ASrc.Attributes.Count - 1 do
    AEntry.Attributes.Add(ASrc.Attributes.Strings[I]);

  for I := 0 to ASrc.Methods.Count - 1 do
  begin
    M   := TMethodDecl(ASrc.Methods.Items[I]);
    Sig := BuildRoutineSig(M, AIface, ADeps);
    AEntry.Methods.Add(Sig);
  end;

  { VTableLayout: pre-semantic every VTableSlot is -1, so the layout
    list stays empty.  Phase 4 (run AnalyseUnit then Export) will
    populate it. }
end;

function BuildTypeEntry(ASrc:   TTypeDecl;
                        AIface: TUnitInterface;
                        ADeps:  TObjectList): TTypeEntry;
var
  GenDef:   TGenericTypeDef;
begin
  Result := TTypeEntry.Create;
  Result.Name := ASrc.Name;
  Result.Def  := CloneTypeDef(ASrc.Def);
  Result.IsClass   := ASrc.Def is TClassTypeDef;
  Result.IsGeneric := ASrc.Def is TGenericTypeDef;

  if ASrc.Def is TClassTypeDef then
    PopulateClassEntry(Result, TClassTypeDef(ASrc.Def), AIface, ADeps)
  else if ASrc.Def is TGenericTypeDef then
  begin
    { Generic class — the class body lives inside the wrapper. }
    GenDef := TGenericTypeDef(ASrc.Def);
    if GenDef.ClassDef <> nil then
      PopulateClassEntry(Result, GenDef.ClassDef, AIface, ADeps);
  end;
end;

function BuildConstEntry(ASrc:        TConstDecl;
                         AIface:      TUnitInterface;
                         ADeps: TObjectList)
                         : TConstEntry;
begin
  Result := TConstEntry.Create;
  Result.Decl    := CloneConstDecl(ASrc);
  Result.TypeRef := ResolveTypeRef(ASrc.TypeName, AIface, ADeps);
end;

{ Locate impl-section TMethodDecl whose name matches AName.
  Returns nil if not found.  Used to pair interface-section forward
  decls (which carry no body) with their implementation. }
function FindImplBody(AUnit: TUnit; const AName: string): TMethodDecl;
var
  I: Integer;
  M: TMethodDecl;
begin
  Result := nil;
  if AUnit.ImplBlock = nil then Exit;
  for I := 0 to AUnit.ImplBlock.ProcDecls.Count - 1 do
  begin
    M := TMethodDecl(AUnit.ImplBlock.ProcDecls.Items[I]);
    if SameText(M.Name, AName) then
    begin
      Result := M;
      Exit;
    end;
  end;
end;

function BuildRoutineSig(ASrc:        TMethodDecl;
                         AIface:      TUnitInterface;
                         ADeps: TObjectList)
                         : TRoutineSig;
var
  I:      Integer;
  PSrc:   TMethodParam;
  PCopy:  TMethodParam;
begin
  Result := TRoutineSig.Create;
  Result.Name         := ASrc.Name;
  Result.IsFunction   := ASrc.ReturnTypeName <> '';
  Result.IsInline     := ASrc.IsInline or ASrc.IsInlineCandidate;
  Result.IsPublished  := ASrc.IsPublished;
  Result.IsExternal   := ASrc.IsExternal;
  Result.ExternalName := ASrc.ExternalName;
  Result.ReturnType   := ResolveTypeRef(ASrc.ReturnTypeName, AIface, ADeps);

  for I := 0 to ASrc.Params.Count - 1 do
  begin
    PSrc  := TMethodParam(ASrc.Params.Items[I]);
    PCopy := CloneMethodParam(PSrc);
    Result.Params.Add(PCopy);
  end;
end;

{ ----- Walk passes ----------------------------------------------- }

{ Forward-declared class merging: a `type TFoo = class;` in the
  interface section parses to a TClassTypeDef with empty Fields and
  Methods.  The full body is in the implementation section.  For
  separate compilation the exported interface must carry the full
  body — locate the impl-side completion and substitute it.

  This is the documented impl-leak (see TUnitInterface unit header). }
function FindImplClassCompletion(AUnit: TUnit;
                                 const AName: string): TClassTypeDef;
var
  I: Integer;
  D: TTypeDecl;
begin
  Result := nil;
  if AUnit.ImplBlock = nil then Exit;
  for I := 0 to AUnit.ImplBlock.TypeDecls.Count - 1 do
  begin
    D := TTypeDecl(AUnit.ImplBlock.TypeDecls.Items[I]);
    if not SameText(D.Name, AName) then Continue;
    if D.Def is TClassTypeDef then
    begin
      Result := TClassTypeDef(D.Def);
      Exit;
    end;
  end;
end;

function IsForwardClass(ADef: TClassTypeDef): Boolean;
begin
  Result := (ADef.Fields.Count = 0) and (ADef.Methods.Count = 0);
end;

procedure ExportTypes(AUnit:  TUnit;
                      AIface: TUnitInterface;
                      ADeps:  TObjectList);
var
  I:        Integer;
  Decl:     TTypeDecl;
  ClassDef: TClassTypeDef;
  ImplDef:  TClassTypeDef;
  Entry:    TTypeEntry;
begin
  if AUnit.IntfBlock = nil then Exit;
  for I := 0 to AUnit.IntfBlock.TypeDecls.Count - 1 do
  begin
    Decl := TTypeDecl(AUnit.IntfBlock.TypeDecls.Items[I]);

    if Decl.Def is TClassTypeDef then
    begin
      ClassDef := TClassTypeDef(Decl.Def);
      if IsForwardClass(ClassDef) then
      begin
        ImplDef := FindImplClassCompletion(AUnit, Decl.Name);
        if ImplDef <> nil then
        begin
          Entry := TTypeEntry.Create;
          Entry.Name    := Decl.Name;
          Entry.Def     := CloneClassTypeDef(ImplDef);
          Entry.IsClass := True;
          PopulateClassEntry(Entry, ImplDef, AIface, ADeps);
          AIface.AddType(Entry);
          Continue;
        end;
      end;
    end;

    AIface.AddType(BuildTypeEntry(Decl, AIface, ADeps));
  end;
end;

procedure ExportConsts(AUnit:       TUnit;
                       AIface:      TUnitInterface;
                       ADeps: TObjectList);
var
  I:    Integer;
  Decl: TConstDecl;
begin
  if AUnit.IntfBlock = nil then Exit;
  for I := 0 to AUnit.IntfBlock.ConstDecls.Count - 1 do
  begin
    Decl := TConstDecl(AUnit.IntfBlock.ConstDecls.Items[I]);
    AIface.AddConst(BuildConstEntry(Decl, AIface, ADeps));
  end;
end;

procedure ExportRoutines(AUnit:       TUnit;
                         AIface:      TUnitInterface;
                         ADeps: TObjectList);
var
  I:    Integer;
  Decl: TMethodDecl;
begin
  if AUnit.IntfBlock = nil then Exit;
  for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]);
    AIface.AddRoutine(BuildRoutineSig(Decl, AIface, ADeps));
  end;
end;

{ Pair interface-section inline routines with their impl-side body
  and stash the cloned Block as a TInlineBody. }
procedure ExportInlineBodies(AUnit: TUnit; AIface: TUnitInterface);
var
  I:        Integer;
  Decl:     TMethodDecl;
  ImplDecl: TMethodDecl;
  Body:     TInlineBody;
begin
  if AUnit.IntfBlock = nil then Exit;
  for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]);
    if not Decl.IsInline then Continue;
    if Decl.TypeParams <> nil then Continue;  { generic handled below }

    ImplDecl := FindImplBody(AUnit, Decl.Name);
    if ImplDecl = nil then Continue;
    if ImplDecl.Body = nil then Continue;

    Body := TInlineBody.Create;
    Body.RoutineName := Decl.Name;
    Body.Block       := CloneBlock(ImplDecl.Body);
    AIface.AddInlineBody(Body);
  end;
end;

{ Pair interface-section generic routine declarations with their
  impl-side body, and emit TGenericBody entries for generic types
  (whose Def is TGenericTypeDef). }
procedure ExportGenericBodies(AUnit: TUnit; AIface: TUnitInterface);
var
  I:        Integer;
  Decl:     TMethodDecl;
  ImplDecl: TMethodDecl;
  TDecl:    TTypeDecl;
  GenDef:   TGenericTypeDef;
  GBody:    TGenericBody;
  J:        Integer;
begin
  if AUnit.IntfBlock = nil then Exit;

  { Generic free routines. }
  for I := 0 to AUnit.IntfBlock.ProcDecls.Count - 1 do
  begin
    Decl := TMethodDecl(AUnit.IntfBlock.ProcDecls.Items[I]);
    if Decl.TypeParams = nil then Continue;

    ImplDecl := FindImplBody(AUnit, Decl.Name);
    if ImplDecl = nil then Continue;
    if ImplDecl.Body = nil then Continue;

    GBody := TGenericBody.Create;
    GBody.Name       := Decl.Name;
    GBody.IsType     := False;
    GBody.RoutineSig := BuildRoutineSig(Decl, AIface, nil);
    GBody.Body       := CloneBlock(ImplDecl.Body);
    for J := 0 to Decl.TypeParams.Count - 1 do
    begin
      GBody.TypeParams.Add(Decl.TypeParams.Strings[J]);
      if Decl.TypeParamConstraints <> nil then
        GBody.Constraints.Add(Decl.TypeParamConstraints.Strings[J])
      else
        GBody.Constraints.Add('');
    end;
    AIface.AddGenericBody(GBody);
  end;

  { Generic types — Def is already cloned into the TTypeEntry; we
    just register the parallel TGenericBody for body access. }
  for I := 0 to AUnit.IntfBlock.TypeDecls.Count - 1 do
  begin
    TDecl := TTypeDecl(AUnit.IntfBlock.TypeDecls.Items[I]);
    if not (TDecl.Def is TGenericTypeDef) then Continue;

    GenDef := TGenericTypeDef(TDecl.Def);
    GBody := TGenericBody.Create;
    GBody.Name    := TDecl.Name;
    GBody.IsType  := True;
    GBody.TypeDef := CloneTypeDef(TDecl.Def);
    for J := 0 to GenDef.ParamNames.Count - 1 do
    begin
      GBody.TypeParams.Add(GenDef.ParamNames.Strings[J]);
      if GenDef.ParamConstraints <> nil then
        GBody.Constraints.Add(GenDef.ParamConstraints.Strings[J])
      else
        GBody.Constraints.Add('');
    end;
    AIface.AddGenericBody(GBody);
  end;
end;

procedure CopyUsedUnits(AUnit: TUnit; AIface: TUnitInterface);
var
  I: Integer;
begin
  if AUnit.UsedUnits = nil then Exit;
  for I := 0 to AUnit.UsedUnits.Count - 1 do
    AIface.UsedUnits.Add(AUnit.UsedUnits.Strings[I]);
end;

{ ----- Top-level ------------------------------------------------- }

function ExportUnitInterface(AUnit: TUnit;
                             ADeps: TObjectList)
                             : TUnitInterface;
begin
  Result := TUnitInterface.Create(AUnit.Name);
  Result.SourceFile := AUnit.SourceFile;

  CopyUsedUnits(AUnit, Result);

  { Types FIRST — subsequent passes' ResolveTypeRef calls need to be
    able to find local types in the index. }
  ExportTypes   (AUnit, Result, ADeps);
  ExportConsts  (AUnit, Result, ADeps);
  ExportRoutines(AUnit, Result, ADeps);

  ExportInlineBodies (AUnit, Result);
  ExportGenericBodies(AUnit, Result);
end;

end.
