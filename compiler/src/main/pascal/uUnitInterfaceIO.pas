{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ uUnitInterfaceIO — text-based serializer / deserializer for
  TUnitInterface.

  Phase 6c-E starter.  The on-disk story for separate compilation
  needs a stable, parser-free way to materialise a TUnitInterface
  from a byte sequence.  This unit owns that mapping.

  Format (v1):
    Magic + version on a single line, then length-prefixed string
    records.  Lengths are decimal ASCII followed by ':' and the
    raw bytes (no escaping needed since lengths drive consumption).

    BLAISE-IFACE 1\n
    <unit-name lpstr>
    CONST <count>\n
      <name lpstr><typeref lpstr><int64><strval lpstr><flags byte>
    END\n

  Where:
    <lpstr>     = "<decimal-len>:" followed by <len> raw bytes
    <int64>     = lpstr containing the decimal digits
    <flags byte>= '0' / '1' / '2' / '3'
                  bit 0 = IsString, bit 1 = IsFloat

  TypeRef is rendered as "UnitName.TypeName" — '$builtin.Integer',
  '<thisunit>.TFoo', or '.<empty>' for untyped consts.

  Scope of this commit: unit name + const records only.  Vars,
  types, routines, and class/generic bodies land in follow-up
  commits.  The plumbing — magic header, length-prefixed strings,
  cursor-based reader — is the load-bearing part; extending it to
  more record types is mechanical.

  Why text and not binary: easier to diff and inspect during
  development, no endianness concerns, no bit-twiddling.  Once the
  layout stabilises we can re-encode as a compact binary form
  without changing the surface API. }

unit uUnitInterfaceIO;

interface

uses
  Classes, SysUtils, streams, strutils, uAST, uUnitInterface;

const
  IFACE_MAGIC   = 'BLAISE-IFACE';
  IFACE_VERSION = 1;

type
  EIfaceFormatError = class(Exception);

{ Render AIface into a string.  Caller owns the buffer. }
function WriteUnitInterface(AIface: TUnitInterface): string;

{ Parse AText into a freshly-allocated TUnitInterface.  Caller owns
  the returned interface.  Raises EIfaceFormatError on a malformed
  input or version mismatch. }
function ReadUnitInterface(const AText: string): TUnitInterface;

{ File wrappers.  Caller owns the returned interface. }
procedure WriteUnitInterfaceToFile(AIface: TUnitInterface; const APath: string);
function  ReadUnitInterfaceFromFile(const APath: string): TUnitInterface;

{ FNV-1a 64-bit content hash, lowercase hex.  Cheap, no crypto deps,
  change-detection grade — sufficient for iface-vs-source freshness
  checks but NOT suitable for adversarial integrity. }
function ContentHashFnv1a64(const AContent: string): string;

implementation

{ ----- Writer ----------------------------------------------------- }

{ Length-prefixed string: "<len>:bytes".  Lets the reader consume
  exactly <len> UTF-8 bytes without worrying about embedded ':',
  newlines, or quotes. }
function EncodeLpstr(const S: string): string;
begin
  Result := IntToStr(Length(S)) + ':' + S;
end;

function EncodeInt64(V: Int64): string;
begin
  Result := EncodeLpstr(IntToStr(V));
end;

function EncodeFlags(AIsString, AIsFloat: Boolean): string;
var
  B: Integer;
begin
  B := 0;
  if AIsString then B := B or 1;
  if AIsFloat  then B := B or 2;
  Result := IntToStr(B);
end;

{ Pass the ref as two strings to dodge the documented record-with-
  strings-as-const-param codegen bug (memory:
  project_record_const_param_crash.md). }
function EncodeQualRefParts(const AUnitName, ATypeName: string): string;
begin
  Result := EncodeLpstr(AUnitName + '.' + ATypeName);
end;

function WriteConsts(AIface: TUnitInterface): string;
var
  I:  Integer;
  C:  TConstEntry;
  SB: TStringBuilder;
begin
  SB := TStringBuilder.Create();
  try
    SB.AppendLine('CONST ' + IntToStr(AIface.Consts.Count));
    for I := 0 to AIface.Consts.Count - 1 do
    begin
      C := TConstEntry(AIface.Consts.Items[I]);
      SB.AppendLine(
        EncodeLpstr(C.Decl.Name) +
        EncodeQualRefParts(C.TypeRef.UnitName, C.TypeRef.TypeName) +
        EncodeInt64(C.Decl.IntVal) +
        EncodeLpstr(C.Decl.StrVal) +
        EncodeFlags(C.Decl.IsString, C.Decl.IsFloat));
    end;
    SB.AppendLine('END');
    Result := SB.ToString();
  finally
    SB.Free();
  end;
end;

function WriteVars(AIface: TUnitInterface): string;
var
  I:  Integer;
  V:  TVarEntry;
  SB: TStringBuilder;
begin
  SB := TStringBuilder.Create();
  try
    SB.AppendLine('VAR ' + IntToStr(AIface.Vars.Count));
    for I := 0 to AIface.Vars.Count - 1 do
    begin
      V := TVarEntry(AIface.Vars.Items[I]);
      SB.AppendLine(
        EncodeLpstr(V.Name) +
        EncodeQualRefParts(V.TypeRef.UnitName, V.TypeRef.TypeName) +
        EncodeBool(V.IsThreadVar));
    end;
    SB.AppendLine('END');
    Result := SB.ToString();
  finally
    SB.Free();
  end;
end;

{ Enum members: encode name=ordinal pairs.  Members.Objects[i]
  holds the explicit ordinal (TEnumTypeDef.AddMember stashes it
  there as a pointer-cast int), so a naive name-only encoding
  rounds back to ordinal 0 for everything.  Renders as
  '<name>=<ord>,<name>=<ord>,…' inside the outer lpstr. }
function EncodeEnumMembers(AEnum: TEnumTypeDef): string;
var
  I:    Integer;
  Acc:  string;
begin
  Acc := '';
  for I := 0 to AEnum.Members.Count - 1 do
  begin
    if I > 0 then Acc := Acc + ',';
    Acc := Acc + AEnum.Members.Strings[I] + '=' + IntToStr(AEnum.OrdinalAt(I));
  end;
  Result := EncodeLpstr(Acc);
end;

{ Tag a TTypeEntry by what its Def is.  Procedural, generic, and
  generic-interface kinds are still skipped on write — they need
  richer payloads (param resolution / template parameter lists) and
  belong in follow-up commits along with inline + generic bodies. }
function TypeEntryKind(AEntry: TTypeEntry): string;
begin
  if      AEntry.Def is TEnumTypeDef         then Result := 'enum'
  else if AEntry.Def is TSetTypeDef          then Result := 'set'
  else if AEntry.Def is TTypeAliasDef        then Result := 'alias'
  else if AEntry.Def is TRecordTypeDef       then Result := 'record'
  else if AEntry.Def is TClassTypeDef        then Result := 'class'
  else if AEntry.Def is TInterfaceTypeDef    then Result := 'interface'
  else if AEntry.Def is TProceduralTypeDef   then Result := 'proc'
  else if AEntry.Def is TGenericTypeDef      then Result := 'generic-class'
  else if AEntry.Def is TGenericInterfaceDef then Result := 'generic-interface'
  else                                            Result := '';
end;

{ ----- TYPE-block payload helpers --------------------------------

  Every value emitted into the TYPE block is an lpstr.  Numeric
  counts and boolean flags are stringified into lpstrs too, which
  costs a few extra bytes but keeps the reader's primitive set
  trivially small (only ReadLpstrAt).  Sequences (attributes,
  implements, fields, methods) are emitted as a count lpstr
  followed by `count` records. }

function EncodeCount(N: Integer): string;
begin
  Result := EncodeLpstr(IntToStr(N));
end;

function EncodeBool(B: Boolean): string;
begin
  if B then Result := EncodeLpstr('1')
       else Result := EncodeLpstr('0');
end;

function EncodeStringList(ASL: TStringList): string;
var
  I: Integer;
begin
  Result := EncodeCount(ASL.Count);
  for I := 0 to ASL.Count - 1 do
    Result := Result + EncodeLpstr(ASL.Strings[I]);
end;

function EncodeFieldList(AFields: TObjectList): string;
var
  I, J: Integer;
  F:    TFieldDecl;
  TotalNames: Integer;
begin
  { TFieldDecl carries Names: TStringList (multi-name fields like
    'X, Y: Integer').  Flatten to one record per name for symmetry
    with how TSymbolTable.AddField is called. }
  TotalNames := 0;
  for I := 0 to AFields.Count - 1 do
    Inc(TotalNames, TFieldDecl(AFields.Items[I]).Names.Count);

  Result := EncodeCount(TotalNames);
  for I := 0 to AFields.Count - 1 do
  begin
    F := TFieldDecl(AFields.Items[I]);
    for J := 0 to F.Names.Count - 1 do
      Result := Result +
                EncodeLpstr(F.Names.Strings[J]) +
                EncodeLpstr(F.TypeName) +
                EncodeBool(F.IsWeak);
  end;
end;

{ Per-method routine sig including class-method extras
  (VTableSlot, ResolvedQbeName, IsVirtual, IsOverride).  Used by
  class + interface payloads. }
function EncodeMethodSig(AR: TRoutineSig): string;
var
  J: Integer;
  P: TMethodParam;
begin
  Result :=
    EncodeLpstr(AR.Name) +
    EncodeBool (AR.IsFunction) +
    EncodeQualRefParts(AR.ReturnType.UnitName, AR.ReturnType.TypeName) +
    EncodeBool (AR.IsVirtual) +
    EncodeBool (AR.IsOverride) +
    EncodeLpstr(AR.ResolvedQbeName) +
    EncodeLpstr(IntToStr(AR.VTableSlot)) +
    EncodeCount(AR.Params.Count);
  for J := 0 to AR.Params.Count - 1 do
  begin
    P := TMethodParam(AR.Params.Items[J]);
    Result := Result +
              EncodeLpstr(P.ParamName) +
              EncodeLpstr(P.TypeName) +
              EncodeParamFlags(P);
  end;
end;

function EncodeMethodList(AMethods: TObjectList): string;
var
  I: Integer;
begin
  Result := EncodeCount(AMethods.Count);
  for I := 0 to AMethods.Count - 1 do
    Result := Result + EncodeMethodSig(TRoutineSig(AMethods.Items[I]));
end;

function WriteRecordPayload(AEntry: TTypeEntry): string;
var
  Def: TRecordTypeDef;
begin
  Def := TRecordTypeDef(AEntry.Def);
  Result := EncodeBool(Def.IsPacked) +
            EncodeFieldList(Def.Fields);
end;

function EncodePropertyList(AList: TObjectList): string;
var
  I: Integer;
  P: TPropertyDecl;
begin
  Result := EncodeCount(AList.Count);
  for I := 0 to AList.Count - 1 do
  begin
    P := TPropertyDecl(AList.Items[I]);
    Result := Result +
              EncodeLpstr(P.Name) +
              EncodeLpstr(P.TypeName) +
              EncodeLpstr(P.ReadName) +
              EncodeLpstr(P.WriteName) +
              EncodeLpstr(P.IndexParamName) +
              EncodeLpstr(P.IndexTypeName);
  end;
end;

function WriteClassPayload(AEntry: TTypeEntry): string;
var
  Def: TClassTypeDef;
begin
  Def := TClassTypeDef(AEntry.Def);
  Result :=
    EncodeQualRefParts(AEntry.ParentClass.UnitName, AEntry.ParentClass.TypeName) +
    EncodeLpstr(IntToStr(AEntry.InstanceSize)) +
    EncodeStringList(AEntry.Attributes) +
    EncodeStringList(AEntry.Implements) +
    EncodeFieldList(Def.Fields) +
    EncodeMethodList(AEntry.Methods) +
    EncodePropertyList(Def.Properties);
end;

{ Encode a TMethodDecl (AST) using the same per-method payload shape
  as EncodeMethodSig, but pulling fields off the AST node.  Interface
  methods live in Def.Methods (TInterfaceTypeDef carries them
  natively), not in AEntry.Methods.  This keeps the writer and the
  importer (uSemanticImport.RegisterInterface, which walks
  Def.Methods) symmetric. }
function EncodeMethodDecl(AM: TMethodDecl): string;
var
  J: Integer;
  P: TMethodParam;
begin
  Result :=
    EncodeLpstr(AM.Name) +
    EncodeBool (AM.ReturnTypeName <> '') +
    EncodeLpstr(AM.ReturnTypeName) +  { stored raw, not a qualref —
                                         interfaces don't carry
                                         resolved cross-unit refs }
    EncodeBool (AM.IsVirtual) +
    EncodeBool (AM.IsOverride) +
    EncodeCount(AM.Params.Count);
  for J := 0 to AM.Params.Count - 1 do
  begin
    P := TMethodParam(AM.Params.Items[J]);
    Result := Result +
              EncodeLpstr(P.ParamName) +
              EncodeLpstr(P.TypeName) +
              EncodeParamFlags(P);
  end;
end;

function EncodeMethodDeclList(AList: TObjectList): string;
var
  I: Integer;
begin
  Result := EncodeCount(AList.Count);
  for I := 0 to AList.Count - 1 do
    Result := Result + EncodeMethodDecl(TMethodDecl(AList.Items[I]));
end;

{ Encode <count> followed by <count> (name, constraint) pairs.  Used
  by both generic-class and generic-interface payloads. }
function EncodeTypeParamList(ANames, AConstraints: TStringList): string;
var
  I: Integer;
  Constraint: string;
begin
  Result := EncodeCount(ANames.Count);
  for I := 0 to ANames.Count - 1 do
  begin
    if (AConstraints <> nil) and (I < AConstraints.Count) then
      Constraint := AConstraints.Strings[I]
    else
      Constraint := '';
    Result := Result + EncodeLpstr(ANames.Strings[I]) + EncodeLpstr(Constraint);
  end;
end;

function WriteGenericClassPayload(AEntry: TTypeEntry): string;
var
  Def:      TGenericTypeDef;
  ClassDef: TClassTypeDef;
  J:        Integer;
  M:        TMethodDecl;
begin
  Def := TGenericTypeDef(AEntry.Def);
  ClassDef := Def.ClassDef;
  Result := EncodeTypeParamList(Def.ParamNames, Def.ParamConstraints);
  if ClassDef <> nil then
  begin
    { Same payload shape as a regular class — uSemanticExport ran
      PopulateClassEntry on the inner ClassDef, so the AEntry-level
      ParentClass / Implements / Attributes / Methods are already
      populated.  InstanceSize stays 0 for the template (no
      concrete layout until instantiation). }
    Result := Result +
              EncodeQualRefParts(AEntry.ParentClass.UnitName,
                                 AEntry.ParentClass.TypeName) +
              EncodeLpstr(IntToStr(AEntry.InstanceSize)) +
              EncodeStringList(AEntry.Attributes) +
              EncodeStringList(AEntry.Implements) +
              EncodeFieldList(ClassDef.Fields) +
              EncodeMethodList(AEntry.Methods);
    { Method bodies, parallel to the method list.  Consumers need
      these to instantiate the template against a concrete type
      argument (the body gets cloned and re-analysed with T bound
      to the concrete type). }
    for J := 0 to ClassDef.Methods.Count - 1 do
    begin
      M := TMethodDecl(ClassDef.Methods.Items[J]);
      Result := Result + EncodeBlock(M.Body);
    end;
  end
  else
    { Defensive: encode "has-body" flag = false so the reader can
      detect a templates-without-bodies case without throwing. }
    Result := Result +
              EncodeQualRefParts('', '') +
              EncodeLpstr('0') +
              EncodeCount(0) + EncodeCount(0) +
              EncodeCount(0) + EncodeCount(0);
end;

function WriteGenericInterfacePayload(AEntry: TTypeEntry): string;
var
  Def:     TGenericInterfaceDef;
  IntfDef: TInterfaceTypeDef;
begin
  Def := TGenericInterfaceDef(AEntry.Def);
  IntfDef := Def.IntfDef;
  Result := EncodeTypeParamList(Def.ParamNames, Def.ParamConstraints);
  if IntfDef <> nil then
    Result := Result +
              EncodeLpstr(IntfDef.ParentName) +
              EncodeMethodDeclList(IntfDef.Methods)
  else
    Result := Result + EncodeLpstr('') + EncodeCount(0);
end;

function WriteProcPayload(AEntry: TTypeEntry): string;
var
  Def: TProceduralTypeDef;
  J:   Integer;
  P:   TMethodParam;
begin
  Def := TProceduralTypeDef(AEntry.Def);
  Result :=
    EncodeBool (Def.IsFunction) +
    EncodeBool (Def.IsMethodPtr) +
    EncodeLpstr(Def.ReturnTypeName) +
    EncodeCount(Def.Params.Count);
  for J := 0 to Def.Params.Count - 1 do
  begin
    P := TMethodParam(Def.Params.Items[J]);
    Result := Result +
              EncodeLpstr(P.ParamName) +
              EncodeLpstr(P.TypeName) +
              EncodeParamFlags(P);
  end;
end;

function WriteInterfacePayload(AEntry: TTypeEntry): string;
var
  Def: TInterfaceTypeDef;
begin
  Def := TInterfaceTypeDef(AEntry.Def);
  Result :=
    EncodeLpstr(Def.ParentName) +
    EncodeMethodDeclList(Def.Methods);
end;

function WriteTypes(AIface: TUnitInterface): string;
var
  I:      Integer;
  E:      TTypeEntry;
  SB:     TStringBuilder;
  Kind:   string;
  Eligible: TObjectList;
begin
  Eligible := TObjectList.Create(False);
  SB := TStringBuilder.Create();
  try
    for I := 0 to AIface.Types.Count - 1 do
    begin
      E := TTypeEntry(AIface.Types.Items[I]);
      if TypeEntryKind(E) <> '' then Eligible.Add(E);
    end;

    SB.AppendLine('TYPE ' + IntToStr(Eligible.Count));
    for I := 0 to Eligible.Count - 1 do
    begin
      E := TTypeEntry(Eligible.Items[I]);
      Kind := TypeEntryKind(E);
      if Kind = 'enum' then
        SB.AppendLine(EncodeLpstr('enum') +
               EncodeLpstr(E.Name) +
               EncodeEnumMembers(TEnumTypeDef(E.Def)))
      else if Kind = 'set' then
        SB.AppendLine(EncodeLpstr('set') +
               EncodeLpstr(E.Name) +
               EncodeLpstr(TSetTypeDef(E.Def).BaseTypeName))
      else if Kind = 'alias' then
        SB.AppendLine(EncodeLpstr('alias') +
               EncodeLpstr(E.Name) +
               EncodeLpstr(TTypeAliasDef(E.Def).TypeName))
      else if Kind = 'record' then
        SB.AppendLine(EncodeLpstr('record') +
               EncodeLpstr(E.Name) +
               WriteRecordPayload(E))
      else if Kind = 'class' then
        SB.AppendLine(EncodeLpstr('class') +
               EncodeLpstr(E.Name) +
               WriteClassPayload(E))
      else if Kind = 'interface' then
        SB.AppendLine(EncodeLpstr('interface') +
               EncodeLpstr(E.Name) +
               WriteInterfacePayload(E))
      else if Kind = 'proc' then
        SB.AppendLine(EncodeLpstr('proc') +
               EncodeLpstr(E.Name) +
               WriteProcPayload(E))
      else if Kind = 'generic-class' then
        SB.AppendLine(EncodeLpstr('generic-class') +
               EncodeLpstr(E.Name) +
               WriteGenericClassPayload(E))
      else { generic-interface }
        SB.AppendLine(EncodeLpstr('generic-interface') +
               EncodeLpstr(E.Name) +
               WriteGenericInterfacePayload(E));
    end;
    SB.AppendLine('END');
    Result := SB.ToString();
  finally
    SB.Free();
    Eligible.Free();
  end;
end;

{ Param flags pack: bit 0 = IsVar, bit 1 = IsConst, bit 2 = IsOpenArray,
  bit 3 = IsOut.  Render as a single decimal lpstr for symmetry with the
  rest of the format. }
function EncodeParamFlags(AParam: TMethodParam): string;
var
  B: Integer;
begin
  B := 0;
  if AParam.IsVarParam   then B := B or 1;
  if AParam.IsConstParam then B := B or 2;
  if AParam.IsOpenArray  then B := B or 4;
  if AParam.IsOutParam   then B := B or 8;
  Result := EncodeLpstr(IntToStr(B));
end;

function WriteRoutines(AIface: TUnitInterface): string;
var
  I, J:   Integer;
  R:      TRoutineSig;
  P:      TMethodParam;
  SB:     TStringBuilder;
  Line:   string;
begin
  SB := TStringBuilder.Create();
  try
    SB.AppendLine('ROUT ' + IntToStr(AIface.Routines.Count));
    for I := 0 to AIface.Routines.Count - 1 do
    begin
      R := TRoutineSig(AIface.Routines.Items[I]);
      Line :=
        EncodeLpstr(R.Name) +
        EncodeLpstr(IntToStr(Ord(R.IsFunction))) +
        EncodeQualRefParts(R.ReturnType.UnitName, R.ReturnType.TypeName) +
        EncodeLpstr(IntToStr(R.Params.Count));
      for J := 0 to R.Params.Count - 1 do
      begin
        P    := TMethodParam(R.Params.Items[J]);
        Line := Line +
                EncodeLpstr(P.ParamName) +
                EncodeLpstr(P.TypeName) +
                EncodeParamFlags(P);
      end;
      Line := Line + EncodeLpstr(R.CallingConv);
      SB.AppendLine(Line);
    end;
    SB.AppendLine('END');
    Result := SB.ToString();
  finally
    SB.Free();
  end;
end;

function WriteMeta(AIface: TUnitInterface): string;
var
  SB: TStringBuilder;
begin
  SB := TStringBuilder.Create();
  try
    SB.AppendLine('META');
    SB.AppendLine(EncodeLpstr(AIface.SourceFile) +
           EncodeLpstr(AIface.SourceHash) +
           EncodeLpstr(AIface.CompilerId) +
           EncodeInt64(AIface.SourceModTime) +
           EncodeStringList(AIface.UsedUnits));
    SB.AppendLine('END');
    Result := SB.ToString();
  finally
    SB.Free();
  end;
end;

{ ----- AST body serialiser ---------------------------------------

  Encodes TASTExpr / TASTStmt / TBlock trees inline within the
  surrounding lpstr stream.  Each node is a sequence of lpstrs:
    <kind lpstr>(<field>…)*
  where kind is a short string tag and the field set depends on
  the kind.  nil children are encoded as the kind 'nil'.

  Scope: every node TASTSerializer.CloneExpr / CloneStmt accepts.
  Anything new added to uAST will compile clean here but trip the
  format-error fallback at read time — a structural change in the
  AST needs a matching version bump in the wire format. }

function EncodeExpr(AE: TASTExpr): string; forward;
function EncodeStmt(AStmt: TASTStmt): string; forward;
function EncodeBlock(AB: TBlock): string; forward;

function EncodeExprList(AList: TObjectList): string;
var
  I: Integer;
begin
  Result := EncodeCount(AList.Count);
  for I := 0 to AList.Count - 1 do
    Result := Result + EncodeExpr(TASTExpr(AList.Items[I]));
end;

function EncodeStmtList(AList: TObjectList): string;
var
  I: Integer;
begin
  Result := EncodeCount(AList.Count);
  for I := 0 to AList.Count - 1 do
    Result := Result + EncodeStmt(TASTStmt(AList.Items[I]));
end;

function EncodeExpr(AE: TASTExpr): string;
begin
  if AE = nil then begin Result := EncodeLpstr('nil'); Exit; end;

  if AE is TIntLiteral then
    Result := EncodeLpstr('int') +
              EncodeLpstr(IntToStr(TIntLiteral(AE).Value))
  else if AE is TFloatLiteral then
    Result := EncodeLpstr('float') +
              EncodeLpstr(TFloatLiteral(AE).Value)
  else if AE is TStringLiteral then
    Result := EncodeLpstr('str') +
              EncodeLpstr(TStringLiteral(AE).Value)
  else if AE is TNilLiteral then
    Result := EncodeLpstr('nillit')
  else if AE is TIdentExpr then
    Result := EncodeLpstr('id') +
              EncodeLpstr(TIdentExpr(AE).Name)
  else if AE is TBinaryExpr then
    Result := EncodeLpstr('bin') +
              EncodeLpstr(IntToStr(Ord(TBinaryExpr(AE).Op))) +
              EncodeExpr(TBinaryExpr(AE).Left) +
              EncodeExpr(TBinaryExpr(AE).Right)
  else if AE is TNotExpr then
    Result := EncodeLpstr('not') +
              EncodeExpr(TNotExpr(AE).Expr)
  else if AE is TFuncCallExpr then
    Result := EncodeLpstr('call') +
              EncodeLpstr(TFuncCallExpr(AE).Name) +
              EncodeExprList(TFuncCallExpr(AE).Args)
  else if AE is TMethodCallExpr then
    Result := EncodeLpstr('mcall') +
              EncodeLpstr(TMethodCallExpr(AE).ObjectName) +
              EncodeLpstr(TMethodCallExpr(AE).Name) +
              EncodeExpr(TMethodCallExpr(AE).ObjExpr) +
              EncodeExprList(TMethodCallExpr(AE).Args)
  else if AE is TFieldAccessExpr then
    Result := EncodeLpstr('field') +
              EncodeLpstr(TFieldAccessExpr(AE).RecordName) +
              EncodeLpstr(TFieldAccessExpr(AE).FieldName) +
              EncodeExpr(TFieldAccessExpr(AE).Base) +
              EncodeExpr(TFieldAccessExpr(AE).PropIndexExpr)
  else if AE is TDerefExpr then
    Result := EncodeLpstr('deref') +
              EncodeExpr(TDerefExpr(AE).Expr)
  else if AE is TAddrOfExpr then
    Result := EncodeLpstr('addr') +
              EncodeExpr(TAddrOfExpr(AE).Expr)
  else if AE is TStringSubscriptExpr then
    Result := EncodeLpstr('ssub') +
              EncodeExpr(TStringSubscriptExpr(AE).StrExpr) +
              EncodeExpr(TStringSubscriptExpr(AE).IndexExpr)
  else if AE is TArrayLiteralExpr then
    Result := EncodeLpstr('alit') +
              EncodeExprList(TArrayLiteralExpr(AE).Elements)
  else if AE is TIsExpr then
    Result := EncodeLpstr('isop') +
              EncodeExpr(TIsExpr(AE).Obj) +
              EncodeLpstr(TIsExpr(AE).TypeName)
  else if AE is TAsExpr then
    Result := EncodeLpstr('asop') +
              EncodeExpr(TAsExpr(AE).Obj) +
              EncodeLpstr(TAsExpr(AE).TypeName)
  else if AE is TSupportsExpr then
    Result := EncodeLpstr('supp') +
              EncodeExpr(TSupportsExpr(AE).Obj) +
              EncodeLpstr(TSupportsExpr(AE).IntfTypeName) +
              EncodeLpstr(TSupportsExpr(AE).OutVarName)
  else
    raise EIfaceFormatError.Create(
      'EncodeExpr: unhandled expression node ' + AE.ClassName);
end;

function EncodeExceptHandler(AH: TExceptHandlerClause): string;
begin
  Result := EncodeLpstr(AH.VarName) +
            EncodeLpstr(AH.TypeName) +
            EncodeStmt(AH.Body);
end;

function EncodeCaseBranch(AB: TCaseBranch): string;
begin
  Result := EncodeExprList(AB.Values) +
            EncodeStmt(AB.Stmt);
end;

function EncodeStmt(AStmt: TASTStmt): string;
var
  I: Integer;
  TES: TTryExceptStmt;
  CS:  TCaseStmt;
begin
  if AStmt = nil then begin Result := EncodeLpstr('nil'); Exit; end;

  if AStmt is TAssignment then
    Result := EncodeLpstr('asn') +
              EncodeLpstr(TAssignment(AStmt).Name) +
              EncodeExpr(TAssignment(AStmt).Expr)
  else if AStmt is TCompoundStmt then
    Result := EncodeLpstr('comp') +
              EncodeStmtList(TCompoundStmt(AStmt).Stmts)
  else if AStmt is TIfStmt then
    Result := EncodeLpstr('if') +
              EncodeExpr(TIfStmt(AStmt).Condition) +
              EncodeStmt(TIfStmt(AStmt).ThenStmt) +
              EncodeStmt(TIfStmt(AStmt).ElseStmt)
  else if AStmt is TWhileStmt then
    Result := EncodeLpstr('while') +
              EncodeExpr(TWhileStmt(AStmt).Condition) +
              EncodeStmt(TWhileStmt(AStmt).Body)
  else if AStmt is TRepeatStmt then
    Result := EncodeLpstr('rep') +
              EncodeStmt(TRepeatStmt(AStmt).Body) +
              EncodeExpr(TRepeatStmt(AStmt).Condition)
  else if AStmt is TForStmt then
    Result := EncodeLpstr('for') +
              EncodeLpstr(TForStmt(AStmt).VarName) +
              EncodeExpr (TForStmt(AStmt).StartExpr) +
              EncodeExpr (TForStmt(AStmt).EndExpr) +
              EncodeBool (TForStmt(AStmt).IsDownTo) +
              EncodeStmt (TForStmt(AStmt).Body)
  else if AStmt is TForInStmt then
    Result := EncodeLpstr('forin') +
              EncodeLpstr(TForInStmt(AStmt).VarName) +
              EncodeExpr (TForInStmt(AStmt).CollExpr) +
              EncodeStmt (TForInStmt(AStmt).Body)
  else if AStmt is TTryFinallyStmt then
    Result := EncodeLpstr('tryfin') +
              EncodeStmt(TTryFinallyStmt(AStmt).TryBody) +
              EncodeStmt(TTryFinallyStmt(AStmt).FinallyBody)
  else if AStmt is TTryExceptStmt then
  begin
    TES := TTryExceptStmt(AStmt);
    Result := EncodeLpstr('tryex') +
              EncodeStmt (TES.TryBody) +
              EncodeCount(TES.Handlers.Count);
    for I := 0 to TES.Handlers.Count - 1 do
      Result := Result + EncodeExceptHandler(
        TExceptHandlerClause(TES.Handlers.Items[I]));
    Result := Result + EncodeStmt(TES.ElseBody) +
                       EncodeStmt(TES.ExceptBody);
  end
  else if AStmt is TRaiseStmt then
    Result := EncodeLpstr('raise') +
              EncodeExpr(TRaiseStmt(AStmt).Expr)
  else if AStmt is TExitStmt then
    Result := EncodeLpstr('exit')
  else if AStmt is TBreakStmt then
    Result := EncodeLpstr('brk')
  else if AStmt is TContinueStmt then
    Result := EncodeLpstr('cont')
  else if AStmt is TCaseStmt then
  begin
    CS := TCaseStmt(AStmt);
    Result := EncodeLpstr('case') +
              EncodeExpr (CS.Selector) +
              EncodeCount(CS.Branches.Count);
    for I := 0 to CS.Branches.Count - 1 do
      Result := Result + EncodeCaseBranch(TCaseBranch(CS.Branches.Items[I]));
    Result := Result + EncodeStmt(CS.ElseStmt);
  end
  else if AStmt is TFieldAssignment then
    Result := EncodeLpstr('fasn') +
              EncodeLpstr(TFieldAssignment(AStmt).RecordName) +
              EncodeLpstr(TFieldAssignment(AStmt).FieldName) +
              EncodeExpr (TFieldAssignment(AStmt).Expr) +
              EncodeExpr (TFieldAssignment(AStmt).ObjExpr) +
              EncodeExpr (TFieldAssignment(AStmt).PropIndexExpr)
  else if AStmt is TStaticSubscriptAssign then
    Result := EncodeLpstr('ssasn') +
              EncodeLpstr(TStaticSubscriptAssign(AStmt).ArrayName) +
              EncodeExpr (TStaticSubscriptAssign(AStmt).IndexExpr) +
              EncodeExpr (TStaticSubscriptAssign(AStmt).ValueExpr)
  else if AStmt is TPointerWriteStmt then
    Result := EncodeLpstr('pw') +
              EncodeExpr(TPointerWriteStmt(AStmt).PtrExpr) +
              EncodeExpr(TPointerWriteStmt(AStmt).ValExpr)
  else if AStmt is TProcCall then
    Result := EncodeLpstr('pcall') +
              EncodeLpstr(TProcCall(AStmt).Name) +
              EncodeExprList(TProcCall(AStmt).Args)
  else if AStmt is TMethodCallStmt then
    Result := EncodeLpstr('mcs') +
              EncodeLpstr(TMethodCallStmt(AStmt).ObjectName) +
              EncodeLpstr(TMethodCallStmt(AStmt).Name) +
              EncodeExpr (TMethodCallStmt(AStmt).ObjExpr) +
              EncodeExprList(TMethodCallStmt(AStmt).Args)
  else if AStmt is TInheritedCallStmt then
    Result := EncodeLpstr('inh') +
              EncodeLpstr(TInheritedCallStmt(AStmt).Name) +
              EncodeExprList(TInheritedCallStmt(AStmt).Args)
  else
    raise EIfaceFormatError.Create(
      'EncodeStmt: unhandled statement node ' + AStmt.ClassName);
end;

{ Block payload: flag, then a flattened list of statements.  Local
  decls (type/const/var/proc) inside the block are NOT serialised
  yet — bodies of generic free routines typically don't declare
  nested types, and the importer doesn't currently re-emit nested
  proc decls.  Add as needed; nil ABlock encodes as a single
  'nil' lpstr. }
function EncodeBlock(AB: TBlock): string;
begin
  if AB = nil then
  begin Result := EncodeLpstr('nil'); Exit; end;
  Result := EncodeLpstr('block') + EncodeStmtList(AB.Stmts);
end;

{ Emit only generic free routines.  Generic class/interface
  templates are already in the TYPE block under 'generic-class' /
  'generic-interface' kinds — including those here would
  double-register.  Body AST is NOT serialised yet (no statement /
  expression writer); the wire-side MethodDecl comes back without
  a Body, which downstream instantiation will need.  Until the AST
  body serialiser lands, disk-loaded generic routines are
  signature-only. }
function WriteGenericRoutines(AIface: TUnitInterface): string;
var
  I:   Integer;
  G:   TGenericBody;
  SB:  TStringBuilder;
  Eligible: TObjectList;
begin
  Eligible := TObjectList.Create(False);
  SB := TStringBuilder.Create();
  try
    for I := 0 to AIface.GenericBodies.Count - 1 do
    begin
      G := TGenericBody(AIface.GenericBodies.Items[I]);
      if not G.IsType then Eligible.Add(G);
    end;
    SB.AppendLine('GENROUT ' + IntToStr(Eligible.Count));
    for I := 0 to Eligible.Count - 1 do
    begin
      G := TGenericBody(Eligible.Items[I]);
      SB.AppendLine(
        EncodeLpstr(G.Name) +
        EncodeTypeParamList(G.TypeParams, G.Constraints) +
        EncodeMethodDecl(G.MethodDecl) +
        EncodeBlock(G.MethodDecl.Body));
    end;
    SB.AppendLine('END');
    Result := SB.ToString();
  finally
    SB.Free();
    Eligible.Free();
  end;
end;

function WriteInlineBodies(AIface: TUnitInterface): string;
var
  I:  Integer;
  B:  TInlineBody;
  SB: TStringBuilder;
begin
  SB := TStringBuilder.Create();
  try
    SB.AppendLine('INLINE ' + IntToStr(AIface.InlineBodies.Count));
    for I := 0 to AIface.InlineBodies.Count - 1 do
    begin
      B := TInlineBody(AIface.InlineBodies.Items[I]);
      SB.AppendLine(EncodeLpstr(B.RoutineName) + EncodeBlock(B.Block));
    end;
    SB.AppendLine('END');
    Result := SB.ToString();
  finally
    SB.Free();
  end;
end;

function WriteUnitInterface(AIface: TUnitInterface): string;
begin
  Result :=
    IFACE_MAGIC + ' ' + IntToStr(IFACE_VERSION) + #10 +
    EncodeLpstr(AIface.Name) + #10 +
    WriteMeta           (AIface) +
    WriteTypes          (AIface) +
    WriteConsts         (AIface) +
    WriteVars           (AIface) +
    WriteRoutines       (AIface) +
    WriteGenericRoutines(AIface) +
    WriteInlineBodies   (AIface);
end;

{ ----- Reader ----------------------------------------------------- }

{ Cursor state passed by var-ref into the per-record readers — keeps
  the API surface scalar-friendly so we avoid the const-record-param
  string-field crash documented in memory. }

{ Char-classification on integer ordinals — Blaise lacks a Char
  type and S[i] returns a 1-byte string, so route through Ord() to
  get scalar Integer comparisons. }
function IsWhitespaceOrd(C: Integer): Boolean;
begin
  Result := (C = 32) or (C = 9) or (C = 10) or (C = 13);
end;

function IsUpperOrd(C: Integer): Boolean;
begin
  Result := (C >= Ord('A')) and (C <= Ord('Z'));
end;

function IsDigitOrd(C: Integer): Boolean;
begin
  Result := (C >= Ord('0')) and (C <= Ord('9'));
end;

{ Indexing convention throughout this unit: Blaise strings are
  0-indexed.  S[0] is the first byte; valid positions are 0 ..
  Length(S)-1.  Copy(S, start, len) treats start as 0-based.  Pos
  returns 0-based offset or -1 for not found.  APos cursor is
  0-based. }

procedure SkipWhitespace(const AText: string; var APos: Integer);
begin
  while (APos < Length(AText)) and IsWhitespaceOrd(Ord(AText[APos])) do
    Inc(APos);
end;

function ReadLpstrAt(const AText: string; var APos: Integer): string;
var
  ColonPos: Integer;
  Len:      Integer;
  LenStr:   string;
begin
  SkipWhitespace(AText, APos);
  ColonPos := APos;
  while (ColonPos < Length(AText)) and (AText[ColonPos] <> ':') do
    Inc(ColonPos);
  if ColonPos >= Length(AText) then
    raise EIfaceFormatError.Create('lpstr: missing '':'' separator');
  LenStr := Copy(AText, APos, ColonPos - APos);
  Len    := StrToInt(LenStr);
  if ColonPos + 1 + Len > Length(AText) then
    raise EIfaceFormatError.Create(Format(
      'lpstr: %d bytes requested, only %d available', [Len, Length(AText) - ColonPos - 1]));
  Result := Copy(AText, ColonPos + 1, Len);
  APos   := ColonPos + 1 + Len;
end;

function ReadInt64At(const AText: string; var APos: Integer): Int64;
begin
  Result := StrToInt64(ReadLpstrAt(AText, APos));
end;

function ReadFlagsAt(const AText: string; var APos: Integer;
                     out AIsString, AIsFloat: Boolean): Integer;
var
  B: Integer;
begin
  SkipWhitespace(AText, APos);
  if APos >= Length(AText) then
    raise EIfaceFormatError.Create('flags: end-of-input');
  B := Ord(AText[APos]) - Ord('0');
  Inc(APos);
  AIsString := (B and 1) <> 0;
  AIsFloat  := (B and 2) <> 0;
  Result := B;
end;

{ Split 'Unit.Type' into two strings.  Avoids passing TQualTypeRef
  records — same record-with-strings codegen bug that bit
  uSemanticImport.ResolveRef. }
procedure DecodeQualRef(const ASrc: string; var AUnit, AType: string);
var
  Dot: Integer;
begin
  { Blaise Pos and Copy are 0-based. }
  Dot := Pos('.', ASrc);
  if Dot < 0 then
  begin
    AUnit := '';
    AType := ASrc;
  end
  else
  begin
    AUnit := Copy(ASrc, 0, Dot);
    AType := Copy(ASrc, Dot + 1, Length(ASrc) - Dot - 1);
  end;
end;

{ Read an unterminated keyword (letters only) at the current cursor;
  consume it and advance past trailing whitespace.  Used for record
  tags ('CONST', 'END', etc.). }
function ReadTag(const AText: string; var APos: Integer): string;
var
  Start: Integer;
begin
  SkipWhitespace(AText, APos);
  Start := APos;
  while (APos < Length(AText)) and IsUpperOrd(Ord(AText[APos])) do
    Inc(APos);
  Result := Copy(AText, Start, APos - Start);
end;

function ReadDecimalAt(const AText: string; var APos: Integer): Integer;
var
  Start: Integer;
begin
  SkipWhitespace(AText, APos);
  Start := APos;
  while (APos < Length(AText)) and IsDigitOrd(Ord(AText[APos])) do
    Inc(APos);
  if APos = Start then
    raise EIfaceFormatError.Create('expected decimal digits');
  Result := StrToInt(Copy(AText, Start, APos - Start));
end;

procedure ReadHeader(const AText: string; var APos: Integer);
var
  MagicPos: Integer;
  Ver:      Integer;
begin
  SkipWhitespace(AText, APos);
  { Blaise Pos: 0-based result, -1 = not found.  Match at the
    cursor's current position means MagicPos = APos. }
  MagicPos := Pos(IFACE_MAGIC, AText);
  if MagicPos < 0 then
    raise EIfaceFormatError.Create('missing magic header');
  if MagicPos <> APos then
    raise EIfaceFormatError.Create(Format(
      'magic ''%s'' not at expected position %d (found at %d)',
      [IFACE_MAGIC, APos, MagicPos]));
  Inc(APos, Length(IFACE_MAGIC));
  SkipWhitespace(AText, APos);
  Ver := ReadDecimalAt(AText, APos);
  if Ver <> IFACE_VERSION then
    raise EIfaceFormatError.Create(Format(
      'unsupported version %d (this build understands %d)',
      [Ver, IFACE_VERSION]));
end;

procedure ReadConsts(const AText: string; var APos: Integer;
                     AIface: TUnitInterface);
var
  Count:    Integer;
  I:        Integer;
  Entry:    TConstEntry;
  Name:     string;
  RefStr:   string;
  IntVal:   Int64;
  StrVal:   string;
  IsString: Boolean;
  IsFloat:  Boolean;
  RefUnit:  string;
  RefType:  string;
begin
  Count := ReadDecimalAt(AText, APos);
  for I := 1 to Count do
  begin
    Name     := ReadLpstrAt(AText, APos);
    RefStr   := ReadLpstrAt(AText, APos);
    IntVal   := ReadInt64At(AText, APos);
    StrVal   := ReadLpstrAt(AText, APos);
    ReadFlagsAt(AText, APos, IsString, IsFloat);
    DecodeQualRef(RefStr, RefUnit, RefType);

    Entry := TConstEntry.Create();
    Entry.Decl := TConstDecl.Create();
    Entry.Decl.Name     := Name;
    Entry.Decl.IntVal   := IntVal;
    Entry.Decl.StrVal   := StrVal;
    Entry.Decl.IsString := IsString;
    Entry.Decl.IsFloat  := IsFloat;
    Entry.TypeRef       := MakeQualRef(RefUnit, RefType);
    AIface.AddConst(Entry);
  end;
  { Trailing 'END' marker — keeps the format extensible: future
    record types follow the same tag/payload/END pattern. }
  if ReadTag(AText, APos) <> 'END' then
    raise EIfaceFormatError.Create('CONST block: missing END marker');
end;

procedure ReadVars(const AText: string; var APos: Integer;
                   AIface: TUnitInterface);
var
  Count:   Integer;
  I:       Integer;
  Entry:   TVarEntry;
  RefStr:  string;
  RefUnit: string;
  RefType: string;
begin
  Count := ReadDecimalAt(AText, APos);
  for I := 1 to Count do
  begin
    Entry := TVarEntry.Create();
    Entry.Name := ReadLpstrAt(AText, APos);
    RefStr     := ReadLpstrAt(AText, APos);
    DecodeQualRef(RefStr, RefUnit, RefType);
    Entry.TypeRef    := MakeQualRef(RefUnit, RefType);
    Entry.IsThreadVar := DecodeBool(AText, APos);
    AIface.AddVar(Entry);
  end;
  if ReadTag(AText, APos) <> 'END' then
    raise EIfaceFormatError.Create('VAR block: missing END marker');
end;

{ Split a comma-joined member list back into a TStringList.  Empty
  input ⇒ empty list. }
procedure SplitMembers(const ASrc: string; ATarget: TStringList);
var
  Cur: string;
  P:   Integer;
begin
  Cur := ASrc;
  P   := Pos(',', Cur);
  while P >= 0 do
  begin
    ATarget.Add(Copy(Cur, 0, P));
    Cur := Copy(Cur, P + 1, Length(Cur) - P - 1);
    P   := Pos(',', Cur);
  end;
  if Length(Cur) > 0 then ATarget.Add(Cur);
end;

{ Parse 'name=ord,name=ord,…' into an EnumTypeDef using AddMember so
  the ordinal stash lands in Members.Objects[i] (where OrdinalAt
  reads it back from). }
procedure LoadEnumMembers(const ASrc: string; AEnum: TEnumTypeDef);
var
  Pairs: TStringList;
  I:     Integer;
  Pair:  string;
  Eq:    Integer;
  NameP: string;
  OrdP:  Integer;
begin
  Pairs := TStringList.Create();
  try
    SplitMembers(ASrc, Pairs);
    for I := 0 to Pairs.Count - 1 do
    begin
      Pair := Pairs.Strings[I];
      Eq   := Pos('=', Pair);
      if Eq < 0 then
      begin
        { Tolerate bare names from an older/hand-written .bif —
          assume sequential ordinals. }
        AEnum.AddMember(Pair, I);
      end
      else
      begin
        NameP := Copy(Pair, 0, Eq);
        OrdP  := StrToInt(Copy(Pair, Eq + 1, Length(Pair) - Eq - 1));
        AEnum.AddMember(NameP, OrdP);
      end;
    end;
  finally
    Pairs.Free();
  end;
end;

function ReadExpr(const AText: string; var APos: Integer): TASTExpr; forward;
function ReadStmt(const AText: string; var APos: Integer): TASTStmt; forward;
function ReadBlock(const AText: string; var APos: Integer): TBlock; forward;

procedure ReadExprList(const AText: string; var APos: Integer;
                       ATarget: TObjectList);
var
  C, I: Integer;
begin
  C := StrToInt(ReadLpstrAt(AText, APos));
  for I := 1 to C do ATarget.Add(ReadExpr(AText, APos));
end;

procedure ReadStmtList(const AText: string; var APos: Integer;
                       ATarget: TObjectList);
var
  C, I: Integer;
begin
  C := StrToInt(ReadLpstrAt(AText, APos));
  for I := 1 to C do ATarget.Add(ReadStmt(AText, APos));
end;

function ReadExceptHandler(const AText: string; var APos: Integer):
  TExceptHandlerClause;
var
  Body: TASTStmt;
begin
  Result := TExceptHandlerClause.Create();
  Result.VarName  := ReadLpstrAt(AText, APos);
  Result.TypeName := ReadLpstrAt(AText, APos);
  Body := ReadStmt(AText, APos);
  if Body is TCompoundStmt then
    Result.Body := TCompoundStmt(Body)
  else
  begin
    { Body always encoded via EncodeStmt of a TCompoundStmt — should
      never see anything else.  Defensive: wrap. }
    Result.Body := TCompoundStmt.Create();
    if Body <> nil then Result.Body.Stmts.Add(Body);
  end;
end;

function ReadCaseBranch(const AText: string; var APos: Integer): TCaseBranch;
begin
  Result := TCaseBranch.Create();
  ReadExprList(AText, APos, Result.Values);
  Result.Stmt := ReadStmt(AText, APos);
end;

function ReadExpr(const AText: string; var APos: Integer): TASTExpr;
var
  Kind: string;
  IL:   TIntLiteral;
  FL:   TFloatLiteral;
  SL:   TStringLiteral;
  IE:   TIdentExpr;
  BE:   TBinaryExpr;
  NE:   TNotExpr;
  FCE:  TFuncCallExpr;
  MCE:  TMethodCallExpr;
  FA:   TFieldAccessExpr;
  DE:   TDerefExpr;
  AoE:  TAddrOfExpr;
  SS:   TStringSubscriptExpr;
  AL:   TArrayLiteralExpr;
  IsE:  TIsExpr;
  AsE:  TAsExpr;
  SuE:  TSupportsExpr;
begin
  Kind := ReadLpstrAt(AText, APos);
  if Kind = 'nil' then begin Result := nil; Exit; end;

  if Kind = 'int' then
  begin
    IL := TIntLiteral.Create();
    IL.Value := StrToInt64(ReadLpstrAt(AText, APos));
    Result := IL;
  end
  else if Kind = 'float' then
  begin
    FL := TFloatLiteral.Create();
    FL.Value := ReadLpstrAt(AText, APos);
    Result := FL;
  end
  else if Kind = 'str' then
  begin
    SL := TStringLiteral.Create();
    SL.Value := ReadLpstrAt(AText, APos);
    Result := SL;
  end
  else if Kind = 'nillit' then
    Result := TNilLiteral.Create()
  else if Kind = 'id' then
  begin
    IE := TIdentExpr.Create();
    IE.Name := ReadLpstrAt(AText, APos);
    Result := IE;
  end
  else if Kind = 'bin' then
  begin
    BE := TBinaryExpr.Create();
    BE.Op    := TBinaryOp(StrToInt(ReadLpstrAt(AText, APos)));
    BE.Left  := ReadExpr(AText, APos);
    BE.Right := ReadExpr(AText, APos);
    Result := BE;
  end
  else if Kind = 'not' then
  begin
    NE := TNotExpr.Create();
    NE.Expr := ReadExpr(AText, APos);
    Result := NE;
  end
  else if Kind = 'call' then
  begin
    FCE := TFuncCallExpr.Create();
    FCE.Name := ReadLpstrAt(AText, APos);
    ReadExprList(AText, APos, FCE.Args);
    Result := FCE;
  end
  else if Kind = 'mcall' then
  begin
    MCE := TMethodCallExpr.Create();
    MCE.ObjectName := ReadLpstrAt(AText, APos);
    MCE.Name       := ReadLpstrAt(AText, APos);
    MCE.ObjExpr    := ReadExpr(AText, APos);
    ReadExprList(AText, APos, MCE.Args);
    Result := MCE;
  end
  else if Kind = 'field' then
  begin
    FA := TFieldAccessExpr.Create();
    FA.RecordName    := ReadLpstrAt(AText, APos);
    FA.FieldName     := ReadLpstrAt(AText, APos);
    FA.Base          := ReadExpr(AText, APos);
    FA.PropIndexExpr := ReadExpr(AText, APos);
    Result := FA;
  end
  else if Kind = 'deref' then
  begin
    DE := TDerefExpr.Create();
    DE.Expr := ReadExpr(AText, APos);
    Result := DE;
  end
  else if Kind = 'addr' then
  begin
    AoE := TAddrOfExpr.Create();
    AoE.Expr := ReadExpr(AText, APos);
    Result := AoE;
  end
  else if Kind = 'ssub' then
  begin
    SS := TStringSubscriptExpr.Create();
    SS.StrExpr   := ReadExpr(AText, APos);
    SS.IndexExpr := ReadExpr(AText, APos);
    Result := SS;
  end
  else if Kind = 'alit' then
  begin
    AL := TArrayLiteralExpr.Create();
    ReadExprList(AText, APos, AL.Elements);
    Result := AL;
  end
  else if Kind = 'isop' then
  begin
    IsE := TIsExpr.Create();
    IsE.Obj      := ReadExpr(AText, APos);
    IsE.TypeName := ReadLpstrAt(AText, APos);
    Result := IsE;
  end
  else if Kind = 'asop' then
  begin
    AsE := TAsExpr.Create();
    AsE.Obj      := ReadExpr(AText, APos);
    AsE.TypeName := ReadLpstrAt(AText, APos);
    Result := AsE;
  end
  else if Kind = 'supp' then
  begin
    SuE := TSupportsExpr.Create();
    SuE.Obj          := ReadExpr(AText, APos);
    SuE.IntfTypeName := ReadLpstrAt(AText, APos);
    SuE.OutVarName   := ReadLpstrAt(AText, APos);
    Result := SuE;
  end
  else
    raise EIfaceFormatError.Create(
      'ReadExpr: unknown expression kind ''' + Kind + '''');
end;

function ReadStmt(const AText: string; var APos: Integer): TASTStmt;
var
  Kind: string;
  ASn:  TAssignment;
  CSn:  TCompoundStmt;
  IFn:  TIfStmt;
  WSn:  TWhileStmt;
  RSn:  TRepeatStmt;
  FSn:  TForStmt;
  FISn: TForInStmt;
  TFSn: TTryFinallyStmt;
  TESn: TTryExceptStmt;
  RaSn: TRaiseStmt;
  CSSn: TCaseStmt;
  FASn: TFieldAssignment;
  SSAn: TStaticSubscriptAssign;
  PWSn: TPointerWriteStmt;
  PCn:  TProcCall;
  MCSn: TMethodCallStmt;
  ICSn: TInheritedCallStmt;
  C, I: Integer;
  Body: TASTStmt;
begin
  Kind := ReadLpstrAt(AText, APos);
  if Kind = 'nil' then begin Result := nil; Exit; end;

  if Kind = 'asn' then
  begin
    ASn := TAssignment.Create();
    ASn.Name := ReadLpstrAt(AText, APos);
    ASn.Expr := ReadExpr(AText, APos);
    Result := ASn;
  end
  else if Kind = 'comp' then
  begin
    CSn := TCompoundStmt.Create();
    ReadStmtList(AText, APos, CSn.Stmts);
    Result := CSn;
  end
  else if Kind = 'if' then
  begin
    IFn := TIfStmt.Create();
    IFn.Condition := ReadExpr(AText, APos);
    IFn.ThenStmt  := ReadStmt(AText, APos);
    IFn.ElseStmt  := ReadStmt(AText, APos);
    Result := IFn;
  end
  else if Kind = 'while' then
  begin
    WSn := TWhileStmt.Create();
    WSn.Condition := ReadExpr(AText, APos);
    WSn.Body      := ReadStmt(AText, APos);
    Result := WSn;
  end
  else if Kind = 'rep' then
  begin
    RSn := TRepeatStmt.Create();
    Body := ReadStmt(AText, APos);
    if Body is TCompoundStmt then
      RSn.Body := TCompoundStmt(Body)
    else
    begin
      RSn.Body := TCompoundStmt.Create();
      if Body <> nil then RSn.Body.Stmts.Add(Body);
    end;
    RSn.Condition := ReadExpr(AText, APos);
    Result := RSn;
  end
  else if Kind = 'for' then
  begin
    FSn := TForStmt.Create();
    FSn.VarName   := ReadLpstrAt(AText, APos);
    FSn.StartExpr := ReadExpr(AText, APos);
    FSn.EndExpr   := ReadExpr(AText, APos);
    FSn.IsDownTo  := DecodeBool(AText, APos);
    FSn.Body      := ReadStmt(AText, APos);
    Result := FSn;
  end
  else if Kind = 'forin' then
  begin
    FISn := TForInStmt.Create();
    FISn.VarName  := ReadLpstrAt(AText, APos);
    FISn.CollExpr := ReadExpr(AText, APos);
    FISn.Body     := ReadStmt(AText, APos);
    Result := FISn;
  end
  else if Kind = 'tryfin' then
  begin
    TFSn := TTryFinallyStmt.Create();
    Body := ReadStmt(AText, APos);
    if Body is TCompoundStmt then TFSn.TryBody := TCompoundStmt(Body)
                              else TFSn.TryBody := TCompoundStmt.Create();
    Body := ReadStmt(AText, APos);
    if Body is TCompoundStmt then TFSn.FinallyBody := TCompoundStmt(Body)
                              else TFSn.FinallyBody := TCompoundStmt.Create();
    Result := TFSn;
  end
  else if Kind = 'tryex' then
  begin
    TESn := TTryExceptStmt.Create();
    Body := ReadStmt(AText, APos);
    if Body is TCompoundStmt then TESn.TryBody := TCompoundStmt(Body)
                              else TESn.TryBody := TCompoundStmt.Create();
    C := StrToInt(ReadLpstrAt(AText, APos));
    for I := 1 to C do
      TESn.Handlers.Add(ReadExceptHandler(AText, APos));
    Body := ReadStmt(AText, APos);
    if Body is TCompoundStmt then TESn.ElseBody := TCompoundStmt(Body)
                              else TESn.ElseBody := nil;
    Body := ReadStmt(AText, APos);
    if Body is TCompoundStmt then TESn.ExceptBody := TCompoundStmt(Body)
                              else TESn.ExceptBody := nil;
    Result := TESn;
  end
  else if Kind = 'raise' then
  begin
    RaSn := TRaiseStmt.Create();
    RaSn.Expr := ReadExpr(AText, APos);
    Result := RaSn;
  end
  else if Kind = 'exit' then Result := TExitStmt.Create()
  else if Kind = 'brk'  then Result := TBreakStmt.Create()
  else if Kind = 'cont' then Result := TContinueStmt.Create()
  else if Kind = 'case' then
  begin
    CSSn := TCaseStmt.Create();
    CSSn.Selector := ReadExpr(AText, APos);
    C := StrToInt(ReadLpstrAt(AText, APos));
    for I := 1 to C do
      CSSn.Branches.Add(ReadCaseBranch(AText, APos));
    CSSn.ElseStmt := ReadStmt(AText, APos);
    Result := CSSn;
  end
  else if Kind = 'fasn' then
  begin
    FASn := TFieldAssignment.Create();
    FASn.RecordName    := ReadLpstrAt(AText, APos);
    FASn.FieldName     := ReadLpstrAt(AText, APos);
    FASn.Expr          := ReadExpr(AText, APos);
    FASn.ObjExpr       := ReadExpr(AText, APos);
    FASn.PropIndexExpr := ReadExpr(AText, APos);
    Result := FASn;
  end
  else if Kind = 'ssasn' then
  begin
    SSAn := TStaticSubscriptAssign.Create();
    SSAn.ArrayName := ReadLpstrAt(AText, APos);
    SSAn.IndexExpr := ReadExpr(AText, APos);
    SSAn.ValueExpr := ReadExpr(AText, APos);
    Result := SSAn;
  end
  else if Kind = 'pw' then
  begin
    PWSn := TPointerWriteStmt.Create();
    PWSn.PtrExpr := ReadExpr(AText, APos);
    PWSn.ValExpr := ReadExpr(AText, APos);
    Result := PWSn;
  end
  else if Kind = 'pcall' then
  begin
    PCn := TProcCall.Create();
    PCn.Name := ReadLpstrAt(AText, APos);
    ReadExprList(AText, APos, PCn.Args);
    Result := PCn;
  end
  else if Kind = 'mcs' then
  begin
    MCSn := TMethodCallStmt.Create();
    MCSn.ObjectName := ReadLpstrAt(AText, APos);
    MCSn.Name       := ReadLpstrAt(AText, APos);
    MCSn.ObjExpr    := ReadExpr(AText, APos);
    ReadExprList(AText, APos, MCSn.Args);
    Result := MCSn;
  end
  else if Kind = 'inh' then
  begin
    ICSn := TInheritedCallStmt.Create();
    ICSn.Name := ReadLpstrAt(AText, APos);
    ReadExprList(AText, APos, ICSn.Args);
    Result := ICSn;
  end
  else
    raise EIfaceFormatError.Create(
      'ReadStmt: unknown statement kind ''' + Kind + '''');
end;

function ReadBlock(const AText: string; var APos: Integer): TBlock;
var
  Kind: string;
begin
  Kind := ReadLpstrAt(AText, APos);
  if Kind = 'nil' then begin Result := nil; Exit; end;
  if Kind <> 'block' then
    raise EIfaceFormatError.Create('ReadBlock: expected ''block'' got ''' + Kind + '''');
  Result := TBlock.Create();
  ReadStmtList(AText, APos, Result.Stmts);
end;

function DecodeCount(const AText: string; var APos: Integer): Integer;
begin
  Result := StrToInt(ReadLpstrAt(AText, APos));
end;

function DecodeBool(const AText: string; var APos: Integer): Boolean;
begin
  Result := ReadLpstrAt(AText, APos) = '1';
end;

procedure ReadStringListBlock(const AText: string; var APos: Integer;
                              ATarget: TStringList);
var
  C, I: Integer;
begin
  C := DecodeCount(AText, APos);
  for I := 1 to C do ATarget.Add(ReadLpstrAt(AText, APos));
end;

{ Read a flattened field list into a TRecordTypeDef's Fields list.
  Each field is emitted with a single Name (the writer flattened
  multi-name decls); the reader rebuilds one TFieldDecl per name. }
procedure ReadFieldList(const AText: string; var APos: Integer;
                        ATarget: TObjectList);
var
  C, I:    Integer;
  FldName: string;
  FldType: string;
  IsWeak:  Boolean;
  F:       TFieldDecl;
begin
  C := DecodeCount(AText, APos);
  for I := 1 to C do
  begin
    FldName := ReadLpstrAt(AText, APos);
    FldType := ReadLpstrAt(AText, APos);
    IsWeak  := DecodeBool(AText, APos);
    F := TFieldDecl.Create();
    F.Names.Add(FldName);
    F.TypeName := FldType;
    F.IsWeak   := IsWeak;
    ATarget.Add(F);
  end;
end;

{ Inverse of EncodeMethodSig — builds a TRoutineSig from the
  per-method payload. }
function ReadMethodSig(const AText: string; var APos: Integer): TRoutineSig;
var
  RefStr:   string;
  RefUnit:  string;
  RefType:  string;
  Pc, J:    Integer;
  Param:    TMethodParam;
  FlagsStr: string;
begin
  Result := TRoutineSig.Create();
  Result.Name        := ReadLpstrAt(AText, APos);
  Result.IsFunction  := DecodeBool(AText, APos);
  RefStr             := ReadLpstrAt(AText, APos);
  DecodeQualRef(RefStr, RefUnit, RefType);
  Result.ReturnType  := MakeQualRef(RefUnit, RefType);
  Result.IsVirtual   := DecodeBool(AText, APos);
  Result.IsOverride  := DecodeBool(AText, APos);
  Result.ResolvedQbeName := ReadLpstrAt(AText, APos);
  Result.VTableSlot  := StrToInt(ReadLpstrAt(AText, APos));
  Pc := DecodeCount(AText, APos);
  for J := 1 to Pc do
  begin
    Param := TMethodParam.Create();
    Param.ParamName := ReadLpstrAt(AText, APos);
    Param.TypeName  := ReadLpstrAt(AText, APos);
    FlagsStr := ReadLpstrAt(AText, APos);
    DecodeParamFlags(StrToInt(FlagsStr), Param);
    Result.Params.Add(Param);
  end;
end;

procedure ReadMethodList(const AText: string; var APos: Integer;
                         ATarget: TObjectList);
var
  C, I: Integer;
begin
  C := DecodeCount(AText, APos);
  for I := 1 to C do ATarget.Add(ReadMethodSig(AText, APos));
end;

procedure ReadRecordPayload(const AText: string; var APos: Integer;
                            AEntry: TTypeEntry);
var
  Def: TRecordTypeDef;
begin
  Def := TRecordTypeDef.Create();
  Def.IsPacked := DecodeBool(AText, APos);
  ReadFieldList(AText, APos, Def.Fields);
  AEntry.Def := Def;
end;

procedure ReadClassPayload(const AText: string; var APos: Integer;
                           AEntry: TTypeEntry);
var
  Def:     TClassTypeDef;
  RefStr:  string;
  RefUnit: string;
  RefType: string;
begin
  Def := TClassTypeDef.Create();
  RefStr := ReadLpstrAt(AText, APos);
  DecodeQualRef(RefStr, RefUnit, RefType);
  AEntry.ParentClass  := MakeQualRef(RefUnit, RefType);
  Def.ParentName      := RefType;
  AEntry.InstanceSize := StrToInt64(ReadLpstrAt(AText, APos));
  ReadStringListBlock(AText, APos, AEntry.Attributes);
  ReadStringListBlock(AText, APos, AEntry.Implements);
  ReadFieldList(AText, APos, Def.Fields);
  ReadMethodList(AText, APos, AEntry.Methods);
  ReadPropertyList(AText, APos, Def.Properties);
  AEntry.IsClass := True;
  AEntry.Def     := Def;
end;

function ReadMethodDecl(const AText: string; var APos: Integer): TMethodDecl;
var
  HasReturn: Boolean;
  Pc, J:     Integer;
  Param:     TMethodParam;
  FlagsStr:  string;
begin
  Result := TMethodDecl.Create();
  Result.Name           := ReadLpstrAt(AText, APos);
  HasReturn             := DecodeBool(AText, APos);
  Result.ReturnTypeName := ReadLpstrAt(AText, APos);
  if not HasReturn then Result.ReturnTypeName := '';
  Result.IsVirtual      := DecodeBool(AText, APos);
  Result.IsOverride     := DecodeBool(AText, APos);
  Pc := DecodeCount(AText, APos);
  for J := 1 to Pc do
  begin
    Param := TMethodParam.Create();
    Param.ParamName := ReadLpstrAt(AText, APos);
    Param.TypeName  := ReadLpstrAt(AText, APos);
    FlagsStr := ReadLpstrAt(AText, APos);
    DecodeParamFlags(StrToInt(FlagsStr), Param);
    Result.Params.Add(Param);
  end;
end;

procedure ReadMethodDeclList(const AText: string; var APos: Integer;
                             ATarget: TObjectList);
var
  C, I: Integer;
begin
  C := DecodeCount(AText, APos);
  for I := 1 to C do ATarget.Add(ReadMethodDecl(AText, APos));
end;

procedure ReadPropertyList(const AText: string; var APos: Integer;
                           ATarget: TObjectList);
var
  C, I: Integer;
  P:    TPropertyDecl;
begin
  C := DecodeCount(AText, APos);
  for I := 1 to C do
  begin
    P := TPropertyDecl.Create();
    P.Name           := ReadLpstrAt(AText, APos);
    P.TypeName       := ReadLpstrAt(AText, APos);
    P.ReadName       := ReadLpstrAt(AText, APos);
    P.WriteName      := ReadLpstrAt(AText, APos);
    P.IndexParamName := ReadLpstrAt(AText, APos);
    P.IndexTypeName  := ReadLpstrAt(AText, APos);
    ATarget.Add(P);
  end;
end;

procedure ReadInlineBodies(const AText: string; var APos: Integer;
                           AIface: TUnitInterface);
var
  Count, I: Integer;
  B:        TInlineBody;
begin
  Count := ReadDecimalAt(AText, APos);
  for I := 1 to Count do
  begin
    B := TInlineBody.Create();
    B.RoutineName := ReadLpstrAt(AText, APos);
    B.Block       := ReadBlock(AText, APos);
    AIface.AddInlineBody(B);
  end;
  if ReadTag(AText, APos) <> 'END' then
    raise EIfaceFormatError.Create('INLINE block: missing END marker');
end;

procedure ReadGenericRoutines(const AText: string; var APos: Integer;
                              AIface: TUnitInterface);
var
  Count, I, J: Integer;
  G:           TGenericBody;
  Name:        string;
  MD:          TMethodDecl;
begin
  Count := ReadDecimalAt(AText, APos);
  for I := 1 to Count do
  begin
    Name := ReadLpstrAt(AText, APos);
    G := TGenericBody.Create();
    G.Name   := Name;
    G.IsType := False;
    ReadTypeParamList(AText, APos, G.TypeParams, G.Constraints);
    MD := ReadMethodDecl(AText, APos);
    { ReadMethodDecl doesn't reconstitute TypeParams (the
      method-decl payload omits them — they're encoded once at the
      GenericBody level).  Copy them across so a downstream
      instantiation sees a complete TMethodDecl template. }
    MD.TypeParams := TStringList.Create();
    for J := 0 to G.TypeParams.Count - 1 do
      MD.TypeParams.Add(G.TypeParams.Strings[J]);
    MD.Body := ReadBlock(AText, APos);
    if MD.Body <> nil then MD.OwnBody := True;
    G.MethodDecl := MD;
    AIface.AddGenericBody(G);
  end;
  if ReadTag(AText, APos) <> 'END' then
    raise EIfaceFormatError.Create('GENROUT block: missing END marker');
end;

procedure ReadMeta(const AText: string; var APos: Integer;
                   AIface: TUnitInterface);
var
  C, I: Integer;
begin
  AIface.SourceFile    := ReadLpstrAt(AText, APos);
  AIface.SourceHash    := ReadLpstrAt(AText, APos);
  AIface.CompilerId    := ReadLpstrAt(AText, APos);
  AIface.SourceModTime := ReadInt64At(AText, APos);
  C := DecodeCount(AText, APos);
  for I := 1 to C do
    AIface.UsedUnits.Add(ReadLpstrAt(AText, APos));
  if ReadTag(AText, APos) <> 'END' then
    raise EIfaceFormatError.Create('META block: missing END marker');
end;

procedure ReadTypeParamList(const AText: string; var APos: Integer;
                            ANames, AConstraints: TStringList);
var
  C, I: Integer;
begin
  C := DecodeCount(AText, APos);
  for I := 1 to C do
  begin
    ANames.Add(ReadLpstrAt(AText, APos));
    AConstraints.Add(ReadLpstrAt(AText, APos));
  end;
end;

procedure ReadGenericClassPayload(const AText: string; var APos: Integer;
                                  AEntry: TTypeEntry);
var
  Def:      TGenericTypeDef;
  ClassDef: TClassTypeDef;
  RefStr:   string;
  RefUnit:  string;
  RefType:  string;
  J, K:     Integer;
  Sig:      TRoutineSig;
  MD:       TMethodDecl;
  SrcPar:   TMethodParam;
  NewPar:   TMethodParam;
begin
  Def := TGenericTypeDef.Create();
  ReadTypeParamList(AText, APos, Def.ParamNames, Def.ParamConstraints);

  { Inner ClassDef: the ctor already created an empty one — free
    it and rebuild from the wire. }
  Def.ClassDef.Free();
  ClassDef := TClassTypeDef.Create();
  Def.ClassDef := ClassDef;

  RefStr := ReadLpstrAt(AText, APos);
  DecodeQualRef(RefStr, RefUnit, RefType);
  AEntry.ParentClass  := MakeQualRef(RefUnit, RefType);
  ClassDef.ParentName := RefType;
  AEntry.InstanceSize := StrToInt64(ReadLpstrAt(AText, APos));
  ReadStringListBlock(AText, APos, AEntry.Attributes);
  ReadStringListBlock(AText, APos, AEntry.Implements);
  ReadFieldList(AText, APos, ClassDef.Fields);
  ReadMethodList(AText, APos, AEntry.Methods);

  { Method bodies — parallel to AEntry.Methods, attached to
    ClassDef.Methods as full TMethodDecl objects so InstantiateGeneric
    can clone + substitute when the consumer references this template. }
  for J := 0 to AEntry.Methods.Count - 1 do
  begin
    Sig := TRoutineSig(AEntry.Methods.Items[J]);
    MD := TMethodDecl.Create();
    MD.Name           := Sig.Name;
    MD.OwnerTypeName  := AEntry.Name;
    MD.IsVirtual      := Sig.IsVirtual;
    MD.IsOverride     := Sig.IsOverride;
    MD.ReturnTypeName := Sig.ReturnType.TypeName;
    for K := 0 to Sig.Params.Count - 1 do
    begin
      SrcPar := TMethodParam(Sig.Params.Items[K]);
      NewPar := TMethodParam.Create();
      NewPar.ParamName    := SrcPar.ParamName;
      NewPar.TypeName     := SrcPar.TypeName;
      NewPar.IsVarParam   := SrcPar.IsVarParam;
      NewPar.IsConstParam := SrcPar.IsConstParam;
      NewPar.IsOpenArray  := SrcPar.IsOpenArray;
      MD.Params.Add(NewPar);
    end;
    MD.Body := ReadBlock(AText, APos);
    MD.OwnBody := MD.Body <> nil;
    ClassDef.Methods.Add(MD);
  end;

  AEntry.IsGeneric := True;
  AEntry.Def       := Def;
end;

procedure ReadGenericInterfacePayload(const AText: string; var APos: Integer;
                                      AEntry: TTypeEntry);
var
  Def:     TGenericInterfaceDef;
  IntfDef: TInterfaceTypeDef;
begin
  Def := TGenericInterfaceDef.Create();
  ReadTypeParamList(AText, APos, Def.ParamNames, Def.ParamConstraints);
  Def.IntfDef.Free();
  IntfDef := TInterfaceTypeDef.Create();
  Def.IntfDef := IntfDef;
  IntfDef.ParentName := ReadLpstrAt(AText, APos);
  ReadMethodDeclList(AText, APos, IntfDef.Methods);
  AEntry.IsGeneric := True;
  AEntry.Def       := Def;
end;

procedure ReadProcPayload(const AText: string; var APos: Integer;
                          AEntry: TTypeEntry);
var
  Def:      TProceduralTypeDef;
  Pc, J:    Integer;
  Param:    TMethodParam;
  FlagsStr: string;
begin
  Def := TProceduralTypeDef.Create();
  Def.IsFunction     := DecodeBool(AText, APos);
  Def.IsMethodPtr    := DecodeBool(AText, APos);
  Def.ReturnTypeName := ReadLpstrAt(AText, APos);
  Pc := DecodeCount(AText, APos);
  for J := 1 to Pc do
  begin
    Param := TMethodParam.Create();
    Param.ParamName := ReadLpstrAt(AText, APos);
    Param.TypeName  := ReadLpstrAt(AText, APos);
    FlagsStr := ReadLpstrAt(AText, APos);
    DecodeParamFlags(StrToInt(FlagsStr), Param);
    Def.Params.Add(Param);
  end;
  AEntry.Def := Def;
end;

procedure ReadInterfacePayload(const AText: string; var APos: Integer;
                               AEntry: TTypeEntry);
var
  Def: TInterfaceTypeDef;
begin
  Def := TInterfaceTypeDef.Create();
  Def.ParentName := ReadLpstrAt(AText, APos);
  ReadMethodDeclList(AText, APos, Def.Methods);
  AEntry.Def := Def;
end;

procedure ReadTypes(const AText: string; var APos: Integer;
                    AIface: TUnitInterface);
var
  Count:    Integer;
  I:        Integer;
  Kind:     string;
  Name:     string;
  Payload:  string;
  Entry:    TTypeEntry;
  EnumDef:  TEnumTypeDef;
  SetDef:   TSetTypeDef;
  AliasDef: TTypeAliasDef;
begin
  Count := ReadDecimalAt(AText, APos);
  for I := 1 to Count do
  begin
    Kind  := ReadLpstrAt(AText, APos);
    Name  := ReadLpstrAt(AText, APos);
    Entry := TTypeEntry.Create();
    Entry.Name := Name;

    if Kind = 'enum' then
    begin
      Payload := ReadLpstrAt(AText, APos);
      EnumDef := TEnumTypeDef.Create();
      LoadEnumMembers(Payload, EnumDef);
      Entry.Def := EnumDef;
    end
    else if Kind = 'set' then
    begin
      Payload := ReadLpstrAt(AText, APos);
      SetDef := TSetTypeDef.Create();
      SetDef.BaseTypeName := Payload;
      Entry.Def := SetDef;
    end
    else if Kind = 'alias' then
    begin
      Payload := ReadLpstrAt(AText, APos);
      AliasDef := TTypeAliasDef.Create();
      AliasDef.TypeName := Payload;
      Entry.Def := AliasDef;
    end
    else if Kind = 'record' then
      ReadRecordPayload(AText, APos, Entry)
    else if Kind = 'class' then
      ReadClassPayload(AText, APos, Entry)
    else if Kind = 'interface' then
      ReadInterfacePayload(AText, APos, Entry)
    else if Kind = 'proc' then
      ReadProcPayload(AText, APos, Entry)
    else if Kind = 'generic-class' then
      ReadGenericClassPayload(AText, APos, Entry)
    else if Kind = 'generic-interface' then
      ReadGenericInterfacePayload(AText, APos, Entry)
    else
    begin
      Entry.Free();
      raise EIfaceFormatError.Create('TYPE block: unknown kind ''' + Kind + '''');
    end;
    AIface.AddType(Entry);
  end;
  if ReadTag(AText, APos) <> 'END' then
    raise EIfaceFormatError.Create('TYPE block: missing END marker');
end;

{ Inverse of EncodeParamFlags. }
procedure DecodeParamFlags(AFlags: Integer; AParam: TMethodParam);
begin
  AParam.IsVarParam   := (AFlags and 1) <> 0;
  AParam.IsConstParam := (AFlags and 2) <> 0;
  AParam.IsOpenArray  := (AFlags and 4) <> 0;
  AParam.IsOutParam   := (AFlags and 8) <> 0;
end;

procedure ReadRoutines(const AText: string; var APos: Integer;
                       AIface: TUnitInterface);
var
  Count:    Integer;
  I, J:     Integer;
  PCount:   Integer;
  R:        TRoutineSig;
  RefStr:   string;
  RefUnit:  string;
  RefType:  string;
  IsFnStr:  string;
  Param:    TMethodParam;
  FlagsStr: string;
begin
  Count := ReadDecimalAt(AText, APos);
  for I := 1 to Count do
  begin
    R := TRoutineSig.Create();
    R.Name        := ReadLpstrAt(AText, APos);
    IsFnStr       := ReadLpstrAt(AText, APos);
    R.IsFunction  := IsFnStr <> '0';
    RefStr        := ReadLpstrAt(AText, APos);
    DecodeQualRef(RefStr, RefUnit, RefType);
    R.ReturnType  := MakeQualRef(RefUnit, RefType);
    PCount := StrToInt(ReadLpstrAt(AText, APos));
    for J := 1 to PCount do
    begin
      Param := TMethodParam.Create();
      Param.ParamName := ReadLpstrAt(AText, APos);
      Param.TypeName  := ReadLpstrAt(AText, APos);
      FlagsStr := ReadLpstrAt(AText, APos);
      DecodeParamFlags(StrToInt(FlagsStr), Param);
      R.Params.Add(Param);
    end;
    R.CallingConv := ReadLpstrAt(AText, APos);
    AIface.AddRoutine(R);
  end;
  if ReadTag(AText, APos) <> 'END' then
    raise EIfaceFormatError.Create('ROUT block: missing END marker');
end;

function ReadUnitInterface(const AText: string): TUnitInterface;
var
  Cur:    Integer;
  UName:  string;
  Tag:    string;
begin
  Cur := 0;  { 0-based cursor }
  ReadHeader(AText, Cur);
  UName := ReadLpstrAt(AText, Cur);
  Result := TUnitInterface.Create(UName);
  try
    while Cur < Length(AText) do
    begin
      SkipWhitespace(AText, Cur);
      if Cur >= Length(AText) then Break;
      Tag := ReadTag(AText, Cur);
      if      Tag = 'CONST'   then ReadConsts         (AText, Cur, Result)
      else if Tag = 'VAR'     then ReadVars           (AText, Cur, Result)
      else if Tag = 'TYPE'    then ReadTypes          (AText, Cur, Result)
      else if Tag = 'ROUT'    then ReadRoutines       (AText, Cur, Result)
      else if Tag = 'META'    then ReadMeta           (AText, Cur, Result)
      else if Tag = 'GENROUT' then ReadGenericRoutines(AText, Cur, Result)
      else if Tag = 'INLINE'  then ReadInlineBodies   (AText, Cur, Result)
      else if Tag = ''        then Break
      else
        raise EIfaceFormatError.Create(Format(
          'unknown record tag ''%s'' at position %d', [Tag, Cur]));
    end;
  except
    Result.Free();
    raise;
  end;
end;

{ FNV-1a 64-bit content hash.  Cheap, no crypto deps, change-
  detection grade.  Returned as a lowercase hex string for stable
  text-format encoding.

  Constants assembled from 32-bit halves because Blaise's literal
  parser caps numeric literals at Int64 range; FNV_OFFSET is
  >9.2e18 and doesn't fit. }
function ContentHashFnv1a64(const AContent: string): string;
var
  I:    Integer;
  H:    UInt64;
  Lo:   Integer;
  FnvOffset: UInt64;
  FnvPrime:  UInt64;
begin
  FnvOffset := (UInt64($cbf29ce4) shl 32) or UInt64($84222325);
  FnvPrime  := (UInt64($00000100) shl 32) or UInt64($000001b3);
  H := FnvOffset;
  for I := 0 to Length(AContent) - 1 do
  begin
    H := H xor UInt64(Byte(AContent[I + 1]));
    H := H * FnvPrime;
  end;
  Result := '';
  for I := 15 downto 0 do
  begin
    Lo := Integer((H shr (I * 4)) and $f);
    if Lo < 10 then Result := Result + Chr(Ord('0') + Lo)
              else Result := Result + Chr(Ord('a') + Lo - 10);
  end;
end;

procedure WriteUnitInterfaceToFile(AIface: TUnitInterface; const APath: string);
var
  Bytes: string;
  Src:   string;
  FIn:   TFileInputStream;
  FOut:  TFileOutputStream;
begin
  { Populate source-content hash from disk if SourceFile is set and
    readable.  Empty hash on absent/unreadable source — at load time
    that disables the source-match path and forces compiler-id-match
    fallback. }
  if (AIface.SourceFile <> '') and FileExists(AIface.SourceFile) then
  begin
    try
      FIn := TFileInputStream.Create(AIface.SourceFile);
      try
        SetLength(Src, Integer(FIn.Size()));
        if Length(Src) > 0 then
          FIn.Read(PChar(Src), Length(Src));
      finally
        FIn.Free();
      end;
      AIface.SourceHash := ContentHashFnv1a64(Src);
    except
      { Swallow IO failure — best-effort population. }
      AIface.SourceHash := '';
    end;
  end;

  Bytes := WriteUnitInterface(AIface);
  FOut := TFileOutputStream.Create(APath);
  try
    if Length(Bytes) > 0 then
      FOut.Write(PChar(Bytes), Length(Bytes));
  finally
    FOut.Close();
    FOut.Free();
  end;
end;

function ReadUnitInterfaceFromFile(const APath: string): TUnitInterface;
var
  Bytes: string;
  FIn:   TFileInputStream;
begin
  FIn := TFileInputStream.Create(APath);
  try
    SetLength(Bytes, Integer(FIn.Size()));
    if Length(Bytes) > 0 then
      FIn.Read(PChar(Bytes), Length(Bytes));
  finally
    FIn.Free();
  end;
  Result := ReadUnitInterface(Bytes);
end;

end.
