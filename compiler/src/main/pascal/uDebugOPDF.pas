{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uDebugOPDF;

{ OPDF debug information emitter.
  Produces a companion .opdf.s GNU assembly file that the linker folds into
  the ELF .opdf section.  The existing pdr debugger reads that section without
  modification.

  Platform note: section and relocation syntax targets Linux x86_64 (ELF).
  For macOS arm64 (Mach-O) change the .section directive to
  ".section __DATA,__opdf" and review .quad relocation constraints. }

interface

uses
  SysUtils, Classes, contnrs, uAST, uSymbolTable;

type
  TOPDFEmitter = class
  private
    FProgram:    TProgram;
    FSourceFile: string;
    FOutput:     TStringList;
    FTypeNames:  TStringList;   { sorted; Objects[i] = Pointer(PtrUInt(TypeID)) }
    FEmitted:    TStringList;   { sorted canonical names already written }
    FRecordCount:       Integer;
    FTotRecIdx:         Integer;  { FOutput line index of the TotalRecords placeholder }
    FUnitDirRecCountIdx: Integer;  { FOutput line index of the UnitDirectory RecordCount placeholder }
    FDone:        Boolean;

    function  FNV1a32(const S: string): Cardinal;
    function  GetOrAllocTypeID(const AName: string): Cardinal;
    function  HasBeenEmitted(const AName: string): Boolean;
    procedure MarkEmitted(const AName: string);
    procedure L(const AText: string);
    procedure EmitRecHdr(ARecType: Byte; ARecSize: Integer);
    procedure EmitNameLen(const AStr: string);
    procedure EmitNameData(const AStr: string);
    procedure EmitStrField(const AStr: string);
    procedure EmitSection;
    procedure EmitHeader;
    procedure EmitTypeDesc(AType: TTypeDesc);
    procedure EmitPrimitive(AType: TTypeDesc);
    procedure EmitEnum(AType: TEnumTypeDesc);
    procedure EmitRecord(AType: TRecordTypeDesc);
    procedure EmitClass(AType: TRecordTypeDesc);
    procedure EmitUtf8Str;
    procedure EmitGlobalVar(const AVarName: string; AType: TTypeDesc);
    procedure EmitFunctionScope(AMethod: TMethodDecl; AScopeID: Integer;
                                ADeclIdx: Integer; const ANextLabel: string);
    procedure EmitParameters(AMethod: TMethodDecl);
    procedure EmitLocalVars(ABlock: TBlock; AScopeID: Integer);
    procedure EmitFunctionScope_Main(AScopeID, ADeclIdx: Integer);
    procedure EmitUnitDirectory;
    procedure EmitPointer(AType: TPointerTypeDesc);
    procedure EmitArray(AType: TTypeDesc);
    procedure EmitSet(AType: TSetTypeDesc);
    procedure EmitInterface(AType: TInterfaceTypeDesc);
    procedure EmitProperties(AClass: TRecordTypeDesc);
    procedure EmitConstants;
    procedure EmitAllTypes;
    procedure EmitGlobalVars;
    procedure EmitFunctionScopes;
    procedure CollectStmtLines(AStmt: TASTStmt; ALines: TStringList);
    procedure EmitLineInfoForBlock(ABlock: TBlock; const AFuncLabel, AFuncName: string);
    procedure EmitLineInfoForScope(AMethod: TMethodDecl);
    procedure PatchTotalRecords;
    procedure PatchUnitDirRecordCount;
    procedure DoEmit;
    function  FuncLabel(AMethod: TMethodDecl): string;
    function  CanonicalName(AType: TTypeDesc): string;
    function  FieldsPayloadSize(ARec: TRecordTypeDesc): Integer;
    procedure EmitFields(ARec: TRecordTypeDesc);
  public
    constructor Create(AProgram: TProgram; const ASourceFile: string);
    destructor Destroy; override;
    procedure EmitToFile(const AFileName: string);
    function  GetOutput: string;
  end;

implementation

const
  REC_PRIMITIVE = 1;
  REC_GLOBALVAR = 2;
  REC_ANSISTR   = 4;   { kept for reference; Blaise now emits recUtf8Str instead }
  REC_UTF8STR   = 23;
  REC_POINTER   = 6;
  REC_ARRAY     = 7;
  REC_RECORD    = 8;
  REC_CLASS     = 9;
  REC_PROPERTY  = 10;
  REC_LOCALVAR  = 12;
  REC_PARAMETER = 13;
  REC_LINEINFO  = 14;
  REC_FUNCSCOPE = 15;
  REC_INTERFACE = 16;
  REC_ENUM      = 17;
  REC_SET       = 18;
  REC_UNITDIR   = 19;
  REC_CONSTANT  = 20;

  SK_INTEGER = 0;
  SK_BOOLEAN = 1;

  LOC_RBP = 1;

  PAT_FIELD  = 0;  { property accessor: direct field offset }
  PAT_METHOD = 1;  { property accessor: method call }
  PAT_NONE   = 2;  { property accessor: no accessor }

  CK_ORD    = 0;  { constant kind: ordinal (Int64) }
  CK_STRING = 1;  { constant kind: string bytes }

constructor TOPDFEmitter.Create(AProgram: TProgram; const ASourceFile: string);
begin
  inherited Create();
  FProgram    := AProgram;
  FSourceFile := ASourceFile;
  FOutput     := TStringList.Create();
  FTypeNames  := TStringList.Create();
  FTypeNames.Sorted        := True;
  FTypeNames.CaseSensitive := True;
  FEmitted    := TStringList.Create();
  FEmitted.Sorted        := True;
  FEmitted.CaseSensitive := True;
  FRecordCount        := 0;
  FTotRecIdx          := -1;
  FUnitDirRecCountIdx := -1;
  FDone               := False;
end;

destructor TOPDFEmitter.Destroy;
begin
  FEmitted.Free();
  FTypeNames.Free();
  FOutput.Free();
  inherited Destroy();
end;

procedure TOPDFEmitter.L(const AText: string);
begin
  FOutput.Add(AText);
end;

function TOPDFEmitter.FNV1a32(const S: string): Cardinal;
const
  FNV_PRIME  = $01000193;
  FNV_OFFSET = $811C9DC5;
var
  I: Integer;
begin
  Result := FNV_OFFSET;
  for I := 1 to Length(S) do
  begin
    Result := Result xor Cardinal(Ord(S[I]));
    Result := Result * FNV_PRIME;
  end;
  if Result = 0 then
    Result := 1;
end;

function TOPDFEmitter.GetOrAllocTypeID(const AName: string): Cardinal;
var
  Idx: Integer;
begin
  if FTypeNames.Find(AName, Idx) then
    Result := Cardinal(PtrUInt(FTypeNames.Objects[Idx]))
  else
  begin
    Result := FNV1a32(AName);
    FTypeNames.AddObject(AName, TObject(PtrUInt(Result)));
  end;
end;

function TOPDFEmitter.HasBeenEmitted(const AName: string): Boolean;
var
  Idx: Integer;
begin
  Result := FEmitted.Find(AName, Idx);
end;

procedure TOPDFEmitter.MarkEmitted(const AName: string);
begin
  if not HasBeenEmitted(AName) then
    FEmitted.Add(AName);
end;

procedure TOPDFEmitter.EmitRecHdr(ARecType: Byte; ARecSize: Integer);
begin
  L('    .byte ' + IntToStr(ARecType) + '  # RecType');
  L('    .int  ' + IntToStr(ARecSize) + '  # RecSize');
  FRecordCount := FRecordCount + 1;
end;

procedure TOPDFEmitter.EmitNameLen(const AStr: string);
begin
  L('    .word ' + IntToStr(Length(AStr)) + '  # NameLen');
end;

procedure TOPDFEmitter.EmitNameData(const AStr: string);
begin
  if Length(AStr) > 0 then
    L('    .ascii "' + AStr + '"');
end;

procedure TOPDFEmitter.EmitStrField(const AStr: string);
begin
  EmitNameLen(AStr);
  EmitNameData(AStr);
end;

function TOPDFEmitter.CanonicalName(AType: TTypeDesc): string;
var
  SA: TStaticArrayTypeDesc;
begin
  if AType = nil then
  begin
    Exit('Pointer');
  end;
  case AType.Kind of
    tyString:
      Result := 'Utf8String';
    tyPointer:
      if TPointerTypeDesc(AType).BaseType = nil then
        Result := 'Pointer'
      else
        Result := '^' + CanonicalName(TPointerTypeDesc(AType).BaseType);
    tyStaticArray:
    begin
      SA := TStaticArrayTypeDesc(AType);
      if SA.Name <> '' then
        Result := SA.Name
      else
        Result := 'array[' + IntToStr(SA.LowBound) + '..' +
                  IntToStr(SA.HighBound) + '] of ' +
                  CanonicalName(SA.ElementType);
    end;
    tyOpenArray:
      if AType.Name <> '' then
        Result := AType.Name
      else
        Result := 'array of ' + CanonicalName(TOpenArrayTypeDesc(AType).ElementType);
  else
    if AType.Name = '' then
      Result := 'Pointer'
    else
      Result := AType.Name;
  end;
end;

function TOPDFEmitter.FieldsPayloadSize(ARec: TRecordTypeDesc): Integer;
var
  I: Integer;
  F: TFieldInfo;
begin
  Result := 0;
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Items[I]);
    Result := Result + 4 + 4 + 2 + Length(F.Name);
  end;
end;

procedure TOPDFEmitter.EmitFields(ARec: TRecordTypeDesc);
var
  I: Integer;
  F: TFieldInfo;
  FTypeName: string;
begin
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Items[I]);
    if F.TypeDesc <> nil then
      FTypeName := CanonicalName(F.TypeDesc)
    else
      FTypeName := 'Pointer';
    L('    # field: ' + F.Name);
    L('    .int  ' + IntToStr(GetOrAllocTypeID(FTypeName)) + '  # FieldTypeID');
    L('    .int  ' + IntToStr(F.Offset) + '  # Offset');
    EmitStrField(F.Name);
  end;
end;

procedure TOPDFEmitter.EmitTypeDesc(AType: TTypeDesc);
var
  CName: string;
begin
  if AType = nil then Exit;
  CName := CanonicalName(AType);
  if HasBeenEmitted(CName) then Exit;
  case AType.Kind of
    tyInteger, tyInt64, tyUInt32, tyUInt64,
    tySmallInt, tyWord, tyByte, tyBoolean:
      EmitPrimitive(AType);
    tyString:
      EmitUtf8Str();
    tyEnum:
      EmitEnum(TEnumTypeDesc(AType));
    tyRecord:
      EmitRecord(TRecordTypeDesc(AType));
    tyClass:
      EmitClass(TRecordTypeDesc(AType));
    tyPointer:
      EmitPointer(TPointerTypeDesc(AType));
    tyStaticArray, tyOpenArray, tyDynArray:
      EmitArray(AType);
    tySet:
      EmitSet(TSetTypeDesc(AType));
    tyInterface:
      EmitInterface(TInterfaceTypeDesc(AType));
  else
    { tyVoid, tyNil, tyPChar: no OPDF record }
  end;
end;

procedure TOPDFEmitter.EmitPrimitive(AType: TTypeDesc);
var
  CName: string;
  SubKind, IsSigned, SzB: Byte;
  RecSize: Integer;
begin
  CName := CanonicalName(AType);
  if HasBeenEmitted(CName) then Exit;
  MarkEmitted(CName);

  SzB      := AType.RawSize();
  case AType.Kind of
    tyBoolean:         begin SubKind := SK_BOOLEAN; IsSigned := 0; end;
    tyInt64, tyInteger, tySmallInt:
                       begin SubKind := SK_INTEGER;  IsSigned := 1; end;
  else
    SubKind := SK_INTEGER; IsSigned := 0;
  end;
  RecSize := 9 + Length(CName);

  L('');
  L('    # recPrimitive: ' + CName);
  EmitRecHdr(REC_PRIMITIVE, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  L('    .byte ' + IntToStr(SzB) + '  # SizeInBytes');
  L('    .byte ' + IntToStr(IsSigned) + '  # IsSigned');
  L('    .byte ' + IntToStr(SubKind) + '  # SubKind');
  EmitStrField(CName);
end;

procedure TOPDFEmitter.EmitUtf8Str;
const
  CNAME    = 'Utf8String';
  { Data-pointer convention: variable holds pointer to char data.
    The 12-byte header lives before it at negative offsets:
      data_ptr − 12 = RefCount
      data_ptr −  8 = Length    (byte count = character count for ASCII range)
      data_ptr −  4 = Capacity
    Encoding is always UTF-8; no code-page or element-size fields. }
  RC_OFFSET  = -12;
  LEN_OFFSET = -8;
  CAP_OFFSET = -4;
var
  RecSize: Integer;
begin
  if HasBeenEmitted(CNAME) then Exit;
  MarkEmitted(CNAME);
  RecSize := 12 + Length(CNAME);   { TDefUtf8String fixed part = 12 bytes }
  L('');
  L('    # recUtf8Str: Utf8String (data_ptr-12=RC, data_ptr-8=Len, data_ptr-4=Cap, data_ptr+0=chars)');
  EmitRecHdr(REC_UTF8STR, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CNAME)) + '  # TypeID');
  L('    .word ' + IntToStr(RC_OFFSET)  + '  # RefCountOffset');
  L('    .word ' + IntToStr(LEN_OFFSET) + '  # LengthOffset');
  L('    .word ' + IntToStr(CAP_OFFSET) + '  # CapacityOffset');
  EmitStrField(CNAME);
end;

procedure TOPDFEmitter.EmitEnum(AType: TEnumTypeDesc);
var
  CName: string;
  RecSize, MembSize, I: Integer;
begin
  CName := AType.Name;
  if HasBeenEmitted(CName) then Exit;
  MarkEmitted(CName);

  MembSize := 0;
  for I := 0 to AType.Members.Count - 1 do
    MembSize := MembSize + 8 + 2 + Length(AType.Members.Strings[I]);

  RecSize := 11 + Length(CName) + MembSize;

  L('');
  L('    # recEnum: ' + CName);
  EmitRecHdr(REC_ENUM, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  L('    .byte 4                          # SizeInBytes');
  L('    .int  ' + IntToStr(AType.Members.Count) + '  # MemberCount');
  EmitStrField(CName);
  for I := 0 to AType.Members.Count - 1 do
  begin
    L('    # member: ' + AType.Members.Strings[I]);
    L('    .quad ' + IntToStr(I) + '  # Value');
    EmitStrField(AType.Members.Strings[I]);
  end;
end;

procedure TOPDFEmitter.EmitRecord(AType: TRecordTypeDesc);
var
  CName: string;
  RecSize, I: Integer;
  F: TFieldInfo;
begin
  CName := AType.Name;
  if HasBeenEmitted(CName) then Exit;
  MarkEmitted(CName);

  for I := 0 to AType.Fields.Count - 1 do
  begin
    F := TFieldInfo(AType.Fields.Items[I]);
    if F.TypeDesc <> nil then
      EmitTypeDesc(F.TypeDesc);
  end;

  RecSize := 14 + Length(CName) + FieldsPayloadSize(AType);

  L('');
  L('    # recRecord: ' + CName);
  EmitRecHdr(REC_RECORD, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  L('    .int  ' + IntToStr(AType.Fields.Count) + '  # FieldCount');
  L('    .int  ' + IntToStr(AType.TotalSize()) + '  # TotalSize');
  EmitStrField(CName);
  EmitFields(AType);
end;

procedure TOPDFEmitter.EmitClass(AType: TRecordTypeDesc);
var
  CName, ParentName: string;
  ParentID: Cardinal;
  RecSize, I: Integer;
  F: TFieldInfo;
begin
  CName := AType.Name;
  if HasBeenEmitted(CName) then Exit;
  MarkEmitted(CName);

  if AType.Parent <> nil then
  begin
    EmitClass(AType.Parent);
    ParentName := AType.Parent.Name;
    ParentID   := GetOrAllocTypeID(ParentName);
  end
  else
  begin
    ParentName := '';
    ParentID   := 0;
  end;

  for I := 0 to AType.Fields.Count - 1 do
  begin
    F := TFieldInfo(AType.Fields.Items[I]);
    if F.TypeDesc <> nil then
      EmitTypeDesc(F.TypeDesc);
  end;

  RecSize := 26 + Length(CName) + FieldsPayloadSize(AType);

  L('');
  L('    # recClass: ' + CName);
  EmitRecHdr(REC_CLASS, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  L('    .int  ' + IntToStr(ParentID) + '  # ParentTypeID');
  if AType.HasVTable() then
    L('    .quad vtable_' + CName + '  # VMTAddress')
  else
    L('    .quad 0  # VMTAddress (no vtable)');
  L('    .int  ' + IntToStr(AType.TotalSize()) + '  # InstanceSize');
  L('    .int  ' + IntToStr(AType.Fields.Count) + '  # FieldCount');
  EmitStrField(CName);
  EmitFields(AType);
  EmitProperties(AType);
end;

procedure TOPDFEmitter.EmitGlobalVar(const AVarName: string; AType: TTypeDesc);
var
  CName: string;
  RecSize: Integer;
begin
  if AType <> nil then
  begin
    CName := CanonicalName(AType);
    EmitTypeDesc(AType);
  end
  else
    CName := 'Pointer';

  RecSize := 14 + Length(AVarName);

  L('');
  L('    # recGlobalVar: ' + AVarName);
  EmitRecHdr(REC_GLOBALVAR, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  L('    .quad ' + AVarName + '  # Address (linker-resolved)');
  EmitStrField(AVarName);
end;

procedure TOPDFEmitter.EmitFunctionScope(AMethod: TMethodDecl; AScopeID: Integer;
  ADeclIdx: Integer; const ANextLabel: string);
var
  FuncName, Label_: string;
  RecSize: Integer;
begin
  FuncName := AMethod.Name;
  Label_   := FuncLabel(AMethod);
  RecSize  := 24 + Length(FuncName);

  L('');
  L('    # recFunctionScope: ' + FuncName);
  EmitRecHdr(REC_FUNCSCOPE, RecSize);
  L('    .int  ' + IntToStr(AScopeID) + '  # ScopeID');
  L('    .quad ' + Label_ + '  # LowPC');
  if ANextLabel <> '' then
    L('    .quad ' + ANextLabel + '  # HighPC (approx: next function start)')
  else
    L('    .quad 0  # HighPC (last function)');
  L('    .word ' + IntToStr(ADeclIdx) + '  # DeclIndex');
  EmitStrField(FuncName);
end;

procedure TOPDFEmitter.EmitParameters(AMethod: TMethodDecl);
var
  I: Integer;
  P: TMethodParam;
  CName: string;
  RecSize: Integer;
begin
  for I := 0 to AMethod.Params.Count - 1 do
  begin
    P := TMethodParam(AMethod.Params.Items[I]);
    if P.ResolvedType <> nil then
      CName := CanonicalName(P.ResolvedType)
    else
      CName := 'Pointer';
    RecSize := 9 + Length(P.ParamName);
    L('');
    L('    # recParameter: ' + P.ParamName);
    EmitRecHdr(REC_PARAMETER, RecSize);
    L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
    L('    .byte ' + IntToStr(Ord(P.IsVarParam)) + '  # IsVar');
    L('    .byte ' + IntToStr(Ord(P.IsConstParam)) + '  # IsConst');
    L('    .byte 0  # IsOut');
    EmitStrField(P.ParamName);
  end;
end;

procedure TOPDFEmitter.EmitLocalVars(ABlock: TBlock; AScopeID: Integer);
var
  DeclIdx, RBPOffset: Integer;
  I, J: Integer;
  V: TVarDecl;
  CName, VarName: string;
  RawSz, RecSize: Integer;
begin
  DeclIdx   := 0;
  RBPOffset := 0;
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    V := TVarDecl(ABlock.Decls.Items[I]);
    if V.IsGlobal then Continue;
    if V.ResolvedType <> nil then
    begin
      CName  := CanonicalName(V.ResolvedType);
      RawSz  := V.ResolvedType.RawSize();
    end
    else
    begin
      CName := 'Pointer';
      RawSz := 8;
    end;
    RBPOffset := RBPOffset - ((RawSz + 7) and (-8));  { round up to 8-byte alignment; -8 = not 7 }
    for J := 0 to V.Names.Count - 1 do
    begin
      VarName := V.Names.Strings[J];
      RecSize := 15 + Length(VarName);
      L('');
      L('    # recLocalVar: ' + VarName);
      EmitRecHdr(REC_LOCALVAR, RecSize);
      L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
      L('    .int  ' + IntToStr(AScopeID) + '  # ScopeID');
      L('    .byte ' + IntToStr(LOC_RBP) + '  # LocationExpr (RBP-relative)');
      L('    .word ' + IntToStr(DeclIdx) + '  # DeclIndex');
      EmitNameLen(VarName);
      L('    .word ' + IntToStr(RBPOffset) + '  # LocationData (RBP offset)');
      EmitNameData(VarName);
      DeclIdx := DeclIdx + 1;
    end;
  end;
end;

function TOPDFEmitter.FuncLabel(AMethod: TMethodDecl): string;
begin
  if AMethod.OwnerTypeName = '' then
    Result := AMethod.Name
  else
    Result := AMethod.OwnerTypeName + '_' + AMethod.Name;
end;

procedure TOPDFEmitter.EmitSection;
begin
  L('    # OPDF debug companion file — generated by Blaise compiler');
  L('    # Platform: linux-x86_64 (ELF)');
  L('    # macOS arm64 adaptation: change .section to .section __DATA,__opdf');
  L('    .section .opdf, "aw", @progbits');
  L('');
  L('.Lopdf_start:');
end;

procedure TOPDFEmitter.EmitHeader;
begin
  L('    # OPDF header (32 bytes)');
  L('    .byte 79, 80, 68, 70           # Magic: OPDF');
  L('    .word 1                        # Version');
  L('    .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0  # BuildID (zeroed)');
  L('    .byte 2                        # TargetArch: archX86_64');
  L('    .byte 8                        # PointerSize: 8');
  FTotRecIdx := FOutput.Count;
  L('    .int  0                        # TotalRecords (patched at end)');
  L('    .int  1                        # Flags: OPDF_FLAG_HAS_DIRECTORY');
end;

procedure TOPDFEmitter.EmitFunctionScope_Main(AScopeID, ADeclIdx: Integer);
var
  ProgName: string;
  RecSize: Integer;
begin
  ProgName := FProgram.Name;
  RecSize  := 24 + Length(ProgName);
  L('');
  L('    # recFunctionScope: ' + ProgName);
  EmitRecHdr(REC_FUNCSCOPE, RecSize);
  L('    .int  ' + IntToStr(AScopeID) + '  # ScopeID');
  L('    .quad main  # LowPC (program entry point)');
  L('    .quad 0  # HighPC (last scope)');
  L('    .word ' + IntToStr(ADeclIdx) + '  # DeclIndex');
  EmitStrField(ProgName);
  EmitLineInfoForBlock(FProgram.Block, 'main', ProgName);
end;

procedure TOPDFEmitter.EmitUnitDirectory;
var
  DirName: string;
  RecSize: Integer;
begin
  DirName := FProgram.Name;
  RecSize := 14 + Length(DirName);  { 4(UnitCount)+4(Offset)+4(Count)+2(NameLen) }
  L('');
  L('    # recUnitDirectory');
  EmitRecHdr(REC_UNITDIR, RecSize);
  L('    .int  1  # UnitCount');
  L('    .int  .Lopdf_unit0_start - .Lopdf_start  # RecordOffset');
  FUnitDirRecCountIdx := FOutput.Count;
  L('    .int  0  # RecordCount (patched)');
  EmitStrField(DirName);
  L('');
  L('.Lopdf_unit0_start:');
end;

procedure TOPDFEmitter.EmitPointer(AType: TPointerTypeDesc);
var
  CName: string;
  TargetID: Cardinal;
  RecSize: Integer;
begin
  CName := CanonicalName(AType);
  if HasBeenEmitted(CName) then Exit;
  MarkEmitted(CName);

  if AType.BaseType <> nil then
  begin
    EmitTypeDesc(AType.BaseType);
    TargetID := GetOrAllocTypeID(CanonicalName(AType.BaseType));
  end
  else
    TargetID := 0;

  RecSize := 10 + Length(CName);
  L('');
  L('    # recPointer: ' + CName);
  EmitRecHdr(REC_POINTER, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  L('    .int  ' + IntToStr(TargetID) + '  # TargetTypeID (0 = untyped)');
  EmitStrField(CName);
end;

procedure TOPDFEmitter.EmitArray(AType: TTypeDesc);
var
  CName, ElemName: string;
  ElemID: Cardinal;
  SA: TStaticArrayTypeDesc;
  IsDyn, RecSize: Integer;
begin
  CName := CanonicalName(AType);
  if HasBeenEmitted(CName) then Exit;
  MarkEmitted(CName);

  if AType.Kind = tyStaticArray then
  begin
    SA := TStaticArrayTypeDesc(AType);
    EmitTypeDesc(SA.ElementType);
    ElemName := CanonicalName(SA.ElementType);
    ElemID   := GetOrAllocTypeID(ElemName);
    IsDyn    := 0;
    RecSize  := 12 + Length(CName) + 16;  { 12 fixed + name + 1×TArrayBound (16 bytes) }
    L('');
    L('    # recArray (static): ' + CName);
    EmitRecHdr(REC_ARRAY, RecSize);
    L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
    L('    .int  ' + IntToStr(ElemID) + '  # ElementTypeID');
    L('    .byte 1  # Dimensions');
    L('    .byte ' + IntToStr(IsDyn) + '  # IsDynamic');
    EmitStrField(CName);
    L('    .quad ' + IntToStr(SA.LowBound) + '  # LowerBound');
    L('    .quad ' + IntToStr(SA.HighBound) + '  # UpperBound');
  end
  else if AType.Kind = tyDynArray then
  begin
    EmitTypeDesc(TDynArrayTypeDesc(AType).ElementType);
    ElemName := CanonicalName(TDynArrayTypeDesc(AType).ElementType);
    ElemID   := GetOrAllocTypeID(ElemName);
    IsDyn    := 1;
    RecSize  := 12 + Length(CName);
    L('');
    L('    # recArray (dynamic): ' + CName);
    EmitRecHdr(REC_ARRAY, RecSize);
    L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
    L('    .int  ' + IntToStr(ElemID) + '  # ElementTypeID');
    L('    .byte 1  # Dimensions');
    L('    .byte ' + IntToStr(IsDyn) + '  # IsDynamic');
    EmitStrField(CName);
  end
  else
  begin
    EmitTypeDesc(TOpenArrayTypeDesc(AType).ElementType);
    ElemName := CanonicalName(TOpenArrayTypeDesc(AType).ElementType);
    ElemID   := GetOrAllocTypeID(ElemName);
    IsDyn    := 1;
    RecSize  := 12 + Length(CName);
    L('');
    L('    # recArray (dynamic): ' + CName);
    EmitRecHdr(REC_ARRAY, RecSize);
    L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
    L('    .int  ' + IntToStr(ElemID) + '  # ElementTypeID');
    L('    .byte 1  # Dimensions');
    L('    .byte ' + IntToStr(IsDyn) + '  # IsDynamic');
    EmitStrField(CName);
  end;
end;

procedure TOPDFEmitter.EmitSet(AType: TSetTypeDesc);
var
  CName: string;
  BaseID: Cardinal;
  SzB, RecSize: Integer;
begin
  CName := AType.Name;
  if CName = '' then CName := 'set of ' + AType.BaseType.Name;
  if HasBeenEmitted(CName) then Exit;
  MarkEmitted(CName);

  EmitTypeDesc(AType.BaseType);
  BaseID := GetOrAllocTypeID(AType.BaseType.Name);

  SzB := AType.RawSize();
  RecSize := 15 + Length(CName);  { 4(TypeID)+4(BaseTypeID)+1(SzB)+4(LBound)+2(NameLen) }

  L('');
  L('    # recSet: ' + CName);
  EmitRecHdr(REC_SET, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  L('    .int  ' + IntToStr(BaseID) + '  # BaseTypeID');
  L('    .byte ' + IntToStr(SzB) + '  # SizeInBytes');
  L('    .int  0  # LowerBound');
  EmitStrField(CName);
end;

procedure TOPDFEmitter.EmitInterface(AType: TInterfaceTypeDesc);
var
  CName: string;
  ParentID: Cardinal;
  I, MethodRecSize, RecSize: Integer;
  MName: string;
begin
  CName := AType.Name;
  if HasBeenEmitted(CName) then Exit;
  MarkEmitted(CName);

  if AType.Parent <> nil then
  begin
    EmitInterface(AType.Parent);
    ParentID := GetOrAllocTypeID(AType.Parent.Name);
  end
  else
    ParentID := 0;

  MethodRecSize := 0;
  for I := 0 to AType.MethodCount() - 1 do
    MethodRecSize := MethodRecSize + 7 + Length(AType.MethodName(I));

  RecSize := 31 + Length(CName) + MethodRecSize;
  { 4(TypeID)+4(ParentID)+1(IntfType)+16(GUID)+4(MethodCount)+2(NameLen) = 31 }

  L('');
  L('    # recInterface: ' + CName);
  EmitRecHdr(REC_INTERFACE, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  L('    .int  ' + IntToStr(ParentID) + '  # ParentTypeID');
  L('    .byte 0  # IntfType: itfCOM');
  L('    .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0  # GUID (zeroed)');
  L('    .int  ' + IntToStr(AType.MethodCount()) + '  # MethodCount');
  EmitStrField(CName);
  for I := 0 to AType.MethodCount() - 1 do
  begin
    MName := AType.MethodName(I);
    L('    # method: ' + MName);
    L('    .int  0  # ReturnTypeID (0 = procedure)');
    L('    .byte 0  # ParamCount');
    EmitStrField(MName);
  end;
end;

procedure TOPDFEmitter.EmitProperties(AClass: TRecordTypeDesc);
var
  I: Integer;
  PI: TPropertyInfo;
  PropTypeID, ClassTypeID: Cardinal;
  ReadType, WriteType: Integer;
  RecSize: Integer;
  RF: TFieldInfo;
begin
  if AClass.Properties.Count = 0 then Exit;
  ClassTypeID := GetOrAllocTypeID(AClass.Name);
  for I := 0 to AClass.Properties.Count - 1 do
  begin
    PI := TPropertyInfo(AClass.Properties.Items[I]);
    if PI.TypeDesc <> nil then
      PropTypeID := GetOrAllocTypeID(CanonicalName(PI.TypeDesc))
    else
      PropTypeID := 0;

    { Determine read accessor type }
    if PI.ReadField <> '' then
      ReadType := PAT_FIELD
    else if PI.ReadMethod <> '' then
      ReadType := PAT_METHOD
    else
      ReadType := PAT_NONE;

    { Determine write accessor type }
    if PI.WriteField <> '' then
      WriteType := PAT_FIELD
    else if PI.WriteMethod <> '' then
      WriteType := PAT_METHOD
    else
      WriteType := PAT_NONE;

    RecSize := 28 + Length(PI.Name);
    { 4(ClassTypeID)+4(PropTypeID)+1(ReadType)+1(WriteType)+8(ReadAddr)+8(WriteAddr)+2(NameLen) }

    L('');
    L('    # recProperty: ' + PI.Name);
    EmitRecHdr(REC_PROPERTY, RecSize);
    L('    .int  ' + IntToStr(ClassTypeID) + '  # ClassTypeID');
    L('    .int  ' + IntToStr(PropTypeID) + '  # PropertyTypeID');
    L('    .byte ' + IntToStr(ReadType) + '  # ReadType');
    L('    .byte ' + IntToStr(WriteType) + '  # WriteType');

    { ReadAddr }
    if ReadType = PAT_FIELD then
    begin
      RF := AClass.FindField(PI.ReadField);
      if RF <> nil then
        L('    .quad ' + IntToStr(RF.Offset) + '  # ReadAddr (field offset)')
      else
        L('    .quad 0  # ReadAddr (field not found)');
    end
    else if ReadType = PAT_METHOD then
      L('    .quad ' + AClass.Name + '_' + PI.ReadMethod + '  # ReadAddr (getter)')
    else
      L('    .quad 0  # ReadAddr (none)');

    { WriteAddr }
    if WriteType = PAT_FIELD then
    begin
      RF := AClass.FindField(PI.WriteField);
      if RF <> nil then
        L('    .quad ' + IntToStr(RF.Offset) + '  # WriteAddr (field offset)')
      else
        L('    .quad 0  # WriteAddr (field not found)');
    end
    else if WriteType = PAT_METHOD then
      L('    .quad ' + AClass.Name + '_' + PI.WriteMethod + '  # WriteAddr (setter)')
    else
      L('    .quad 0  # WriteAddr (none)');

    EmitStrField(PI.Name);
  end;
end;

procedure TOPDFEmitter.EmitConstants;
var
  I: Integer;
  C: TConstDecl;
  TypeID: Cardinal;
  RecSize: Integer;
begin
  for I := 0 to FProgram.Block.ConstDecls.Count - 1 do
  begin
    C := TConstDecl(FProgram.Block.ConstDecls.Items[I]);
    if C.IsString then
    begin
      TypeID  := GetOrAllocTypeID('AnsiString');
      RecSize := 9 + Length(C.StrVal) + Length(C.Name);
      L('');
      L('    # recConstant: ' + C.Name);
      EmitRecHdr(REC_CONSTANT, RecSize);
      L('    .int  ' + IntToStr(TypeID) + '  # TypeID');
      L('    .byte ' + IntToStr(CK_STRING) + '  # ConstKind: ckString');
      L('    .word ' + IntToStr(Length(C.StrVal)) + '  # ValueLen');
      EmitNameLen(C.Name);
      if Length(C.StrVal) > 0 then
        L('    .ascii "' + C.StrVal + '"  # Value');
      EmitNameData(C.Name);
    end
    else
    begin
      TypeID  := 0;  { untyped integer constant }
      RecSize := 17 + Length(C.Name);  { 9 fixed + 8 (Int64 value) + name }
      L('');
      L('    # recConstant: ' + C.Name);
      EmitRecHdr(REC_CONSTANT, RecSize);
      L('    .int  ' + IntToStr(TypeID) + '  # TypeID');
      L('    .byte ' + IntToStr(CK_ORD) + '  # ConstKind: ckOrd');
      L('    .word 8  # ValueLen');
      EmitNameLen(C.Name);
      L('    .quad ' + IntToStr(C.IntVal) + '  # Value');
      EmitNameData(C.Name);
    end;
  end;
end;

procedure TOPDFEmitter.EmitAllTypes;
var
  I: Integer;
  TD: TTypeDecl;
  TDesc: TTypeDesc;
  GI: TGenericInstance;
begin
  EmitUtf8Str();
  if FProgram.SymbolTable <> nil then
  begin
    EmitPrimitive(FProgram.SymbolTable.TypeInteger);
    EmitPrimitive(FProgram.SymbolTable.TypeInt64);
    EmitPrimitive(FProgram.SymbolTable.TypeByte);
    EmitPrimitive(FProgram.SymbolTable.TypeBoolean);
  end;
  for I := 0 to FProgram.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(FProgram.Block.TypeDecls.Items[I]);
    if FProgram.SymbolTable <> nil then
    begin
      TDesc := FProgram.SymbolTable.FindType(TD.Name);
      if TDesc <> nil then
        EmitTypeDesc(TDesc);
    end;
  end;
  for I := 0 to FProgram.GenericInstances.Count - 1 do
  begin
    GI := TGenericInstance(FProgram.GenericInstances.Items[I]);
    if (GI.TypeDesc <> nil) and (GI.TypeDesc.Kind = tyClass) then
      EmitTypeDesc(GI.TypeDesc);
  end;
end;

procedure TOPDFEmitter.EmitGlobalVars;
var
  I, J: Integer;
  V: TVarDecl;
begin
  for I := 0 to FProgram.Block.Decls.Count - 1 do
  begin
    V := TVarDecl(FProgram.Block.Decls.Items[I]);
    if not V.IsGlobal then Continue;
    for J := 0 to V.Names.Count - 1 do
      EmitGlobalVar(V.Names.Strings[J], V.ResolvedType);
  end;
end;

procedure TOPDFEmitter.EmitFunctionScopes;
var
  I, NextI, ScopeID, DeclIdx: Integer;
  M, NM: TMethodDecl;
  Labels: TStringList;
  NextLabel: string;
begin
  Labels := TStringList.Create();
  try
    for I := 0 to FProgram.Block.ProcDecls.Count - 1 do
    begin
      M := TMethodDecl(FProgram.Block.ProcDecls.Items[I]);
      if M.IsExternal or (M.Body = nil) then
        Labels.Add('')
      else
        Labels.Add(FuncLabel(M));
    end;

    ScopeID := 0;
    DeclIdx := 0;
    for I := 0 to FProgram.Block.ProcDecls.Count - 1 do
    begin
      M := TMethodDecl(FProgram.Block.ProcDecls.Items[I]);
      if M.IsExternal or (M.Body = nil) then Continue;

      ScopeID := ScopeID + 1;

      NextLabel := '';
      NextI := I + 1;
      while NextI < Labels.Count do
      begin
        if Labels.Strings[NextI] <> '' then
        begin
          NextLabel := Labels.Strings[NextI];
          Break;
        end;
        NextI := NextI + 1;
      end;

      EmitFunctionScope(M, ScopeID, DeclIdx, NextLabel);
      EmitParameters(M);
      if M.Body <> nil then
        EmitLocalVars(M.Body, ScopeID);
      EmitLineInfoForScope(M);

      DeclIdx := DeclIdx + 1;
    end;

    { Main program body — emit as a function scope keyed on 'main' }
    if FProgram.Block.Stmts.Count > 0 then
    begin
      ScopeID := ScopeID + 1;
      EmitFunctionScope_Main(ScopeID, DeclIdx);
    end;
  finally
    Labels.Free();
  end;
end;

procedure TOPDFEmitter.CollectStmtLines(AStmt: TASTStmt; ALines: TStringList);
var
  I: Integer;
  Key: string;
begin
  if AStmt = nil then Exit;
  if AStmt.Line > 0 then
  begin
    Key := IntToStr(AStmt.Line);
    if ALines.IndexOf(Key) < 0 then
      ALines.AddObject(Key, TObject(PtrUInt(AStmt.Col)));
  end;
  if AStmt is TCompoundStmt then
  begin
    for I := 0 to TCompoundStmt(AStmt).Stmts.Count - 1 do
      CollectStmtLines(TASTStmt(TCompoundStmt(AStmt).Stmts.Items[I]), ALines);
  end
  else if AStmt is TIfStmt then
  begin
    CollectStmtLines(TIfStmt(AStmt).ThenStmt, ALines);
    CollectStmtLines(TIfStmt(AStmt).ElseStmt, ALines);
  end
  else if AStmt is TWhileStmt then
    CollectStmtLines(TWhileStmt(AStmt).Body, ALines)
  else if AStmt is TRepeatStmt then
    CollectStmtLines(TRepeatStmt(AStmt).Body, ALines)
  else if AStmt is TForStmt then
    CollectStmtLines(TForStmt(AStmt).Body, ALines)
  else if AStmt is TForInStmt then
    CollectStmtLines(TForInStmt(AStmt).Body, ALines)
  else if AStmt is TTryFinallyStmt then
  begin
    CollectStmtLines(TTryFinallyStmt(AStmt).TryBody, ALines);
    CollectStmtLines(TTryFinallyStmt(AStmt).FinallyBody, ALines);
  end
  else if AStmt is TTryExceptStmt then
  begin
    CollectStmtLines(TTryExceptStmt(AStmt).TryBody, ALines);
    CollectStmtLines(TTryExceptStmt(AStmt).ExceptBody, ALines);
  end
  else if AStmt is TCaseStmt then
  begin
    for I := 0 to TCaseStmt(AStmt).Branches.Count - 1 do
      CollectStmtLines(TCaseBranch(TCaseStmt(AStmt).Branches.Items[I]).Stmt, ALines);
    CollectStmtLines(TCaseStmt(AStmt).ElseStmt, ALines);
  end;
end;

procedure TOPDFEmitter.EmitLineInfoForBlock(ABlock: TBlock;
  const AFuncLabel, AFuncName: string);
var
  Lines: TStringList;
  I, LineNum, ColNum, RecSize: Integer;
begin
  Lines := TStringList.Create();
  try
    for I := 0 to ABlock.Stmts.Count - 1 do
      CollectStmtLines(TASTStmt(ABlock.Stmts.Items[I]), Lines);
    if Lines.Count = 0 then Exit;
    RecSize := 16 + Length(FSourceFile);
    for I := 0 to Lines.Count - 1 do
    begin
      LineNum := StrToInt(Lines.Strings[I]);
      ColNum := Integer(PtrUInt(Lines.Objects[I]));
      L('');
      L('    # recLineInfo: line ' + Lines.Strings[I] + ' in ' + AFuncName);
      EmitRecHdr(REC_LINEINFO, RecSize);
      L('    .quad ' + AFuncLabel + '  # Address (function start; per-stmt addr needs QBE label support)');
      L('    .int  ' + IntToStr(LineNum) + '  # LineNumber');
      L('    .word ' + IntToStr(ColNum) + '  # ColumnNumber');
      EmitStrField(FSourceFile);
    end;
  finally
    Lines.Free();
  end;
end;

procedure TOPDFEmitter.EmitLineInfoForScope(AMethod: TMethodDecl);
begin
  if AMethod.Body = nil then Exit;
  EmitLineInfoForBlock(AMethod.Body, FuncLabel(AMethod), AMethod.Name);
end;

procedure TOPDFEmitter.PatchTotalRecords;
begin
  if FTotRecIdx >= 0 then
    FOutput.Strings[FTotRecIdx] := '    .int  ' + IntToStr(FRecordCount) +
                                  '                        # TotalRecords';
end;

procedure TOPDFEmitter.PatchUnitDirRecordCount;
begin
  { RecordCount for the unit = all records except the directory record itself }
  if FUnitDirRecCountIdx >= 0 then
    FOutput.Strings[FUnitDirRecCountIdx] := '    .int  ' + IntToStr(FRecordCount - 1) +
                                           '  # RecordCount';
end;

procedure TOPDFEmitter.DoEmit;
begin
  if FDone then Exit;
  FDone := True;
  EmitSection();
  EmitHeader();
  EmitUnitDirectory();
  EmitAllTypes();
  EmitGlobalVars();
  EmitConstants();
  EmitFunctionScopes();
  PatchTotalRecords();
  PatchUnitDirRecordCount();
end;

procedure TOPDFEmitter.EmitToFile(const AFileName: string);
begin
  DoEmit();
  FOutput.SaveToFile(AFileName);
end;

function TOPDFEmitter.GetOutput: string;
begin
  DoEmit();
  Result := FOutput.Text;
end;

end.
