{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

unit uSymbolTable;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, contnrs;

type
  { ------------------------------------------------------------------ }
  {  Type descriptors                                                   }
  { ------------------------------------------------------------------ }

  TTypeKind = (
    tyInteger,    { Int32  — QBE 'w' }
    tyInt64,      { Int64  — QBE 'l' }
    tyUInt32,     { UInt32 — QBE 'w' unsigned }
    tyByte,       { Byte   — QBE 'b' }
    tyBoolean,    { Boolean — stored as byte, 0/1 only }
    tyString,     { ARC-managed UTF-8 string }
    tyRecord,     { Stack-allocated aggregate (Phase 2) }
    tyClass,      { Heap-allocated, single-inheritance (Phase 2) }
    tyInterface,  { Zero-GUID interface reference (Phase 3) }
    tyVoid,       { No value — used as procedure return type }
    tyNil,        { Pseudo-type for the nil literal; compatible with tyClass }
    tyPointer,    { Typed or untyped pointer — QBE 'l'; see TPointerTypeDesc }
    tyEnum,       { Enumeration type — stored as QBE 'w' (Integer); see TEnumTypeDesc }
    tyOpenArray,  { Open-array parameter — two-register ABI: data ptr + high index }
    tyStaticArray, { Fixed-size array: stack-allocated, compile-time bounds }
    tyPChar, { Opaque C pointer for interop: PChar(str) / string(pchar) }
    tySet    { Bit-set over an enum base type — QBE 'w' (≤32 members) or 'l' (≤64) }
  );

  TTypeDesc = class
  public
    Kind: TTypeKind;
    Name: string;
    function IsNumeric: Boolean;
    function IsString: Boolean;
    function IsOrdinal: Boolean;
    function IsRecord: Boolean;
    { Size in bytes for QBE allocation. }
    function ByteSize: Integer;
    { QBE alloc alignment: 4 for integer-only records, 8 for pointer/string. }
    function AllocAlign: Integer;
    { True storage footprint for a single value: 1 for Byte/Boolean, 4 for Integer,
      8 for pointer/string/Int64.  Use for array element sizing; ByteSize pads
      small scalars to 4 for standalone-variable alignment. }
    function RawSize: Integer;
  end;

  { Typed or untyped pointer descriptor.
    BaseType = nil means untyped 'Pointer'; non-nil means '^BaseType'. }
  TPointerTypeDesc = class(TTypeDesc)
  public
    BaseType: TTypeDesc;  { not owned; nil = untyped Pointer }
  end;

  { Open-array parameter descriptor.
    Carries the element type; the two-register ABI (data ptr + high index)
    is handled entirely in the parser, semantic pass, and codegen. }
  TOpenArrayTypeDesc = class(TTypeDesc)
  public
    ElementType: TTypeDesc;  { not owned }
  end;

  { Static array descriptor: fixed-size, stack-allocated, compile-time bounds.
    Element access: base_ptr + (I − LowBound) × ElementType.ByteSize. }
  TStaticArrayTypeDesc = class(TTypeDesc)
  public
    ElementType: TTypeDesc;  { not owned }
    LowBound:    Integer;
    HighBound:   Integer;
  end;

  { Enum type descriptor.  Members are ordered; ordinal values are 0..N-1.
    Stored as QBE 'w' (same as Integer).  Each member is also registered in
    the symbol table as a skConstant with this type descriptor. }
  TEnumTypeDesc = class(TTypeDesc)
  public
    Members: TStringList;  { owned — ordered member names }
    constructor Create(const AName: string);
    destructor  Destroy; override;
    function    OrdinalOf(const AMember: string): Integer;
  end;

  { Set type descriptor.  BaseType is the element enum; BitCount is the number
    of bits required (= BaseType.Members.Count).  Stored as QBE 'w' for ≤32
    members, 'l' for 33–64.  Each member ordinal N maps to bit (1 shl N). }
  TSetTypeDesc = class(TTypeDesc)
  public
    BaseType: TEnumTypeDesc;  { not owned }
    BitCount: Integer;        { = BaseType.Members.Count }
  end;

  { Field entry inside a record type descriptor. }
  TFieldInfo = class
  public
    Name:     string;
    TypeDesc: TTypeDesc;  { not owned }
    Offset:   Integer;    { byte offset from record base }
    IsWeak:   Boolean;    { set when the class field was declared [Weak];
                            field cleanup emits _WeakClear for weak fields
                            and field assignment bypasses addref/release. }
  end;

  { One entry in a class vtable — tracks slot index and implementing method. }
  TVTableEntry = class
  public
    Slot:     Integer;  { index in vtable }
    MethName: string;   { unqualified method name }
    ImplName: string;   { fully-qualified QBE label, e.g. $TDog_Speak }
  end;

  TInterfaceTypeDesc = class;  { forward }

  { Property descriptor — one per declared property on a class. }
  TPropertyInfo = class
  public
    Name:        string;
    TypeDesc:    TTypeDesc;   { not owned — resolved by semantic analysis }
    ReadField:   string;      { '' if method-backed read }
    ReadMethod:  string;      { '' if field-backed read }
    WriteField:  string;      { '' if method-backed write or read-only }
    WriteMethod: string;      { '' if field-backed write or read-only }
  end;

  { Extended type descriptor for record types. }
  TRecordTypeDesc = class(TTypeDesc)
  private
    FFields:          TObjectList;  { owned TFieldInfo }
    FKeys:            TStringList;  { sorted, case-insensitive; Objects[] = TFieldInfo (not owned) }
    FParent:          TRecordTypeDesc;   { not owned; nil for root classes }
    FVTable:          TObjectList;  { owned TVTableEntry; nil if no virtual methods }
    FImplements:      TObjectList;  { not owned — TInterfaceTypeDesc references }
    FProperties:      TObjectList;  { owned TPropertyInfo }
    FHasDestroyMethod: Boolean;     { True when the class declares a 'Destroy' method }
  public
    constructor Create(const AName: string; AKind: TTypeKind = tyRecord);
    destructor Destroy; override;
    procedure AddField(const AName: string; AType: TTypeDesc);
    function  FindField(const AName: string): TFieldInfo;
    function  TotalSize: Integer;
    function  MaxAlign: Integer;

    { Vtable management }
    function  HasVTable: Boolean;
    function  VTableCount: Integer;
    function  VTableEntryAt(ASlot: Integer): TVTableEntry;
    function  FindVTableSlot(const AMethodName: string): Integer;
    function  AddVTableSlot(const AMethodName, AImplName: string): Integer;
    procedure OverrideVTableSlot(ASlot: Integer; const AImplName: string);
    procedure CopyVTableFrom(AParent: TRecordTypeDesc);

    { Interface implements tracking }
    procedure AddImplements(AIntf: TInterfaceTypeDesc);
    function  ImplementsCount: Integer;
    function  ImplementsIntfAt(AIndex: Integer): TInterfaceTypeDesc;

    { Property tracking }
    procedure AddProperty(AProp: TPropertyInfo);
    function  FindProperty(const AName: string): TPropertyInfo;

    property  Fields: TObjectList read FFields;
    property  Parent: TRecordTypeDesc read FParent write FParent;
    property  HasDestroyMethod: Boolean
              read FHasDestroyMethod write FHasDestroyMethod;
  end;

  { Type descriptor for zero-GUID interface types (Phase 3). }
  TInterfaceTypeDesc = class(TTypeDesc)
  private
    FMethods:     TStringList;  { method names, case-insensitive }
    FReturnTypes: TStringList;  { parallel: return type name, '' = procedure }
    FParent:      TInterfaceTypeDesc;  { not owned; nil if no parent }
  public
    constructor Create(const AName: string);
    destructor Destroy; override;
    procedure AddMethod(const AName: string;
                const AReturnTypeName: string = '');
    function  HasMethod(const AName: string): Boolean;
    function  MethodCount: Integer;
    function  MethodName(AIndex: Integer): string;
    function  MethodReturnTypeName(AIndex: Integer): string;
    function  MethodIndex(const AName: string): Integer;
    property  Parent: TInterfaceTypeDesc read FParent write FParent;
  end;

  { ------------------------------------------------------------------ }
  {  Symbols                                                            }
  { ------------------------------------------------------------------ }

  TSymbolKind = (
    skVariable,
    skType,
    skProcedure,
    skFunction,
    skParameter,
    skVarParameter,
    skConstant     { built-in or user-declared constant; ConstValue holds the integer value }
  );

  TParamDesc = class
  public
    Name:     string;
    TypeDesc: TTypeDesc;  { not owned }
    IsConst:  Boolean;
    IsVar:    Boolean;
  end;

  TSymbol = class
  public
    Name:       string;
    Kind:       TSymbolKind;
    TypeDesc:   TTypeDesc;    { not owned; nil for procedures }
    Params:     TObjectList;  { owned TParamDesc; populated for procedures/functions }
    ConstValue:  Int64;       { valid when Kind = skConstant; integer/bool/enum value }
    ConstString: string;      { valid when Kind = skConstant and type is tyString }
    IsWeak:     Boolean;      { true for variables declared [Weak]; codegen
                                keys off this to emit _WeakAssign instead
                                of the strong addref/release pattern. }
    IsGlobal:   Boolean;      { true for program-level variables; codegen uses
                                QBE data-section storage instead of stack alloc }
    constructor Create(const AName: string; AKind: TSymbolKind; AType: TTypeDesc);
    destructor Destroy; override;
  end;

  { ------------------------------------------------------------------ }
  {  Scope                                                              }
  { ------------------------------------------------------------------ }

  TScope = class
  private
    FParent:  TScope;
    FSymbols: TObjectList;  { owns all TSymbol in this scope }
    FKeys:    TStringList;  { sorted, case-insensitive; Objects[] = TSymbol (not owned) }
  public
    constructor Create(AParent: TScope);
    destructor Destroy; override;
    property Parent: TScope read FParent;
    { Returns False if name already defined in this scope; caller must free ASymbol. }
    function Define(ASymbol: TSymbol): Boolean;
    function LookupLocal(const AName: string): TSymbol;
    function Lookup(const AName: string): TSymbol;
  end;

  { ------------------------------------------------------------------ }
  {  Symbol table                                                       }
  { ------------------------------------------------------------------ }

  TSymbolTable = class
  private
    FScopeStack: TObjectList;   { owned TScope, index 0 = global }
    FAllTypes:   TObjectList;   { owned TTypeDesc }
    FGenerics:   TStringList;   { non-owning: base name → TGenericTypeDef* (void ptr) }

    FTypeInteger: TTypeDesc;
    FTypeInt64:   TTypeDesc;
    FTypeUInt32:  TTypeDesc;
    FTypeByte:    TTypeDesc;
    FTypeBoolean: TTypeDesc;
    FTypeString:  TTypeDesc;
    FTypeVoid:    TTypeDesc;
    FTypeNil:     TTypeDesc;
    FTypePointer: TPointerTypeDesc;  { untyped Pointer }
    FTypePChar:   TTypeDesc;         { opaque C pointer }

    function GetCurrentScope: TScope;
    function GetScopeDepth: Integer;
    function NewType(AKind: TTypeKind; const AName: string): TTypeDesc;
    procedure RegisterBuiltins;
  public
    constructor Create;
    destructor Destroy; override;

    { Scope management }
    function  PushScope: TScope;
    procedure PopScope;
    property  CurrentScope: TScope read GetCurrentScope;
    property  ScopeDepth: Integer read GetScopeDepth;

    { Symbol management — owns ASymbol on success; caller must free on False }
    function Define(ASymbol: TSymbol): Boolean;
    { Define in global (outermost) scope regardless of current push depth. }
    function DefineGlobal(ASymbol: TSymbol): Boolean;
    function Lookup(const AName: string): TSymbol;

    { Type lookup — case-insensitive, returns nil if not found }
    function FindType(const AName: string): TTypeDesc;

    { Creates a new TRecordTypeDesc, registers it in FAllTypes, and returns it.
      Caller must then add fields and register it as a skType symbol. }
    function NewRecordType(const AName: string): TRecordTypeDesc;

    { Creates a new class type descriptor (tyClass, heap-allocated). }
    function NewClassType(const AName: string): TRecordTypeDesc;

    { Creates a new interface type descriptor (tyInterface). }
    function NewInterfaceType(const AName: string): TInterfaceTypeDesc;

    { Creates a typed pointer descriptor '^BaseType'. Registered in FAllTypes. }
    function NewPointerType(const AName: string; ABase: TTypeDesc): TPointerTypeDesc;
    function NewEnumType(const AName: string): TEnumTypeDesc;
    function NewSetType(const AName: string; ABase: TEnumTypeDesc): TSetTypeDesc;

    { Creates an open-array type descriptor for element type AElementType.
      Registered in FAllTypes so the table owns the lifetime. }
    function NewOpenArrayType(AElementType: TTypeDesc): TOpenArrayTypeDesc;

    { Creates a static array type descriptor. Registered in FAllTypes. }
    function NewStaticArrayType(AElementType: TTypeDesc;
      ALow, AHigh: Integer): TStaticArrayTypeDesc;

    { Generic template registry — stores TGenericTypeDef as TObject to avoid
      circular unit dependency with uAST. Callers cast the result. }
    procedure RegisterGeneric(const AName: string; ATempl: TObject);
    function  FindGeneric(const AName: string): TObject;

    { Convenience type accessors }
    property TypeInteger: TTypeDesc read FTypeInteger;
    property TypeInt64:   TTypeDesc read FTypeInt64;
    property TypeUInt32:  TTypeDesc read FTypeUInt32;
    property TypeByte:    TTypeDesc read FTypeByte;
    property TypeBoolean: TTypeDesc read FTypeBoolean;
    property TypeString:  TTypeDesc read FTypeString;
    property TypeVoid:    TTypeDesc    read FTypeVoid;
    property TypeNil:     TTypeDesc    read FTypeNil;
    property TypePointer: TPointerTypeDesc read FTypePointer;
    property TypePChar:   TTypeDesc        read FTypePChar;
  end;

implementation

{ ------------------------------------------------------------------ }
{ TTypeDesc                                                           }
{ ------------------------------------------------------------------ }

function TTypeDesc.IsNumeric: Boolean;
begin
  Result := Kind in [tyInteger, tyInt64, tyUInt32, tyByte, tyEnum];
end;

function TTypeDesc.IsString: Boolean;
begin
  Result := Kind = tyString;
end;

function TTypeDesc.IsOrdinal: Boolean;
begin
  Result := Kind in [tyInteger, tyInt64, tyUInt32, tyByte, tyBoolean, tyEnum];
end;

function TTypeDesc.IsRecord: Boolean;
begin
  Result := Kind = tyRecord;
end;

function TTypeDesc.RawSize: Integer;
begin
  case Kind of
    tyByte, tyBoolean: Result := 1;
    tyInteger, tyUInt32, tyEnum: Result := 4;
    tyInt64, tyString, tyClass, tyPointer, tyNil: Result := 8;
    tyRecord: Result := TRecordTypeDesc(Self).TotalSize;
    tySet: if TSetTypeDesc(Self).BitCount <= 32 then Result := 4 else Result := 8;
    tyStaticArray:
      Result := (TStaticArrayTypeDesc(Self).HighBound -
                 TStaticArrayTypeDesc(Self).LowBound + 1) *
                 TStaticArrayTypeDesc(Self).ElementType.RawSize;
  else
    Result := 8;
  end;
end;

function TTypeDesc.ByteSize: Integer;
begin
  case Kind of
    tyInteger, tyUInt32, tyEnum: Result := 4;
    tyInt64:             Result := 8;
    tyByte, tyBoolean:   Result := 4;  { stored as word, same as AllocAlign }
    tyString:            Result := 8;  { pointer size on 64-bit }
    tyRecord:            Result := TRecordTypeDesc(Self).TotalSize;
    tyNil:               Result := 8;
    tySet: if TSetTypeDesc(Self).BitCount <= 32 then Result := 4 else Result := 8;
    tyStaticArray:
      Result := (TStaticArrayTypeDesc(Self).HighBound -
                 TStaticArrayTypeDesc(Self).LowBound + 1) *
                 TStaticArrayTypeDesc(Self).ElementType.RawSize;
  else
    Result := 8;
  end;
end;

function TTypeDesc.AllocAlign: Integer;
begin
  case Kind of
    tyInteger, tyUInt32, tyEnum: Result := 4;
    tyByte, tyBoolean:   Result := 4;  { round up to word boundary }
    tyInt64, tyString:   Result := 8;
    tyRecord:            Result := TRecordTypeDesc(Self).MaxAlign;
    tySet: if TSetTypeDesc(Self).BitCount <= 32 then Result := 4 else Result := 8;
    tyStaticArray: Result := TStaticArrayTypeDesc(Self).ElementType.AllocAlign;
  else
    Result := 8;
  end;
end;

{ ------------------------------------------------------------------ }
{ TRecordTypeDesc                                                     }
{ ------------------------------------------------------------------ }

constructor TRecordTypeDesc.Create(const AName: string; AKind: TTypeKind = tyRecord);
begin
  inherited Create;
  Kind        := AKind;
  Name        := AName;
  FFields     := TObjectList.Create(True);
  FKeys       := TStringList.Create;
  FKeys.Sorted        := True;
  FKeys.CaseSensitive := False;
  FKeys.Duplicates    := dupIgnore;
  FVTable     := nil;  { allocated on first use }
  FImplements := TObjectList.Create(False);  { not owned }
  FProperties := TObjectList.Create(True);   { owned TPropertyInfo }
end;

destructor TRecordTypeDesc.Destroy;
begin
  FProperties.Free;
  FImplements.Free;
  FKeys.Free;
  FFields.Free;
  FVTable.Free;
  inherited Destroy;
end;

procedure TRecordTypeDesc.AddField(const AName: string; AType: TTypeDesc);
var
  Info:   TFieldInfo;
  Offset: Integer;
begin
  Offset := TotalSize;  { next available byte (includes vptr if present) }
  Info          := TFieldInfo.Create;
  Info.Name     := AName;
  Info.TypeDesc := AType;
  Info.Offset   := Offset;
  FFields.Add(Info);
  FKeys.AddObject(AName, Info);
end;

function TRecordTypeDesc.FindField(const AName: string): TFieldInfo;
var
  Idx: Integer;
begin
  if FKeys.Find(AName, Idx) then
    Result := TFieldInfo(FKeys.Objects[Idx])
  else
    Result := nil;
end;

function TRecordTypeDesc.TotalSize: Integer;
var
  I: Integer;
begin
  { vptr (8 bytes) precedes all fields when this class has a vtable }
  if HasVTable then
    Result := 8
  else
    Result := 0;
  for I := 0 to FFields.Count - 1 do
    Inc(Result, TFieldInfo(FFields[I]).TypeDesc.ByteSize);
end;

function TRecordTypeDesc.MaxAlign: Integer;
var
  I, A: Integer;
begin
  Result := 4;
  if HasVTable then
    Result := 8;  { vptr requires 8-byte alignment }
  for I := 0 to FFields.Count - 1 do
  begin
    A := TFieldInfo(FFields[I]).TypeDesc.AllocAlign;
    if A > Result then
      Result := A;
  end;
end;

function TRecordTypeDesc.HasVTable: Boolean;
begin
  Result := (FVTable <> nil) and (FVTable.Count > 0);
end;

function TRecordTypeDesc.VTableCount: Integer;
begin
  if FVTable = nil then
    Result := 0
  else
    Result := FVTable.Count;
end;

function TRecordTypeDesc.VTableEntryAt(ASlot: Integer): TVTableEntry;
begin
  if (FVTable = nil) or (ASlot < 0) or (ASlot >= FVTable.Count) then
    Result := nil
  else
    Result := TVTableEntry(FVTable[ASlot]);
end;

function TRecordTypeDesc.FindVTableSlot(const AMethodName: string): Integer;
var
  I: Integer;
  E: TVTableEntry;
begin
  Result := -1;
  if FVTable = nil then Exit;
  for I := 0 to FVTable.Count - 1 do
  begin
    E := TVTableEntry(FVTable[I]);
    if SameText(E.MethName, AMethodName) then
    begin
      Result := I;
      Exit;
    end;
  end;
end;

function TRecordTypeDesc.AddVTableSlot(const AMethodName, AImplName: string): Integer;
var
  E: TVTableEntry;
begin
  if FVTable = nil then
    FVTable := TObjectList.Create(True);
  E            := TVTableEntry.Create;
  E.Slot       := FVTable.Count;
  E.MethName := AMethodName;
  E.ImplName   := AImplName;
  FVTable.Add(E);
  Result := E.Slot;
end;

procedure TRecordTypeDesc.OverrideVTableSlot(ASlot: Integer; const AImplName: string);
begin
  if (FVTable <> nil) and (ASlot >= 0) and (ASlot < FVTable.Count) then
    TVTableEntry(FVTable[ASlot]).ImplName := AImplName;
end;

procedure TRecordTypeDesc.AddImplements(AIntf: TInterfaceTypeDesc);
begin
  FImplements.Add(AIntf);
end;

function TRecordTypeDesc.ImplementsCount: Integer;
begin
  Result := FImplements.Count;
end;

function TRecordTypeDesc.ImplementsIntfAt(AIndex: Integer): TInterfaceTypeDesc;
begin
  Result := TInterfaceTypeDesc(FImplements[AIndex]);
end;

procedure TRecordTypeDesc.CopyVTableFrom(AParent: TRecordTypeDesc);
var
  I: Integer;
  Src, Dst: TVTableEntry;
begin
  if (AParent = nil) or (AParent.VTableCount = 0) then Exit;
  if FVTable = nil then
    FVTable := TObjectList.Create(True);
  for I := 0 to AParent.VTableCount - 1 do
  begin
    Src      := AParent.VTableEntryAt(I);
    Dst      := TVTableEntry.Create;
    Dst.Slot       := Src.Slot;
    Dst.MethName := Src.MethName;
    Dst.ImplName   := Src.ImplName;
    FVTable.Add(Dst);
  end;
end;

{ ------------------------------------------------------------------ }
{ TInterfaceTypeDesc                                                  }
{ ------------------------------------------------------------------ }

procedure TRecordTypeDesc.AddProperty(AProp: TPropertyInfo);
begin
  FProperties.Add(AProp);
end;

function TRecordTypeDesc.FindProperty(const AName: string): TPropertyInfo;
var
  I: Integer;
begin
  for I := 0 to FProperties.Count - 1 do
    if SameText(TPropertyInfo(FProperties[I]).Name, AName) then
    begin
      Result := TPropertyInfo(FProperties[I]);
      Exit;
    end;
  Result := nil;
end;

constructor TInterfaceTypeDesc.Create(const AName: string);
begin
  inherited Create;
  Kind         := tyInterface;
  Name         := AName;
  FMethods     := TStringList.Create;
  FMethods.CaseSensitive := False;
  FReturnTypes := TStringList.Create;
  FParent      := nil;
end;

destructor TInterfaceTypeDesc.Destroy;
begin
  FReturnTypes.Free;
  FMethods.Free;
  inherited Destroy;
end;

procedure TInterfaceTypeDesc.AddMethod(const AName: string;
  const AReturnTypeName: string);
begin
  FMethods.Add(AName);
  FReturnTypes.Add(AReturnTypeName);
end;

function TInterfaceTypeDesc.HasMethod(const AName: string): Boolean;
begin
  Result := FMethods.IndexOf(AName) >= 0;
end;

function TInterfaceTypeDesc.MethodCount: Integer;
begin
  Result := FMethods.Count;
end;

function TInterfaceTypeDesc.MethodName(AIndex: Integer): string;
begin
  Result := FMethods[AIndex];
end;

function TInterfaceTypeDesc.MethodReturnTypeName(AIndex: Integer): string;
begin
  Result := FReturnTypes[AIndex];
end;

function TInterfaceTypeDesc.MethodIndex(const AName: string): Integer;
begin
  Result := FMethods.IndexOf(AName);
end;

{ ------------------------------------------------------------------ }
{ TSymbol                                                             }
{ ------------------------------------------------------------------ }

constructor TSymbol.Create(const AName: string; AKind: TSymbolKind; AType: TTypeDesc);
begin
  inherited Create;
  Name     := AName;
  Kind     := AKind;
  TypeDesc := AType;
  Params   := TObjectList.Create(True);
  IsWeak   := False;
end;

destructor TSymbol.Destroy;
begin
  Params.Free;
  inherited Destroy;
end;

{ ------------------------------------------------------------------ }
{ TScope                                                              }
{ ------------------------------------------------------------------ }

constructor TScope.Create(AParent: TScope);
begin
  inherited Create;
  FParent  := AParent;
  FSymbols := TObjectList.Create(True);
  FKeys    := TStringList.Create;
  FKeys.Sorted        := True;
  FKeys.CaseSensitive := False;
  FKeys.Duplicates    := dupIgnore;  { we check manually before inserting }
end;

destructor TScope.Destroy;
begin
  FKeys.Free;
  FSymbols.Free;
  inherited Destroy;
end;

function TScope.Define(ASymbol: TSymbol): Boolean;
var
  Idx: Integer;
begin
  if FKeys.Find(ASymbol.Name, Idx) then
  begin
    Result := False;
    Exit;
  end;
  FSymbols.Add(ASymbol);
  { Store the TSymbol pointer directly in the string list's Objects slot. }
  FKeys.AddObject(ASymbol.Name, ASymbol);
  Result := True;
end;

function TScope.LookupLocal(const AName: string): TSymbol;
var
  Idx: Integer;
begin
  if FKeys.Find(AName, Idx) then
    Result := TSymbol(FKeys.Objects[Idx])
  else
    Result := nil;
end;

function TScope.Lookup(const AName: string): TSymbol;
var
  S: TScope;
begin
  S := Self;
  while S <> nil do
  begin
    Result := S.LookupLocal(AName);
    if Result <> nil then
      Exit;
    S := S.FParent;
  end;
  Result := nil;
end;

{ ------------------------------------------------------------------ }
{ TEnumTypeDesc                                                       }
{ ------------------------------------------------------------------ }

constructor TEnumTypeDesc.Create(const AName: string);
begin
  inherited Create;
  Kind    := tyEnum;
  Name    := AName;
  Members := TStringList.Create;
end;

destructor TEnumTypeDesc.Destroy;
begin
  Members.Free;
  inherited Destroy;
end;

function TEnumTypeDesc.OrdinalOf(const AMember: string): Integer;
var
  I: Integer;
begin
  for I := 0 to Members.Count - 1 do
    if SameText(Members[I], AMember) then
    begin
      Result := I;
      Exit;
    end;
  Result := -1;
end;

{ ------------------------------------------------------------------ }
{ TSymbolTable                                                        }
{ ------------------------------------------------------------------ }

constructor TSymbolTable.Create;
begin
  inherited Create;
  FScopeStack := TObjectList.Create(True);
  FAllTypes   := TObjectList.Create(True);
  FGenerics   := TStringList.Create;
  FGenerics.CaseSensitive := True;
  { Global scope — parent = nil }
  FScopeStack.Add(TScope.Create(nil));
  RegisterBuiltins;
end;

destructor TSymbolTable.Destroy;
begin
  FGenerics.Free;
  FScopeStack.Free;
  FAllTypes.Free;
  inherited Destroy;
end;

function TSymbolTable.NewType(AKind: TTypeKind; const AName: string): TTypeDesc;
begin
  Result      := TTypeDesc.Create;
  Result.Kind := AKind;
  Result.Name := AName;
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewRecordType(const AName: string): TRecordTypeDesc;
begin
  Result := TRecordTypeDesc.Create(AName, tyRecord);
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewClassType(const AName: string): TRecordTypeDesc;
begin
  Result := TRecordTypeDesc.Create(AName, tyClass);
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewInterfaceType(const AName: string): TInterfaceTypeDesc;
begin
  Result := TInterfaceTypeDesc.Create(AName);
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewPointerType(const AName: string; ABase: TTypeDesc): TPointerTypeDesc;
begin
  Result          := TPointerTypeDesc.Create;
  Result.Kind     := tyPointer;
  Result.Name     := AName;
  Result.BaseType := ABase;
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewEnumType(const AName: string): TEnumTypeDesc;
begin
  Result := TEnumTypeDesc.Create(AName);
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewSetType(const AName: string; ABase: TEnumTypeDesc): TSetTypeDesc;
begin
  Result          := TSetTypeDesc.Create;
  Result.Kind     := tySet;
  Result.Name     := AName;
  Result.BaseType := ABase;
  Result.BitCount := ABase.Members.Count;
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewOpenArrayType(AElementType: TTypeDesc): TOpenArrayTypeDesc;
begin
  Result             := TOpenArrayTypeDesc.Create;
  Result.Kind        := tyOpenArray;
  Result.Name        := 'array of ' + AElementType.Name;
  Result.ElementType := AElementType;
  FAllTypes.Add(Result);
end;

function TSymbolTable.NewStaticArrayType(AElementType: TTypeDesc;
  ALow, AHigh: Integer): TStaticArrayTypeDesc;
begin
  Result             := TStaticArrayTypeDesc.Create;
  Result.Kind        := tyStaticArray;
  Result.Name        := Format('array[%d..%d] of %s', [ALow, AHigh, AElementType.Name]);
  Result.ElementType := AElementType;
  Result.LowBound    := ALow;
  Result.HighBound   := AHigh;
  FAllTypes.Add(Result);
end;

procedure TSymbolTable.RegisterGeneric(const AName: string; ATempl: TObject);
begin
  FGenerics.AddObject(AName, ATempl);
end;

function TSymbolTable.FindGeneric(const AName: string): TObject;
var
  Idx: Integer;
begin
  Idx := FGenerics.IndexOf(AName);
  if Idx >= 0 then
    Result := FGenerics.Objects[Idx]
  else
    Result := nil;
end;

procedure TSymbolTable.RegisterBuiltins;
var
  Sym: TSymbol;
begin
  { Primitive types }
  FTypeInteger := NewType(tyInteger, 'Integer');
  FTypeInt64   := NewType(tyInt64,   'Int64');
  FTypeUInt32  := NewType(tyUInt32,  'UInt32');
  FTypeByte    := NewType(tyByte,    'Byte');
  FTypeBoolean := NewType(tyBoolean, 'Boolean');
  FTypeString  := NewType(tyString,  'string');
  FTypeVoid    := NewType(tyVoid,    'void');
  FTypeNil     := NewType(tyNil,     'nil');
  FTypePointer := NewPointerType('Pointer', nil);  { untyped pointer }
  FTypePChar   := NewType(tyPChar, 'PChar');

  { Register type names as skType symbols in global scope }
  Define(TSymbol.Create('Integer', skType, FTypeInteger));
  Define(TSymbol.Create('Int64',   skType, FTypeInt64));
  Define(TSymbol.Create('UInt32',  skType, FTypeUInt32));
  Define(TSymbol.Create('Byte',    skType, FTypeByte));
  Define(TSymbol.Create('Boolean', skType, FTypeBoolean));
  Define(TSymbol.Create('string',  skType, FTypeString));
  Define(TSymbol.Create('Pointer', skType, FTypePointer));
  Define(TSymbol.Create('PChar',   skType, FTypePChar));

  { TObject — root of the class hierarchy; no fields, no parent }
  Define(TSymbol.Create('TObject', skType, NewClassType('TObject')));

  { IInterface — root of the interface hierarchy; no methods }
  Define(TSymbol.Create('IInterface', skType, NewInterfaceType('IInterface')));

  { Boolean constants }
  Sym := TSymbol.Create('True',  skConstant, FTypeBoolean);
  Sym.ConstValue := 1;
  Define(Sym);
  Sym := TSymbol.Create('False', skConstant, FTypeBoolean);
  Sym.ConstValue := 0;
  Define(Sym);

  { Built-in I/O procedures }
  Sym := TSymbol.Create('Write',   skProcedure, nil);
  Define(Sym);
  Sym := TSymbol.Create('WriteLn', skProcedure, nil);
  Define(Sym);

  { Built-in set procedures }
  Sym := TSymbol.Create('Include', skProcedure, nil);
  Define(Sym);
  Sym := TSymbol.Create('Exclude', skProcedure, nil);
  Define(Sym);

  { Built-in memory management }
  Sym := TSymbol.Create('GetMem',     skFunction,  FTypePointer);
  Define(Sym);
  Sym := TSymbol.Create('ReallocMem', skFunction,  FTypePointer);
  Define(Sym);
  Sym := TSymbol.Create('FreeMem',    skProcedure, nil);
  Define(Sym);

  { Built-in string operations }
  Sym := TSymbol.Create('Format',    skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('Length',    skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('Pos',       skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('Copy',      skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('UpperCase', skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('LowerCase', skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('Trim',      skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('SameText',  skFunction, FTypeBoolean);
  Define(Sym);
  Sym := TSymbol.Create('IntToStr',  skFunction, FTypeString);
  Define(Sym);
  Sym := TSymbol.Create('StrToInt',  skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('CompareStr',  skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('CompareText', skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('OrdAt',       skFunction, FTypeInteger);
  Define(Sym);
  Sym := TSymbol.Create('Chr',         skFunction, FTypeString);
  Define(Sym);
  { Memory utilities }
  Sym := TSymbol.Create('ZeroMem',      skProcedure, nil); Define(Sym);
  Sym := TSymbol.Create('_ClassAddRef', skProcedure, nil); Define(Sym);
  Sym := TSymbol.Create('_ClassRelease',skProcedure, nil); Define(Sym);
  { CLI arguments }
  Sym := TSymbol.Create('ParamCount', skFunction,  FTypeInteger); Define(Sym);
  Sym := TSymbol.Create('ParamStr',   skFunction,  FTypeString);  Define(Sym);
  { File I/O }
  Sym := TSymbol.Create('ReadFile',   skFunction,  FTypeString);  Define(Sym);
  Sym := TSymbol.Create('WriteFile',  skProcedure, nil);          Define(Sym);
  Sym := TSymbol.Create('AppendFile', skProcedure, nil);          Define(Sym);
  Sym := TSymbol.Create('FileExists',             skFunction,  FTypeBoolean); Define(Sym);
  Sym := TSymbol.Create('DeleteFile',             skProcedure, nil);          Define(Sym);
  Sym := TSymbol.Create('CurrentExceptionMessage', skFunction,  FTypeString);  Define(Sym);
  { Environment and process }
  Sym := TSymbol.Create('GetEnvVar',  skFunction,  FTypeString);  Define(Sym);
  Sym := TSymbol.Create('GetEnvironmentVariable', skFunction, FTypeString); Define(Sym);
  Sym := TSymbol.Create('Exec',       skFunction,  FTypeInteger); Define(Sym);
  Sym := TSymbol.Create('Halt',       skProcedure, nil);          Define(Sym);
  { File path manipulation }
  Sym := TSymbol.Create('ChangeFileExt',                skFunction, FTypeString); Define(Sym);
  Sym := TSymbol.Create('ExtractFileName',              skFunction, FTypeString); Define(Sym);
  Sym := TSymbol.Create('ExtractFilePath',              skFunction, FTypeString); Define(Sym);
  Sym := TSymbol.Create('IncludeTrailingPathDelimiter', skFunction, FTypeString); Define(Sym);
end;

function TSymbolTable.DefineGlobal(ASymbol: TSymbol): Boolean;
begin
  Result := TScope(FScopeStack[0]).Define(ASymbol);
end;

function TSymbolTable.GetCurrentScope: TScope;
begin
  Result := TScope(FScopeStack[FScopeStack.Count - 1]);
end;

function TSymbolTable.GetScopeDepth: Integer;
begin
  Result := FScopeStack.Count;
end;

function TSymbolTable.PushScope: TScope;
begin
  Result := TScope.Create(CurrentScope);
  FScopeStack.Add(Result);
end;

procedure TSymbolTable.PopScope;
begin
  if FScopeStack.Count > 1 then
    FScopeStack.Delete(FScopeStack.Count - 1);
end;

function TSymbolTable.Define(ASymbol: TSymbol): Boolean;
begin
  Result := CurrentScope.Define(ASymbol);
end;

function TSymbolTable.Lookup(const AName: string): TSymbol;
begin
  Result := CurrentScope.Lookup(AName);
end;

function TSymbolTable.FindType(const AName: string): TTypeDesc;
var
  Sym: TSymbol;
begin
  Sym := CurrentScope.Lookup(AName);
  if (Sym <> nil) and (Sym.Kind = skType) then
    Result := Sym.TypeDesc
  else
    Result := nil;
end;

end.
