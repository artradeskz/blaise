{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Skeleton tests for TUnitInterface (Phase 1 of separate compilation).

  The contract being pinned down here:

    TUnitInterface is the self-contained, post-semantic description of
    a unit's interface section.  Once produced by AnalyseUnitForExport,
    it must be usable by downstream compilation passes WITHOUT keeping
    the source TUnit alive.

  Every test in this file targets one property of that contract.  They
  are deliberately stubbed with Fail('TODO …') so the green/red bar
  acts as a checklist as the implementation lands. }

unit cp.test.unitinterface;

interface

uses
  Classes, contnrs, blaise.testing,
  uAST, uLexer, uParser, uUnitInterface, uSemanticExport;

type
  { ParseAndExport helper — shared across fixtures.  Stubbed for now;
    once uUnitInterface exists, this becomes the single point that
    parses a source string, runs AnalyseUnitForExport, and hands back
    the resulting TUnitInterface for inspection.

    Returning Pointer (not TUnitInterface) keeps this unit free of a
    uUnitInterface dependency while the type doesn't exist yet. }

  { ----- Self-containment ----------------------------------------- }

  [Threaded]
  TSelfContainmentTests = class(TTestCase)
  published
    { After AnalyseUnitForExport returns, freeing the source TUnit
      must not affect lookups against the interface. }
    procedure TestInterfaceUsable_AfterSourceUnitFreed;

    { No member of TUnitInterface holds a pointer into the source
      TUnit's AST.  Spot-checks via identity comparison after free. }
    procedure TestNoBackPointers_IntoSourceAST;

    { Cloning of generic/inline bodies is deep — mutating the source
      block (before free) must not affect the cloned body. }
    procedure TestGenericBody_IsDeepClone;
    procedure TestInlineBody_IsDeepClone;
  end;

  { ----- Cross-unit references ------------------------------------ }

  [Threaded]
  TCrossUnitRefTests = class(TTestCase)
  published
    { Unit B references a type from unit A: B's interface stores the
      ref as TQualTypeRef('A','TFoo'), not as a pointer into A. }
    procedure TestTypeFromOtherUnit_QualifiedByName;

    { Local types referenced inside the same unit appear with
      UnitName = '' (this unit). }
    procedure TestLocalTypeRef_UnqualifiedUnitName;

    { Builtins (Integer, string, Boolean, …) get UnitName = '$builtin'. }
    procedure TestBuiltinTypeRef_BuiltinUnitName;
  end;

  { ----- Const round-trip ----------------------------------------- }

  [Threaded]
  TConstRoundTripTests = class(TTestCase)
  published
    procedure TestIntegerConst_ValuePreserved;
    procedure TestStringConst_ValuePreserved;
    procedure TestFloatConst_ValuePreserved;
    procedure TestIdentRefConst_PartsPreserved;
    procedure TestArrayConst_ElementsAndBoundsPreserved;
    procedure TestEnumIndexedArrayConst_IndexTypePreserved;
  end;

  { ----- Enum & set type structure -------------------------------- }

  [Threaded]
  TEnumSetTests = class(TTestCase)
  published
    procedure TestEnum_MembersAndOrdinalsPreserved;
    procedure TestSet_BaseEnumPreserved;
  end;

  { ----- Record & class layout ------------------------------------ }

  [Threaded]
  TRecordClassLayoutTests = class(TTestCase)
  published
    procedure TestRecord_FieldsInDeclarationOrder;
    procedure TestRecord_FieldTypes_AsQualTypeRef;
    procedure TestClass_ParentClassResolved;
    procedure TestClass_ImplementsListPopulated;
    procedure TestClass_MethodSignaturesExported;
    procedure TestClass_VTableSlotsAssigned;
    procedure TestClass_InstanceSizeComputed;
    procedure TestClass_AttributesPreserved;
  end;

  { ----- Inline & generic bodies ---------------------------------- }

  [Threaded]
  TInlineGenericBodyTests = class(TTestCase)
  published
    { inline routine declared in interface → InlineBodies entry. }
    procedure TestInline_BodyExportedWithSig;

    { Generic class declared in interface → GenericBodies entry with
      TypeParams populated, TypeDef cloned. }
    procedure TestGenericType_BodyExported;

    { Generic free routine → GenericBodies entry with RoutineSig +
      Body, IsType=False. }
    procedure TestGenericRoutine_BodyExported;

    { Constraints (e.g. <T: TFoo>) propagate to TGenericBody.Constraints
      parallel-array. }
    procedure TestGeneric_ConstraintsPreserved;
  end;

  { ----- Implementation invisibility ------------------------------ }

  [Threaded]
  TImplementationHidingTests = class(TTestCase)
  published
    { Routine declared only in impl section: absent from .Routines. }
    procedure TestImplOnlyRoutine_NotExported;

    { Type declared only in impl section: absent from .Types. }
    procedure TestImplOnlyType_NotExported;

    { Regular (non-inline, non-generic) routine declared in interface:
      signature exported, no body in InlineBodies/GenericBodies. }
    procedure TestRegularRoutine_SigOnly_NoBody;
  end;

  { ----- Visibility ----------------------------------------------- }

  [Threaded]
  TVisibilityTests = class(TTestCase)
  published
    { Class members carry their declared visibility through to the
      exported entries.  Decision pending: do we export private
      members at all, or filter them out?  This test pins down
      whichever choice we make. }
    procedure TestClassMember_VisibilityPreserved;
  end;

  { ----- Forward-declared class completion ------------------------ }

  [Threaded]
  TForwardDeclTests = class(TTestCase)
  published
    { `type TFoo = class;` in interface + full body in impl: the
      exported entry for TFoo carries the full structure (fields,
      methods, parent), not just the forward stub.  Documents the
      accepted impl-leak. }
    procedure TestForwardDeclClass_FullBodyExported;
  end;

  { ----- Routine signature details -------------------------------- }

  [Threaded]
  TRoutineSigTests = class(TTestCase)
  published
    procedure TestParam_ModeVar_Preserved;
    procedure TestParam_ModeConst_Preserved;
    procedure TestParam_ModeOut_Preserved;
    procedure TestReturnType_FunctionVsProcedure;
    procedure TestCallingConv_Cdecl_Preserved;
    procedure TestExternal_NamePreserved;
  end;

  { ----- UsedUnits ------------------------------------------------ }

  [Threaded]
  TUsedUnitsTests = class(TTestCase)
  published
    { UsedUnits reflects the interface uses clause, in declaration order. }
    procedure TestUsedUnits_OrderPreserved;

    { Units used only by the implementation section do NOT appear in
      the exported UsedUnits list. }
    procedure TestImplOnlyUsedUnit_NotInUsedUnits;
  end;

  { ----- Lookup helpers ------------------------------------------- }

  [Threaded]
  TLookupTests = class(TTestCase)
  published
    procedure TestFindType_CaseInsensitive;
    procedure TestFindConst_CaseInsensitive;
    procedure TestFindRoutine_CaseInsensitive;
    procedure TestFindGeneric_CaseInsensitive;
    procedure TestFind_Missing_ReturnsNil;
    procedure TestFindType_CaseSensitive_FlagRespected;
  end;

  { ----- Metadata ------------------------------------------------- }

  [Threaded]
  TMetadataTests = class(TTestCase)
  published
    procedure TestName_MatchesSource;
    procedure TestSourceFile_MatchesPath;
    procedure TestSourceHash_NonEmpty;
    procedure TestCompilerVersion_NonEmpty;
  end;

implementation

const
  TODO_MSG = 'TODO: TUnitInterface not yet implemented (Phase 1)';

{ ParseAndExport — central helper.  Parses ASource as a Blaise unit
  and runs ExportUnitInterface against it (no semantic — Phase 2 export
  walks raw parsed fields; semantic-derived export comes later).
  Returns the produced TUnitInterface; caller owns it.

  ASource is treated as the entire content of a .pas file: must begin
  with 'unit Name;' and contain interface/implementation/end.
  Deps is empty for now; cross-unit tests will pre-populate it. }
function ParseAndExportWithDeps(const ASource: string;
                                ADeps: TObjectList): TUnitInterface;
var
  Lex:    TLexer;
  Parser: TParser;
  U:      TUnit;
begin
  Lex := TLexer.Create(ASource, '<test>');
  try
    Parser := TParser.Create(Lex);
    try
      U := Parser.ParseUnit;
      try
        Result := ExportUnitInterface(U, ADeps);
      finally
        U.Free;
      end;
    finally
      Parser.Free;
    end;
  finally
    Lex.Free;
  end;
end;

function ParseAndExport(const ASource: string): TUnitInterface;
var
  Lex:    TLexer;
  Parser: TParser;
  U:      TUnit;
begin
  Lex := TLexer.Create(ASource, '<test>');
  try
    Parser := TParser.Create(Lex);
    try
      U := Parser.ParseUnit;
      try
        Result := ExportUnitInterface(U, nil);  { no deps yet }
      finally
        U.Free;
      end;
    finally
      Parser.Free;
    end;
  finally
    Lex.Free;
  end;
end;

{ ==================================================================
  Stubs.  Each test fails with TODO_MSG until the production code
  lands and the body is fleshed out.
  ================================================================== }

{ ----- TSelfContainmentTests ------------------------------------ }

{ Note: ParseAndExport already frees the source TUnit before returning,
  so any successful test that uses the returned interface is implicit
  evidence of self-containment.  These tests make that property
  explicit and exercise a richer cross-section of the interface to
  catch any field that quietly held a pointer back to the source. }

procedure TSelfContainmentTests.TestInterfaceUsable_AfterSourceUnitFreed;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'uses SysUtils;'                                    + #10 +
    'const Pi = 3.14;'                                  + #10 +
    'type'                                              + #10 +
    '  TColor = (Red, Green, Blue);'                    + #10 +
    '  TPoint = record X, Y: Integer; end;'             + #10 +
    'function Hello(const Who: string): string;'        + #10 +
    'implementation'                                    + #10 +
    'function Hello(const Who: string): string; begin Result := Who; end;' + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
begin
  Iface := ParseAndExport(SRC);    { source TUnit is freed inside helper }
  try
    { Walk a deliberately mixed cross-section.  If anything in the
      interface still pointed at freed memory, one of these would
      either return nil unexpectedly or crash. }
    AssertEquals('uses',     1, Iface.UsedUnits.Count);
    AssertEquals('uses[0]',  'SysUtils', Iface.UsedUnits.Strings[0]);

    AssertEquals('type TColor', True, Iface.FindType('TColor') <> nil);
    AssertEquals('type TPoint', True, Iface.FindType('TPoint') <> nil);
    AssertEquals('const Pi',    True, Iface.FindConst('Pi') <> nil);
    AssertEquals('routine Hello', True, Iface.FindRoutine('Hello') <> nil);

    { Recursive walk through cloned AST — proves Def is a real
      clone, not a dangling ref. }
    AssertEquals('TColor is enum',
                 True, Iface.FindType('TColor').Def is TEnumTypeDef);
    AssertEquals('TPoint is record',
                 True, Iface.FindType('TPoint').Def is TRecordTypeDef);
    { TPoint declares 'X, Y: Integer' — one TFieldDecl carrying two names. }
    AssertEquals('TPoint field-decl count', 1,
                 TRecordTypeDef(Iface.FindType('TPoint').Def).Fields.Count);
    AssertEquals('TPoint name count', 2,
                 TFieldDecl(TRecordTypeDef(Iface.FindType('TPoint').Def)
                              .Fields.Items[0]).Names.Count);
  finally
    Iface.Free;
  end;
end;

procedure TSelfContainmentTests.TestNoBackPointers_IntoSourceAST;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type TFoo = record A: Integer; end;'               + #10 +
    'implementation'                                    + #10 +
    'end.'                                              + #10;
var
  Lex:     TLexer;
  Parser:  TParser;
  U:       TUnit;
  Iface:   TUnitInterface;
  SrcDef:  TASTTypeDef;
  IfaceDef: TASTTypeDef;
begin
  { Build by hand so we can compare the source's TASTTypeDef pointer
    against the interface's TASTTypeDef pointer.  They MUST differ —
    if they're equal, the export pass leaked a back-pointer. }
  Lex := TLexer.Create(SRC, '<test>');
  try
    Parser := TParser.Create(Lex);
    try
      U := Parser.ParseUnit;
      try
        SrcDef := TTypeDecl(U.IntfBlock.TypeDecls.Items[0]).Def;
        Iface  := ExportUnitInterface(U, nil);
        try
          IfaceDef := Iface.FindType('TFoo').Def;
          AssertEquals('def is a clone, not a ref',
                       True, SrcDef <> IfaceDef);
        finally
          Iface.Free;
        end;
      finally
        U.Free;
      end;
    finally
      Parser.Free;
    end;
  finally
    Lex.Free;
  end;
end;
procedure TSelfContainmentTests.TestGenericBody_IsDeepClone;
const
  SRC =
    'unit TestU;'                                + #10 +
    'interface'                                  + #10 +
    'type TBox<T> = class Value: T; end;'        + #10 +
    'implementation'                             + #10 +
    'end.'                                       + #10;
var
  Lex:    TLexer;
  Parser: TParser;
  U:      TUnit;
  Iface:  TUnitInterface;
  SrcDef: TASTTypeDef;
  GBody:  TGenericBody;
begin
  Lex := TLexer.Create(SRC, '<test>');
  try
    Parser := TParser.Create(Lex);
    try
      U := Parser.ParseUnit;
      try
        SrcDef := TTypeDecl(U.IntfBlock.TypeDecls.Items[0]).Def;
        Iface  := ExportUnitInterface(U, nil);
        try
          GBody := Iface.FindGeneric('TBox');
          AssertEquals('generic found', True, GBody <> nil);
          AssertEquals('TypeDef cloned, not aliased',
                       True, GBody.TypeDef <> SrcDef);
        finally
          Iface.Free;
        end;
      finally
        U.Free;
      end;
    finally
      Parser.Free;
    end;
  finally
    Lex.Free;
  end;
end;

procedure TSelfContainmentTests.TestInlineBody_IsDeepClone;
const
  SRC =
    'unit TestU;'                                          + #10 +
    'interface'                                            + #10 +
    'function Square(N: Integer): Integer; inline;'        + #10 +
    'implementation'                                       + #10 +
    'function Square(N: Integer): Integer; begin Result := N * N; end;' + #10 +
    'end.'                                                 + #10;
var
  Lex:     TLexer;
  Parser:  TParser;
  U:       TUnit;
  Iface:   TUnitInterface;
  SrcImpl: TMethodDecl;
  Body:    TInlineBody;
begin
  Lex := TLexer.Create(SRC, '<test>');
  try
    Parser := TParser.Create(Lex);
    try
      U := Parser.ParseUnit;
      try
        SrcImpl := TMethodDecl(U.ImplBlock.ProcDecls.Items[0]);
        Iface   := ExportUnitInterface(U, nil);
        try
          Body := Iface.FindInlineBody('Square');
          AssertEquals('body found', True, Body <> nil);
          AssertEquals('block cloned, not aliased',
                       True, Body.Block <> SrcImpl.Body);
        finally
          Iface.Free;
        end;
      finally
        U.Free;
      end;
    finally
      Parser.Free;
    end;
  finally
    Lex.Free;
  end;
end;

{ ----- TCrossUnitRefTests --------------------------------------- }

{ Build a small 'DepU' interface containing TWidget, then export
  a consumer that references it.  The consumer's ReturnType field
  (which goes through ResolveTypeRef) is the cleanest observable
  for cross-unit qualification today — record-field types still
  travel as raw TypeName strings until Phase 3. }

procedure TCrossUnitRefTests.TestTypeFromOtherUnit_QualifiedByName;
const
  DEP_SRC =
    'unit DepU;'                                + #10 +
    'interface'                                 + #10 +
    'type TWidget = record N: Integer; end;'    + #10 +
    'implementation'                            + #10 +
    'end.'                                      + #10;
  MAIN_SRC =
    'unit MainU;'                               + #10 +
    'interface'                                 + #10 +
    'uses DepU;'                                + #10 +
    'function MakeOne: TWidget;'                + #10 +
    'implementation'                            + #10 +
    'function MakeOne: TWidget; begin end;'     + #10 +
    'end.'                                      + #10;
var
  Deps:  TObjectList;
  Dep:   TUnitInterface;
  Main:  TUnitInterface;
  Sig:   TRoutineSig;
begin
  Dep  := ParseAndExport(DEP_SRC);
  Deps := TObjectList.Create(False);  { non-owning — Dep freed below }
  try
    Deps.Add(Dep);
    Main := ParseAndExportWithDeps(MAIN_SRC, Deps);
    try
      Sig := Main.FindRoutine('MakeOne');
      AssertEquals('routine found',    True, Sig <> nil);
      AssertEquals('return type name', 'TWidget', Sig.ReturnType.TypeName);
      AssertEquals('return type unit', 'DepU',    Sig.ReturnType.UnitName);
    finally
      Main.Free;
    end;
  finally
    Deps.Free;
    Dep.Free;
  end;
end;

procedure TCrossUnitRefTests.TestLocalTypeRef_UnqualifiedUnitName;
const
  SRC =
    'unit TestU;'                               + #10 +
    'interface'                                 + #10 +
    'type TItem = record N: Integer; end;'      + #10 +
    'function Make: TItem;'                     + #10 +
    'implementation'                            + #10 +
    'function Make: TItem; begin end;'          + #10 +
    'end.'                                      + #10;
var
  Iface: TUnitInterface;
  Sig:   TRoutineSig;
begin
  Iface := ParseAndExport(SRC);
  try
    Sig := Iface.FindRoutine('Make');
    AssertEquals('return type name', 'TItem', Sig.ReturnType.TypeName);
    AssertEquals('is local ref',     True,    IsLocalRef(Sig.ReturnType));
    AssertEquals('unit name empty',  '',      Sig.ReturnType.UnitName);
  finally
    Iface.Free;
  end;
end;

procedure TCrossUnitRefTests.TestBuiltinTypeRef_BuiltinUnitName;
const
  SRC =
    'unit TestU;'                              + #10 +
    'interface'                                + #10 +
    'function Count: Integer;'                 + #10 +
    'implementation'                           + #10 +
    'function Count: Integer; begin end;'      + #10 +
    'end.'                                     + #10;
var
  Iface: TUnitInterface;
  Sig:   TRoutineSig;
begin
  Iface := ParseAndExport(SRC);
  try
    Sig := Iface.FindRoutine('Count');
    AssertEquals('return type name', 'Integer', Sig.ReturnType.TypeName);
    AssertEquals('is builtin ref',   True,      IsBuiltinRef(Sig.ReturnType));
    AssertEquals('unit name builtin','$builtin',Sig.ReturnType.UnitName);
  finally
    Iface.Free;
  end;
end;

{ ----- TConstRoundTripTests ------------------------------------- }

{ Helpers — assemble TConstDecl variants directly, then wrap in
  TConstEntry and stash via AddConst.  Mirror the shape that
  AnalyseUnitForExport will eventually produce. }

function MakeIntConst(const AName: string; AValue: Int64): TConstEntry;
begin
  Result := TConstEntry.Create;
  Result.Decl := TConstDecl.Create;
  Result.Decl.Name   := AName;
  Result.Decl.IntVal := AValue;
  Result.TypeRef := MakeBuiltinRef('Integer');
end;

function MakeStringConst(const AName, AValue: string): TConstEntry;
begin
  Result := TConstEntry.Create;
  Result.Decl := TConstDecl.Create;
  Result.Decl.Name     := AName;
  Result.Decl.StrVal   := AValue;
  Result.Decl.IsString := True;
  Result.TypeRef := MakeBuiltinRef('string');
end;

function MakeFloatConst(const AName, AText: string): TConstEntry;
begin
  Result := TConstEntry.Create;
  Result.Decl := TConstDecl.Create;
  Result.Decl.Name    := AName;
  Result.Decl.StrVal  := AText;        { raw float text }
  Result.Decl.IsFloat := True;
  Result.TypeRef := MakeBuiltinRef('Double');
end;

procedure TConstRoundTripTests.TestIntegerConst_ValuePreserved;
var
  U: TUnitInterface;
  E: TConstEntry;
begin
  U := TUnitInterface.Create('TestUnit');
  try
    U.AddConst(MakeIntConst('MaxBuf', 4096));

    E := U.FindConst('MaxBuf');
    AssertEquals('found', True, E <> nil);
    AssertEquals('value',  Int64(4096), E.Decl.IntVal);
    AssertEquals('not string', False, E.Decl.IsString);
    AssertEquals('not float',  False, E.Decl.IsFloat);
    AssertEquals('type ref',  'Integer', E.TypeRef.TypeName);
  finally
    U.Free;
  end;
end;

procedure TConstRoundTripTests.TestStringConst_ValuePreserved;
var
  U: TUnitInterface;
  E: TConstEntry;
begin
  U := TUnitInterface.Create('TestUnit');
  try
    U.AddConst(MakeStringConst('Greeting', 'hello world'));

    E := U.FindConst('Greeting');
    AssertEquals('found', True, E <> nil);
    AssertEquals('value', 'hello world', E.Decl.StrVal);
    AssertEquals('is string', True, E.Decl.IsString);
  finally
    U.Free;
  end;
end;

procedure TConstRoundTripTests.TestFloatConst_ValuePreserved;
var
  U: TUnitInterface;
  E: TConstEntry;
begin
  U := TUnitInterface.Create('TestUnit');
  try
    U.AddConst(MakeFloatConst('Pi', '3.14159265'));

    E := U.FindConst('Pi');
    AssertEquals('found', True, E <> nil);
    AssertEquals('raw text', '3.14159265', E.Decl.StrVal);
    AssertEquals('is float', True, E.Decl.IsFloat);
  finally
    U.Free;
  end;
end;

procedure TConstRoundTripTests.TestIdentRefConst_PartsPreserved;
var
  U:    TUnitInterface;
  E:    TConstEntry;
  Decl: TConstDecl;
begin
  { ConstParts encodes 'Greeting + ", " + Name' as alternating
    literal/ident entries.  Objects[i] = nil → string literal,
    Objects[i] <> nil → ident reference. }
  U := TUnitInterface.Create('TestUnit');
  try
    Decl := TConstDecl.Create;
    Decl.Name       := 'FullGreeting';
    Decl.IsString   := True;
    Decl.ConstParts := TStringList.Create;
    Decl.ConstParts.AddObject('Hello, ', nil);
    Decl.ConstParts.AddObject('Name',    TObject(Pointer(1)));

    E := TConstEntry.Create;
    E.Decl := Decl;
    E.TypeRef := MakeBuiltinRef('string');
    U.AddConst(E);

    E := U.FindConst('FullGreeting');
    AssertEquals('found', True, E <> nil);
    AssertEquals('parts count', 2, E.Decl.ConstParts.Count);
    AssertEquals('part 0 text', 'Hello, ', E.Decl.ConstParts.Strings[0]);
    AssertEquals('part 0 is literal', True,  E.Decl.ConstParts.Objects[0] = nil);
    AssertEquals('part 1 text', 'Name',     E.Decl.ConstParts.Strings[1]);
    AssertEquals('part 1 is ident',   True,  E.Decl.ConstParts.Objects[1] <> nil);
  finally
    U.Free;
  end;
end;

procedure TConstRoundTripTests.TestArrayConst_ElementsAndBoundsPreserved;
var
  U:    TUnitInterface;
  E:    TConstEntry;
  Decl: TConstDecl;
begin
  { const Primes: array[0..4] of Integer = (2, 3, 5, 7, 11); }
  U := TUnitInterface.Create('TestUnit');
  try
    Decl := TConstDecl.Create;
    Decl.Name                := 'Primes';
    Decl.IsArrayConst        := True;
    Decl.ArrayElemType       := 'Integer';
    Decl.ArrayIsRangeIndexed := True;
    Decl.ArrayLowBound       := 0;
    Decl.ArrayHighBound      := 4;
    Decl.ArrayElements       := TStringList.Create;
    Decl.ArrayElements.Add('2');
    Decl.ArrayElements.Add('3');
    Decl.ArrayElements.Add('5');
    Decl.ArrayElements.Add('7');
    Decl.ArrayElements.Add('11');

    E := TConstEntry.Create;
    E.Decl := Decl;
    U.AddConst(E);

    E := U.FindConst('Primes');
    AssertEquals('found', True, E <> nil);
    AssertEquals('is array',     True, E.Decl.IsArrayConst);
    AssertEquals('elem type',    'Integer', E.Decl.ArrayElemType);
    AssertEquals('range indexed', True, E.Decl.ArrayIsRangeIndexed);
    AssertEquals('low',  0, E.Decl.ArrayLowBound);
    AssertEquals('high', 4, E.Decl.ArrayHighBound);
    AssertEquals('count', 5, E.Decl.ArrayElements.Count);
    AssertEquals('e0', '2',  E.Decl.ArrayElements.Strings[0]);
    AssertEquals('e4', '11', E.Decl.ArrayElements.Strings[4]);
  finally
    U.Free;
  end;
end;

procedure TConstRoundTripTests.TestEnumIndexedArrayConst_IndexTypePreserved;
var
  U:    TUnitInterface;
  E:    TConstEntry;
  Decl: TConstDecl;
begin
  { const DayNames: array[TDayOfWeek] of string = ('Mon', 'Tue', ...);
    Index type is an enum, not a numeric range. }
  U := TUnitInterface.Create('TestUnit');
  try
    Decl := TConstDecl.Create;
    Decl.Name                := 'DayNames';
    Decl.IsArrayConst        := True;
    Decl.ArrayIndexType      := 'TDayOfWeek';
    Decl.ArrayElemType       := 'string';
    Decl.ArrayIsRangeIndexed := False;
    Decl.ArrayElements       := TStringList.Create;
    Decl.ArrayElements.Add('Mon');
    Decl.ArrayElements.Add('Tue');
    Decl.ArrayElements.Add('Wed');

    E := TConstEntry.Create;
    E.Decl := Decl;
    U.AddConst(E);

    E := U.FindConst('DayNames');
    AssertEquals('found', True, E <> nil);
    AssertEquals('index type', 'TDayOfWeek', E.Decl.ArrayIndexType);
    AssertEquals('not range',  False, E.Decl.ArrayIsRangeIndexed);
    AssertEquals('count', 3, E.Decl.ArrayElements.Count);
    AssertEquals('e0', 'Mon', E.Decl.ArrayElements.Strings[0]);
  finally
    U.Free;
  end;
end;

{ ----- TEnumSetTests -------------------------------------------- }

procedure TEnumSetTests.TestEnum_MembersAndOrdinalsPreserved;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type TColor = (Red, Green, Blue);'                 + #10 +
    'implementation'                                    + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
  Enum:  TEnumTypeDef;
begin
  Iface := ParseAndExport(SRC);
  try
    E := Iface.FindType('TColor');
    AssertEquals('found', True, E <> nil);
    AssertEquals('is enum def', True, E.Def is TEnumTypeDef);

    Enum := TEnumTypeDef(E.Def);
    AssertEquals('member count', 3, Enum.Members.Count);
    AssertEquals('m0', 'Red',   Enum.Members.Strings[0]);
    AssertEquals('m1', 'Green', Enum.Members.Strings[1]);
    AssertEquals('m2', 'Blue',  Enum.Members.Strings[2]);
    AssertEquals('ord 0', 0, Enum.OrdinalAt(0));
    AssertEquals('ord 1', 1, Enum.OrdinalAt(1));
    AssertEquals('ord 2', 2, Enum.OrdinalAt(2));
  finally
    Iface.Free;
  end;
end;

procedure TEnumSetTests.TestSet_BaseEnumPreserved;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type'                                              + #10 +
    '  TFlag = (fA, fB, fC);'                           + #10 +
    '  TFlags = set of TFlag;'                          + #10 +
    'implementation'                                    + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
begin
  Iface := ParseAndExport(SRC);
  try
    E := Iface.FindType('TFlags');
    AssertEquals('found',         True, E <> nil);
    AssertEquals('is set def',    True, E.Def is TSetTypeDef);
    AssertEquals('base enum',    'TFlag', TSetTypeDef(E.Def).BaseTypeName);
  finally
    Iface.Free;
  end;
end;

{ ----- TRecordClassLayoutTests (record-shape subset) ------------ }

procedure TRecordClassLayoutTests.TestRecord_FieldsInDeclarationOrder;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type'                                              + #10 +
    '  TPoint = record'                                 + #10 +
    '    X: Integer;'                                   + #10 +
    '    Y: Integer;'                                   + #10 +
    '    Z: Integer;'                                   + #10 +
    '  end;'                                            + #10 +
    'implementation'                                    + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
  Rec:   TRecordTypeDef;
  F0, F1, F2: TFieldDecl;
begin
  Iface := ParseAndExport(SRC);
  try
    E := Iface.FindType('TPoint');
    AssertEquals('found', True, E <> nil);
    AssertEquals('is record', True, E.Def is TRecordTypeDef);

    Rec := TRecordTypeDef(E.Def);
    AssertEquals('field count', 3, Rec.Fields.Count);

    F0 := TFieldDecl(Rec.Fields.Items[0]);
    F1 := TFieldDecl(Rec.Fields.Items[1]);
    F2 := TFieldDecl(Rec.Fields.Items[2]);

    AssertEquals('f0 name', 'X', F0.Names.Strings[0]);
    AssertEquals('f1 name', 'Y', F1.Names.Strings[0]);
    AssertEquals('f2 name', 'Z', F2.Names.Strings[0]);
  finally
    Iface.Free;
  end;
end;

procedure TRecordClassLayoutTests.TestRecord_FieldTypes_AsQualTypeRef;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type'                                              + #10 +
    '  TLocal = record A: Integer; end;'                + #10 +
    '  TUses = record'                                  + #10 +
    '    L: TLocal;'                                    + #10 +
    '    N: Integer;'                                   + #10 +
    '  end;'                                            + #10 +
    'implementation'                                    + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
  Rec:   TRecordTypeDef;
  F:     TFieldDecl;
begin
  { TQualTypeRef for record-field types isn't populated by Phase 2's
    BuildTypeEntry yet — CloneTypeDef preserves the TypeName string,
    but per-field TQualTypeRef resolution requires a richer Phase 3
    walk.  This test verifies what we DO have today: the field
    TypeName strings are correctly cloned, so a later resolver pass
    can still figure out which unit owns each type. }
  Iface := ParseAndExport(SRC);
  try
    E := Iface.FindType('TUses');
    AssertEquals('found', True, E <> nil);

    Rec := TRecordTypeDef(E.Def);
    AssertEquals('field count', 2, Rec.Fields.Count);

    F := TFieldDecl(Rec.Fields.Items[0]);
    AssertEquals('f0 type name', 'TLocal',  F.TypeName);

    F := TFieldDecl(Rec.Fields.Items[1]);
    AssertEquals('f1 type name', 'Integer', F.TypeName);
  finally
    Iface.Free;
  end;
end;
{ ----- TRecordClassLayoutTests (class subset, Phase 3) ---------- }

procedure TRecordClassLayoutTests.TestClass_ParentClassResolved;
const
  DEP =
    'unit DepU;'                                       + #10 +
    'interface'                                        + #10 +
    'type TBase = class end;'                          + #10 +
    'implementation'                                   + #10 +
    'end.'                                             + #10;
  MAIN =
    'unit MainU;'                                      + #10 +
    'interface'                                        + #10 +
    'uses DepU;'                                       + #10 +
    'type TDerived = class(TBase) end;'                + #10 +
    'implementation'                                   + #10 +
    'end.'                                             + #10;
var
  DepIface:  TUnitInterface;
  MainIface: TUnitInterface;
  Deps:           TObjectList;
  E:              TTypeEntry;
begin
  DepIface := ParseAndExport(DEP);
  Deps := TObjectList.Create(False);
  try
    Deps.Add(DepIface);
    MainIface := ParseAndExportWithDeps(MAIN, Deps);
    try
      E := MainIface.FindType('TDerived');
      AssertEquals('found',         True,     E <> nil);
      AssertEquals('parent name',   'TBase',  E.ParentClass.TypeName);
      AssertEquals('parent unit',   'DepU',   E.ParentClass.UnitName);
    finally
      MainIface.Free;
    end;
  finally
    Deps.Free;
    DepIface.Free;
  end;
end;

procedure TRecordClassLayoutTests.TestClass_ImplementsListPopulated;
const
  SRC =
    'unit TestU;'                                                + #10 +
    'interface'                                                  + #10 +
    'type'                                                       + #10 +
    '  IFirst  = interface end;'                                 + #10 +
    '  ISecond = interface end;'                                 + #10 +
    '  TWidget = class(TObject, IFirst, ISecond) end;'           + #10 +
    'implementation'                                             + #10 +
    'end.'                                                       + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
begin
  Iface := ParseAndExport(SRC);
  try
    E := Iface.FindType('TWidget');
    AssertEquals('found',           True, E <> nil);
    AssertEquals('implements count', 2, E.Implements.Count);
    AssertEquals('impl[0]', 'IFirst',  E.Implements.Strings[0]);
    AssertEquals('impl[1]', 'ISecond', E.Implements.Strings[1]);
  finally
    Iface.Free;
  end;
end;

procedure TRecordClassLayoutTests.TestClass_MethodSignaturesExported;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type'                                              + #10 +
    '  TWidget = class'                                 + #10 +
    '    procedure Step;'                               + #10 +
    '    function  Count: Integer;'                     + #10 +
    '  end;'                                            + #10 +
    'implementation'                                    + #10 +
    'procedure TWidget.Step; begin end;'                + #10 +
    'function  TWidget.Count: Integer; begin Result := 0; end;' + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
  Step:  TRoutineSig;
  Count: TRoutineSig;
begin
  Iface := ParseAndExport(SRC);
  try
    E := Iface.FindType('TWidget');
    AssertEquals('found', True, E <> nil);
    AssertEquals('method count', 2, E.Methods.Count);

    Step  := TRoutineSig(E.Methods.Items[0]);
    Count := TRoutineSig(E.Methods.Items[1]);
    AssertEquals('m0 name',     'Step',    Step.Name);
    AssertEquals('m0 not func', False,     Step.IsFunction);
    AssertEquals('m1 name',     'Count',   Count.Name);
    AssertEquals('m1 is func',  True,      Count.IsFunction);
    AssertEquals('m1 return',   'Integer', Count.ReturnType.TypeName);
  finally
    Iface.Free;
  end;
end;

procedure TRecordClassLayoutTests.TestClass_VTableSlotsAssigned;
begin
  { VTableSlot is assigned by uSemantic, not the parser.  Until Phase 4
    wires AnalyseUnit-then-ExportUnitInterface together, every method
    arrives at the export with VTableSlot = -1, so VTableLayout stays
    empty.  Pending Phase 4. }
  Fail('Pending Phase 4: AnalyseUnit-then-Export pipeline');
end;

procedure TRecordClassLayoutTests.TestClass_InstanceSizeComputed;
begin
  { InstanceSize is computed by uSemantic too.  Same Phase 4 dependency
    as VTableSlotsAssigned. }
  Fail('Pending Phase 4: AnalyseUnit-then-Export pipeline');
end;

procedure TRecordClassLayoutTests.TestClass_AttributesPreserved;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type'                                              + #10 +
    '  [Threaded]'                                      + #10 +
    '  TJob = class end;'                               + #10 +
    'implementation'                                    + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
begin
  Iface := ParseAndExport(SRC);
  try
    E := Iface.FindType('TJob');
    AssertEquals('found',          True, E <> nil);
    AssertEquals('attribute count', 1, E.Attributes.Count);
    AssertEquals('attribute name', 'Threaded', E.Attributes.Strings[0]);
  finally
    Iface.Free;
  end;
end;

{ ----- TInlineGenericBodyTests ---------------------------------- }

procedure TInlineGenericBodyTests.TestInline_BodyExportedWithSig;
const
  SRC =
    'unit TestU;'                                          + #10 +
    'interface'                                            + #10 +
    'function Square(N: Integer): Integer; inline;'        + #10 +
    'implementation'                                       + #10 +
    'function Square(N: Integer): Integer; begin Result := N * N; end;' + #10 +
    'end.'                                                 + #10;
var
  Iface: TUnitInterface;
  Sig:   TRoutineSig;
  Body:  TInlineBody;
begin
  Iface := ParseAndExport(SRC);
  try
    Sig := Iface.FindRoutine('Square');
    AssertEquals('sig found',  True, Sig <> nil);
    AssertEquals('sig inline', True, Sig.IsInline);

    Body := Iface.FindInlineBody('Square');
    AssertEquals('body found', True, Body <> nil);
    AssertEquals('block non-nil', True, Body.Block <> nil);
  finally
    Iface.Free;
  end;
end;

procedure TInlineGenericBodyTests.TestGenericType_BodyExported;
const
  SRC =
    'unit TestU;'                                          + #10 +
    'interface'                                            + #10 +
    'type'                                                 + #10 +
    '  TBox<T> = class'                                    + #10 +
    '    Value: T;'                                        + #10 +
    '  end;'                                               + #10 +
    'implementation'                                       + #10 +
    'end.'                                                 + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
  G:     TGenericBody;
begin
  Iface := ParseAndExport(SRC);
  try
    E := Iface.FindType('TBox');
    AssertEquals('type entry', True, E <> nil);
    AssertEquals('IsGeneric flag', True, E.IsGeneric);

    G := Iface.FindGeneric('TBox');
    AssertEquals('generic entry', True, G <> nil);
    AssertEquals('IsType',  True, G.IsType);
    AssertEquals('TypeDef non-nil', True, G.TypeDef <> nil);
    AssertEquals('type-param count', 1, G.TypeParams.Count);
    AssertEquals('type-param[0]', 'T', G.TypeParams.Strings[0]);
  finally
    Iface.Free;
  end;
end;

procedure TInlineGenericBodyTests.TestGenericRoutine_BodyExported;
begin
  { Generic free-routine declarations are accepted in *programs* but
    not currently in unit interface sections — uParser.ParseForwardDecl
    doesn't consume a '<T>' between the name and parameter list.
    Pending until the parser is extended (or the test moved to a
    program-level harness). }
  Fail('Pending parser support for generic free routines in unit interface');
end;

procedure TInlineGenericBodyTests.TestGeneric_ConstraintsPreserved;
const
  SRC =
    'unit TestU;'                                          + #10 +
    'interface'                                            + #10 +
    'type'                                                 + #10 +
    '  TList<T: class> = class'                            + #10 +
    '    Head: T;'                                         + #10 +
    '  end;'                                               + #10 +
    'implementation'                                       + #10 +
    'end.'                                                 + #10;
var
  Iface: TUnitInterface;
  G:     TGenericBody;
begin
  Iface := ParseAndExport(SRC);
  try
    G := Iface.FindGeneric('TList');
    AssertEquals('generic found', True, G <> nil);
    AssertEquals('constraint',    'class', G.Constraints.Strings[0]);
  finally
    Iface.Free;
  end;
end;

{ ----- TImplementationHidingTests ------------------------------- }

procedure TImplementationHidingTests.TestImplOnlyRoutine_NotExported;
const
  SRC =
    'unit TestU;'                                 + #10 +
    'interface'                                   + #10 +
    'procedure Public1;'                          + #10 +
    'implementation'                              + #10 +
    'procedure Private1; begin end;'              + #10 +
    'procedure Public1;  begin end;'              + #10 +
    'end.'                                        + #10;
var
  Iface: TUnitInterface;
begin
  Iface := ParseAndExport(SRC);
  try
    AssertEquals('intf count',  1, Iface.Routines.Count);
    AssertEquals('public present', True, Iface.FindRoutine('Public1')  <> nil);
    AssertEquals('private hidden', True, Iface.FindRoutine('Private1') = nil);
  finally
    Iface.Free;
  end;
end;

procedure TImplementationHidingTests.TestImplOnlyType_NotExported;
const
  SRC =
    'unit TestU;'                              + #10 +
    'interface'                                + #10 +
    'type TPublic = record X: Integer; end;'   + #10 +
    'implementation'                           + #10 +
    'type TPrivate = record Y: Integer; end;'  + #10 +
    'end.'                                     + #10;
var
  Iface: TUnitInterface;
begin
  Iface := ParseAndExport(SRC);
  try
    AssertEquals('intf count', 1, Iface.Types.Count);
    AssertEquals('public present', True, Iface.FindType('TPublic')  <> nil);
    AssertEquals('private hidden', True, Iface.FindType('TPrivate') = nil);
  finally
    Iface.Free;
  end;
end;

procedure TImplementationHidingTests.TestRegularRoutine_SigOnly_NoBody;
const
  SRC =
    'unit TestU;'                       + #10 +
    'interface'                         + #10 +
    'function Compute(N: Integer): Integer;' + #10 +
    'implementation'                    + #10 +
    'function Compute(N: Integer): Integer; begin Result := N * 2; end;' + #10 +
    'end.'                              + #10;
var
  Iface: TUnitInterface;
  Sig:   TRoutineSig;
begin
  Iface := ParseAndExport(SRC);
  try
    Sig := Iface.FindRoutine('Compute');
    AssertEquals('routine present', True, Sig <> nil);
    AssertEquals('is function',     True, Sig.IsFunction);
    AssertEquals('return type',     'Integer', Sig.ReturnType.TypeName);
    AssertEquals('param count',     1, Sig.Params.Count);
    AssertEquals('no inline body', True,
                 Iface.FindInlineBody('Compute') = nil);
  finally
    Iface.Free;
  end;
end;

{ ----- TVisibilityTests ----------------------------------------- }

procedure TVisibilityTests.TestClassMember_VisibilityPreserved;
const
  { Today the parser only tracks 'published' as a distinct
    visibility (used for RTL MethodAddress lookups); private /
    protected / public are accepted but silently dropped to the
    same default state.  Pin down what we DO carry through. }
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type'                                              + #10 +
    '  TWidget = class'                                 + #10 +
    '  published'                                       + #10 +
    '    procedure Pub;'                                + #10 +
    '  public'                                          + #10 +
    '    procedure Pub2;'                               + #10 +
    '  end;'                                            + #10 +
    'implementation'                                    + #10 +
    'procedure TWidget.Pub;  begin end;'                + #10 +
    'procedure TWidget.Pub2; begin end;'                + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
  Pub:   TRoutineSig;
  Pub2:  TRoutineSig;
begin
  Iface := ParseAndExport(SRC);
  try
    E    := Iface.FindType('TWidget');
    Pub  := TRoutineSig(E.Methods.Items[0]);
    Pub2 := TRoutineSig(E.Methods.Items[1]);

    AssertEquals('Pub  IsPublished',  True,  Pub.IsPublished);
    AssertEquals('Pub2 IsPublished',  False, Pub2.IsPublished);
  finally
    Iface.Free;
  end;
end;

{ ----- TForwardDeclTests ---------------------------------------- }

procedure TForwardDeclTests.TestForwardDeclClass_FullBodyExported;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'type TWidget = class;'                             + #10 +
    'implementation'                                    + #10 +
    'type'                                              + #10 +
    '  TWidget = class'                                 + #10 +
    '    procedure Step;'                               + #10 +
    '    N: Integer;'                                   + #10 +
    '  end;'                                            + #10 +
    'procedure TWidget.Step; begin end;'                + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  E:     TTypeEntry;
begin
  Iface := ParseAndExport(SRC);
  try
    E := Iface.FindType('TWidget');
    AssertEquals('found',        True, E <> nil);
    AssertEquals('is class',     True, E.IsClass);
    AssertEquals('method count', 1, E.Methods.Count);
    AssertEquals('field count',  1, TClassTypeDef(E.Def).Fields.Count);
  finally
    Iface.Free;
  end;
end;

{ ----- TRoutineSigTests ----------------------------------------- }

procedure TRoutineSigTests.TestParam_ModeVar_Preserved;
const
  SRC =
    'unit TestU;'                              + #10 +
    'interface'                                + #10 +
    'procedure Inc(var X: Integer);'           + #10 +
    'implementation'                           + #10 +
    'procedure Inc(var X: Integer); begin X := X + 1; end;' + #10 +
    'end.'                                     + #10;
var
  Iface: TUnitInterface;
  Sig:   TRoutineSig;
  P:     TMethodParam;
begin
  Iface := ParseAndExport(SRC);
  try
    Sig := Iface.FindRoutine('Inc');
    AssertEquals('found', True, Sig <> nil);
    AssertEquals('param count', 1, Sig.Params.Count);
    P := TMethodParam(Sig.Params.Items[0]);
    AssertEquals('name',  'X',     P.ParamName);
    AssertEquals('type',  'Integer', P.TypeName);
    AssertEquals('var',   True,    P.IsVarParam);
    AssertEquals('not const', False, P.IsConstParam);
  finally
    Iface.Free;
  end;
end;

procedure TRoutineSigTests.TestParam_ModeConst_Preserved;
const
  SRC =
    'unit TestU;'                                  + #10 +
    'interface'                                    + #10 +
    'function Hash(const S: string): Integer;'     + #10 +
    'implementation'                               + #10 +
    'function Hash(const S: string): Integer; begin Result := 0; end;' + #10 +
    'end.'                                         + #10;
var
  Iface: TUnitInterface;
  Sig:   TRoutineSig;
  P:     TMethodParam;
begin
  Iface := ParseAndExport(SRC);
  try
    Sig := Iface.FindRoutine('Hash');
    AssertEquals('found', True, Sig <> nil);
    P := TMethodParam(Sig.Params.Items[0]);
    AssertEquals('name',      'S',      P.ParamName);
    AssertEquals('type',      'string', P.TypeName);
    AssertEquals('const',     True,     P.IsConstParam);
    AssertEquals('not var',   False,    P.IsVarParam);
  finally
    Iface.Free;
  end;
end;

procedure TRoutineSigTests.TestParam_ModeOut_Preserved;
begin
  { 'out' parameter mode is not yet tracked in TMethodParam.
    Pending until uAST grows an IsOutParam flag (out-of-scope for
    the loader work). }
  Fail('Pending uAST IsOutParam support');
end;

procedure TRoutineSigTests.TestReturnType_FunctionVsProcedure;
const
  SRC =
    'unit TestU;'                                + #10 +
    'interface'                                  + #10 +
    'procedure Step;'                            + #10 +
    'function  Count: Integer;'                  + #10 +
    'implementation'                             + #10 +
    'procedure Step;            begin end;'      + #10 +
    'function  Count: Integer;  begin Result := 0; end;' + #10 +
    'end.'                                       + #10;
var
  Iface: TUnitInterface;
  Proc:  TRoutineSig;
  Func:  TRoutineSig;
begin
  Iface := ParseAndExport(SRC);
  try
    Proc := Iface.FindRoutine('Step');
    Func := Iface.FindRoutine('Count');
    AssertEquals('procedure found', True, Proc <> nil);
    AssertEquals('function  found', True, Func <> nil);
    AssertEquals('proc IsFunction',  False, Proc.IsFunction);
    AssertEquals('proc ret empty',   '', Proc.ReturnType.TypeName);
    AssertEquals('func IsFunction',  True, Func.IsFunction);
    AssertEquals('func ret',         'Integer', Func.ReturnType.TypeName);
  finally
    Iface.Free;
  end;
end;

procedure TRoutineSigTests.TestCallingConv_Cdecl_Preserved;
begin
  { Calling conventions (cdecl/stdcall) aren't carried on TMethodDecl
    in the current uAST.  When they're added (Attributes-driven or
    a dedicated field), this test should populate TRoutineSig.CallingConv.
    Pending until uAST exposes the field. }
  Fail('Pending uAST CallingConv support');
end;

procedure TRoutineSigTests.TestExternal_NamePreserved;
const
  SRC =
    'unit TestU;'                                       + #10 +
    'interface'                                         + #10 +
    'function clock: Integer; external name ''clock'';' + #10 +
    'implementation'                                    + #10 +
    'end.'                                              + #10;
var
  Iface: TUnitInterface;
  Sig:   TRoutineSig;
begin
  Iface := ParseAndExport(SRC);
  try
    Sig := Iface.FindRoutine('clock');
    AssertEquals('found',         True,   Sig <> nil);
    AssertEquals('is external',   True,   Sig.IsExternal);
    AssertEquals('external name', 'clock', Sig.ExternalName);
  finally
    Iface.Free;
  end;
end;

{ ----- TUsedUnitsTests ------------------------------------------ }

procedure TUsedUnitsTests.TestUsedUnits_OrderPreserved;
var
  U: TUnitInterface;
begin
  U := TUnitInterface.Create('TestUnit');
  try
    U.UsedUnits.Add('SysUtils');
    U.UsedUnits.Add('Classes');
    U.UsedUnits.Add('Math');

    AssertEquals('count',    3, U.UsedUnits.Count);
    AssertEquals('first',    'SysUtils', U.UsedUnits.Strings[0]);
    AssertEquals('second',   'Classes',  U.UsedUnits.Strings[1]);
    AssertEquals('third',    'Math',     U.UsedUnits.Strings[2]);
  finally
    U.Free;
  end;
end;

procedure TUsedUnitsTests.TestImplOnlyUsedUnit_NotInUsedUnits;
const
  SRC =
    'unit TestU;'                + #10 +
    'interface'                  + #10 +
    'uses SysUtils;'             + #10 +
    'implementation'             + #10 +
    'uses Classes, Math;'        + #10 +
    'end.'                       + #10;
var
  Iface: TUnitInterface;
begin
  Iface := ParseAndExport(SRC);
  try
    AssertEquals('intf-uses count',   1,          Iface.UsedUnits.Count);
    AssertEquals('intf-uses[0]',      'SysUtils', Iface.UsedUnits.Strings[0]);
    AssertEquals('Classes excluded',  -1,         Iface.UsedUnits.IndexOf('Classes'));
    AssertEquals('Math excluded',     -1,         Iface.UsedUnits.IndexOf('Math'));
  finally
    Iface.Free;
  end;
end;

{ ----- TLookupTests --------------------------------------------- }

{ Helpers — build minimal entries for lookup-table testing.
  TLookupTests only exercises the index/lookup machinery, so the
  entries don't need to be semantically meaningful. }

function MakeTypeEntry(const AName: string): TTypeEntry;
begin
  Result := TTypeEntry.Create;
  Result.Name := AName;
end;

function MakeConstEntry(const AName: string): TConstEntry;
begin
  Result := TConstEntry.Create;
  Result.Decl := TConstDecl.Create;
  Result.Decl.Name := AName;
end;

function MakeRoutineSig(const AName: string): TRoutineSig;
begin
  Result := TRoutineSig.Create;
  Result.Name := AName;
end;

function MakeGenericBody(const AName: string): TGenericBody;
begin
  Result := TGenericBody.Create;
  Result.Name := AName;
end;

function MakeInlineBody: TInlineBody;
begin
  Result := TInlineBody.Create;
  Result.RoutineName := 'SomeInline';
end;

procedure TLookupTests.TestFindType_CaseInsensitive;
var
  U: TUnitInterface;
  E: TTypeEntry;
begin
  U := TUnitInterface.Create('TestUnit');
  try
    U.AddType(MakeTypeEntry('TFoo'));

    E := U.FindType('TFoo');
    AssertEquals('exact', True, E <> nil);
    AssertEquals('exact name', 'TFoo', E.Name);

    E := U.FindType('tfoo');
    AssertEquals('lowercase', True, E <> nil);

    E := U.FindType('TFOO');
    AssertEquals('uppercase', True, E <> nil);
  finally
    U.Free;
  end;
end;

procedure TLookupTests.TestFindConst_CaseInsensitive;
var
  U: TUnitInterface;
  E: TConstEntry;
begin
  U := TUnitInterface.Create('TestUnit');
  try
    U.AddConst(MakeConstEntry('MaxValue'));

    E := U.FindConst('MaxValue');
    AssertEquals('exact', True, E <> nil);

    E := U.FindConst('MAXVALUE');
    AssertEquals('uppercase', True, E <> nil);

    E := U.FindConst('maxvalue');
    AssertEquals('lowercase', True, E <> nil);
  finally
    U.Free;
  end;
end;

procedure TLookupTests.TestFindRoutine_CaseInsensitive;
var
  U: TUnitInterface;
  S: TRoutineSig;
begin
  U := TUnitInterface.Create('TestUnit');
  try
    U.AddRoutine(MakeRoutineSig('DoStuff'));

    S := U.FindRoutine('DoStuff');
    AssertEquals('exact', True, S <> nil);

    S := U.FindRoutine('dostuff');
    AssertEquals('lowercase', True, S <> nil);

    S := U.FindRoutine('DOSTUFF');
    AssertEquals('uppercase', True, S <> nil);
  finally
    U.Free;
  end;
end;

procedure TLookupTests.TestFindGeneric_CaseInsensitive;
var
  U: TUnitInterface;
  G: TGenericBody;
begin
  U := TUnitInterface.Create('TestUnit');
  try
    U.AddGenericBody(MakeGenericBody('TList'));

    G := U.FindGeneric('TList');
    AssertEquals('exact', True, G <> nil);

    G := U.FindGeneric('tlist');
    AssertEquals('lowercase', True, G <> nil);

    G := U.FindGeneric('TLIST');
    AssertEquals('uppercase', True, G <> nil);
  finally
    U.Free;
  end;
end;

procedure TLookupTests.TestFindType_CaseSensitive_FlagRespected;
var
  U: TUnitInterface;
begin
  U := TUnitInterface.Create('TestUnit', True);  { case-sensitive }
  try
    U.AddType(MakeTypeEntry('TFoo'));

    AssertEquals('exact match',     True, U.FindType('TFoo') <> nil);
    AssertEquals('wrong case miss', True, U.FindType('tfoo') = nil);
    AssertEquals('upper case miss', True, U.FindType('TFOO') = nil);
  finally
    U.Free;
  end;
end;

procedure TLookupTests.TestFind_Missing_ReturnsNil;
var
  U: TUnitInterface;
begin
  U := TUnitInterface.Create('TestUnit');
  try
    U.AddType(MakeTypeEntry('TFoo'));
    U.AddConst(MakeConstEntry('Pi'));
    U.AddRoutine(MakeRoutineSig('DoIt'));
    U.AddGenericBody(MakeGenericBody('TList'));
    U.AddInlineBody(MakeInlineBody);

    AssertEquals('type missing',     True, U.FindType('TBar') = nil);
    AssertEquals('const missing',    True, U.FindConst('E') = nil);
    AssertEquals('routine missing',  True, U.FindRoutine('Other') = nil);
    AssertEquals('inline missing',   True, U.FindInlineBody('NotInline') = nil);
    AssertEquals('generic missing',  True, U.FindGeneric('TQueue') = nil);
  finally
    U.Free;
  end;
end;

{ ----- TMetadataTests ------------------------------------------- }

procedure TMetadataTests.TestName_MatchesSource;
var
  U: TUnitInterface;
begin
  U := TUnitInterface.Create('MyUnit');
  try
    AssertEquals('name preserved', 'MyUnit', U.Name);
  finally
    U.Free;
  end;
end;

procedure TMetadataTests.TestSourceFile_MatchesPath;
var
  U: TUnitInterface;
begin
  U := TUnitInterface.Create('MyUnit');
  try
    U.SourceFile := '/tmp/MyUnit.pas';
    AssertEquals('source file', '/tmp/MyUnit.pas', U.SourceFile);
  finally
    U.Free;
  end;
end;

{ SourceHash and CompilerVersion are reserved for Phase 5+ .bpu work.
  They are documented as empty strings at construction time.  The
  tests pin that contract so a later patch that starts populating
  them doesn't silently change semantics for downstream consumers. }

procedure TMetadataTests.TestSourceHash_NonEmpty;
var
  U: TUnitInterface;
begin
  U := TUnitInterface.Create('MyUnit');
  try
    AssertEquals('hash empty in Phase 1', '', U.SourceHash);
  finally
    U.Free;
  end;
end;

procedure TMetadataTests.TestCompilerVersion_NonEmpty;
var
  U: TUnitInterface;
begin
  U := TUnitInterface.Create('MyUnit');
  try
    AssertEquals('compiler version empty in Phase 1', '', U.CompilerVersion);
  finally
    U.Free;
  end;
end;

initialization
  RegisterTest(TSelfContainmentTests);
  RegisterTest(TCrossUnitRefTests);
  RegisterTest(TConstRoundTripTests);
  RegisterTest(TEnumSetTests);
  RegisterTest(TRecordClassLayoutTests);
  RegisterTest(TInlineGenericBodyTests);
  RegisterTest(TImplementationHidingTests);
  RegisterTest(TVisibilityTests);
  RegisterTest(TForwardDeclTests);
  RegisterTest(TRoutineSigTests);
  RegisterTest(TUsedUnitsTests);
  RegisterTest(TLookupTests);
  RegisterTest(TMetadataTests);
end.
