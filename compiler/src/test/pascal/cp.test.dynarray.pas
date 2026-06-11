{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.dynarray;

{ Tests for dynamic array type declarations:
  parsing, semantic analysis, and QBE IR code generation.

  Dynamic arrays (array of T) are heap-allocated, reference-counted
  arrays with runtime length stored in a 2-word header before element 0.
  Layout: [refcount:4][length:4][element 0][element 1]...
  The variable slot holds a pointer to element 0 (nil = unassigned). }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

type
  TDynArrayTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    function CountOccurrences(const AHaystack, ANeedle: string): Integer;
  published
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_DynArray_TypeAlias_AcceptsDecl;
    procedure TestParse_DynArray_InlineVarDecl_AcceptsDecl;
    procedure TestParse_DynArray_Combined_TypeAndVar;
    procedure TestParse_DynArray_TypeName_EncodesCorrectly;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_DynArray_Kind;
    procedure TestSemantic_DynArray_ElementType_Integer;
    procedure TestSemantic_DynArray_ElementType_String;
    procedure TestSemantic_DynArray_Var_ResolvesToDynArray;

    { ------------------------------------------------------------------ }
    { Codegen                                                              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_DynArray_Var_AllocatedAsPointerSlot;
    procedure TestCodegen_DynArray_Var_ZeroInitialised;
    procedure TestCodegen_DynArray_SetLength_CallsRTL;
    procedure TestCodegen_DynArray_Length_CallsRTL;
    procedure TestCodegen_DynArray_Read_ComputesOffset;
    procedure TestCodegen_DynArray_Write_ComputesOffset;
    procedure TestCodegen_DynArray_High_CallsRTL;
    procedure TestCodegen_DynArray_Low_ReturnsZero;
    procedure TestCodegen_DynArray_AddrOfElement_ComputesOffset;
    procedure TestCodegen_DynArray_AddrOfRecordFieldElement;
    procedure TestSemantic_DynArray_High_Accepted;
    procedure TestSemantic_DynArray_Low_Accepted;

    { ------------------------------------------------------------------ }
    { Record elements: a[i] := r copies; a[i].F := v assigns in place      }
    { ------------------------------------------------------------------ }
    procedure TestParse_DynArray_RecordElem_FieldAssign_Accepted;
    procedure TestCodegen_DynArray_RecordElem_Write_FieldwiseCopy;
    procedure TestCodegen_DynArray_RecordElem_FieldAssign_StringARC;

    { ------------------------------------------------------------------ }
    { Array-typed FIELDS: r.A[i] := v writes the element, not the array    }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_RecordField_DynArrayElemAssign_Accepted;
    procedure TestParse_ChainedField_DynArrayElemAssign_Accepted;
    procedure TestCodegen_RecordField_DynArrayElemWrite_StoresElement;
    procedure TestCodegen_ClassField_DynArrayElemWrite_StoresElement;
  end;

implementation

function TDynArrayTests.ParseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try Result := P.Parse(); finally P.Free(); L.Free(); end;
end;

function TDynArrayTests.AnalyseSrc(const ASrc: string): TProgram;
var A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create();
  try A.Analyse(Result); finally A.Free(); end;
end;

function TDynArrayTests.GenIR(const ASrc: string): string;
var Prog: TProgram; CG: TCodeGenQBE;
begin
  Prog := AnalyseSrc(ASrc);
  try
    CG := TCodeGenQBE.Create();
    try CG.Generate(Prog); Result := CG.GetOutput(); finally CG.Free(); end;
  finally Prog.Free(); end;
end;

function TDynArrayTests.CountOccurrences(
  const AHaystack, ANeedle: string): Integer;
var Pos2, I: Integer;
begin
  Result := 0;
  I := 0;
  repeat
    Pos2 := PosEx(ANeedle, AHaystack, I);
    if Pos2 < 0 then Break;
    Inc(Result);
    I := Pos2 + Length(ANeedle);
  until False;
end;

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TDynArrayTests.TestParse_DynArray_TypeAlias_AcceptsDecl;
var Prog: TProgram;
begin
  Prog := ParseSrc('''
      program Prg;
      type
        TIntArr = array of Integer;
      begin
      end.
      ''');
  try
    AssertEquals('one type decl', 1, Prog.Block.TypeDecls.Count);
  finally Prog.Free(); end;
end;

procedure TDynArrayTests.TestParse_DynArray_InlineVarDecl_AcceptsDecl;
var Prog: TProgram;
begin
  Prog := ParseSrc('''
      program Prg;
      var
        A: array of Integer;
      begin
      end.
      ''');
  try
    AssertEquals('one var decl', 1, Prog.Block.Decls.Count);
  finally Prog.Free(); end;
end;

procedure TDynArrayTests.TestParse_DynArray_Combined_TypeAndVar;
var Prog: TProgram;
begin
  Prog := ParseSrc('''
      program Prg;
      type
        TStrArr = array of string;
      var
        S: TStrArr;
      begin
      end.
      ''');
  try
    AssertEquals('one type decl', 1, Prog.Block.TypeDecls.Count);
    AssertEquals('one var decl', 1, Prog.Block.Decls.Count);
  finally Prog.Free(); end;
end;

procedure TDynArrayTests.TestParse_DynArray_TypeName_EncodesCorrectly;
var Prog: TProgram; TD: TTypeDecl; AD: TTypeAliasDef;
begin
  Prog := ParseSrc('''
      program Prg;
      type
        TIntArr = array of Integer;
      begin
      end.
      ''');
  try
    TD := TTypeDecl(Prog.Block.TypeDecls.Items[0]);
    AD := TTypeAliasDef(TD.Def);
    AssertEquals('type name encoded as array of Integer',
      'array of Integer', AD.TypeName);
  finally Prog.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TDynArrayTests.TestSemantic_DynArray_Kind;
var Prog: TProgram; Sym: TSymbol;
begin
  Prog := AnalyseSrc('''
      program Prg;
      type
        TIntArr = array of Integer;
      begin
      end.
      ''');
  try
    Sym := Prog.SymbolTable.Lookup('TIntArr');
    AssertTrue('TIntArr symbol found', Sym <> nil);
    AssertEquals('kind is tyDynArray', Ord(tyDynArray), Ord(Sym.TypeDesc.Kind));
  finally Prog.Free(); end;
end;

procedure TDynArrayTests.TestSemantic_DynArray_ElementType_Integer;
var Prog: TProgram; Sym: TSymbol; DAT: TDynArrayTypeDesc;
begin
  Prog := AnalyseSrc('''
      program Prg;
      type
        TIntArr = array of Integer;
      begin
      end.
      ''');
  try
    Sym := Prog.SymbolTable.Lookup('TIntArr');
    DAT := TDynArrayTypeDesc(Sym.TypeDesc);
    AssertEquals('element type is Integer', 'Integer', DAT.ElementType.Name);
  finally Prog.Free(); end;
end;

procedure TDynArrayTests.TestSemantic_DynArray_ElementType_String;
var Prog: TProgram; Sym: TSymbol; DAT: TDynArrayTypeDesc;
begin
  Prog := AnalyseSrc('''
      program Prg;
      type
        TStrArr = array of string;
      begin
      end.
      ''');
  try
    Sym := Prog.SymbolTable.Lookup('TStrArr');
    DAT := TDynArrayTypeDesc(Sym.TypeDesc);
    AssertEquals('element type is string', 'string', DAT.ElementType.Name);
  finally Prog.Free(); end;
end;

procedure TDynArrayTests.TestSemantic_DynArray_Var_ResolvesToDynArray;
var Prog: TProgram; VD: TVarDecl;
begin
  Prog := AnalyseSrc('''
      program Prg;
      var
        A: array of Integer;
      begin
      end.
      ''');
  try
    VD := TVarDecl(Prog.Block.Decls.Items[0]);
    AssertEquals('var resolved to tyDynArray',
      Ord(tyDynArray), Ord(VD.ResolvedType.Kind));
  finally Prog.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                        }
{ ------------------------------------------------------------------ }

procedure TDynArrayTests.TestCodegen_DynArray_Var_AllocatedAsPointerSlot;
var IR: string;
begin
  IR := GenIR('''
      program Prg;
      procedure Foo;
      var A: array of Integer;
      begin
      end;
      begin
      end.
      ''');
  AssertTrue('alloc8 8 for dyn array var',
    Self.CountOccurrences(IR, 'alloc8 8') > 0);
end;

procedure TDynArrayTests.TestCodegen_DynArray_Var_ZeroInitialised;
var IR: string;
begin
  IR := GenIR('''
      program Prg;
      procedure Foo;
      var A: array of Integer;
      begin
      end;
      begin
      end.
      ''');
  AssertTrue('storel 0 for nil init',
    Self.CountOccurrences(IR, 'storel 0,') > 0);
end;

procedure TDynArrayTests.TestCodegen_DynArray_SetLength_CallsRTL;
var IR: string;
begin
  IR := GenIR('''
      program Prg;
      procedure Foo;
      var A: array of Integer;
      begin
        SetLength(A, 5);
      end;
      begin
      end.
      ''');
  AssertTrue('calls _DynArraySetLength',
    Self.CountOccurrences(IR, 'call $_DynArraySetLength(') > 0);
end;

procedure TDynArrayTests.TestCodegen_DynArray_Length_CallsRTL;
var IR: string;
begin
  IR := GenIR('''
      program Prg;
      procedure Foo;
      var A: array of Integer; N: Integer;
      begin
        N := Length(A);
      end;
      begin
      end.
      ''');
  AssertTrue('calls _DynArrayLength',
    Self.CountOccurrences(IR, 'call $_DynArrayLength(') > 0);
end;

procedure TDynArrayTests.TestCodegen_DynArray_Read_ComputesOffset;
var IR: string;
begin
  IR := GenIR('''
      program Prg;
      procedure Foo;
      var A: array of Integer; X: Integer;
      begin
        SetLength(A, 3);
        X := A[1];
      end;
      begin
      end.
      ''');
  { Element read: loads data ptr, computes offset via mul + add, then loadw }
  AssertTrue('mul for element offset in read',
    Self.CountOccurrences(IR, 'mul') > 0);
  AssertTrue('loadw for integer element read',
    Self.CountOccurrences(IR, 'loadw') > 0);
end;

procedure TDynArrayTests.TestCodegen_DynArray_Write_ComputesOffset;
var IR: string;
begin
  IR := GenIR('''
      program Prg;
      procedure Foo;
      var A: array of Integer;
      begin
        SetLength(A, 3);
        A[0] := 99;
      end;
      begin
      end.
      ''');
  { Element write: storew for Integer element }
  AssertTrue('storew for integer element write',
    Self.CountOccurrences(IR, 'storew') > 0);
end;

procedure TDynArrayTests.TestSemantic_DynArray_High_Accepted;
var Prog: TProgram;
begin
  { High() on a named dynamic array type must not raise a semantic error }
  Prog := AnalyseSrc('''
      program Prg;
      type Tar = array of Integer;
      var ar: Tar;
          i: Integer;
      begin
        i := High(ar);
      end.
      ''');
  AssertNotNil('program parsed and analysed without error', Prog);
  Prog.Free();
end;

procedure TDynArrayTests.TestSemantic_DynArray_Low_Accepted;
var Prog: TProgram;
begin
  { Low() on a named dynamic array type must not raise a semantic error }
  Prog := AnalyseSrc('''
      program Prg;
      type Tar = array of Integer;
      var ar: Tar;
          i: Integer;
      begin
        i := Low(ar);
      end.
      ''');
  AssertNotNil('program parsed and analysed without error', Prog);
  Prog.Free();
end;

procedure TDynArrayTests.TestCodegen_DynArray_High_CallsRTL;
var IR: string;
begin
  { High(dynArr) = DynArrayLength(dynArr) - 1; must call _DynArrayLength }
  IR := GenIR('''
      program Prg;
      type Tar = array of Integer;
      var ar: Tar;
          i: Integer;
      begin
        SetLength(ar, 15);
        i := High(ar);
        WriteLn(i);
      end.
      ''');
  AssertTrue('calls _DynArrayLength for High(dynArr)',
    Pos('_DynArrayLength', IR) > 0);
end;

procedure TDynArrayTests.TestCodegen_DynArray_Low_ReturnsZero;
var IR: string;
begin
  { Low(dynArr) is always 0; must emit a copy of 0 }
  IR := GenIR('''
      program Prg;
      type Tar = array of Integer;
      var ar: Tar;
          i: Integer;
      begin
        i := Low(ar);
        WriteLn(i);
      end.
      ''');
  AssertTrue('emits constant 0 for Low(dynArr)',
    Pos('copy 0', IR) > 0);
end;

procedure TDynArrayTests.TestCodegen_DynArray_AddrOfElement_ComputesOffset;
var IR: string;
begin
  { Regression: @A[i] on a dyn-array used to raise "Unsupported L-value
    form for var argument" because EmitAddrOfExpr only handled static
    and open arrays.  The fix mirrors the open-array shape (element
    size from TDynArrayTypeDesc.ElementType.RawSize, no LowBound).
    Verify the offset arithmetic + base load are emitted without
    going through a temporary aggregate copy. }
  IR := GenIR('''
      program Prg;
      type TRec = record X: Integer; end;
           PRec = ^TRec;
      var A: array of TRec;
          P: PRec;
      begin
        SetLength(A, 3);
        P := @A[1]
      end.
      ''');
  AssertTrue('mul for element offset in @A[i]',
    Self.CountOccurrences(IR, 'mul') > 0);
  AssertTrue('add to combine base + offset',
    Self.CountOccurrences(IR, 'add') > 0);
end;

procedure TDynArrayTests.TestCodegen_DynArray_AddrOfRecordFieldElement;
var IR: string;
begin
  IR := GenIR('''
      program Prg;
      type TRec = record X: Integer; end;
           PRec = ^TRec;
           THolder = record Items: array of TRec; end;
      var A: array of TRec;
          H: THolder;
          P: PRec;
      begin
        SetLength(A, 3);
        H.Items := A;
        P := @H.Items[1]
      end.
      ''');
  AssertTrue('mul for element offset in @Rec.DynArr[i]',
    Self.CountOccurrences(IR, 'mul') > 0);
  AssertTrue('add to combine base + offset',
    Self.CountOccurrences(IR, 'add') > 0);
end;

procedure TDynArrayTests.TestParse_DynArray_RecordElem_FieldAssign_Accepted;
var Prog: TProgram;
begin
  { a[i].Field := v on the statement LHS used to raise
    "Expected ':=' but got '.'" — the subscript statement branch only
    accepted ':=' directly after ']'. }
  Prog := ParseSrc('''
      program Prg;
      type TRec = record Name: String; Number: Integer; end;
      var A: array of TRec;
      begin
        SetLength(A, 2);
        A[0].Name := 'hello';
        A[1].Number := 42;
      end.
      ''');
  AssertNotNil('program with a[i].Field := v parses', Prog);
  Prog.Free();
end;

procedure TDynArrayTests.TestCodegen_DynArray_RecordElem_Write_FieldwiseCopy;
var IR: string;
begin
  { a[i] := r with a record element must copy the record contents
    (ARC-aware fieldwise copy), not store the address of r into the
    element slot. }
  IR := GenIR('''
      program Prg;
      type TRec = record Name: String; Number: Integer; end;
      procedure Foo;
      var A: array of TRec;
          R: TRec;
      begin
        SetLength(A, 2);
        A[0] := R;
      end;
      begin
      end.
      ''');
  AssertTrue('string field retained during element copy',
    Self.CountOccurrences(IR, 'call $_StringAddRef') > 0);
  AssertEquals('record address must not be stored into the element',
    0, Self.CountOccurrences(IR, 'storel %_var_R,'));
end;

procedure TDynArrayTests.TestCodegen_DynArray_RecordElem_FieldAssign_StringARC;
var IR: string;
begin
  { a[i].Name := s must write through the element address with string ARC
    (retain new value, release old element field). }
  IR := GenIR('''
      program Prg;
      type TRec = record Name: String; Number: Integer; end;
      var A: array of TRec;
          S: String;
      begin
        SetLength(A, 1);
        S := 'hello';
        A[0].Name := S;
      end.
      ''');
  AssertTrue('retains the new string value',
    Self.CountOccurrences(IR, 'call $_StringAddRef') > 0);
  AssertTrue('releases the old element field value',
    Self.CountOccurrences(IR, 'call $_StringRelease') > 0);
end;

procedure TDynArrayTests.TestSemantic_RecordField_DynArrayElemAssign_Accepted;
var Prog: TProgram;
begin
  { r.A[0] := 10 used to fail semantic with "expected 'array of Integer'
    but got 'Integer'" — the subscript was treated as an indexed-property
    index and dropped from the LHS type. }
  Prog := AnalyseSrc('''
      program Prg;
      type
        TIA = array of Integer;
        TR  = record A: TIA; end;
      var r: TR;
      begin
        SetLength(r.A, 3);
        r.A[0] := 10;
      end.
      ''');
  AssertNotNil('record-field element assign analyses', Prog);
  Prog.Free();
end;

procedure TDynArrayTests.TestParse_ChainedField_DynArrayElemAssign_Accepted;
var Prog: TProgram;
begin
  { c.N.A[0] := 7 used to fail parse with "Expected 'end' but got '['" —
    the chained L-value walker refused a subscript after the final field. }
  Prog := ParseSrc('''
      program Prg;
      type
        TIA    = array of Integer;
        TInner = record A: TIA; end;
        TC     = class N: TInner; end;
      var c: TC;
      begin
        c := TC.Create();
        SetLength(c.N.A, 3);
        c.N.A[0] := 7;
      end.
      ''');
  AssertNotNil('chained field element assign parses', Prog);
  Prog.Free();
end;

procedure TDynArrayTests.TestCodegen_RecordField_DynArrayElemWrite_StoresElement;
var IR: string;
begin
  IR := GenIR('''
      program Prg;
      type
        TIA = array of Integer;
        TR  = record A: TIA; end;
      procedure Foo;
      var r: TR;
      begin
        SetLength(r.A, 3);
        r.A[1] := 10;
      end;
      begin
      end.
      ''');
  AssertTrue('element offset arithmetic emitted',
    Self.CountOccurrences(IR, 'mul') > 0);
  AssertTrue('integer element stored with storew',
    Self.CountOccurrences(IR, 'storew') > 0);
end;

procedure TDynArrayTests.TestCodegen_ClassField_DynArrayElemWrite_StoresElement;
var IR: string;
begin
  IR := GenIR('''
      program Prg;
      type
        TIA = array of Integer;
        TC  = class A: TIA; end;
      procedure Foo;
      var c: TC;
      begin
        c := TC.Create();
        SetLength(c.A, 3);
        c.A[1] := 10;
      end;
      begin
      end.
      ''');
  AssertTrue('element offset arithmetic emitted',
    Self.CountOccurrences(IR, 'mul') > 0);
  AssertTrue('integer element stored with storew',
    Self.CountOccurrences(IR, 'storew') > 0);
end;

initialization
  RegisterTest(TDynArrayTests);

end.
