{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

unit cp.test.inherit;

{$mode objfpc}{$H+}

{ Tests for class inheritance, self-referential types, and nil. }

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TInheritTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { nil literal                                                          }
    { ------------------------------------------------------------------ }
    procedure TestLexer_Nil_Keyword;
    procedure TestParse_Nil_IsTNilLiteral;
    procedure TestSemantic_Nil_AssignToClassVar_OK;
    procedure TestSemantic_Nil_AssignToIntVar_RaisesError;
    procedure TestSemantic_Nil_CompareWithClassVar_OK;
    procedure TestCodegen_Nil_StoresZero;
    procedure TestCodegen_Nil_CompareEmitsCeql;

    { ------------------------------------------------------------------ }
    { Self-referential types                                               }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_SelfRef_DoesNotRaiseError;
    procedure TestSemantic_SelfRef_FieldTypeIsClass;
    procedure TestCodegen_SelfRef_Create_AllocatesCorrectSize;

    { ------------------------------------------------------------------ }
    { Class inheritance — fields                                           }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Inherit_ParentFieldVisible;
    procedure TestSemantic_Inherit_ChildFieldVisible;
    procedure TestSemantic_Inherit_TotalSizeIncludesParent;
    procedure TestCodegen_Inherit_Create_AllocatesTotalSize;
    procedure TestCodegen_Inherit_ParentFieldOffset;
    procedure TestCodegen_Inherit_ChildFieldOffset;

    { ------------------------------------------------------------------ }
    { Class inheritance — methods                                          }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Inherit_MethodCallOnChild_Resolves;
    procedure TestSemantic_Inherit_UnknownMethod_RaisesError;
    procedure TestCodegen_Inherit_MethodCallUsesParentFunctionName;

    { ------------------------------------------------------------------ }
    { 'inherited' keyword                                                  }
    { ------------------------------------------------------------------ }
    procedure TestLexer_Inherited_IsOwnToken;
    procedure TestParse_Inherited_NoArgs_CreatesNode;
    procedure TestSemantic_Inherited_NoArgs_OK;
    procedure TestSemantic_Inherited_WithArgs_OK;
    procedure TestCodegen_Inherited_NoArgs_CallsParentMethod;
    procedure TestCodegen_Inherited_WithArgs_ForwardsArgs;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TInheritTests.ParseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse;
  finally
    P.Free; L.Free;
  end;
end;

function TInheritTests.AnalyseSrc(const ASrc: string): TProgram;
var A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create;
  try
    A.Analyse(Result);
  finally
    A.Free;
  end;
end;

function TInheritTests.GenIR(const ASrc: string): string;
var Prog: TProgram; CG: TCodeGenQBE;
begin
  Prog := AnalyseSrc(ASrc);
  try
    CG := TCodeGenQBE.Create;
    try
      CG.Generate(Prog);
      Result := CG.GetOutput;
    finally
      CG.Free;
    end;
  finally
    Prog.Free;
  end;
end;

procedure TInheritTests.AnalyseExpectError(const ASrc: string);
var Prog: TProgram;
begin
  try
    Prog := AnalyseSrc(ASrc);
    Prog.Free;
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ;
  end;
end;

{ ------------------------------------------------------------------ }
{ Shared source snippets                                               }
{ ------------------------------------------------------------------ }

const
  SrcNilAssign =
    'program P;'          + LineEnding +
    'var C: TNode;'       + LineEnding +  { forward ref — TNode defined after }
    'type'                + LineEnding +
    '  TNode = class'     + LineEnding +
    '    Value: Integer;' + LineEnding +
    '    Next:  TNode;'   + LineEnding +
    '  end;'              + LineEnding +
    'var N: TNode;'       + LineEnding +
    'begin'               + LineEnding +
    '  N := TNode.Create;'+ LineEnding +
    '  N.Next := nil'     + LineEnding +
    'end.';

  SrcSelfRef =
    'program P;'          + LineEnding +
    'type'                + LineEnding +
    '  TNode = class'     + LineEnding +
    '    Value: Integer;' + LineEnding +
    '    Next:  TNode;'   + LineEnding +
    '  end;'              + LineEnding +
    'var N: TNode;'       + LineEnding +
    'begin'               + LineEnding +
    '  N := TNode.Create;'+ LineEnding +
    '  N.Value := 1;'     + LineEnding +
    '  N.Next := nil'     + LineEnding +
    'end.';

  SrcInherit =
    'program P;'               + LineEnding +
    'type'                     + LineEnding +
    '  TAnimal = class'        + LineEnding +
    '    Age: Integer;'        + LineEnding +
    '  end;'                   + LineEnding +
    '  TDog = class(TAnimal)'  + LineEnding +
    '    Legs: Integer;'       + LineEnding +
    '  end;'                   + LineEnding +
    'var D: TDog;'             + LineEnding +
    'begin'                    + LineEnding +
    '  D := TDog.Create;'      + LineEnding +
    '  D.Age := 3;'            + LineEnding +
    '  D.Legs := 4'            + LineEnding +
    'end.';

  SrcInheritMethod =
    'program P;'                       + LineEnding +
    'type'                             + LineEnding +
    '  TBase = class'                  + LineEnding +
    '    X: Integer;'                  + LineEnding +
    '    procedure SetX(V: Integer);'  + LineEnding +
    '    begin'                        + LineEnding +
    '      Self.X := V'                + LineEnding +
    '    end;'                         + LineEnding +
    '  end;'                           + LineEnding +
    '  TChild = class(TBase)'          + LineEnding +
    '    Y: Integer;'                  + LineEnding +
    '  end;'                           + LineEnding +
    'var C: TChild;'                   + LineEnding +
    'begin'                            + LineEnding +
    '  C := TChild.Create;'            + LineEnding +
    '  C.SetX(10);'                    + LineEnding +
    '  C.Y := 20'                      + LineEnding +
    'end.';

{ ------------------------------------------------------------------ }
{ nil literal tests                                                   }
{ ------------------------------------------------------------------ }

procedure TInheritTests.TestLexer_Nil_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('nil');
  try
    T := L.Next;
    AssertEquals('nil token', Ord(tkNil), Ord(T.Kind));
  finally L.Free; end;
end;

procedure TInheritTests.TestParse_Nil_IsTNilLiteral;
var
  Prog:   TProgram;
  Assign: TFieldAssignment;
begin
  Prog := ParseSrc(SrcSelfRef);
  try
    { third stmt: N.Next := nil }
    AssertTrue('stmt is TFieldAssignment', Prog.Block.Stmts[2] is TFieldAssignment);
    Assign := TFieldAssignment(Prog.Block.Stmts[2]);
    AssertTrue('rhs is TNilLiteral', Assign.Expr is TNilLiteral);
  finally Prog.Free; end;
end;

procedure TInheritTests.TestSemantic_Nil_AssignToClassVar_OK;
begin
  AnalyseSrc(SrcSelfRef).Free;
end;

procedure TInheritTests.TestSemantic_Nil_AssignToIntVar_RaisesError;
begin
  AnalyseExpectError(
    'program P;'         + LineEnding +
    'var N: Integer;'    + LineEnding +
    'begin'              + LineEnding +
    '  N := nil'         + LineEnding +
    'end.');
end;

procedure TInheritTests.TestSemantic_Nil_CompareWithClassVar_OK;
begin
  AnalyseSrc(
    'program P;'               + LineEnding +
    'type'                     + LineEnding +
    '  TFoo = class'           + LineEnding +
    '    X: Integer;'          + LineEnding +
    '  end;'                   + LineEnding +
    'var F: TFoo;'             + LineEnding +
    'var N: Integer;'          + LineEnding +
    'begin'                    + LineEnding +
    '  F := TFoo.Create;'      + LineEnding +
    '  if F = nil then'        + LineEnding +
    '    N := 0'               + LineEnding +
    '  else'                   + LineEnding +
    '    N := 1'               + LineEnding +
    'end.').Free;
end;

procedure TInheritTests.TestCodegen_Nil_StoresZero;
var IR: string;
begin
  IR := GenIR(SrcSelfRef);
  { N.Next := nil should store 0 (null pointer) }
  AssertTrue('nil stores 0', Pos('storel 0', IR) > 0);
end;

procedure TInheritTests.TestCodegen_Nil_CompareEmitsCeql;
var IR: string;
begin
  IR := GenIR(
    'program P;'               + LineEnding +
    'type'                     + LineEnding +
    '  TFoo = class'           + LineEnding +
    '    X: Integer;'          + LineEnding +
    '  end;'                   + LineEnding +
    'var F: TFoo;'             + LineEnding +
    'var N: Integer;'          + LineEnding +
    'begin'                    + LineEnding +
    '  F := TFoo.Create;'      + LineEnding +
    '  if F = nil then'        + LineEnding +
    '    N := 0'               + LineEnding +
    'end.');
  AssertTrue('ceql for pointer comparison', Pos('ceql', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Self-referential type tests                                         }
{ ------------------------------------------------------------------ }

procedure TInheritTests.TestSemantic_SelfRef_DoesNotRaiseError;
begin
  AnalyseSrc(SrcSelfRef).Free;
end;

procedure TInheritTests.TestSemantic_SelfRef_FieldTypeIsClass;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  CD:   TClassTypeDef;
  FD:   TFieldDecl;
begin
  Prog := AnalyseSrc(SrcSelfRef);
  try
    TD := TTypeDecl(Prog.Block.TypeDecls[0]);
    CD := TClassTypeDef(TD.Def);
    { Second field: Next: TNode }
    FD := TFieldDecl(CD.Fields[1]);
    AssertNotNull('Next field resolved', FD.ResolvedType);
    AssertEquals('Next field is tyClass',
      Ord(tyClass), Ord(FD.ResolvedType.Kind));
  finally Prog.Free; end;
end;

procedure TInheritTests.TestCodegen_SelfRef_Create_AllocatesCorrectSize;
var IR: string;
begin
  IR := GenIR(SrcSelfRef);
  { TNode has Integer (4 bytes) + TNode pointer (8 bytes) = 12 bytes,
    aligned to 8 → 12 bytes total.  _ClassAlloc is called with TotalSize
    plus a pointer to the class's field-cleanup function. }
  AssertTrue('_ClassAlloc 12 bytes for TNode with cleanup fn',
    Pos('call $_ClassAlloc(l 12, l $_FieldCleanup_TNode)', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Inheritance — field tests                                           }
{ ------------------------------------------------------------------ }

procedure TInheritTests.TestSemantic_Inherit_ParentFieldVisible;
begin
  { D.Age := 3 should resolve — Age is inherited from TAnimal }
  AnalyseSrc(SrcInherit).Free;
end;

procedure TInheritTests.TestSemantic_Inherit_ChildFieldVisible;
begin
  { D.Legs := 4 should resolve — Legs is TDog's own field }
  AnalyseSrc(SrcInherit).Free;
end;

procedure TInheritTests.TestSemantic_Inherit_TotalSizeIncludesParent;
var
  Prog:  TProgram;
  Sym:   TSymbol;
  RT:    TRecordTypeDesc;
begin
  Prog := AnalyseSrc(SrcInherit);
  try
    { TAnimal: Age (4 bytes) = 4 total.
      TDog: Age (4) + Legs (4) = 8 total. }
    Sym := Prog.SymbolTable.Lookup('TDog');
    AssertNotNull('TDog symbol', Sym);
    RT := TRecordTypeDesc(Sym.TypeDesc);
    AssertEquals('TDog total size = 8', 8, RT.TotalSize);
  finally Prog.Free; end;
end;

procedure TInheritTests.TestCodegen_Inherit_Create_AllocatesTotalSize;
var IR: string;
begin
  IR := GenIR(SrcInherit);
  { TDog.Create passes TotalSize (8 bytes: Age + Legs) to _ClassAlloc along
    with its per-class field-cleanup function. }
  AssertTrue('_ClassAlloc 8 bytes for TDog with cleanup fn',
    Pos('call $_ClassAlloc(l 8, l $_FieldCleanup_TDog)', IR) > 0);
end;

procedure TInheritTests.TestCodegen_Inherit_ParentFieldOffset;
var IR: string;
begin
  IR := GenIR(SrcInherit);
  { Age is at offset 0 in TDog (first field, inherited).
    storew to the base pointer — no offset add needed. }
  AssertTrue('Age field at offset 0 (storew to base ptr)',
    Pos('storew', IR) > 0);
end;

procedure TInheritTests.TestCodegen_Inherit_ChildFieldOffset;
var IR: string;
begin
  IR := GenIR(SrcInherit);
  { Legs is at offset 4 in TDog — codegen must emit an add 4 }
  AssertTrue('Legs field at offset 4 (add 4)',
    Pos(', 4', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Inheritance — method tests                                          }
{ ------------------------------------------------------------------ }

procedure TInheritTests.TestSemantic_Inherit_MethodCallOnChild_Resolves;
begin
  { C.SetX(10) should resolve even though SetX is defined on TBase }
  AnalyseSrc(SrcInheritMethod).Free;
end;

procedure TInheritTests.TestSemantic_Inherit_UnknownMethod_RaisesError;
begin
  AnalyseExpectError(
    'program P;'                      + LineEnding +
    'type'                            + LineEnding +
    '  TBase = class'                 + LineEnding +
    '    X: Integer;'                 + LineEnding +
    '  end;'                          + LineEnding +
    '  TChild = class(TBase)'         + LineEnding +
    '    Y: Integer;'                 + LineEnding +
    '  end;'                          + LineEnding +
    'var C: TChild;'                  + LineEnding +
    'begin'                           + LineEnding +
    '  C := TChild.Create;'           + LineEnding +
    '  C.NoSuchMethod'                + LineEnding +
    'end.');
end;

procedure TInheritTests.TestCodegen_Inherit_MethodCallUsesParentFunctionName;
var IR: string;
begin
  IR := GenIR(SrcInheritMethod);
  { C.SetX(10) must call $TBase_SetX, not $TChild_SetX }
  AssertTrue('call $TBase_SetX for inherited method',
    Pos('call $TBase_SetX', IR) > 0);
  AssertFalse('no $TChild_SetX emitted',
    Pos('$TChild_SetX', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ 'inherited' keyword tests                                          }
{ ------------------------------------------------------------------ }

const
  SrcInheritedNoArgs =
    'program P;'                      + LineEnding +
    'type'                            + LineEnding +
    '  TBase = class'                 + LineEnding +
    '    X: Integer;'                 + LineEnding +
    '    procedure Init;'             + LineEnding +
    '  end;'                          + LineEnding +
    '  TChild = class(TBase)'         + LineEnding +
    '    Y: Integer;'                 + LineEnding +
    '    procedure Init;'             + LineEnding +
    '  end;'                          + LineEnding +
    'procedure TBase.Init;'           + LineEnding +
    'begin'                           + LineEnding +
    '  Self.X := 0'                   + LineEnding +
    'end;'                            + LineEnding +
    'procedure TChild.Init;'          + LineEnding +
    'begin'                           + LineEnding +
    '  inherited Init;'               + LineEnding +
    '  Self.Y := 0'                   + LineEnding +
    'end;'                            + LineEnding +
    'var C: TChild;'                  + LineEnding +
    'begin'                           + LineEnding +
    '  C := TChild.Create'            + LineEnding +
    'end.';

  SrcInheritedWithArgs =
    'program P;'                      + LineEnding +
    'type'                            + LineEnding +
    '  TBase = class'                 + LineEnding +
    '    X: Integer;'                 + LineEnding +
    '    procedure SetX(V: Integer);' + LineEnding +
    '  end;'                          + LineEnding +
    '  TChild = class(TBase)'         + LineEnding +
    '    procedure SetX(V: Integer);' + LineEnding +
    '  end;'                          + LineEnding +
    'procedure TBase.SetX(V: Integer);' + LineEnding +
    'begin'                           + LineEnding +
    '  Self.X := V'                   + LineEnding +
    'end;'                            + LineEnding +
    'procedure TChild.SetX(V: Integer);' + LineEnding +
    'begin'                           + LineEnding +
    '  inherited SetX(V)'             + LineEnding +
    'end;'                            + LineEnding +
    'var C: TChild;'                  + LineEnding +
    'begin'                           + LineEnding +
    '  C := TChild.Create'            + LineEnding +
    'end.';

procedure TInheritTests.TestLexer_Inherited_IsOwnToken;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('inherited');
  try
    T := L.Next;
    AssertEquals('inherited token kind', Ord(tkInherited), Ord(T.Kind));
  finally L.Free; end;
end;

procedure TInheritTests.TestParse_Inherited_NoArgs_CreatesNode;
var
  Prog:  TProgram;
  MDecl: TMethodDecl;
  Stmt:  TASTStmt;
begin
  Prog := ParseSrc(SrcInheritedNoArgs);
  try
    { TChild.Init is the second standalone proc (ProcDecls[1]) }
    AssertTrue('at least 2 ProcDecls', Prog.Block.ProcDecls.Count >= 2);
    MDecl := TMethodDecl(Prog.Block.ProcDecls[1]);
    AssertNotNull('TChild.Init found', MDecl);
    AssertTrue('body has at least one stmt', MDecl.Body.Stmts.Count >= 1);
    Stmt := TASTStmt(MDecl.Body.Stmts[0]);
    AssertTrue('first stmt is TInheritedCallStmt', Stmt is TInheritedCallStmt);
    AssertEquals('method name is Init',
      'Init', TInheritedCallStmt(Stmt).Name);
  finally Prog.Free; end;
end;

procedure TInheritTests.TestSemantic_Inherited_NoArgs_OK;
begin
  AnalyseSrc(SrcInheritedNoArgs).Free;
end;

procedure TInheritTests.TestSemantic_Inherited_WithArgs_OK;
begin
  AnalyseSrc(SrcInheritedWithArgs).Free;
end;

procedure TInheritTests.TestCodegen_Inherited_NoArgs_CallsParentMethod;
var IR: string;
begin
  IR := GenIR(SrcInheritedNoArgs);
  AssertTrue('call $TBase_Init in IR', Pos('call $TBase_Init', IR) > 0);
end;

procedure TInheritTests.TestCodegen_Inherited_WithArgs_ForwardsArgs;
var IR: string;
begin
  IR := GenIR(SrcInheritedWithArgs);
  AssertTrue('call $TBase_SetX in IR', Pos('call $TBase_SetX', IR) > 0);
end;

initialization
  RegisterTest(TInheritTests);

end.
