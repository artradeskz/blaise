{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.classof;

{$mode objfpc}{$H+}

{ Tests for 'class of TFoo' metaclass type support — Step 11a. }

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TClassOfTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { Parser }
    procedure TestParse_ClassOf_AsAlias;
    procedure TestParse_ClassOf_VarDecl;
    procedure TestParse_ClassOf_FieldType;

    { Semantic }
    procedure TestSemantic_ClassOf_TypeIsMetaClass;
    procedure TestSemantic_ClassOf_BaseClass;
    procedure TestSemantic_AssignClassIdent_ToMetaClass;
    procedure TestSemantic_AssignDescendant_ToBaseMetaClass;
    procedure TestSemantic_RejectUnrelatedClass_ToMetaClass;
    procedure TestSemantic_RejectClassOf_Nonclass;
    procedure TestSemantic_MetaClass_AcceptedAsPointerArg;
    procedure TestSemantic_CompareTwoMetaClassValues;

    { Codegen }
    procedure TestCodegen_ClassIdent_EmitsTypeinfo;
    procedure TestCodegen_MetaClassVar_StorelTypeinfo;
    procedure TestCodegen_MetaClassEquality_UsesCEQL;

    { ClassCreate builtin (Step 11e): runtime construction via a
      metaclass value.  Lowers to '_ClassCreate(Cls)' followed by a
      static call to the resolved constructor. }
    procedure TestSemantic_ClassCreate_RejectsNonMetaclassFirstArg;
    procedure TestCodegen_ClassCreate_EmitsAllocAndCtorCall;
    procedure TestCodegen_ClassCreate_NoCtor_OnlyAllocCalled;
  end;

implementation

function TClassOfTests.ParseSrc(const ASrc: string): TProgram;
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

function TClassOfTests.AnalyseSrc(const ASrc: string): TProgram;
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

function TClassOfTests.GenIR(const ASrc: string): string;
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

procedure TClassOfTests.AnalyseExpectError(const ASrc: string);
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
{  Parser                                                             }
{ ------------------------------------------------------------------ }

procedure TClassOfTests.TestParse_ClassOf_AsAlias;
const
  Src =
    'program P;'                             + LineEnding +
    'type'                                   + LineEnding +
    '  TBase = class(TObject) end;'          + LineEnding +
    '  TBaseClass = class of TBase;'         + LineEnding +
    'begin end.';
var Prog: TProgram;
begin
  Prog := ParseSrc(Src);
  try
    AssertEquals('two type decls', 2, Prog.Block.TypeDecls.Count);
  finally
    Prog.Free;
  end;
end;

procedure TClassOfTests.TestParse_ClassOf_VarDecl;
const
  Src =
    'program P;'                             + LineEnding +
    'type'                                   + LineEnding +
    '  TBase = class(TObject) end;'          + LineEnding +
    'var C: class of TBase;'                 + LineEnding +
    'begin end.';
var Prog: TProgram;
begin
  Prog := ParseSrc(Src);
  try
    AssertEquals('one var decl', 1, Prog.Block.Decls.Count);
  finally
    Prog.Free;
  end;
end;

procedure TClassOfTests.TestParse_ClassOf_FieldType;
const
  Src =
    'program P;'                             + LineEnding +
    'type'                                   + LineEnding +
    '  TBase = class(TObject) end;'          + LineEnding +
    '  TWrap = class(TObject)'               + LineEnding +
    '    Cls: class of TBase;'               + LineEnding +
    '  end;'                                 + LineEnding +
    'begin end.';
var Prog: TProgram;
begin
  Prog := ParseSrc(Src);
  try
    AssertEquals('two type decls', 2, Prog.Block.TypeDecls.Count);
  finally
    Prog.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{  Semantic                                                            }
{ ------------------------------------------------------------------ }

procedure TClassOfTests.TestSemantic_ClassOf_TypeIsMetaClass;
const
  Src =
    'program P;'                             + LineEnding +
    'type'                                   + LineEnding +
    '  TBase = class(TObject) end;'          + LineEnding +
    'var C: class of TBase;'                 + LineEnding +
    'begin end.';
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := AnalyseSrc(Src);
  try
    VD := TVarDecl(Prog.Block.Decls.Items[0]);
    AssertEquals('var type kind is tyMetaClass',
      Ord(tyMetaClass), Ord(VD.ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TClassOfTests.TestSemantic_ClassOf_BaseClass;
const
  Src =
    'program P;'                             + LineEnding +
    'type'                                   + LineEnding +
    '  TBase = class(TObject) end;'          + LineEnding +
    'var C: class of TBase;'                 + LineEnding +
    'begin end.';
var
  Prog: TProgram;
  VD:   TVarDecl;
  MC:   TMetaClassTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    VD := TVarDecl(Prog.Block.Decls.Items[0]);
    MC := TMetaClassTypeDesc(VD.ResolvedType);
    AssertNotNull('metaclass has BaseClass', MC.BaseClass);
    AssertEquals('BaseClass is TBase', 'TBase', MC.BaseClass.Name);
  finally
    Prog.Free;
  end;
end;

procedure TClassOfTests.TestSemantic_AssignClassIdent_ToMetaClass;
const
  Src =
    'program P;'                             + LineEnding +
    'type'                                   + LineEnding +
    '  TBase = class(TObject) end;'          + LineEnding +
    'var C: class of TBase;'                 + LineEnding +
    'begin'                                  + LineEnding +
    '  C := TBase'                           + LineEnding +
    'end.';
var Prog: TProgram;
begin
  { Should analyse without error. }
  Prog := AnalyseSrc(Src);
  try
    AssertEquals('one stmt', 1, Prog.Block.Stmts.Count);
  finally
    Prog.Free;
  end;
end;

procedure TClassOfTests.TestSemantic_AssignDescendant_ToBaseMetaClass;
const
  Src =
    'program P;'                             + LineEnding +
    'type'                                   + LineEnding +
    '  TBase    = class(TObject) end;'       + LineEnding +
    '  TDerived = class(TBase) end;'         + LineEnding +
    'var C: class of TBase;'                 + LineEnding +
    'begin'                                  + LineEnding +
    '  C := TDerived'                        + LineEnding +
    'end.';
var Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertEquals('one stmt', 1, Prog.Block.Stmts.Count);
  finally
    Prog.Free;
  end;
end;

procedure TClassOfTests.TestSemantic_RejectUnrelatedClass_ToMetaClass;
const
  Src =
    'program P;'                             + LineEnding +
    'type'                                   + LineEnding +
    '  TBase  = class(TObject) end;'         + LineEnding +
    '  TOther = class(TObject) end;'         + LineEnding +
    'var C: class of TBase;'                 + LineEnding +
    'begin'                                  + LineEnding +
    '  C := TOther'                          + LineEnding +
    'end.';
begin
  AnalyseExpectError(Src);
end;

procedure TClassOfTests.TestSemantic_RejectClassOf_Nonclass;
const
  Src =
    'program P;'                             + LineEnding +
    'type'                                   + LineEnding +
    '  TInt = class of Integer;'             + LineEnding +
    'begin end.';
begin
  AnalyseExpectError(Src);
end;

procedure TClassOfTests.TestSemantic_MetaClass_AcceptedAsPointerArg;
const
  Src =
    'program P;'                             + LineEnding +
    'type'                                   + LineEnding +
    '  TBase = class(TObject) end;'          + LineEnding +
    'procedure Take(const P: Pointer);'      + LineEnding +
    'begin end;'                             + LineEnding +
    'begin'                                  + LineEnding +
    '  Take(TBase)'                          + LineEnding +
    'end.';
var Prog: TProgram;
begin
  { A metaclass-typed value passes through an untyped Pointer arg. }
  Prog := AnalyseSrc(Src);
  try
    AssertEquals('one stmt', 1, Prog.Block.Stmts.Count);
  finally
    Prog.Free;
  end;
end;

procedure TClassOfTests.TestSemantic_CompareTwoMetaClassValues;
const
  Src =
    'program P;'                             + LineEnding +
    'type'                                   + LineEnding +
    '  TBase    = class(TObject) end;'       + LineEnding +
    '  TDerived = class(TBase) end;'         + LineEnding +
    'var B: Boolean;'                        + LineEnding +
    'begin'                                  + LineEnding +
    '  B := TBase = TDerived'                + LineEnding +
    'end.';
var Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertEquals('one stmt', 1, Prog.Block.Stmts.Count);
  finally
    Prog.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{  Codegen                                                             }
{ ------------------------------------------------------------------ }

procedure TClassOfTests.TestCodegen_ClassIdent_EmitsTypeinfo;
const
  Src =
    'program P;'                             + LineEnding +
    'type'                                   + LineEnding +
    '  TBase = class(TObject) end;'          + LineEnding +
    'var C: class of TBase;'                 + LineEnding +
    'begin'                                  + LineEnding +
    '  C := TBase'                           + LineEnding +
    'end.';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('IR copies $typeinfo_TBase into a temp',
    Pos('copy $typeinfo_TBase', IR) > 0);
end;

procedure TClassOfTests.TestCodegen_MetaClassVar_StorelTypeinfo;
const
  Src =
    'program P;'                             + LineEnding +
    'type'                                   + LineEnding +
    '  TBase = class(TObject) end;'          + LineEnding +
    'var C: class of TBase;'                 + LineEnding +
    'begin'                                  + LineEnding +
    '  C := TBase'                           + LineEnding +
    'end.';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('storel into the metaclass var slot',
    Pos('storel', IR) > 0);
  { Program-level vars are emitted as global data, not stack slots. }
  AssertTrue('var C is emitted as 8-byte global pointer slot',
    Pos('export data $C = { l 0 }', IR) > 0);
end;

procedure TClassOfTests.TestCodegen_MetaClassEquality_UsesCEQL;
const
  Src =
    'program P;'                             + LineEnding +
    'type'                                   + LineEnding +
    '  TBase = class(TObject) end;'          + LineEnding +
    'var B: Boolean;'                        + LineEnding +
    'begin'                                  + LineEnding +
    '  B := TBase = TBase'                   + LineEnding +
    'end.';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('metaclass equality uses ceql (pointer compare), not ceqw',
    Pos('ceql', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ ClassCreate builtin                                                  }
{ ------------------------------------------------------------------ }

procedure TClassOfTests.TestSemantic_ClassCreate_RejectsNonMetaclassFirstArg;
begin
  AnalyseExpectError(
    'program P;'                                       + LineEnding +
    'type TFoo = class(TObject) end;'                  + LineEnding +
    'var F: TFoo;'                                     + LineEnding +
    'begin'                                            + LineEnding +
    '  F := ClassCreate(F)'                            + LineEnding +
    'end.'
  );
end;

procedure TClassOfTests.TestCodegen_ClassCreate_EmitsAllocAndCtorCall;
const
  Src =
    'program P;'                                       + LineEnding +
    'type'                                             + LineEnding +
    '  TFoo = class(TObject)'                          + LineEnding +
    '    Value: Integer;'                              + LineEnding +
    '    constructor Create(N: Integer);'              + LineEnding +
    '  end;'                                           + LineEnding +
    'constructor TFoo.Create(N: Integer);'             + LineEnding +
    'begin Self.Value := N end;'                       + LineEnding +
    'var C: class of TFoo; F: TFoo;'                   + LineEnding +
    'begin'                                            + LineEnding +
    '  C := TFoo;'                                     + LineEnding +
    '  F := ClassCreate(C, 7)'                         + LineEnding +
    'end.';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('emits call to $_ClassCreate', Pos('call $_ClassCreate(', IR) > 0);
  AssertTrue('emits static call to TFoo_Create after alloc',
    Pos('call $TFoo_Create(', IR) > 0);
end;

procedure TClassOfTests.TestCodegen_ClassCreate_NoCtor_OnlyAllocCalled;
const
  Src =
    'program P;'                                       + LineEnding +
    'type TFoo = class(TObject) end;'                  + LineEnding +
    'var C: class of TFoo; F: TFoo;'                   + LineEnding +
    'begin'                                            + LineEnding +
    '  C := TFoo;'                                     + LineEnding +
    '  F := ClassCreate(C)'                            + LineEnding +
    'end.';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('emits call to $_ClassCreate', Pos('call $_ClassCreate(', IR) > 0);
  AssertEquals('no constructor call emitted when class declares none',
    0, Pos('TFoo_Create', IR));
end;

initialization
  RegisterTest(TClassOfTests);
end.
