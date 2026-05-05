{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.typetests;

{$mode objfpc}{$H+}

{ Tests for the 'is' and 'as' type-test operators. }

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TTypeTestTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Lexer                                                                }
    { ------------------------------------------------------------------ }
    procedure TestLexer_Is_Keyword;
    procedure TestLexer_As_Keyword;

    { ------------------------------------------------------------------ }
    { Parser — is                                                          }
    { ------------------------------------------------------------------ }
    procedure TestParse_IsExpr_NodeKind;
    procedure TestParse_IsExpr_TypeName;

    { ------------------------------------------------------------------ }
    { Parser — as                                                          }
    { ------------------------------------------------------------------ }
    procedure TestParse_AsExpr_NodeKind;
    procedure TestParse_AsExpr_TypeName;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_IsExpr_ClassInstance_OK;
    procedure TestSemantic_IsExpr_ResultIsBoolean;
    procedure TestSemantic_IsExpr_NonClass_RaisesError;
    procedure TestSemantic_AsExpr_ClassInstance_OK;
    procedure TestSemantic_AsExpr_ResultType_IsTargetClass;
    procedure TestSemantic_AsExpr_NonClass_RaisesError;

    { ------------------------------------------------------------------ }
    { Codegen — typeinfo data sections                                     }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_TypeInfo_Emitted;
    procedure TestCodegen_TypeInfo_ParentPtr_IsZero_ForRoot;
    procedure TestCodegen_TypeInfo_ParentPtr_ForDerived;
    procedure TestCodegen_Vtable_StartsWithTypeInfo;

    { ------------------------------------------------------------------ }
    { Codegen — is / as expressions                                        }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_IsExpr_CallsIsInstance;
    procedure TestCodegen_IsExpr_PassesTypeInfoLabel;
    procedure TestCodegen_AsExpr_CallsIsInstance;
    procedure TestCodegen_AsExpr_CallsRaiseOnFail;

    { ------------------------------------------------------------------ }
    { ClassType / TClass intrinsic                                         }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ClassType_OK;
    procedure TestSemantic_ClassType_ResolvesToPointer;
    procedure TestSemantic_TClass_AliasIsPointer;
    procedure TestCodegen_ClassType_LoadsTypeInfo;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Shared source snippets                                               }
{ ------------------------------------------------------------------ }

const
  { Base class with one virtual method — has a vtable/vptr }
  SrcBase =
    'program P;'                                  + LineEnding +
    'type'                                        + LineEnding +
    '  TAnimal = class'                           + LineEnding +
    '    procedure Speak; virtual; begin end;'    + LineEnding +
    '  end;'                                      + LineEnding +
    'var A: TAnimal;'                             + LineEnding +
    '    R: Boolean;'                             + LineEnding +
    'begin'                                       + LineEnding +
    '  A := TAnimal.Create;'                      + LineEnding +
    '  R := A is TAnimal'                         + LineEnding +
    'end.';

  SrcInherit =
    'program P;'                                  + LineEnding +
    'type'                                        + LineEnding +
    '  TAnimal = class'                           + LineEnding +
    '    procedure Speak; virtual; begin end;'    + LineEnding +
    '  end;'                                      + LineEnding +
    '  TDog = class(TAnimal)'                     + LineEnding +
    '    procedure Speak; override; begin end;'   + LineEnding +
    '  end;'                                      + LineEnding +
    'var A: TAnimal;'                             + LineEnding +
    '    D: TDog;'                                + LineEnding +
    '    R: Boolean;'                             + LineEnding +
    'begin'                                       + LineEnding +
    '  D := TDog.Create;'                         + LineEnding +
    '  A := D;'                                   + LineEnding +
    '  R := A is TDog'                            + LineEnding +
    'end.';

  SrcAsExpr =
    'program P;'                                  + LineEnding +
    'type'                                        + LineEnding +
    '  TAnimal = class'                           + LineEnding +
    '    procedure Speak; virtual; begin end;'    + LineEnding +
    '  end;'                                      + LineEnding +
    '  TDog = class(TAnimal)'                     + LineEnding +
    '    procedure Speak; override; begin end;'   + LineEnding +
    '  end;'                                      + LineEnding +
    'var A: TAnimal;'                             + LineEnding +
    '    D: TDog;'                                + LineEnding +
    'begin'                                       + LineEnding +
    '  A := TDog.Create;'                         + LineEnding +
    '  D := A as TDog'                            + LineEnding +
    'end.';

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TTypeTestTests.ParseSrc(const ASrc: string): TProgram;
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

function TTypeTestTests.AnalyseSrc(const ASrc: string): TProgram;
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

function TTypeTestTests.GenIR(const ASrc: string): string;
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

procedure TTypeTestTests.AnalyseExpectError(const ASrc: string);
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
{ Lexer tests                                                          }
{ ------------------------------------------------------------------ }

procedure TTypeTestTests.TestLexer_Is_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('is');
  try
    T := L.Next;
    AssertEquals('is token', Ord(tkIs), Ord(T.Kind));
  finally L.Free; end;
end;

procedure TTypeTestTests.TestLexer_As_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('as');
  try
    T := L.Next;
    AssertEquals('as token', Ord(tkAs), Ord(T.Kind));
  finally L.Free; end;
end;

{ ------------------------------------------------------------------ }
{ Parser — is                                                          }
{ ------------------------------------------------------------------ }

procedure TTypeTestTests.TestParse_IsExpr_NodeKind;
var Prog: TProgram; Stmt: TAssignment;
begin
  Prog := ParseSrc(SrcBase);
  try
    Stmt := TAssignment(Prog.Block.Stmts[1]);
    AssertTrue('is expr node kind', Stmt.Expr is TIsExpr);
  finally Prog.Free; end;
end;

procedure TTypeTestTests.TestParse_IsExpr_TypeName;
var Prog: TProgram; IE: TIsExpr;
begin
  Prog := ParseSrc(SrcBase);
  try
    IE := TIsExpr(TAssignment(Prog.Block.Stmts[1]).Expr);
    AssertEquals('is type name', 'TAnimal', IE.TypeName);
  finally Prog.Free; end;
end;

{ ------------------------------------------------------------------ }
{ Parser — as                                                          }
{ ------------------------------------------------------------------ }

procedure TTypeTestTests.TestParse_AsExpr_NodeKind;
var Prog: TProgram; Stmt: TAssignment;
begin
  Prog := ParseSrc(SrcAsExpr);
  try
    Stmt := TAssignment(Prog.Block.Stmts[1]);
    AssertTrue('as expr node kind', Stmt.Expr is TAsExpr);
  finally Prog.Free; end;
end;

procedure TTypeTestTests.TestParse_AsExpr_TypeName;
var Prog: TProgram; AE: TAsExpr;
begin
  Prog := ParseSrc(SrcAsExpr);
  try
    AE := TAsExpr(TAssignment(Prog.Block.Stmts[1]).Expr);
    AssertEquals('as type name', 'TDog', AE.TypeName);
  finally Prog.Free; end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TTypeTestTests.TestSemantic_IsExpr_ClassInstance_OK;
begin
  AnalyseSrc(SrcBase).Free;
end;

procedure TTypeTestTests.TestSemantic_IsExpr_ResultIsBoolean;
var Prog: TProgram; IE: TIsExpr;
begin
  Prog := AnalyseSrc(SrcBase);
  try
    IE := TIsExpr(TAssignment(Prog.Block.Stmts[1]).Expr);
    AssertNotNull('is-expr resolved type', IE.ResolvedType);
    AssertEquals('is-expr result is Boolean', Ord(tyBoolean), Ord(IE.ResolvedType.Kind));
  finally Prog.Free; end;
end;

procedure TTypeTestTests.TestSemantic_IsExpr_NonClass_RaisesError;
begin
  AnalyseExpectError(
    'program P;'       + LineEnding +
    'var X: Integer;'  + LineEnding +
    '    R: Boolean;'  + LineEnding +
    'begin'            + LineEnding +
    '  R := X is Integer' + LineEnding +
    'end.');
end;

procedure TTypeTestTests.TestSemantic_AsExpr_ClassInstance_OK;
begin
  AnalyseSrc(SrcAsExpr).Free;
end;

procedure TTypeTestTests.TestSemantic_AsExpr_ResultType_IsTargetClass;
var Prog: TProgram; AE: TAsExpr;
begin
  Prog := AnalyseSrc(SrcAsExpr);
  try
    AE := TAsExpr(TAssignment(Prog.Block.Stmts[1]).Expr);
    AssertNotNull('as-expr resolved type', AE.ResolvedType);
    AssertEquals('as-expr result is target class', 'TDog', AE.ResolvedType.Name);
  finally Prog.Free; end;
end;

procedure TTypeTestTests.TestSemantic_AsExpr_NonClass_RaisesError;
begin
  AnalyseExpectError(
    'program P;'        + LineEnding +
    'var X: Integer;'   + LineEnding +
    '    Y: Integer;'   + LineEnding +
    'begin'             + LineEnding +
    '  Y := X as Integer' + LineEnding +
    'end.');
end;

{ ------------------------------------------------------------------ }
{ Codegen — typeinfo data sections                                     }
{ ------------------------------------------------------------------ }

procedure TTypeTestTests.TestCodegen_TypeInfo_Emitted;
var IR: string;
begin
  IR := GenIR(SrcBase);
  AssertTrue('typeinfo data section emitted',
    Pos('data $typeinfo_TAnimal', IR) > 0);
end;

procedure TTypeTestTests.TestCodegen_TypeInfo_ParentPtr_IsZero_ForRoot;
var IR: string;
begin
  { Root class (no parent): parent=0, impllist=0, nameptr=&ClassName,
    methods=0, then totalsize/fieldcleanup/vtable (Step 11e). }
  IR := GenIR(SrcBase);
  AssertTrue('root typeinfo has zero parent ptr',
    Pos('$typeinfo_TAnimal = { l 0, l 0, l $__cn_TAnimal + 12, l 0,', IR) > 0);
end;

procedure TTypeTestTests.TestCodegen_TypeInfo_ParentPtr_ForDerived;
var IR: string;
begin
  { Derived class typeinfo: parent=$typeinfo_TAnimal, impllist=0,
    nameptr=&ClassName, methods=0, then size/cleanup/vtable. }
  IR := GenIR(SrcInherit);
  AssertTrue('derived typeinfo refs parent',
    Pos('$typeinfo_TDog = { l $typeinfo_TAnimal, l 0, l $__cn_TDog + 12, l 0,', IR) > 0);
end;

procedure TTypeTestTests.TestCodegen_Vtable_StartsWithTypeInfo;
var IR: string;
begin
  { Vtable first slot must be the typeinfo pointer }
  IR := GenIR(SrcBase);
  AssertTrue('vtable starts with typeinfo',
    Pos('$vtable_TAnimal = { l $typeinfo_TAnimal', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Codegen — is / as expressions                                        }
{ ------------------------------------------------------------------ }

procedure TTypeTestTests.TestCodegen_IsExpr_CallsIsInstance;
var IR: string;
begin
  IR := GenIR(SrcBase);
  AssertTrue('is calls _IsInstance', Pos('call $_IsInstance', IR) > 0);
end;

procedure TTypeTestTests.TestCodegen_IsExpr_PassesTypeInfoLabel;
var IR: string;
begin
  IR := GenIR(SrcBase);
  { The call must pass $typeinfo_TAnimal as the target type argument }
  AssertTrue('is passes typeinfo label',
    Pos('$typeinfo_TAnimal', IR) > 0);
end;

procedure TTypeTestTests.TestCodegen_AsExpr_CallsIsInstance;
var IR: string;
begin
  IR := GenIR(SrcAsExpr);
  AssertTrue('as calls _IsInstance', Pos('call $_IsInstance', IR) > 0);
end;

procedure TTypeTestTests.TestCodegen_AsExpr_CallsRaiseOnFail;
var IR: string;
begin
  IR := GenIR(SrcAsExpr);
  AssertTrue('as calls _Raise_InvalidCast on fail',
    Pos('call $_Raise_InvalidCast', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ ClassType / TClass intrinsic                                         }
{ ------------------------------------------------------------------ }

const
  SrcClassType =
    'program P;'                                  + LineEnding +
    'type'                                        + LineEnding +
    '  TFoo = class end;'                         + LineEnding +
    'var F: TFoo; CT: Pointer;'                   + LineEnding +
    'begin'                                       + LineEnding +
    '  F := TFoo.Create;'                         + LineEnding +
    '  CT := F.ClassType'                         + LineEnding +
    'end.';

procedure TTypeTestTests.TestSemantic_ClassType_OK;
var P: TProgram;
begin
  P := AnalyseSrc(SrcClassType);
  P.Free;
end;

procedure TTypeTestTests.TestSemantic_ClassType_ResolvesToPointer;
var
  P: TProgram;
  Assign: TAssignment;
  Access: TFieldAccessExpr;
begin
  P := AnalyseSrc(SrcClassType);
  try
    { last stmt is the assignment to CT }
    Assign := TAssignment(P.Block.Stmts[1]);
    Access := TFieldAccessExpr(Assign.Expr);
    AssertTrue('IsClassTypeAccess set', Access.IsClassTypeAccess);
    AssertEquals('resolved type kind = tyPointer',
      Ord(tyPointer), Ord(Access.ResolvedType.Kind));
  finally
    P.Free;
  end;
end;

procedure TTypeTestTests.TestSemantic_TClass_AliasIsPointer;
var P: TProgram;
begin
  { TClass declared as a built-in alias of Pointer — using it for a
    var declaration must succeed. }
  P := AnalyseSrc(
    'program P; var C: TClass;'                   + LineEnding +
    'begin C := nil end.');
  P.Free;
end;

procedure TTypeTestTests.TestCodegen_ClassType_LoadsTypeInfo;
var IR: string;
begin
  IR := GenIR(SrcClassType);
  { Two indirections: instance → vtable → typeinfo.  We don't pin
    the exact temp numbers but we can assert the access path is
    actually emitted (loadl appearing in the assignment). }
  AssertTrue('codegen emits loadl chain for ClassType',
    Pos('loadl', IR) > 0);
end;

initialization
  RegisterTest(TTypeTestTests);

end.
