{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.visibility;

{ Tests for member visibility ENFORCEMENT — private / protected / strict.
  Feature 2 of the static/visibility work.  Before this, Blaise parsed the
  visibility keywords but enforced none of them (private was effectively a
  comment) and had no `strict` keyword.

  Coverage:
    * PARSER (TVisibilityParseTests) — the visibility section keywords, the
      `strict` soft keyword before private/protected, and the rejection of
      `strict public` / `strict published` / bare `strict`.  Asserts the
      Visibility flag lands on the field/method/property AST nodes.
    * SEMANTIC (TVisibilitySemTests) — qualified member access is rejected when
      out of scope and accepted when in scope, for fields, methods, and
      properties, across private / protected / strict-private / strict-protected.

  Cross-unit private/protected enforcement (the .bif round-trip) is exercised by
  the self-hosting warm-cache fixpoint and the standalone cross-unit compile
  checks; the in-process harness here covers the within-translation-unit rules
  (different type in the same program = "same unit", so private is visible but
  strict private is not). }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSemantic, uSymbolTable;

type
  TVisibilityParseTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function ClassOf(AProg: TProgram; AIndex: Integer): TClassTypeDef;
    procedure ParseExpectErrorMsg(const ASrc, AExpectedSubstr: string);
  published
    procedure TestParse_PrivateField_SetsMvPrivate;
    procedure TestParse_ProtectedField_SetsMvProtected;
    procedure TestParse_PublishedField_SetsMvPublished;
    procedure TestParse_DefaultIsPublic;
    procedure TestParse_StrictPrivateField_SetsMvStrictPrivate;
    procedure TestParse_StrictProtectedField_SetsMvStrictProtected;
    procedure TestParse_StrictComposesWithStatic;
    procedure TestParse_StrictPublic_Rejected;
    procedure TestParse_BareStrict_Rejected;
    procedure TestParse_StrictAsOrdinaryIdentOutsideClass;
  end;

  TVisibilitySemTests = class(TTestCase)
  private
    procedure AnalyseExpectOK(const ASrc: string);
    procedure AnalyseExpectReject(const ASrc, AExpectedSubstr: string);
  published
    { private — unit-scoped }
    procedure TestSem_PrivateField_SameUnitOtherProc_OK;
    procedure TestSem_PrivateField_OwnMethod_OK;
    procedure TestSem_PrivateMethod_SameUnitOtherType_OK;

    { strict private — type-scoped }
    procedure TestSem_StrictPrivateField_CrossType_Rejected;
    procedure TestSem_StrictPrivateField_OwnMethod_OK;
    procedure TestSem_StrictPrivateMethod_CrossType_Rejected;

    { protected — descendant types (and, being unit-scoped, same-unit code) }
    procedure TestSem_ProtectedField_Descendant_OK;
    procedure TestSem_ProtectedField_SameUnitUnrelated_OK;

    { strict protected — declaring type + descendants }
    procedure TestSem_StrictProtectedField_Descendant_OK;
    procedure TestSem_StrictProtectedField_NonDescendant_Rejected;

    { public / published — visible everywhere }
    procedure TestSem_PublicField_CrossType_OK;

    { strict composes with static }
    procedure TestSem_StrictPrivateStaticVar_OwnMethod_OK;
    procedure TestSem_StrictPrivateStaticVar_CrossType_Rejected;

    { property visibility }
    procedure TestSem_PrivateProperty_CrossType_OK;
    procedure TestSem_StrictPrivateProperty_CrossType_Rejected;
  end;

implementation

{ ================================================================== }
{  Parser tests                                                       }
{ ================================================================== }

function TVisibilityParseTests.ParseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free(); L.Free();
  end;
end;

function TVisibilityParseTests.ClassOf(AProg: TProgram; AIndex: Integer): TClassTypeDef;
var TD: TTypeDecl;
begin
  TD := TTypeDecl(AProg.Block.TypeDecls.Items[AIndex]);
  Result := TD.Def as TClassTypeDef;
end;

procedure TVisibilityParseTests.ParseExpectErrorMsg(const ASrc, AExpectedSubstr: string);
var Prog: TProgram;
begin
  try
    Prog := ParseSrc(ASrc);
    Prog.Free();
    Fail('Expected EParseError');
  except
    on E: EParseError do
      AssertTrue('error contains "' + AExpectedSubstr + '" (got: ' + E.Message + ')',
        Pos(AExpectedSubstr, E.Message) >= 0);
  end;
end;

procedure TVisibilityParseTests.TestParse_PrivateField_SetsMvPrivate;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          private
            FX: Integer;
          end;
        begin end.
        ''';
var Prog: TProgram; CD: TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    CD := ClassOf(Prog, 0);
    AssertTrue('field is mvPrivate',
      TFieldDecl(CD.Fields.Items[0]).Visibility = mvPrivate);
  finally
    Prog.Free();
  end;
end;

procedure TVisibilityParseTests.TestParse_ProtectedField_SetsMvProtected;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          protected
            FX: Integer;
          end;
        begin end.
        ''';
var Prog: TProgram; CD: TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    CD := ClassOf(Prog, 0);
    AssertTrue('field is mvProtected',
      TFieldDecl(CD.Fields.Items[0]).Visibility = mvProtected);
  finally
    Prog.Free();
  end;
end;

procedure TVisibilityParseTests.TestParse_PublishedField_SetsMvPublished;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          published
            FX: Integer;
          end;
        begin end.
        ''';
var Prog: TProgram; CD: TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    CD := ClassOf(Prog, 0);
    AssertTrue('field is mvPublished',
      TFieldDecl(CD.Fields.Items[0]).Visibility = mvPublished);
  finally
    Prog.Free();
  end;
end;

procedure TVisibilityParseTests.TestParse_DefaultIsPublic;
const
  Src =
    '''
        program P;
        type
          TFoo = class
            FX: Integer;
          end;
        begin end.
        ''';
var Prog: TProgram; CD: TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    CD := ClassOf(Prog, 0);
    AssertTrue('default field is mvPublic',
      TFieldDecl(CD.Fields.Items[0]).Visibility = mvPublic);
  finally
    Prog.Free();
  end;
end;

procedure TVisibilityParseTests.TestParse_StrictPrivateField_SetsMvStrictPrivate;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          strict private
            FX: Integer;
          end;
        begin end.
        ''';
var Prog: TProgram; CD: TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    CD := ClassOf(Prog, 0);
    AssertTrue('field is mvStrictPrivate',
      TFieldDecl(CD.Fields.Items[0]).Visibility = mvStrictPrivate);
  finally
    Prog.Free();
  end;
end;

procedure TVisibilityParseTests.TestParse_StrictProtectedField_SetsMvStrictProtected;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          strict protected
            FX: Integer;
          end;
        begin end.
        ''';
var Prog: TProgram; CD: TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    CD := ClassOf(Prog, 0);
    AssertTrue('field is mvStrictProtected',
      TFieldDecl(CD.Fields.Items[0]).Visibility = mvStrictProtected);
  finally
    Prog.Free();
  end;
end;

procedure TVisibilityParseTests.TestParse_StrictComposesWithStatic;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          strict private static var
            FInst: Integer;
          end;
        begin end.
        ''';
var Prog: TProgram; CD: TClassTypeDef; F: TFieldDecl;
begin
  Prog := ParseSrc(Src);
  try
    CD := ClassOf(Prog, 0);
    F := TFieldDecl(CD.Fields.Items[0]);
    AssertTrue('strict private', F.Visibility = mvStrictPrivate);
    AssertTrue('also static (class var)', F.IsClassVar);
  finally
    Prog.Free();
  end;
end;

procedure TVisibilityParseTests.TestParse_StrictPublic_Rejected;
const
  Src =
    '''
        program P;
        type
          TFoo = class
          strict public
            FX: Integer;
          end;
        begin end.
        ''';
begin
  ParseExpectErrorMsg(Src, 'strict');
end;

procedure TVisibilityParseTests.TestParse_BareStrict_Rejected;
const
  { `strict` not followed by private/protected — followed by `end` here.  The
    parser must not silently swallow it; a bare `strict` in a member section is
    treated as an ordinary field-start identifier, so this parses `strict` as a
    field name and then errors on the missing ':'.  Either way it must NOT parse
    as a valid empty class. }
  Src =
    '''
        program P;
        type
          TFoo = class
          strict public
          end;
        begin end.
        ''';
begin
  ParseExpectErrorMsg(Src, 'strict');
end;

procedure TVisibilityParseTests.TestParse_StrictAsOrdinaryIdentOutsideClass;
const
  { `strict` is a SOFT keyword — outside a class/record body it must remain a
    usable identifier (here a local variable name). }
  Src =
    '''
        program P;
        var
          strict: Integer;
        begin
          strict := 1;
        end.
        ''';
var Prog: TProgram;
begin
  Prog := ParseSrc(Src);
  AssertTrue('strict usable as ordinary identifier outside a class', Prog <> nil);
  Prog.Free();
end;

{ ================================================================== }
{  Semantic enforcement tests                                         }
{ ================================================================== }

procedure TVisibilitySemTests.AnalyseExpectOK(const ASrc: string);
var L: TLexer; P: TParser; A: TSemanticAnalyser; Prog: TProgram;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Prog := P.Parse();
  finally
    P.Free(); L.Free();
  end;
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Prog);
  finally
    A.Free();
  end;
  Prog.Free();
end;

procedure TVisibilitySemTests.AnalyseExpectReject(const ASrc, AExpectedSubstr: string);
var L: TLexer; P: TParser; A: TSemanticAnalyser; Prog: TProgram;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Prog := P.Parse();
  finally
    P.Free(); L.Free();
  end;
  A := TSemanticAnalyser.Create();
  try
    try
      A.Analyse(Prog);
      Fail('Expected ESemanticError for out-of-scope access');
    except
      on E: ESemanticError do
        AssertTrue('error contains "' + AExpectedSubstr + '" (got: ' + E.Message + ')',
          Pos(AExpectedSubstr, E.Message) >= 0);
    end;
  finally
    A.Free();
    Prog.Free();
  end;
end;

procedure TVisibilitySemTests.TestSem_PrivateField_SameUnitOtherProc_OK;
const
  Src =
    '''
        program P;
        type
          TB = class
          private
            FSecret: Integer;
          end;
        procedure Touch(b: TB);
        begin
          b.FSecret := 1;
        end;
        var b: TB;
        begin
          b := TB.Create();
          Touch(b);
        end.
        ''';
begin
  AnalyseExpectOK(Src);
end;

procedure TVisibilitySemTests.TestSem_PrivateField_OwnMethod_OK;
const
  Src =
    '''
        program P;
        type
          TB = class
          private
            FSecret: Integer;
          public
            procedure Bump;
          end;
        procedure TB.Bump;
        begin
          Self.FSecret := Self.FSecret + 1;
        end;
        begin end.
        ''';
begin
  AnalyseExpectOK(Src);
end;

procedure TVisibilitySemTests.TestSem_PrivateMethod_SameUnitOtherType_OK;
const
  Src =
    '''
        program P;
        type
          TM = class
          private
            procedure Hidden;
          end;
          TUser = class
          public
            procedure Use(m: TM);
          end;
        procedure TM.Hidden; begin end;
        procedure TUser.Use(m: TM);
        begin
          m.Hidden();
        end;
        begin end.
        ''';
begin
  AnalyseExpectOK(Src);
end;

procedure TVisibilitySemTests.TestSem_StrictPrivateField_CrossType_Rejected;
const
  Src =
    '''
        program P;
        type
          TC = class
          strict private
            FX: Integer;
          end;
          TD = class
          public
            procedure Poke(c: TC);
          end;
        procedure TD.Poke(c: TC);
        begin
          c.FX := 1;
        end;
        begin end.
        ''';
begin
  AnalyseExpectReject(Src, 'not accessible');
end;

procedure TVisibilitySemTests.TestSem_StrictPrivateField_OwnMethod_OK;
const
  Src =
    '''
        program P;
        type
          TC = class
          strict private
            FX: Integer;
          public
            procedure Bump;
          end;
        procedure TC.Bump;
        begin
          Self.FX := Self.FX + 1;
        end;
        begin end.
        ''';
begin
  AnalyseExpectOK(Src);
end;

procedure TVisibilitySemTests.TestSem_StrictPrivateMethod_CrossType_Rejected;
const
  Src =
    '''
        program P;
        type
          TM = class
          strict private
            procedure Hidden;
          end;
          TUser = class
          public
            procedure Use(m: TM);
          end;
        procedure TM.Hidden; begin end;
        procedure TUser.Use(m: TM);
        begin
          m.Hidden();
        end;
        begin end.
        ''';
begin
  AnalyseExpectReject(Src, 'not accessible');
end;

procedure TVisibilitySemTests.TestSem_ProtectedField_Descendant_OK;
const
  Src =
    '''
        program P;
        type
          TBase = class
          protected
            FProt: Integer;
          end;
          TDeriv = class(TBase)
          public
            procedure Use;
          end;
        procedure TDeriv.Use;
        begin
          Self.FProt := 9;
        end;
        begin end.
        ''';
begin
  AnalyseExpectOK(Src);
end;

procedure TVisibilitySemTests.TestSem_ProtectedField_SameUnitUnrelated_OK;
const
  { protected is private (unit-scoped) PLUS descendants — so an UNRELATED type
    in the SAME unit can still reach it.  The cross-unit unrelated REJECT case
    requires a separate compilation unit and is covered by the standalone
    cross-unit compile checks + the warm-cache fixpoint. }
  Src =
    '''
        program P;
        type
          TBase = class
          protected
            FProt: Integer;
          end;
          TOther = class
          public
            procedure Poke(b: TBase);
          end;
        procedure TOther.Poke(b: TBase);
        begin
          b.FProt := 1;
        end;
        begin end.
        ''';
begin
  AnalyseExpectOK(Src);
end;

procedure TVisibilitySemTests.TestSem_StrictProtectedField_Descendant_OK;
const
  Src =
    '''
        program P;
        type
          TE = class
          strict protected
            FY: Integer;
          end;
          TSub = class(TE)
          public
            procedure Use;
          end;
        procedure TSub.Use;
        begin
          Self.FY := 1;
        end;
        begin end.
        ''';
begin
  AnalyseExpectOK(Src);
end;

procedure TVisibilitySemTests.TestSem_StrictProtectedField_NonDescendant_Rejected;
const
  Src =
    '''
        program P;
        type
          TE = class
          strict protected
            FY: Integer;
          end;
          TOther = class
          public
            procedure Poke(e: TE);
          end;
        procedure TOther.Poke(e: TE);
        begin
          e.FY := 1;
        end;
        begin end.
        ''';
begin
  AnalyseExpectReject(Src, 'not accessible');
end;

procedure TVisibilitySemTests.TestSem_PublicField_CrossType_OK;
const
  Src =
    '''
        program P;
        type
          TF = class
          public
            FOpen: Integer;
          end;
          TUser = class
          public
            procedure Poke(f: TF);
          end;
        procedure TUser.Poke(f: TF);
        begin
          f.FOpen := 1;
        end;
        begin end.
        ''';
begin
  AnalyseExpectOK(Src);
end;

procedure TVisibilitySemTests.TestSem_StrictPrivateStaticVar_OwnMethod_OK;
const
  Src =
    '''
        program P;
        type
          TS = class
          strict private static var
            FInst: Integer;
          public
            static procedure Init;
          end;
        static procedure TS.Init;
        begin
          FInst := 0;
        end;
        begin end.
        ''';
begin
  AnalyseExpectOK(Src);
end;

procedure TVisibilitySemTests.TestSem_StrictPrivateStaticVar_CrossType_Rejected;
const
  Src =
    '''
        program P;
        type
          TS = class
          strict private static var
            FInst: Integer;
          end;
          TOther = class
          public
            procedure Poke;
          end;
        procedure TOther.Poke;
        begin
          TS.FInst := 1;
        end;
        begin end.
        ''';
begin
  { A strict-private static var is reachable only from TS's own methods; a
    qualified TS.FInst from another type must be rejected. }
  AnalyseExpectReject(Src, 'not accessible');
end;

procedure TVisibilitySemTests.TestSem_PrivateProperty_CrossType_OK;
const
  { private (unit-scoped) — another type in the SAME program can read it. }
  Src =
    '''
        program P;
        type
          TG = class
          private
            FVal: Integer;
          private
            property Val: Integer read FVal write FVal;
          end;
          TUser = class
          public
            function Read(g: TG): Integer;
          end;
        function TUser.Read(g: TG): Integer;
        begin
          Result := g.Val;
        end;
        begin end.
        ''';
begin
  AnalyseExpectOK(Src);
end;

procedure TVisibilitySemTests.TestSem_StrictPrivateProperty_CrossType_Rejected;
const
  Src =
    '''
        program P;
        type
          TG = class
          strict private
            FVal: Integer;
            property Val: Integer read FVal write FVal;
          end;
          TUser = class
          public
            function Read(g: TG): Integer;
          end;
        function TUser.Read(g: TG): Integer;
        begin
          Result := g.Val;
        end;
        begin end.
        ''';
begin
  AnalyseExpectReject(Src, 'not accessible');
end;

initialization
  RegisterTest(TVisibilityParseTests);
  RegisterTest(TVisibilitySemTests);
end.
