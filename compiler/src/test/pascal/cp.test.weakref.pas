{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

{ Tests for the [Weak] attribute: zeroing weak references used to break
  reference cycles under universal ARC.  Organised in the order the
  feature is implemented:

    1. Lexer    — tkLBracket / tkRBracket token recognition.
    2. Parser   — [Ident] attribute list before var and field decls.
    3. Semantic — resolve WeakAttribute (with suffix fallback) and flag
                  the declaration; reject on non-reference types.
    4. Codegen  — weak vars use _WeakAssign / _WeakClear at every ARC
                  insertion site.
    5. E2E      — parent/child cycle that leaks without [Weak] and is
                  valgrind-clean with it.

  Each section is driven by a TDD cycle: failing test first, then the
  minimum code change to pass it.  When tests in a section pass, they
  act as a regression fence for later work. }

unit cp.test.weakref;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TWeakRefTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc, AExpectedFragment: string);
  published
    { ------------------------------------------------------------------ }
    { Lexer — bracket tokens                                               }
    { ------------------------------------------------------------------ }
    procedure TestLex_LBracket;
    procedure TestLex_RBracket;

    { ------------------------------------------------------------------ }
    { Parser — attribute list on var and field declarations                }
    { ------------------------------------------------------------------ }
    procedure TestParse_WeakAttribute_OnVarDecl;
    procedure TestParse_WeakAttribute_OnClassField;
    procedure TestParse_UnknownAttribute_AcceptedSilently;
    procedure TestParse_MultipleAttributes_OnVar;

    { ------------------------------------------------------------------ }
    { Semantic — name resolution + type validation                         }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Weak_OnClassVar_OK;
    procedure TestSemantic_Weak_OnInterfaceVar_OK;
    procedure TestSemantic_Weak_OnInteger_RaisesError;
    procedure TestSemantic_Weak_OnString_RaisesError;
    procedure TestSemantic_WeakAttribute_SuffixMatches_Weak;

    { ------------------------------------------------------------------ }
    { Codegen — weak-ref insertion                                         }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_WeakVarAssign_UsesWeakAssign;
    procedure TestCodegen_WeakVarScopeExit_UsesWeakClear;
    procedure TestCodegen_WeakVarAssign_DoesNotCallClassAddRef;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TWeakRefTests.ParseSrc(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse;
  finally
    P.Free;
    L.Free;
  end;
end;

function TWeakRefTests.AnalyseSrc(const ASrc: string): TProgram;
var
  Prog:     TProgram;
  Analyser: TSemanticAnalyser;
begin
  Prog     := ParseSrc(ASrc);
  Analyser := TSemanticAnalyser.Create;
  try
    Analyser.Analyse(Prog);
    Result := Prog;
  finally
    Analyser.Free;
  end;
end;

function TWeakRefTests.GenIR(const ASrc: string): string;
var
  Prog:     TProgram;
  CG:       TCodeGenQBE;
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

procedure TWeakRefTests.AnalyseExpectError(const ASrc, AExpectedFragment: string);
var
  Raised: Boolean;
  Msg:    string;
begin
  Raised := False;
  Msg    := '';
  try
    AnalyseSrc(ASrc).Free;
  except
    on E: ESemanticError do
    begin
      Raised := True;
      Msg    := E.Message;
    end;
  end;
  AssertTrue('expected ESemanticError', Raised);
  AssertTrue(
    Format('error message %s did not contain %s', [QuotedStr(Msg), QuotedStr(AExpectedFragment)]),
    Pos(LowerCase(AExpectedFragment), LowerCase(Msg)) > 0);
end;

{ ------------------------------------------------------------------ }
{ Lexer                                                               }
{ ------------------------------------------------------------------ }

procedure TWeakRefTests.TestLex_LBracket;
var
  L:   TLexer;
  Tok: TToken;
begin
  L := TLexer.Create('[');
  try
    Tok := L.Next;
    AssertEquals('kind is tkLBracket', Ord(tkLBracket), Ord(Tok.Kind));
  finally
    L.Free;
  end;
end;

procedure TWeakRefTests.TestLex_RBracket;
var
  L:   TLexer;
  Tok: TToken;
begin
  L := TLexer.Create(']');
  try
    Tok := L.Next;
    AssertEquals('kind is tkRBracket', Ord(tkRBracket), Ord(Tok.Kind));
  finally
    L.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser                                                              }
{ ------------------------------------------------------------------ }

const
  SrcWeakOnVar =
    'program P;'                         + LineEnding +
    'type'                               + LineEnding +
    '  TFoo = class'                     + LineEnding +
    '    X: Integer;'                    + LineEnding +
    '  end;'                             + LineEnding +
    'var'                                + LineEnding +
    '  [Weak] F: TFoo;'                  + LineEnding +
    'begin'                              + LineEnding +
    'end.';

  SrcWeakOnField =
    'program P;'                         + LineEnding +
    'type'                               + LineEnding +
    '  TParent = class'                  + LineEnding +
    '  end;'                             + LineEnding +
    '  TChild = class'                   + LineEnding +
    '    [Weak] Parent: TParent;'        + LineEnding +
    '  end;'                             + LineEnding +
    'begin'                              + LineEnding +
    'end.';

  SrcUnknownAttr =
    'program P;'                         + LineEnding +
    'type'                               + LineEnding +
    '  TFoo = class'                     + LineEnding +
    '  end;'                             + LineEnding +
    'var'                                + LineEnding +
    '  [SomeUnknown] F: TFoo;'           + LineEnding +
    'begin'                              + LineEnding +
    'end.';

  SrcMultiAttr =
    'program P;'                         + LineEnding +
    'type'                               + LineEnding +
    '  TFoo = class'                     + LineEnding +
    '  end;'                             + LineEnding +
    'var'                                + LineEnding +
    '  [Weak][SomeOther] F: TFoo;'       + LineEnding +
    'begin'                              + LineEnding +
    'end.';

procedure TWeakRefTests.TestParse_WeakAttribute_OnVarDecl;
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := ParseSrc(SrcWeakOnVar);
  try
    AssertEquals('one var decl in block', 1, Prog.Block.Decls.Count);
    VD := TVarDecl(Prog.Block.Decls[0]);
    AssertNotNull('attributes list allocated', VD.Attributes);
    AssertTrue('Weak attribute recorded',
      VD.Attributes.IndexOf('Weak') >= 0);
  finally
    Prog.Free;
  end;
end;

procedure TWeakRefTests.TestParse_WeakAttribute_OnClassField;
var
  Prog:  TProgram;
  TD:    TTypeDecl;
  Cls:   TClassTypeDef;
  FDecl: TFieldDecl;
  I:     Integer;
begin
  Prog := ParseSrc(SrcWeakOnField);
  try
    { Locate TChild among the type decls and pull its Parent field. }
    TD  := nil;
    for I := 0 to Prog.Block.TypeDecls.Count - 1 do
      if SameText(TTypeDecl(Prog.Block.TypeDecls[I]).Name, 'TChild') then
      begin
        TD := TTypeDecl(Prog.Block.TypeDecls[I]);
        Break;
      end;
    AssertNotNull('TChild declared', TD);
    Cls := TClassTypeDef(TD.Def);
    AssertEquals('TChild has one field', 1, Cls.Fields.Count);
    FDecl := TFieldDecl(Cls.Fields[0]);
    AssertNotNull('field attributes allocated', FDecl.Attributes);
    AssertTrue('Weak attribute recorded on field',
      FDecl.Attributes.IndexOf('Weak') >= 0);
  finally
    Prog.Free;
  end;
end;

procedure TWeakRefTests.TestParse_UnknownAttribute_AcceptedSilently;
var
  Prog: TProgram;
begin
  { Parser must accept attributes it doesn't recognise — forward-compatibility
    with user-defined attributes.  Recording the name is sufficient. }
  Prog := ParseSrc(SrcUnknownAttr);
  try
    AssertEquals('one var decl parsed despite unknown attr',
      1, Prog.Block.Decls.Count);
    AssertTrue('attribute name captured',
      TVarDecl(Prog.Block.Decls[0]).Attributes.IndexOf('SomeUnknown') >= 0);
  finally
    Prog.Free;
  end;
end;

procedure TWeakRefTests.TestParse_MultipleAttributes_OnVar;
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := ParseSrc(SrcMultiAttr);
  try
    VD := TVarDecl(Prog.Block.Decls[0]);
    AssertTrue('Weak recorded',      VD.Attributes.IndexOf('Weak') >= 0);
    AssertTrue('SomeOther recorded', VD.Attributes.IndexOf('SomeOther') >= 0);
  finally
    Prog.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic                                                            }
{ ------------------------------------------------------------------ }

const
  SrcSemWeakClassVar =
    'program P;'                         + LineEnding +
    'type'                               + LineEnding +
    '  TFoo = class'                     + LineEnding +
    '  end;'                             + LineEnding +
    'var'                                + LineEnding +
    '  [Weak] F: TFoo;'                  + LineEnding +
    'begin'                              + LineEnding +
    'end.';

  SrcSemWeakInterfaceVar =
    'program P;'                         + LineEnding +
    'type'                               + LineEnding +
    '  IFoo = interface'                 + LineEnding +
    '    procedure DoIt;'                + LineEnding +
    '  end;'                             + LineEnding +
    'var'                                + LineEnding +
    '  [Weak] F: IFoo;'                  + LineEnding +
    'begin'                              + LineEnding +
    'end.';

  SrcSemWeakInt =
    'program P;'                         + LineEnding +
    'var'                                + LineEnding +
    '  [Weak] N: Integer;'               + LineEnding +
    'begin'                              + LineEnding +
    'end.';

  SrcSemWeakString =
    'program P;'                         + LineEnding +
    'var'                                + LineEnding +
    '  [Weak] S: string;'                + LineEnding +
    'begin'                              + LineEnding +
    'end.';

  SrcSemWeakSuffix =
    'program P;'                         + LineEnding +
    'type'                               + LineEnding +
    '  TFoo = class'                     + LineEnding +
    '  end;'                             + LineEnding +
    'var'                                + LineEnding +
    '  [WeakAttribute] F: TFoo;'         + LineEnding +
    'begin'                              + LineEnding +
    'end.';

procedure TWeakRefTests.TestSemantic_Weak_OnClassVar_OK;
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := AnalyseSrc(SrcSemWeakClassVar);
  try
    VD := TVarDecl(Prog.Block.Decls[0]);
    AssertTrue('IsWeak flag set on class var', VD.IsWeak);
  finally
    Prog.Free;
  end;
end;

procedure TWeakRefTests.TestSemantic_Weak_OnInterfaceVar_OK;
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := AnalyseSrc(SrcSemWeakInterfaceVar);
  try
    VD := TVarDecl(Prog.Block.Decls[0]);
    AssertTrue('IsWeak flag set on interface var', VD.IsWeak);
  finally
    Prog.Free;
  end;
end;

procedure TWeakRefTests.TestSemantic_Weak_OnInteger_RaisesError;
begin
  AnalyseExpectError(SrcSemWeakInt, 'weak');
end;

procedure TWeakRefTests.TestSemantic_Weak_OnString_RaisesError;
begin
  AnalyseExpectError(SrcSemWeakString, 'weak');
end;

procedure TWeakRefTests.TestSemantic_WeakAttribute_SuffixMatches_Weak;
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  { [WeakAttribute] is the long form; the compiler must resolve it the
    same way as [Weak] by stripping the 'Attribute' suffix. }
  Prog := AnalyseSrc(SrcSemWeakSuffix);
  try
    VD := TVarDecl(Prog.Block.Decls[0]);
    AssertTrue('IsWeak set via long form', VD.IsWeak);
  finally
    Prog.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Codegen                                                             }
{ ------------------------------------------------------------------ }

const
  SrcCodegenWeakAssign =
    'program P;'                         + LineEnding +
    'type'                               + LineEnding +
    '  TFoo = class'                     + LineEnding +
    '  end;'                             + LineEnding +
    'var'                                + LineEnding +
    '  Owner:       TFoo;'               + LineEnding +
    '  [Weak] Peek: TFoo;'               + LineEnding +
    'begin'                              + LineEnding +
    '  Owner := TFoo.Create;'            + LineEnding +
    '  Peek  := Owner'                   + LineEnding +
    'end.';

procedure TWeakRefTests.TestCodegen_WeakVarAssign_UsesWeakAssign;
var
  IR: string;
begin
  IR := GenIR(SrcCodegenWeakAssign);
  AssertTrue('weak assignment lowers to _WeakAssign',
    Pos('call $_WeakAssign', IR) > 0);
end;

procedure TWeakRefTests.TestCodegen_WeakVarScopeExit_UsesWeakClear;
var
  IR: string;
begin
  IR := GenIR(SrcCodegenWeakAssign);
  AssertTrue('weak scope exit calls _WeakClear',
    Pos('call $_WeakClear', IR) > 0);
end;

procedure TWeakRefTests.TestCodegen_WeakVarAssign_DoesNotCallClassAddRef;
var
  IR, After: string;
  FirstAssignEnd: Integer;
begin
  { Verify that the *weak* assignment does NOT addref.  Owner := TFoo.Create
    still addrefs (strong).  We crudely split the IR on '_WeakAssign' and
    assert no _ClassAddRef appears in the same basic block on either side
    immediately around the weak call. }
  IR := GenIR(SrcCodegenWeakAssign);
  FirstAssignEnd := Pos('call $_WeakAssign', IR);
  AssertTrue('_WeakAssign call present', FirstAssignEnd > 0);
  { Scan a window of the surrounding 10 lines for a spurious _ClassAddRef
    on the Peek assignment.  A simple heuristic: the lines between the
    _WeakAssign call and the subsequent jmp/ret should not contain a
    _ClassAddRef tied to the weak slot. }
  After := Copy(IR, FirstAssignEnd, 200);
  AssertTrue('no _ClassAddRef adjacent to the weak store',
    Pos('_ClassAddRef', After) = 0);
end;

initialization
  RegisterTest(TWeakRefTests);

end.
