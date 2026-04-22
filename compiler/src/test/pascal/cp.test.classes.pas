{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

unit cp.test.classes;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TClassTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Lexer                                                                }
    { ------------------------------------------------------------------ }
    procedure TestLexer_Class_Keyword;

    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_ClassSection_Exists;
    procedure TestParse_ClassType_Name;
    procedure TestParse_ClassType_SingleField;
    procedure TestParse_ClassType_MultipleFields;
    procedure TestParse_ClassType_WithParent;
    procedure TestParse_ClassVar;
    procedure TestParse_ClassConstructorCall;
    procedure TestParse_ClassFieldAssignment;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ClassType_Registered;
    procedure TestSemantic_ClassType_IsClass;
    procedure TestSemantic_ClassVar_HasClassType;
    procedure TestSemantic_Constructor_TypeIsClass;
    procedure TestSemantic_ClassFieldAssign_OK;
    procedure TestSemantic_ClassFieldAssign_TypeMismatch_RaisesError;
    procedure TestSemantic_ClassFieldAccess_TypeIsFieldType;
    procedure TestSemantic_ClassFieldAccess_UnknownField_RaisesError;

    { ------------------------------------------------------------------ }
    { Code generation                                                      }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_ClassVar_HasPointerAlloc;
    procedure TestCodegen_ClassVar_ZeroInit;
    procedure TestCodegen_Constructor_CallsClassAlloc;
    procedure TestCodegen_ClassFieldStore_LoadsPointer;
    procedure TestCodegen_ClassFieldLoad_LoadsPointer;

    { ------------------------------------------------------------------ }
    { Separate method implementations                                      }
    { ------------------------------------------------------------------ }
    procedure TestParse_SeparateImpl_ForwardDeclNoBody;
    procedure TestParse_SeparateImpl_QualifiedName;
    procedure TestSemantic_SeparateImpl_OK;
    procedure TestCodegen_SeparateImpl_EmitsMethod;

    { ------------------------------------------------------------------ }
    { Free built-in                                                        }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Free_OK;
    procedure TestCodegen_Free_CallsClassRelease;

    { ------------------------------------------------------------------ }
    { ARC on class variables and fields                                    }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_ClassVarAssign_InsertsAddRefRelease;
    procedure TestCodegen_ClassVarScopeExit_EmitsRelease;
    procedure TestCodegen_ClassFieldAssign_InsertsAddRefRelease;
    procedure TestCodegen_FieldCleanup_EmittedPerClass;
    procedure TestCodegen_FieldCleanup_ReleasesClassField;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TClassTests.ParseSrc(const ASrc: string): TProgram;
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

function TClassTests.AnalyseSrc(const ASrc: string): TProgram;
var
  A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create;
  try
    A.Analyse(Result);
  finally
    A.Free;
  end;
end;

function TClassTests.GenIR(const ASrc: string): string;
var
  Prog: TProgram;
  CG:   TCodeGenQBE;
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

procedure TClassTests.AnalyseExpectError(const ASrc: string);
var
  Prog: TProgram;
begin
  try
    Prog := AnalyseSrc(ASrc);
    Prog.Free;
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ; { expected }
  end;
end;

{ ------------------------------------------------------------------ }
{ Lexer                                                               }
{ ------------------------------------------------------------------ }

procedure TClassTests.TestLexer_Class_Keyword;
var
  L: TLexer;
  T: TToken;
begin
  L := TLexer.Create('class');
  try
    T := L.Next;
    AssertEquals('class token', Ord(tkClass), Ord(T.Kind));
  finally
    L.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser                                                              }
{ ------------------------------------------------------------------ }

const
  SrcSimpleClass =
    'program P;'          + LineEnding +
    'type'                + LineEnding +
    '  TFoo = class'      + LineEnding +
    '    X: Integer;'     + LineEnding +
    '  end;'              + LineEnding +
    'begin end.';

procedure TClassTests.TestParse_ClassSection_Exists;
var
  Prog: TProgram;
begin
  Prog := ParseSrc(SrcSimpleClass);
  try
    AssertEquals('1 type decl', 1, Prog.Block.TypeDecls.Count);
  finally
    Prog.Free;
  end;
end;

procedure TClassTests.TestParse_ClassType_Name;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(SrcSimpleClass);
  try
    TD := TTypeDecl(Prog.Block.TypeDecls[0]);
    AssertEquals('Type name', 'TFoo', TD.Name);
    AssertTrue('Is TClassTypeDef', TD.Def is TClassTypeDef);
  finally
    Prog.Free;
  end;
end;

procedure TClassTests.TestParse_ClassType_SingleField;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  Fld:  TFieldDecl;
begin
  Prog := ParseSrc(SrcSimpleClass);
  try
    CD  := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('1 field', 1, CD.Fields.Count);
    Fld := TFieldDecl(CD.Fields[0]);
    AssertEquals('Field name', 'X', Fld.Names[0]);
    AssertEquals('Field type', 'Integer', Fld.TypeName);
  finally
    Prog.Free;
  end;
end;

procedure TClassTests.TestParse_ClassType_MultipleFields;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(
    'program P;'              + LineEnding +
    'type'                    + LineEnding +
    '  TPerson = class'       + LineEnding +
    '    Name: string;'       + LineEnding +
    '    Age: Integer;'       + LineEnding +
    '  end;'                  + LineEnding +
    'begin end.');
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('2 fields', 2, CD.Fields.Count);
    AssertEquals('First field', 'Name', TFieldDecl(CD.Fields[0]).Names[0]);
    AssertEquals('Second field', 'Age',  TFieldDecl(CD.Fields[1]).Names[0]);
  finally
    Prog.Free;
  end;
end;

procedure TClassTests.TestParse_ClassType_WithParent;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(
    'program P;'                    + LineEnding +
    'type'                          + LineEnding +
    '  TAnimal = class'             + LineEnding +
    '    Name: string;'             + LineEnding +
    '  end;'                        + LineEnding +
    '  TDog = class(TAnimal)'       + LineEnding +
    '    Breed: string;'            + LineEnding +
    '  end;'                        + LineEnding +
    'begin end.');
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[1]).Def);
    AssertEquals('Parent class', 'TAnimal', CD.ParentName);
  finally
    Prog.Free;
  end;
end;

procedure TClassTests.TestParse_ClassVar;
var
  Prog: TProgram;
  Decl: TVarDecl;
begin
  Prog := ParseSrc(
    'program P;'          + LineEnding +
    'type'                + LineEnding +
    '  TFoo = class'      + LineEnding +
    '    X: Integer;'     + LineEnding +
    '  end;'              + LineEnding +
    'var F: TFoo;'        + LineEnding +
    'begin end.');
  try
    Decl := TVarDecl(Prog.Block.Decls[0]);
    AssertEquals('Var name', 'F', Decl.Names[0]);
    AssertEquals('Var type', 'TFoo', Decl.TypeName);
  finally
    Prog.Free;
  end;
end;

procedure TClassTests.TestParse_ClassConstructorCall;
var
  Prog:   TProgram;
  Assign: TAssignment;
  Expr:   TFieldAccessExpr;
begin
  Prog := ParseSrc(
    'program P;'          + LineEnding +
    'type'                + LineEnding +
    '  TFoo = class'      + LineEnding +
    '    X: Integer;'     + LineEnding +
    '  end;'              + LineEnding +
    'var F: TFoo;'        + LineEnding +
    'begin'               + LineEnding +
    '  F := TFoo.Create'  + LineEnding +
    'end.');
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertEquals('Assigns to F', 'F', Assign.Name);
    AssertTrue('Expr is TFieldAccessExpr', Assign.Expr is TFieldAccessExpr);
    Expr := TFieldAccessExpr(Assign.Expr);
    AssertEquals('Type name', 'TFoo',   Expr.RecordName);
    AssertEquals('Method',    'Create', Expr.FieldName);
  finally
    Prog.Free;
  end;
end;

procedure TClassTests.TestParse_ClassFieldAssignment;
var
  Prog: TProgram;
  Stmt: TFieldAssignment;
begin
  Prog := ParseSrc(
    'program P;'          + LineEnding +
    'type'                + LineEnding +
    '  TFoo = class'      + LineEnding +
    '    X: Integer;'     + LineEnding +
    '  end;'              + LineEnding +
    'var F: TFoo;'        + LineEnding +
    'begin'               + LineEnding +
    '  F.X := 99'         + LineEnding +
    'end.');
  try
    Stmt := TFieldAssignment(Prog.Block.Stmts[0]);
    AssertEquals('Record var',  'F',  Stmt.RecordName);
    AssertEquals('Field name',  'X',  Stmt.FieldName);
    AssertTrue('Expr is TIntLiteral', Stmt.Expr is TIntLiteral);
  finally
    Prog.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic                                                            }
{ ------------------------------------------------------------------ }

procedure TClassTests.TestSemantic_ClassType_Registered;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcSimpleClass);
  try
    AssertNotNull('TFoo in symbol table',
      Prog.SymbolTable.FindType('TFoo'));
  finally
    Prog.Free;
  end;
end;

procedure TClassTests.TestSemantic_ClassType_IsClass;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcSimpleClass);
  try
    AssertEquals('TFoo is tyClass',
      Ord(tyClass),
      Ord(Prog.SymbolTable.FindType('TFoo').Kind));
  finally
    Prog.Free;
  end;
end;

procedure TClassTests.TestSemantic_ClassVar_HasClassType;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(
    'program P;'          + LineEnding +
    'type'                + LineEnding +
    '  TFoo = class'      + LineEnding +
    '    X: Integer;'     + LineEnding +
    '  end;'              + LineEnding +
    'var F: TFoo;'        + LineEnding +
    'begin end.');
  try
    AssertEquals('F is tyClass',
      Ord(tyClass),
      Ord(TVarDecl(Prog.Block.Decls[0]).ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TClassTests.TestSemantic_Constructor_TypeIsClass;
var
  Prog:   TProgram;
  Assign: TAssignment;
  Expr:   TFieldAccessExpr;
begin
  Prog := AnalyseSrc(
    'program P;'          + LineEnding +
    'type'                + LineEnding +
    '  TFoo = class'      + LineEnding +
    '    X: Integer;'     + LineEnding +
    '  end;'              + LineEnding +
    'var F: TFoo;'        + LineEnding +
    'begin'               + LineEnding +
    '  F := TFoo.Create'  + LineEnding +
    'end.');
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    Expr   := TFieldAccessExpr(Assign.Expr);
    AssertTrue('IsConstructorCall', Expr.IsConstructorCall);
    AssertEquals('ResolvedType is tyClass',
      Ord(tyClass), Ord(Expr.ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TClassTests.TestSemantic_ClassFieldAssign_OK;
begin
  AnalyseSrc(
    'program P;'          + LineEnding +
    'type'                + LineEnding +
    '  TFoo = class'      + LineEnding +
    '    X: Integer;'     + LineEnding +
    '  end;'              + LineEnding +
    'var F: TFoo;'        + LineEnding +
    'begin'               + LineEnding +
    '  F.X := 42'         + LineEnding +
    'end.'
  ).Free;
end;

procedure TClassTests.TestSemantic_ClassFieldAssign_TypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    'program P;'          + LineEnding +
    'type'                + LineEnding +
    '  TFoo = class'      + LineEnding +
    '    X: Integer;'     + LineEnding +
    '  end;'              + LineEnding +
    'var F: TFoo;'        + LineEnding +
    'begin'               + LineEnding +
    '  F.X := ''hello'''  + LineEnding +
    'end.');
end;

procedure TClassTests.TestSemantic_ClassFieldAccess_TypeIsFieldType;
var
  Prog:   TProgram;
  Access: TFieldAccessExpr;
begin
  Prog := AnalyseSrc(
    'program P;'              + LineEnding +
    'type'                    + LineEnding +
    '  TFoo = class'          + LineEnding +
    '    X: Integer;'         + LineEnding +
    '  end;'                  + LineEnding +
    'var F: TFoo; N: Integer;' + LineEnding +
    'begin'                   + LineEnding +
    '  N := F.X'              + LineEnding +
    'end.');
  try
    Access := TFieldAccessExpr(TAssignment(Prog.Block.Stmts[0]).Expr);
    AssertTrue('IsClassAccess', Access.IsClassAccess);
    AssertEquals('Field access type',
      Ord(tyInteger), Ord(Access.ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TClassTests.TestSemantic_ClassFieldAccess_UnknownField_RaisesError;
begin
  AnalyseExpectError(
    'program P;'              + LineEnding +
    'type'                    + LineEnding +
    '  TFoo = class'          + LineEnding +
    '    X: Integer;'         + LineEnding +
    '  end;'                  + LineEnding +
    'var F: TFoo; N: Integer;' + LineEnding +
    'begin'                   + LineEnding +
    '  N := F.Z'              + LineEnding +
    'end.');
end;

{ ------------------------------------------------------------------ }
{ Code generation                                                     }
{ ------------------------------------------------------------------ }

procedure TClassTests.TestCodegen_ClassVar_HasPointerAlloc;
var
  IR: string;
begin
  IR := GenIR(
    'program P;'          + LineEnding +
    'type'                + LineEnding +
    '  TFoo = class'      + LineEnding +
    '    X: Integer;'     + LineEnding +
    '  end;'              + LineEnding +
    'var F: TFoo;'        + LineEnding +
    'begin end.');
  AssertTrue('alloc8 for F', Pos('_var_F', IR) > 0);
  AssertTrue('8-byte alloc', Pos('alloc8', IR) > 0);
end;

procedure TClassTests.TestCodegen_ClassVar_ZeroInit;
var
  IR: string;
begin
  IR := GenIR(
    'program P;'          + LineEnding +
    'type'                + LineEnding +
    '  TFoo = class'      + LineEnding +
    '    X: Integer;'     + LineEnding +
    '  end;'              + LineEnding +
    'var F: TFoo;'        + LineEnding +
    'begin end.');
  AssertTrue('zero init', Pos('storel 0', IR) > 0);
end;

procedure TClassTests.TestCodegen_Constructor_CallsClassAlloc;
var
  IR: string;
begin
  { Class instances are allocated via _ClassAlloc, which prefixes an 8-byte
    refcount header before the user pointer so every Blaise class carries the
    bookkeeping needed for ARC.  The user pointer still points at the vptr
    (offset 0); field offsets are unchanged. }
  IR := GenIR(
    'program P;'          + LineEnding +
    'type'                + LineEnding +
    '  TFoo = class'      + LineEnding +
    '    X: Integer;'     + LineEnding +
    '  end;'              + LineEnding +
    'var F: TFoo;'        + LineEnding +
    'begin'               + LineEnding +
    '  F := TFoo.Create'  + LineEnding +
    'end.');
  AssertTrue('calls _ClassAlloc', Pos('call $_ClassAlloc', IR) > 0);
  AssertTrue('does not call calloc directly', Pos('call $calloc', IR) = 0);
  AssertTrue('stores pointer', Pos('storel', IR) > 0);
end;

procedure TClassTests.TestCodegen_ClassFieldStore_LoadsPointer;
var
  IR: string;
begin
  IR := GenIR(
    'program P;'          + LineEnding +
    'type'                + LineEnding +
    '  TFoo = class'      + LineEnding +
    '    X: Integer;'     + LineEnding +
    '  end;'              + LineEnding +
    'var F: TFoo;'        + LineEnding +
    'begin'               + LineEnding +
    '  F.X := 42'         + LineEnding +
    'end.');
  AssertTrue('loads pointer', Pos('loadl %_var_F', IR) > 0);
  AssertTrue('stores value',  Pos('storew', IR) > 0);
end;

procedure TClassTests.TestCodegen_ClassFieldLoad_LoadsPointer;
var
  IR: string;
begin
  IR := GenIR(
    'program P;'              + LineEnding +
    'type'                    + LineEnding +
    '  TFoo = class'          + LineEnding +
    '    X: Integer;'         + LineEnding +
    '  end;'                  + LineEnding +
    'var F: TFoo; N: Integer;' + LineEnding +
    'begin'                   + LineEnding +
    '  N := F.X'              + LineEnding +
    'end.');
  AssertTrue('loads pointer', Pos('loadl %_var_F', IR) > 0);
  AssertTrue('loads field',   Pos('loadw', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Separate method implementations                                      }
{ ------------------------------------------------------------------ }

const
  SrcSeparateImpl =
    'program P;'                        + LineEnding +
    'type'                              + LineEnding +
    '  TFoo = class'                    + LineEnding +
    '    X: Integer;'                   + LineEnding +
    '    procedure SetX(AVal: Integer);' + LineEnding +
    '  end;'                            + LineEnding +
    'procedure TFoo.SetX(AVal: Integer);' + LineEnding +
    'begin'                             + LineEnding +
    '  Self.X := AVal'                  + LineEnding +
    'end;'                              + LineEnding +
    'var F: TFoo;'                      + LineEnding +
    'begin'                             + LineEnding +
    '  F := TFoo.Create;'               + LineEnding +
    '  F.SetX(42)'                      + LineEnding +
    'end.';

procedure TClassTests.TestParse_SeparateImpl_ForwardDeclNoBody;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcSeparateImpl);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MD := TMethodDecl(CD.Methods[0]);
    AssertNull('class method forward decl has no body', MD.Body);
  finally
    Prog.Free;
  end;
end;

procedure TClassTests.TestParse_SeparateImpl_QualifiedName;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcSeparateImpl);
  try
    { First ProcDecl in block is the standalone impl }
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('owner type name', 'TFoo', MD.OwnerTypeName);
    AssertEquals('method name', 'SetX', MD.Name);
  finally
    Prog.Free;
  end;
end;

procedure TClassTests.TestSemantic_SeparateImpl_OK;
begin
  AnalyseSrc(SrcSeparateImpl).Free;
end;

procedure TClassTests.TestCodegen_SeparateImpl_EmitsMethod;
var IR: string;
begin
  IR := GenIR(SrcSeparateImpl);
  { The method body must appear in the IR as TFoo_SetX }
  AssertTrue('TFoo_SetX emitted', Pos('$TFoo_SetX', IR) > 0);
  { The call site must use it }
  AssertTrue('call to TFoo_SetX', Pos('call $TFoo_SetX', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Free built-in                                                        }
{ ------------------------------------------------------------------ }

const
  SrcFree =
    'program P;'             + LineEnding +
    'type'                   + LineEnding +
    '  TFoo = class'         + LineEnding +
    '    X: Integer;'        + LineEnding +
    '  end;'                 + LineEnding +
    'var F: TFoo;'           + LineEnding +
    'begin'                  + LineEnding +
    '  F := TFoo.Create;'    + LineEnding +
    '  F.Free'               + LineEnding +
    'end.';

procedure TClassTests.TestSemantic_Free_OK;
begin
  AnalyseSrc(SrcFree).Free;
end;

procedure TClassTests.TestCodegen_Free_CallsClassRelease;
var IR: string;
begin
  { Obj.Free is a sanctioned synonym for immediate release under ARC: it
    decrements the refcount (freeing the block and running the field
    cleanup fn at zero) and nil-outs the slot so the scope-exit release
    becomes a no-op. }
  IR := GenIR(SrcFree);
  AssertTrue('calls _ClassRelease',     Pos('call $_ClassRelease', IR) > 0);
  AssertTrue('nil-outs slot after Free', Pos('storel 0, %_var_',   IR) > 0);
  AssertTrue('does not call C free() directly', Pos('call $free(', IR) = 0);
end;

{ ------------------------------------------------------------------ }
{ ARC on class variables and fields                                    }
{ ------------------------------------------------------------------ }

const
  SrcArcBasic =
    'program P;'                  + LineEnding +
    'type'                        + LineEnding +
    '  TFoo = class'              + LineEnding +
    '    X: Integer;'             + LineEnding +
    '  end;'                      + LineEnding +
    'var F: TFoo;'                + LineEnding +
    'begin'                       + LineEnding +
    '  F := TFoo.Create'          + LineEnding +
    'end.';

  SrcArcFieldClass =
    'program P;'                  + LineEnding +
    'type'                        + LineEnding +
    '  TInner = class'            + LineEnding +
    '    V: Integer;'             + LineEnding +
    '  end;'                      + LineEnding +
    '  TOuter = class'            + LineEnding +
    '    Child: TInner;'          + LineEnding +
    '  end;'                      + LineEnding +
    'var A, B: TOuter;'           + LineEnding +
    'begin'                       + LineEnding +
    '  A := TOuter.Create;'       + LineEnding +
    '  B := TOuter.Create;'       + LineEnding +
    '  A.Child := TInner.Create;' + LineEnding +
    '  B.Child := A.Child'        + LineEnding +
    'end.';

procedure TClassTests.TestCodegen_ClassVarAssign_InsertsAddRefRelease;
var IR: string;
begin
  IR := GenIR(SrcArcBasic);
  AssertTrue('addref on new class RHS',
    Pos('call $_ClassAddRef', IR) > 0);
  AssertTrue('release on old class LHS',
    Pos('call $_ClassRelease', IR) > 0);
end;

procedure TClassTests.TestCodegen_ClassVarScopeExit_EmitsRelease;
var IR: string;
begin
  { The variable F must be released at block exit (main_exit label).
    Emitted as part of EmitArcCleanup. }
  IR := GenIR(SrcArcBasic);
  AssertTrue('release at scope exit',
    Pos('call $_ClassRelease', IR) > 0);
  { Two releases: one from overwriting the nil slot during F := Create
    (old=nil, noop at runtime but still emitted), one at scope exit. }
  AssertTrue('at least two class releases emitted',
    (Pos('call $_ClassRelease',
         Copy(IR, Pos('call $_ClassRelease', IR) + 1, MaxInt)) > 0));
end;

procedure TClassTests.TestCodegen_ClassFieldAssign_InsertsAddRefRelease;
var IR: string;
begin
  { A.Child := TInner.Create should load old A.Child, release it, addref the
    new Inner, and store.  The insertion pattern mirrors variable ARC but
    targets a heap-field slot rather than a local. }
  IR := GenIR(SrcArcFieldClass);
  AssertTrue('class field assignment addrefs',
    Pos('call $_ClassAddRef', IR) > 0);
  AssertTrue('class field assignment releases old',
    Pos('call $_ClassRelease', IR) > 0);
end;

procedure TClassTests.TestCodegen_FieldCleanup_EmittedPerClass;
var IR: string;
begin
  IR := GenIR(SrcArcFieldClass);
  AssertTrue('cleanup fn emitted for TInner',
    Pos('function $_FieldCleanup_TInner', IR) > 0);
  AssertTrue('cleanup fn emitted for TOuter',
    Pos('function $_FieldCleanup_TOuter', IR) > 0);
end;

procedure TClassTests.TestCodegen_FieldCleanup_ReleasesClassField;
var IR, OuterBody: string;
  StartPos, EndPos: Integer;
begin
  { TOuter.Child is a TInner — its cleanup fn must release the field.
    Isolate _FieldCleanup_TOuter's body and assert a _ClassRelease appears
    inside it (not in some sibling function). }
  IR       := GenIR(SrcArcFieldClass);
  StartPos := Pos('function $_FieldCleanup_TOuter', IR);
  AssertTrue('TOuter cleanup present', StartPos > 0);
  OuterBody := Copy(IR, StartPos, MaxInt);
  EndPos   := Pos(LineEnding + '}', OuterBody);
  AssertTrue('TOuter cleanup has end', EndPos > 0);
  OuterBody := Copy(OuterBody, 1, EndPos);
  AssertTrue('TOuter cleanup releases class-typed field',
    Pos('call $_ClassRelease', OuterBody) > 0);
end;

initialization
  RegisterTest(TClassTests);

end.
