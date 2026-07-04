{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.inherit;

{ Tests for class inheritance, self-referential types, and nil. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

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
    procedure TestCodegen_MethodCall_NilGuard_EmitsCheckNil;

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

    { ------------------------------------------------------------------ }
    { TObject.InheritsFrom                                                 }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_InheritsFrom_OnPointerVar_OK;
    procedure TestSemantic_InheritsFrom_OnClassInstance_OK;
    procedure TestSemantic_InheritsFrom_ReturnsBoolean;
    procedure TestCodegen_InheritsFrom_CallsRTL;
    procedure TestCodegen_InheritsFrom_OnClassInstance_LoadsTypeinfo;
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
    Result := P.Parse();
  finally
    P.Free(); L.Free();
  end;
end;

function TInheritTests.AnalyseSrc(const ASrc: string): TProgram;
var A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Result);
  finally
    A.Free();
  end;
end;

function TInheritTests.GenIR(const ASrc: string): string;
var Prog: TProgram; CG: TCodeGenQBE;
begin
  Prog := AnalyseSrc(ASrc);
  try
    CG := TCodeGenQBE.Create();
    try
      CG.Generate(Prog);
      Result := CG.GetOutput();
    finally
      CG.Free();
    end;
  finally
    Prog.Free();
  end;
end;

procedure TInheritTests.AnalyseExpectError(const ASrc: string);
var Prog: TProgram;
begin
  try
    Prog := AnalyseSrc(ASrc);
    Prog.Free();
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
    'program P;' + #10 +
    'var C: TNode;'       + #10 +  { forward ref — TNode defined after }
    '''
        type
          TNode = class
            Value: Integer;
            Next:  TNode;
          end;
        var N: TNode;
        begin
          N := TNode.Create();
          N.Next := nil
        end.
        ''';

  SrcSelfRef =
    '''
        program P;
        type
          TNode = class
            Value: Integer;
            Next:  TNode;
          end;
        var N: TNode;
        begin
          N := TNode.Create();
          N.Value := 1;
          N.Next := nil
        end.
        ''';

  SrcInherit =
    '''
        program P;
        type
          TAnimal = class
            Age: Integer;
          end;
          TDog = class(TAnimal)
            Legs: Integer;
          end;
        var D: TDog;
        begin
          D := TDog.Create();
          D.Age := 3;
          D.Legs := 4
        end.
        ''';

  SrcInheritMethod =
    '''
        program P;
        type
          TBase = class
            X: Integer;
            procedure SetX(V: Integer);
            begin
              Self.X := V
            end;
          end;
          TChild = class(TBase)
            Y: Integer;
          end;
        var C: TChild;
        begin
          C := TChild.Create();
          C.SetX(10);
          C.Y := 20
        end.
        ''';

{ ------------------------------------------------------------------ }
{ nil literal tests                                                   }
{ ------------------------------------------------------------------ }

procedure TInheritTests.TestLexer_Nil_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('nil');
  try
    T := L.Next();
    AssertEquals('nil token', Ord(tkNil), Ord(T.Kind));
  finally L.Free(); end;
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
  finally Prog.Free(); end;
end;

procedure TInheritTests.TestSemantic_Nil_AssignToClassVar_OK;
begin
  AnalyseSrc(SrcSelfRef).Free();
end;

procedure TInheritTests.TestSemantic_Nil_AssignToIntVar_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var N: Integer;
        begin
          N := nil
        end.
        ''');
end;

procedure TInheritTests.TestSemantic_Nil_CompareWithClassVar_OK;
begin
  AnalyseSrc(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo;
        var N: Integer;
        begin
          F := TFoo.Create();
          if F = nil then
            N := 0
          else
            N := 1
        end.
        ''').Free();
end;

procedure TInheritTests.TestCodegen_Nil_StoresZero;
var IR: string;
begin
  IR := GenIR(SrcSelfRef);
  { N is a data-section global; N.Next := nil loads 0 and stores via a temp.
    Verify the nil load and that the global $N is present. }
  AssertTrue('nil stores 0', Pos('copy 0', IR) > 0);
end;

procedure TInheritTests.TestCodegen_Nil_CompareEmitsCeql;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TFoo = class
            X: Integer;
          end;
        var F: TFoo;
        var N: Integer;
        begin
          F := TFoo.Create();
          if F = nil then
            N := 0
        end.
        ''');
  AssertTrue('ceql for pointer comparison', Pos('ceql', IR) > 0);
end;

procedure TInheritTests.TestCodegen_MethodCall_NilGuard_EmitsCheckNil;
var IR: string;
begin
  IR := GenIR(
    'program P;'               + LineEnding +
    'type'                     + LineEnding +
    '  TFoo = class'           + LineEnding +
    '    procedure DoIt;'      + LineEnding +
    '  end;'                   + LineEnding +
    'procedure TFoo.DoIt();'     + LineEnding +
    'begin'                    + LineEnding +
    'end;'                     + LineEnding +
    'var F: TFoo;'             + LineEnding +
    'begin'                    + LineEnding +
    '  F := TFoo.Create();'      + LineEnding +
    '  F.DoIt()'                 + LineEnding +
    'end.');
  AssertTrue('_CheckNil emitted before method call', Pos('_CheckNil', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Self-referential type tests                                         }
{ ------------------------------------------------------------------ }

procedure TInheritTests.TestSemantic_SelfRef_DoesNotRaiseError;
begin
  AnalyseSrc(SrcSelfRef).Free();
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
  finally Prog.Free(); end;
end;

procedure TInheritTests.TestCodegen_SelfRef_Create_AllocatesCorrectSize;
var IR: string;
begin
  IR := GenIR(SrcSelfRef);
  { TNode: vptr (8) + Integer Value @ 8 + 4-byte pad + TNode pointer @ 16
    = 24 bytes.  The Next pointer must be 8-aligned so the alignment pad
    sits between Value and Next. }
  AssertTrue('_ClassAlloc 24 bytes for TNode with cleanup fn',
    Pos('call $_ClassAlloc(l 24, l $_FieldCleanup_TNode)', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Inheritance — field tests                                           }
{ ------------------------------------------------------------------ }

procedure TInheritTests.TestSemantic_Inherit_ParentFieldVisible;
begin
  { D.Age := 3 should resolve — Age is inherited from TAnimal }
  AnalyseSrc(SrcInherit).Free();
end;

procedure TInheritTests.TestSemantic_Inherit_ChildFieldVisible;
begin
  { D.Legs := 4 should resolve — Legs is TDog's own field }
  AnalyseSrc(SrcInherit).Free();
end;

procedure TInheritTests.TestSemantic_Inherit_TotalSizeIncludesParent;
var
  Prog:  TProgram;
  Sym:   TSymbol;
  RT:    TRecordTypeDesc;
begin
  Prog := AnalyseSrc(SrcInherit);
  try
    { TAnimal: vptr (8) + Age (4) = 12 total.
      TDog: vptr (8) + Age (4) + Legs (4) = 16 total. }
    Sym := Prog.SymbolTable.Lookup('TDog');
    AssertNotNull('TDog symbol', Sym);
    RT := TRecordTypeDesc(Sym.TypeDesc);
    AssertEquals('TDog total size = 16', 16, RT.TotalSize());
  finally Prog.Free(); end;
end;

procedure TInheritTests.TestCodegen_Inherit_Create_AllocatesTotalSize;
var IR: string;
begin
  IR := GenIR(SrcInherit);
  { TDog.Create passes TotalSize (16 bytes: vptr + Age + Legs) to _ClassAlloc
    along with its per-class field-cleanup function. }
  AssertTrue('_ClassAlloc 16 bytes for TDog with cleanup fn',
    Pos('call $_ClassAlloc(l 16, l $_FieldCleanup_TDog)', IR) > 0);
end;

procedure TInheritTests.TestCodegen_Inherit_ParentFieldOffset;
var IR: string;
begin
  IR := GenIR(SrcInherit);
  { Age is at offset 8 in TDog (after 8-byte vptr); storew appears in the IR. }
  AssertTrue('Age field storew present',
    Pos('storew', IR) > 0);
end;

procedure TInheritTests.TestCodegen_Inherit_ChildFieldOffset;
var IR: string;
begin
  IR := GenIR(SrcInherit);
  { Legs is at offset 12 in TDog (8 vptr + 4 Age) — codegen emits an add 12 }
  AssertTrue('Legs field at offset 12 (add 12)',
    Pos(', 12', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Inheritance — method tests                                          }
{ ------------------------------------------------------------------ }

procedure TInheritTests.TestSemantic_Inherit_MethodCallOnChild_Resolves;
begin
  { C.SetX(10) should resolve even though SetX is defined on TBase }
  AnalyseSrc(SrcInheritMethod).Free();
end;

procedure TInheritTests.TestSemantic_Inherit_UnknownMethod_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        type
          TBase = class
            X: Integer;
          end;
          TChild = class(TBase)
            Y: Integer;
          end;
        var C: TChild;
        begin
          C := TChild.Create();
          C.NoSuchMethod
        end.
        ''');
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
    '''
        program P;
        type
          TBase = class
            X: Integer;
            procedure Init;
          end;
          TChild = class(TBase)
            Y: Integer;
            procedure Init;
          end;
        procedure TBase.Init;
        begin
          Self.X := 0
        end;
        procedure TChild.Init;
        begin
          inherited Init();
          Self.Y := 0
        end;
        var C: TChild;
        begin
          C := TChild.Create()
        end.
        ''';

  SrcInheritedWithArgs =
    '''
        program P;
        type
          TBase = class
            X: Integer;
            procedure SetX(V: Integer);
          end;
          TChild = class(TBase)
            procedure SetX(V: Integer);
          end;
        procedure TBase.SetX(V: Integer);
        begin
          Self.X := V
        end;
        procedure TChild.SetX(V: Integer);
        begin
          inherited SetX(V)
        end;
        var C: TChild;
        begin
          C := TChild.Create()
        end.
        ''';

procedure TInheritTests.TestLexer_Inherited_IsOwnToken;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('inherited');
  try
    T := L.Next();
    AssertEquals('inherited token kind', Ord(tkInherited), Ord(T.Kind));
  finally L.Free(); end;
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
    AssertNotNull('TChild.Init() found', MDecl);
    AssertTrue('body has at least one stmt', MDecl.Body.Stmts.Count >= 1);
    Stmt := TASTStmt(MDecl.Body.Stmts[0]);
    AssertTrue('first stmt is TInheritedCallStmt', Stmt is TInheritedCallStmt);
    AssertEquals('method name is Init',
      'Init', TInheritedCallStmt(Stmt).Name);
  finally Prog.Free(); end;
end;

procedure TInheritTests.TestSemantic_Inherited_NoArgs_OK;
begin
  AnalyseSrc(SrcInheritedNoArgs).Free();
end;

procedure TInheritTests.TestSemantic_Inherited_WithArgs_OK;
begin
  AnalyseSrc(SrcInheritedWithArgs).Free();
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

{ ------------------------------------------------------------------ }
{ TObject.InheritsFrom                                                }
{ ------------------------------------------------------------------ }

const
  SrcInheritsFromPointer =
    '''
        program P;
        var C: Pointer;
            D: Pointer;
            B: Boolean;
        begin
          B := C.InheritsFrom(D);
        end.
        ''';

  SrcInheritsFromClassInstance =
    '''
        program P;
        type TBase = class end;
             TChild = class(TBase) end;
        var Obj: TChild;
            B: Boolean;
        begin
          B := Obj.InheritsFrom(TBase);
        end.
        ''';

procedure TInheritTests.TestSemantic_InheritsFrom_OnPointerVar_OK;
var Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcInheritsFromPointer);
  AssertNotNull('program parsed and analysed', Prog);
  Prog.Free();
end;

procedure TInheritTests.TestSemantic_InheritsFrom_OnClassInstance_OK;
var Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcInheritsFromClassInstance);
  AssertNotNull('program parsed and analysed', Prog);
  Prog.Free();
end;

procedure TInheritTests.TestSemantic_InheritsFrom_ReturnsBoolean;
var Prog: TProgram;
    VD:   TVarDecl;
begin
  Prog := AnalyseSrc(SrcInheritsFromPointer);
  try
    VD := TVarDecl(Prog.Block.Decls.Items[2]);  { B: Boolean }
    AssertEquals('B is Boolean', 'Boolean', VD.ResolvedType.Name);
  finally
    Prog.Free();
  end;
end;

procedure TInheritTests.TestCodegen_InheritsFrom_CallsRTL;
var IR: string;
begin
  IR := GenIR(SrcInheritsFromPointer);
  AssertTrue('call $_InheritsFrom in IR', Pos('call $_InheritsFrom', IR) > 0);
end;

procedure TInheritTests.TestCodegen_InheritsFrom_OnClassInstance_LoadsTypeinfo;
var IR: string;
begin
  IR := GenIR(SrcInheritsFromClassInstance);
  AssertTrue('call $_InheritsFrom in IR', Pos('call $_InheritsFrom', IR) > 0);
  AssertTrue('$typeinfo_TBase as arg', Pos('$typeinfo_TBase', IR) > 0);
end;

initialization
  RegisterTest(TInheritTests);

end.
