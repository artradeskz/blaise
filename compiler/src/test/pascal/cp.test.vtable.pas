{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.vtable;

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

type
  TVTableTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    function IRContains(const AIR, AFragment: string): Boolean;
    procedure AnalyseExpectOK(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Lexer                                                                }
    { ------------------------------------------------------------------ }
    procedure TestLexer_Virtual_Keyword;
    procedure TestLexer_Override_Keyword;

    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_VirtualMethod;
    procedure TestParse_OverrideMethod;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_SubtypeAssign_OK;
    procedure TestSemantic_VirtualMethod_HasSlot;
    procedure TestSemantic_OverrideMethod_InheritsSlot;

    { ------------------------------------------------------------------ }
    { Code generation — vtable data                                        }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_VTableData_Emitted;
    procedure TestCodegen_VTable_ContainsMethodPtr;
    procedure TestCodegen_VTable_Subclass_OverridesEntry;
    procedure TestCodegen_VTable_Subclass_InheritsParentEntry;

    { ------------------------------------------------------------------ }
    { Code generation — object layout                                      }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_Constructor_StoresVTablePtr;
    procedure TestCodegen_MallocSize_IncludesVPtr;
    procedure TestCodegen_FieldOffset_ShiftedByEight;

    { ------------------------------------------------------------------ }
    { Code generation — dispatch                                           }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_VirtualCall_IsIndirect;
    procedure TestCodegen_StaticMethod_IsDirectCall;

    { ------------------------------------------------------------------ }
    { Abstract methods                                                     }
    { ------------------------------------------------------------------ }
    procedure TestParse_AbstractMethod_IsAbstract;
    procedure TestParse_AbstractMethod_IsVirtual;
    procedure TestSemantic_AbstractClass_CannotInstantiate;
    procedure TestSemantic_AbstractMethod_NoBody_OK;
    procedure TestSemantic_ConcreteSubclass_OK;
    procedure TestSemantic_ConcreteSubclass_MissingOverride_Error;
    procedure TestCodegen_AbstractMethod_StubInVTable;
    procedure TestCodegen_AbstractClass_VTableHasStub;
    procedure TestCodegen_ConcreteSubclass_OverridesAbstract;
    { Abstract class that also declares an interface — itab slots for
      the abstract methods must reference $_AbstractMethodError so the
      IR links even though the methods have no body on the abstract
      class.  The class is never instantiated, so the stub is
      statically unreachable. }
    procedure TestCodegen_AbstractClassWithInterface_ItabHasStub;
  end;

implementation

const
  SrcBase =
    '''
        program Prg;
        type
          TAnimal = class
            procedure Speak; virtual; begin end;
          end;
        begin end.
        ''';

  SrcInherit =
    '''
        program Prg;
        type
          TAnimal = class
            procedure Speak; virtual; begin end;
          end;
          TDog = class(TAnimal)
            procedure Speak; override; begin end;
          end;
        begin end.
        ''';

  SrcBaseWithField =
    '''
        program Prg;
        type
          TPoint = class
            X: Integer;
            procedure Reset; virtual; begin end;
          end;
        var P: TPoint;
        begin
          P := TPoint.Create();
          P.X := 5
        end.
        ''';

  SrcStaticMethod =
    '''
        program Prg;
        type
          TFoo = class
            procedure Bar; begin end;
          end;
        var F: TFoo;
        begin
          F := TFoo.Create();
          F.Bar()
        end.
        ''';

  SrcVirtualCall =
    '''
        program Prg;
        type
          TAnimal = class
            procedure Speak; virtual; begin end;
          end;
        var A: TAnimal;
        begin
          A := TAnimal.Create();
          A.Speak()
        end.
        ''';

function TVTableTests.ParseSrc(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  Result := P.Parse();
  P.Free();
  L.Free();
end;

function TVTableTests.GenIR(const ASrc: string): string;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  CG: TCodeGenQBE;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
  finally
    A.Free();
  end;
  CG := TCodeGenQBE.Create();
  try
    CG.Generate(Pr);
    Result := CG.GetOutput();
  finally
    CG.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

function TVTableTests.IRContains(const AIR, AFragment: string): Boolean;
begin
  Result := Pos(AFragment, AIR) > 0;
end;

procedure TVTableTests.AnalyseExpectOK(const ASrc: string);
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);  { must not raise }
  finally
    A.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Lexer                                                                }
{ ------------------------------------------------------------------ }

procedure TVTableTests.TestLexer_Virtual_Keyword;
var
  L: TLexer;
  T: TToken;
begin
  L := TLexer.Create('virtual');
  try
    T := L.Next();
    AssertEquals('virtual token', Ord(tkVirtual), Ord(T.Kind));
  finally
    L.Free();
  end;
end;

procedure TVTableTests.TestLexer_Override_Keyword;
var
  L: TLexer;
  T: TToken;
begin
  L := TLexer.Create('override');
  try
    T := L.Next();
    AssertEquals('override token', Ord(tkOverride), Ord(T.Kind));
  finally
    L.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser                                                               }
{ ------------------------------------------------------------------ }

procedure TVTableTests.TestParse_VirtualMethod;
var
  Prog:  TProgram;
  CDef:  TClassTypeDef;
  MDecl: TMethodDecl;
begin
  Prog  := ParseSrc(SrcBase);
  CDef  := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
  MDecl := TMethodDecl(CDef.Methods[0]);
  AssertTrue('method is virtual', MDecl.IsVirtual);
  Prog.Free();
end;

procedure TVTableTests.TestParse_OverrideMethod;
var
  Prog:  TProgram;
  CDef:  TClassTypeDef;
  MDecl: TMethodDecl;
begin
  Prog  := ParseSrc(SrcInherit);
  CDef  := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[1]).Def);
  MDecl := TMethodDecl(CDef.Methods[0]);
  AssertTrue('method is override', MDecl.IsOverride);
  Prog.Free();
end;

{ ------------------------------------------------------------------ }
{ Semantic                                                             }
{ ------------------------------------------------------------------ }

procedure TVTableTests.TestSemantic_SubtypeAssign_OK;
var
  Src: string;
begin
  Src :=
    '''
        program Prg;
        type
          TBase = class
          end;
          TDerived = class(TBase)
          end;
        var B: TBase;
        var D: TDerived;
        begin
          D := TDerived.Create();
          B := D
        end.
        ''';
  AnalyseExpectOK(Src);
end;

procedure TVTableTests.TestSemantic_VirtualMethod_HasSlot;
var
  Prog:  TProgram;
  L:     TLexer;
  P:     TParser;
  A:     TSemanticAnalyser;
  CDef:  TClassTypeDef;
  MDecl: TMethodDecl;
begin
  L    := TLexer.Create(SrcBase);
  P    := TParser.Create(L);
  Prog := P.Parse();
  A    := TSemanticAnalyser.Create();
  try
    A.Analyse(Prog);
  finally
    A.Free();
  end;
  CDef  := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
  MDecl := TMethodDecl(CDef.Methods[0]);
  AssertTrue('virtual method gets slot >= 0', MDecl.VTableSlot >= 0);
  Prog.Free();
  P.Free();
  L.Free();
end;

procedure TVTableTests.TestSemantic_OverrideMethod_InheritsSlot;
var
  Prog:   TProgram;
  L:      TLexer;
  P:      TParser;
  A:      TSemanticAnalyser;
  CBase:  TClassTypeDef;
  CDeriv: TClassTypeDef;
  MBase:  TMethodDecl;
  MDeriv: TMethodDecl;
begin
  L    := TLexer.Create(SrcInherit);
  P    := TParser.Create(L);
  Prog := P.Parse();
  A    := TSemanticAnalyser.Create();
  try
    A.Analyse(Prog);
  finally
    A.Free();
  end;
  CBase  := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
  CDeriv := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[1]).Def);
  MBase  := TMethodDecl(CBase.Methods[0]);
  MDeriv := TMethodDecl(CDeriv.Methods[0]);
  AssertEquals('override inherits same slot', MBase.VTableSlot, MDeriv.VTableSlot);
  Prog.Free();
  P.Free();
  L.Free();
end;

{ ------------------------------------------------------------------ }
{ Code generation — vtable data                                        }
{ ------------------------------------------------------------------ }

procedure TVTableTests.TestCodegen_VTableData_Emitted;
var
  IR: string;
begin
  IR := GenIR(SrcBase);
  AssertTrue('vtable data section exists',
    IRContains(IR, 'data $vtable_TAnimal'));
end;

procedure TVTableTests.TestCodegen_VTable_ContainsMethodPtr;
var
  IR: string;
begin
  IR := GenIR(SrcBase);
  AssertTrue('vtable contains method pointer',
    IRContains(IR, '$TAnimal_Speak'));
end;

procedure TVTableTests.TestCodegen_VTable_Subclass_OverridesEntry;
var
  IR: string;
begin
  IR := GenIR(SrcInherit);
  AssertTrue('subclass vtable has overriding method',
    IRContains(IR, '$TDog_Speak'));
  AssertTrue('subclass vtable data section exists',
    IRContains(IR, 'data $vtable_TDog'));
end;

procedure TVTableTests.TestCodegen_VTable_Subclass_InheritsParentEntry;
var
  SrcWith2Virtuals: string;
  IR: string;
begin
  SrcWith2Virtuals :=
    '''
        program Prg;
        type
          TAnimal = class
            procedure Speak; virtual; begin end;
            procedure Move; virtual; begin end;
          end;
          TDog = class(TAnimal)
            procedure Speak; override; begin end;
          end;
        begin end.
        ''';
  IR := GenIR(SrcWith2Virtuals);
  AssertTrue('subclass vtable inherits parent Move method',
    IRContains(IR, '$TAnimal_Move'));
end;

{ ------------------------------------------------------------------ }
{ Code generation — object layout                                      }
{ ------------------------------------------------------------------ }

procedure TVTableTests.TestCodegen_Constructor_StoresVTablePtr;
var
  IR: string;
begin
  { SrcVirtualCall constructs TAnimal.Create — vtable ptr must be stored }
  IR := GenIR(SrcVirtualCall);
  AssertTrue('constructor stores vtable ptr',
    IRContains(IR, 'storel $vtable_TAnimal'));
end;

procedure TVTableTests.TestCodegen_MallocSize_IncludesVPtr;
var
  IR: string;
begin
  { TPoint has one Integer field (4 bytes) + vptr (8 bytes) = 12 bytes.
    _ClassAlloc receives TotalSize and a cleanup-fn pointer; the hidden
    refcount header is added internally and does not appear in the size. }
  IR := GenIR(SrcBaseWithField);
  AssertTrue('_ClassAlloc includes vptr size',
    IRContains(IR, 'call $_ClassAlloc(l 12, l $_FieldCleanup_'));
end;

procedure TVTableTests.TestCodegen_FieldOffset_ShiftedByEight;
var
  IR: string;
begin
  { With vptr at offset 0, first field is at offset 8 not 0 }
  IR := GenIR(SrcBaseWithField);
  AssertTrue('field offset is 8 (after vptr)',
    IRContains(IR, ', 8'));
end;

{ ------------------------------------------------------------------ }
{ Code generation — dispatch                                           }
{ ------------------------------------------------------------------ }

procedure TVTableTests.TestCodegen_VirtualCall_IsIndirect;
var
  IR: string;
begin
  IR := GenIR(SrcVirtualCall);
  { Virtual dispatch loads function pointer from vtable and calls via register }
  AssertTrue('virtual call loads vtable',
    IRContains(IR, 'loadl'));
  AssertTrue('virtual call is indirect (call via temp)',
    IRContains(IR, 'call %'));
end;

procedure TVTableTests.TestCodegen_StaticMethod_IsDirectCall;
var
  IR: string;
begin
  IR := GenIR(SrcStaticMethod);
  AssertTrue('static method call is direct',
    IRContains(IR, 'call $TFoo_Bar'));
end;

{ ------------------------------------------------------------------ }
{ Abstract methods                                                     }
{ ------------------------------------------------------------------ }

procedure TVTableTests.TestParse_AbstractMethod_IsAbstract;
var
  L:    TLexer;
  P:    TParser;
  Prog: TProgram;
  TD:   TTypeDecl;
  CD:   TClassTypeDef;
  M:    TMethodDecl;
begin
  L := TLexer.Create(
    '''
    program Prg;
    type
      TShape = class
        procedure Draw; virtual; abstract;
      end;
    begin end.
    ''');
  P    := TParser.Create(L);
  Prog := P.Parse();
  try
    TD := TTypeDecl(Prog.Block.TypeDecls.Items[0]);
    CD := TClassTypeDef(TD.Def);
    M  := TMethodDecl(CD.Methods.Items[0]);
    AssertTrue('IsAbstract set', M.IsAbstract);
  finally
    Prog.Free(); P.Free(); L.Free();
  end;
end;

procedure TVTableTests.TestParse_AbstractMethod_IsVirtual;
var
  L:    TLexer;
  P:    TParser;
  Prog: TProgram;
  TD:   TTypeDecl;
  CD:   TClassTypeDef;
  M:    TMethodDecl;
begin
  L := TLexer.Create(
    '''
    program Prg;
    type
      TShape = class
        procedure Draw; virtual; abstract;
      end;
    begin end.
    ''');
  P    := TParser.Create(L);
  Prog := P.Parse();
  try
    TD := TTypeDecl(Prog.Block.TypeDecls.Items[0]);
    CD := TClassTypeDef(TD.Def);
    M  := TMethodDecl(CD.Methods.Items[0]);
    AssertTrue('IsVirtual set on abstract', M.IsVirtual);
  finally
    Prog.Free(); P.Free(); L.Free();
  end;
end;

procedure TVTableTests.TestSemantic_AbstractClass_CannotInstantiate;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  GotError: Boolean;
begin
  GotError := False;
  L := TLexer.Create(
    '''
    program Prg;
    type
      TShape = class
        procedure Draw; virtual; abstract;
      end;
    var S: TShape;
    begin
      S := TShape.Create()
    end.
    ''');
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    try
      A.Analyse(Pr);
    except
      on E: ESemanticError do GotError := True;
    end;
  finally
    A.Free(); Pr.Free(); P.Free(); L.Free();
  end;
  AssertTrue('abstract class cannot be instantiated', GotError);
end;

procedure TVTableTests.TestSemantic_AbstractMethod_NoBody_OK;
begin
  AnalyseExpectOK(
    '''
    program Prg;
    type
      TShape = class
        procedure Draw; virtual; abstract;
      end;
    begin end.
    ''');
end;

procedure TVTableTests.TestSemantic_ConcreteSubclass_OK;
begin
  AnalyseExpectOK(
    '''
    program Prg;
    type
      TShape = class
        procedure Draw; virtual; abstract;
      end;
      TCircle = class(TShape)
        procedure Draw; override; begin end;
      end;
    var C: TCircle;
    begin
      C := TCircle.Create()
    end.
    ''');
end;

procedure TVTableTests.TestSemantic_ConcreteSubclass_MissingOverride_Error;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  GotError: Boolean;
begin
  GotError := False;
  L := TLexer.Create(
    '''
    program Prg;
    type
      TShape = class
        procedure Draw; virtual; abstract;
      end;
      TCircle = class(TShape)
        { Draw not overridden — should error on instantiation }
      end;
    var C: TCircle;
    begin
      C := TCircle.Create()
    end.
    ''');
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    try
      A.Analyse(Pr);
    except
      on E: ESemanticError do GotError := True;
    end;
  finally
    A.Free(); Pr.Free(); P.Free(); L.Free();
  end;
  AssertTrue('missing override of abstract raises error', GotError);
end;

procedure TVTableTests.TestCodegen_AbstractMethod_StubInVTable;
var IR: string;
begin
  IR := GenIR(
    '''
    program Prg;
    type
      TShape = class
        procedure Draw; virtual; abstract;
      end;
    begin end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  { Abstract method vtable slot must reference the runtime abort stub
    ($_AbstractMethodError, defined in blaise_arc.pas), not a real body }
  AssertTrue('abstract stub in IR', IRContains(IR, '_AbstractMethodError'));
end;

procedure TVTableTests.TestCodegen_AbstractClass_VTableHasStub;
var IR: string;
begin
  IR := GenIR(
    '''
    program Prg;
    type
      TBase = class
        procedure Foo; virtual; abstract;
        procedure Bar; virtual; abstract;
      end;
    begin end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('vtable emitted', IRContains(IR, 'vtable_TBase'));
  AssertTrue('abstract stub present', IRContains(IR, '_AbstractMethodError'));
end;

procedure TVTableTests.TestCodegen_ConcreteSubclass_OverridesAbstract;
var IR: string;
begin
  IR := GenIR(
    '''
    program Prg;
    type
      TShape = class
        procedure Draw; virtual; abstract;
      end;
      TCircle = class(TShape)
        procedure Draw; override; begin end;
      end;
    begin end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  { TCircle vtable should point to TCircle_Draw, not the abstract stub }
  AssertTrue('TCircle_Draw in IR', IRContains(IR, 'TCircle_Draw'));
  AssertTrue('TCircle vtable in IR', IRContains(IR, 'vtable_TCircle'));
end;

procedure TVTableTests.TestCodegen_AbstractClassWithInterface_ItabHasStub;
var IR: string;
begin
  IR := GenIR(
    '''
    program Prg;
    type
      IShape = interface
        procedure Draw;
      end;
      TShape = class(TObject, IShape)
        procedure Draw; virtual; abstract;
      end;
    begin end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('TShape itab emitted', IRContains(IR, 'itab_TShape_IShape'));
  { The itab slot for Draw must reference the runtime stub, not the
    nonexistent TShape_Draw symbol. }
  AssertTrue('itab references stub', IRContains(IR, '_AbstractMethodError'));
end;

initialization
  RegisterTest(TVTableTests);

end.
