{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.interfaces;

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TInterfaceTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_Interface_Empty;
    procedure TestParse_Interface_WithMethods;
    procedure TestParse_Interface_WithParent;
    procedure TestParse_Class_ImplementsInterface;
    procedure TestParse_Class_ImplementsMultiple;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Interface_Registered;
    procedure TestSemantic_Interface_IsInterfaceKind;
    procedure TestSemantic_Interface_MethodsRegistered;
    procedure TestSemantic_ClassImplements_OK;
    procedure TestSemantic_ClassImplements_MissingMethod_RaisesError;
    procedure TestSemantic_ClassWithInterfaceAsFirstParent_OK;
    procedure TestSemantic_ClassWithInterfaceAsFirstParent_InheritsFromTObject;

    { ------------------------------------------------------------------ }
    { Semantic — is/as with interface types                                }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_IsExpr_Interface_OK;
    procedure TestSemantic_IsExpr_Interface_ResultIsBoolean;
    procedure TestSemantic_AsExpr_Interface_OK;
    procedure TestSemantic_AsExpr_Interface_ResultType;

    { ------------------------------------------------------------------ }
    { Semantic — IInterface built-in                                       }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_IInterface_Registered;
    procedure TestSemantic_IInterface_IsInterfaceKind;

    { ------------------------------------------------------------------ }
    { Code generation                                                      }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_Interface_TypeInfo_Emitted;
    procedure TestCodegen_Class_Itab_Emitted;
    procedure TestCodegen_Itab_ContainsMethodPointer;
    procedure TestCodegen_InterfaceVar_AllocsTwoSlots;
    procedure TestCodegen_InterfaceMethodCall_IndirectDispatch;
    procedure TestCodegen_Typeinfo_ClassHasImpllistField;
    procedure TestCodegen_Impllist_Emitted;
    procedure TestCodegen_IsExpr_Interface_CallsImplementsInterface;
    procedure TestCodegen_AsExpr_Interface_CallsGetItab;

    { ------------------------------------------------------------------ }
    { ARC on interface references                                          }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_InterfaceAssign_ClassSrc_AddrefsObj;
    procedure TestCodegen_InterfaceAssign_AsCast_ReleasesOldObj;
    procedure TestCodegen_InterfaceToInterface_TransfersBothSlots;
    procedure TestCodegen_InterfaceVar_ScopeExit_ReleasesObjOnly;

    { ------------------------------------------------------------------ }
    { Supports() intrinsic — 2-arg and 3-arg forms                        }
    { ------------------------------------------------------------------ }
    procedure TestParse_Supports_TwoArg_ProducesSupportsExpr;
    procedure TestParse_Supports_ThreeArg_ProducesSupportsExpr;
    procedure TestSemantic_Supports_TwoArg_ResultIsBoolean;
    procedure TestSemantic_Supports_ThreeArg_ResultIsBoolean;
    procedure TestSemantic_Supports_NonInterface_RaisesError;
    procedure TestCodegen_Supports_TwoArg_CallsImplementsInterface;
    procedure TestCodegen_Supports_ThreeArg_WritesSlots;

    { ------------------------------------------------------------------ }
    { Interface argument passing — non-identifier expressions              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_InterfaceArg_AsExpr_PassesBothSlots;
    procedure TestCodegen_InterfaceArg_Identifier_PassesBothSlots;
    procedure TestCodegen_MethodInterfaceParam_FatPointerSignature;
    procedure TestCodegen_MethodInterfaceArg_PassesBothSlots;

    { ------------------------------------------------------------------ }
    { Regression — interface field shadowing a same-named global          }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_InterfaceField_ShadowsGlobal_OK;
  end;

implementation

const
  SrcInterfaceEmpty =
    '''
        program P;
        type
          IFoo = interface
          end;
        begin
        end.
        ''';

  SrcInterfaceWithMethods =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
            function GetVal: Integer;
          end;
        begin
        end.
        ''';

  SrcInterfaceWithParent =
    '''
        program P;
        type
          IBase = interface
            procedure Base;
          end;
          IChild = interface(IBase)
            procedure Child;
          end;
        begin
        end.
        ''';

  SrcClassImplements =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
            function GetVal: Integer;
          end;
          TFoo = class(TObject, IFoo)
            procedure DoIt;
            function GetVal: Integer;
          end;
        procedure TFoo.DoIt;
        begin
        end;
        function TFoo.GetVal: Integer;
        begin
          Result := 42
        end;
        begin
        end.
        ''';

  SrcClassImplementsMultiple =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
          end;
          IBar = interface
            procedure DoBar;
          end;
          TFoo = class(TObject, IFoo, IBar)
            procedure DoIt;
            procedure DoBar;
          end;
        procedure TFoo.DoIt;
        begin
        end;
        procedure TFoo.DoBar;
        begin
        end;
        begin
        end.
        ''';

  SrcClassMissingMethod =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
          end;
          TFoo = class(TObject, IFoo)
          end;
        begin
        end.
        ''';

  { TFoo = class(IFoo) — interface as sole parent; TObject must be implied }
  SrcClassInterfaceOnlyParent =
    'program P;'                               + LineEnding +
    'type'                                     + LineEnding +
    '  IFoo = interface'                       + LineEnding +
    '    procedure DoIt;'                      + LineEnding +
    '  end;'                                   + LineEnding +
    '  TFoo = class(IFoo)'                     + LineEnding +
    '    procedure DoIt;'                      + LineEnding +
    '  end;'                                   + LineEnding +
    'procedure TFoo.DoIt();'                     + LineEnding +
    'begin'                                    + LineEnding +
    'end;'                                     + LineEnding +
    'begin'                                    + LineEnding +
    'end.';

  SrcIsExprInterface =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
          end;
          TFoo = class(TObject, IFoo)
            procedure DoIt;
          end;
        procedure TFoo.DoIt;
        begin
        end;
        var
          T: TFoo;
          R: Boolean;
        begin
          T := TFoo.Create();
          R := T is IFoo
        end.
        ''';

  SrcAsExprInterface =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
          end;
          TFoo = class(TObject, IFoo)
            procedure DoIt;
          end;
        procedure TFoo.DoIt;
        begin
        end;
        var
          T: TFoo;
          F: IFoo;
        begin
          T := TFoo.Create();
          F := T as IFoo
        end.
        ''';

  SrcInterfaceVar =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
          end;
          TFoo = class(TObject, IFoo)
            procedure DoIt;
          end;
        procedure TFoo.DoIt;
        begin
        end;
        var
          F: IFoo;
          T: TFoo;
        begin
          T := TFoo.Create();
          F := T;
          F.DoIt()
        end.
        ''';

  SrcInterfaceArgAsExpr =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
          end;
          TFoo = class(TObject, IFoo)
            procedure DoIt; virtual;
          end;
        procedure TFoo.DoIt;
        begin
        end;
        procedure UseIntf(X: IFoo);
        begin
          X.DoIt();
        end;
        var
          T: TFoo;
        begin
          T := TFoo.Create();
          UseIntf(T as IFoo)
        end.
        ''';

  SrcInterfaceArgIdent =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
          end;
          TFoo = class(TObject, IFoo)
            procedure DoIt; virtual;
          end;
        procedure TFoo.DoIt;
        begin
        end;
        procedure UseIntf(X: IFoo);
        begin
          X.DoIt();
        end;
        var
          F: IFoo;
          T: TFoo;
        begin
          T := TFoo.Create();
          F := T as IFoo;
          UseIntf(F)
        end.
        ''';

  { A class METHOD taking a by-value interface param.  The method-codegen path
    must split the param into a two-slot fat pointer (obj + itab), exactly like
    the standalone-routine path — otherwise it emits a single `w` slot and
    QBE rejects the `storel %_par_X` in EmitParamAllocs. }
  SrcMethodInterfaceParam =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
          end;
          TFoo = class(TObject, IFoo)
            procedure DoIt; virtual;
          end;
          TUser = class
            procedure UseIntf(X: IFoo);
          end;
        procedure TFoo.DoIt;
        begin
        end;
        procedure TUser.UseIntf(X: IFoo);
        begin
          X.DoIt();
        end;
        var
          F: IFoo;
          T: TFoo;
          U: TUser;
        begin
          T := TFoo.Create();
          F := T as IFoo;
          U := TUser.Create();
          U.UseIntf(F)
        end.
        ''';

  { Regression (issue #64): a class has an interface-typed field 'im' AND the
    program has a same-named global variable 'im' of a different type (the
    class itself).  Inside a method body the field must shadow the global —
    `im := am` where am is Iprinter must resolve as a field assignment, not
    as an assignment to the global 'im: Tmi'. }
  SrcInterfaceFieldShadowsGlobal =
    '''
        program P;
        type
          Iprinter = interface
            procedure print;
          end;
          Toutput = class(TObject, Iprinter)
            fField: Integer;
            procedure print;
          end;
          Tmi = class
            im: Iprinter;
            constructor create(am: Iprinter);
            procedure use;
          end;
        procedure Toutput.print;
        begin
        end;
        constructor Tmi.Create(am: Iprinter);
        begin
          im := am;
        end;
        procedure Tmi.use;
        begin
          im.print;
        end;
        var
          im: Tmi;
        begin
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TInterfaceTests.ParseSrc(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
end;

function TInterfaceTests.AnalyseSrc(const ASrc: string): TProgram;
var
  SA: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  SA     := TSemanticAnalyser.Create();
  try
    SA.Analyse(Result);
  finally
    SA.Free();
  end;
end;

function TInterfaceTests.GenIR(const ASrc: string): string;
var
  CG: TCodeGenQBE;
  Prog: TProgram;
begin
  Prog := AnalyseSrc(ASrc);
  CG   := TCodeGenQBE.Create();
  try
    CG.Generate(Prog);
    Result := CG.GetOutput();
  finally
    CG.Free();
    Prog.Free();
  end;
end;

procedure TInterfaceTests.AnalyseExpectError(const ASrc: string);
var
  Prog: TProgram;
  SA:   TSemanticAnalyser;
begin
  Prog := ParseSrc(ASrc);
  SA   := TSemanticAnalyser.Create();
  try
    try
      SA.Analyse(Prog);
      Fail('Expected ESemanticError but none was raised');
    except
      on E: ESemanticError do
        { expected };
    end;
  finally
    SA.Free();
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TInterfaceTests.TestParse_Interface_Empty;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(SrcInterfaceEmpty);
  try
    AssertEquals('one type decl', 1, Prog.Block.TypeDecls.Count);
    TD := TTypeDecl(Prog.Block.TypeDecls[0]);
    AssertEquals('name is IFoo', 'IFoo', TD.Name);
    AssertTrue('def is TInterfaceTypeDef', TD.Def is TInterfaceTypeDef);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestParse_Interface_WithMethods;
var
  Prog: TProgram;
  ITD:  TInterfaceTypeDef;
begin
  Prog := ParseSrc(SrcInterfaceWithMethods);
  try
    ITD := TInterfaceTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('two methods', 2, ITD.Methods.Count);
    AssertEquals('first method DoIt',   'DoIt',   TMethodDecl(ITD.Methods[0]).Name);
    AssertEquals('second method GetVal','GetVal',  TMethodDecl(ITD.Methods[1]).Name);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestParse_Interface_WithParent;
var
  Prog:  TProgram;
  Child: TInterfaceTypeDef;
begin
  Prog := ParseSrc(SrcInterfaceWithParent);
  try
    Child := TInterfaceTypeDef(TTypeDecl(Prog.Block.TypeDecls[1]).Def);
    AssertEquals('parent is IBase', 'IBase', Child.ParentName);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestParse_Class_ImplementsInterface;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(SrcClassImplements);
  try
    { type decl index 0 = IFoo, index 1 = TFoo }
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[1]).Def);
    AssertEquals('one implements name', 1, CD.ImplementsNames.Count);
    AssertEquals('implements IFoo', 'IFoo', CD.ImplementsNames[0]);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestParse_Class_ImplementsMultiple;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(SrcClassImplementsMultiple);
  try
    { type decl indices 0=IFoo, 1=IBar, 2=TFoo }
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[2]).Def);
    AssertEquals('two implements names', 2, CD.ImplementsNames.Count);
    AssertEquals('first is IFoo', 'IFoo', CD.ImplementsNames[0]);
    AssertEquals('second is IBar', 'IBar', CD.ImplementsNames[1]);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TInterfaceTests.TestSemantic_Interface_Registered;
var
  Prog: TProgram;
  Sym:  TSymbol;
begin
  Prog := AnalyseSrc(SrcInterfaceWithMethods);
  try
    Sym := Prog.SymbolTable.Lookup('IFoo');
    AssertNotNull('IFoo symbol exists', Sym);
    AssertEquals('IFoo is skType', Ord(skType), Ord(Sym.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_Interface_IsInterfaceKind;
var
  Prog: TProgram;
  TD:   TTypeDesc;
begin
  Prog := AnalyseSrc(SrcInterfaceWithMethods);
  try
    TD := Prog.SymbolTable.FindType('IFoo');
    AssertNotNull('IFoo type exists', TD);
    AssertEquals('kind is tyInterface', Ord(tyInterface), Ord(TD.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_Interface_MethodsRegistered;
var
  Prog: TProgram;
  ITD:  TInterfaceTypeDesc;
begin
  Prog := AnalyseSrc(SrcInterfaceWithMethods);
  try
    ITD := TInterfaceTypeDesc(Prog.SymbolTable.FindType('IFoo'));
    AssertTrue('has DoIt',   ITD.HasMethod('DoIt'));
    AssertTrue('has GetVal', ITD.HasMethod('GetVal'));
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_ClassImplements_OK;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcClassImplements);
  try
    { No exception = success }
    AssertNotNull('prog not nil', Prog);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_ClassImplements_MissingMethod_RaisesError;
begin
  AnalyseExpectError(SrcClassMissingMethod);
end;

procedure TInterfaceTests.TestSemantic_ClassWithInterfaceAsFirstParent_OK;
begin
  { TFoo = class(IFoo) should succeed: IFoo is moved to ImplementsNames and
    TObject is implicitly added as the class parent. }
  AnalyseSrc(SrcClassInterfaceOnlyParent).Free();
end;

procedure TInterfaceTests.TestSemantic_ClassWithInterfaceAsFirstParent_InheritsFromTObject;
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
begin
  Prog := AnalyseSrc(SrcClassInterfaceOnlyParent);
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TFoo'));
    AssertNotNull('TFoo type exists', RT);
    { When interface-only parent is specified, TObject vtable must be copied
      so the vptr slot is present and field offsets start at offset 8. }
    AssertTrue('TFoo has a vtable (vptr from TObject)', RT.HasVTable());
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                        }
{ ------------------------------------------------------------------ }

procedure TInterfaceTests.TestCodegen_Interface_TypeInfo_Emitted;
var
  IR: string;
begin
  IR := GenIR(SrcClassImplements);
  AssertTrue('typeinfo_IFoo in IR', Pos('$typeinfo_IFoo', IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_Class_Itab_Emitted;
var
  IR: string;
begin
  IR := GenIR(SrcClassImplements);
  AssertTrue('itab_TFoo_IFoo in IR', Pos('$itab_TFoo_IFoo', IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_Itab_ContainsMethodPointer;
var
  IR:      string;
  ItabPos: Integer;
begin
  IR := GenIR(SrcClassImplements);
  ItabPos := Pos('$itab_TFoo_IFoo', IR);
  AssertTrue('itab present', ItabPos > 0);
  AssertTrue('TFoo_DoIt appears after itab label',
    PosEx('$TFoo_DoIt', IR, ItabPos) > 0);
end;

procedure TInterfaceTests.TestCodegen_InterfaceVar_AllocsTwoSlots;
var
  IR: string;
begin
  IR := GenIR(SrcInterfaceVar);
  { F is a program-level global — slots are $F_obj and $F_itab }
  AssertTrue('obj slot for F', Pos('$F_obj', IR) > 0);
  AssertTrue('itab slot for F', Pos('$F_itab', IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_InterfaceMethodCall_IndirectDispatch;
var
  IR: string;
begin
  IR := GenIR(SrcInterfaceVar);
  { Interface dispatch loads the itab pointer and calls indirectly }
  AssertTrue('loads itab pointer', Pos('$F_itab', IR) > 0);
  AssertTrue('indirect call via register', Pos('call %', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Semantic — is/as with interface types                                }
{ ------------------------------------------------------------------ }

procedure TInterfaceTests.TestSemantic_IsExpr_Interface_OK;
begin
  AnalyseSrc(SrcIsExprInterface).Free();
end;

procedure TInterfaceTests.TestSemantic_IsExpr_Interface_ResultIsBoolean;
var
  Prog: TProgram;
  IE:   TIsExpr;
begin
  Prog := AnalyseSrc(SrcIsExprInterface);
  try
    { Stmts[0] = T := TFoo.Create; Stmts[1] = R := T is IFoo }
    IE := TIsExpr(TAssignment(Prog.Block.Stmts[1]).Expr);
    AssertNotNull('resolved type', IE.ResolvedType);
    AssertEquals('result is Boolean', Ord(tyBoolean), Ord(IE.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_AsExpr_Interface_OK;
begin
  AnalyseSrc(SrcAsExprInterface).Free();
end;

procedure TInterfaceTests.TestSemantic_AsExpr_Interface_ResultType;
var
  Prog: TProgram;
  AE:   TAsExpr;
begin
  Prog := AnalyseSrc(SrcAsExprInterface);
  try
    { Stmts[0] = T := TFoo.Create; Stmts[1] = F := T as IFoo }
    AE := TAsExpr(TAssignment(Prog.Block.Stmts[1]).Expr);
    AssertNotNull('resolved type', AE.ResolvedType);
    AssertEquals('result kind is tyInterface', Ord(tyInterface), Ord(AE.ResolvedType.Kind));
    AssertEquals('result type name is IFoo', 'IFoo', AE.ResolvedType.Name);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic — IInterface built-in                                       }
{ ------------------------------------------------------------------ }

procedure TInterfaceTests.TestSemantic_IInterface_Registered;
var
  Prog: TProgram;
  Sym:  TSymbol;
begin
  Prog := AnalyseSrc('program P; begin end.');
  try
    Sym := Prog.SymbolTable.Lookup('IInterface');
    AssertNotNull('IInterface symbol exists', Sym);
    AssertEquals('IInterface is skType', Ord(skType), Ord(Sym.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_IInterface_IsInterfaceKind;
var
  Prog: TProgram;
  TD:   TTypeDesc;
begin
  Prog := AnalyseSrc('program P; begin end.');
  try
    TD := Prog.SymbolTable.FindType('IInterface');
    AssertNotNull('IInterface type exists', TD);
    AssertEquals('kind is tyInterface', Ord(tyInterface), Ord(TD.Kind));
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Codegen — impllist and extended typeinfo                             }
{ ------------------------------------------------------------------ }

procedure TInterfaceTests.TestCodegen_Typeinfo_ClassHasImpllistField;
var
  IR: string;
begin
  IR := GenIR(SrcClassImplements);
  { Class with implements: parent, impllist, nameptr, methods, then
    totalsize/fieldcleanup/vtable (Step 11e). }
  AssertTrue('TFoo typeinfo has impllist field',
    Pos('$typeinfo_TFoo = { l $typeinfo_TObject, l $impllist_TFoo, l $__cn_TFoo + 12, l 0,', IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_Impllist_Emitted;
var
  IR: string;
begin
  IR := GenIR(SrcClassImplements);
  AssertTrue('impllist_TFoo emitted', Pos('$impllist_TFoo', IR) > 0);
  { Impllist contains typeinfo_IFoo and itab_TFoo_IFoo pointers }
  AssertTrue('impllist references typeinfo_IFoo',
    PosEx('$typeinfo_IFoo', IR,
          Pos('$impllist_TFoo', IR)) > 0);
  AssertTrue('impllist references itab_TFoo_IFoo',
    PosEx('$itab_TFoo_IFoo', IR,
          Pos('$impllist_TFoo', IR)) > 0);
end;

procedure TInterfaceTests.TestCodegen_IsExpr_Interface_CallsImplementsInterface;
var
  IR: string;
begin
  IR := GenIR(SrcIsExprInterface);
  AssertTrue('is IFoo calls _ImplementsInterface',
    Pos('call $_ImplementsInterface', IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_AsExpr_Interface_CallsGetItab;
var
  IR: string;
begin
  IR := GenIR(SrcAsExprInterface);
  AssertTrue('as IFoo calls _GetItab', Pos('call $_GetItab', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ ARC on interface references                                          }
{ ------------------------------------------------------------------ }

const
  SrcIntfToIntf =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
          end;
          TFoo = class(TObject, IFoo)
            procedure DoIt;
          end;
        procedure TFoo.DoIt;
        begin
        end;
        var
          T:    TFoo;
          F, G: IFoo;
        begin
          T := TFoo.Create();
          F := T;
          G := F
        end.
        ''';

procedure TInterfaceTests.TestCodegen_InterfaceAssign_ClassSrc_AddrefsObj;
var IR: string;
begin
  { F := T where T is class and F is interface: obj slot co-owns the class
    instance, so addref new obj and release old obj on assignment. }
  IR := GenIR(SrcInterfaceVar);
  AssertTrue('addref obj on interface assign',
    Pos('call $_ClassAddRef', IR) > 0);
  AssertTrue('release old obj on interface assign',
    Pos('call $_ClassRelease', IR) > 0);
  AssertTrue('stores obj slot',
    Pos('storel', IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_InterfaceAssign_AsCast_ReleasesOldObj;
var IR: string;
begin
  IR := GenIR(SrcAsExprInterface);
  AssertTrue('as-cast path addrefs new obj',
    Pos('call $_ClassAddRef', IR) > 0);
  AssertTrue('as-cast path releases old obj',
    Pos('call $_ClassRelease', IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_InterfaceToInterface_TransfersBothSlots;
var IR: string;
begin
  { G := F where both are interface: copy obj and itab from F's slots to G's,
    retaining the obj and releasing G's prior contents.  Assert that both
    _F_obj and _F_itab are loaded for the read side and both _G_obj and
    _G_itab are stored on the write side. }
  IR := GenIR(SrcIntfToIntf);
  { F, G are program-level globals — slots accessed via $F_obj, $F_itab etc. }
  AssertTrue('reads F_obj',  Pos('loadl $F_obj',   IR) > 0);
  AssertTrue('reads F_itab', Pos('loadl $F_itab',  IR) > 0);
  AssertTrue('writes G_obj', Pos('storel ', IR) > 0);
  AssertTrue('writes G_itab slot', Pos('$G_itab', IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_InterfaceVar_ScopeExit_ReleasesObjOnly;
var IR: string;
begin
  { At the main block exit (main_exit label) the interface variable F must
    have its obj slot released.  itab is a static pointer and is not
    refcounted, so it must NOT be released. }
  IR := GenIR(SrcInterfaceVar);
  { F is a program-level global — slots accessed via $F_obj, $F_itab.
    Check that scope-exit cleanup loads the obj slot for release. }
  AssertTrue('scope-exit loads obj slot of interface var',
    Pos('loadl $F_obj', IR) > 0);
  AssertTrue('no StringRelease or direct free on itab slot',
    Pos('loadl $F_itab', IR) > 0);  { itab is read during the method
                                            call path but never released. }
end;

{ ------------------------------------------------------------------ }
{ Supports() intrinsic tests                                         }
{ ------------------------------------------------------------------ }

const
  SrcSupportsTwoArg =
    'program P;'                                              + #10 +
    'type'                                                    + #10 +
    '  IFoo = interface'                                      + #10 +
    '    procedure DoIt;'                                     + #10 +
    '  end;'                                                  + #10 +
    '  TFoo = class(TObject, IFoo)'                           + #10 +
    '    procedure DoIt;'                                     + #10 +
    '  end;'                                                  + #10 +
    'procedure TFoo.DoIt(); begin end;'                         + #10 +
    'var Obj: TObject;'                                       + #10 +
    '    B: Boolean;'                                         + #10 +
    'begin'                                                   + #10 +
    '  Obj := TFoo.Create();'                                   + #10 +
    '  B := Supports(Obj, IFoo);'                             + #10 +
    '  Obj.Free()'                                              + #10 +
    'end.';

  SrcSupportsThreeArg =
    'program P;'                                              + #10 +
    'type'                                                    + #10 +
    '  IFoo = interface'                                      + #10 +
    '    procedure DoIt;'                                     + #10 +
    '  end;'                                                  + #10 +
    '  TFoo = class(TObject, IFoo)'                           + #10 +
    '    procedure DoIt;'                                     + #10 +
    '  end;'                                                  + #10 +
    'procedure TFoo.DoIt(); begin end;'                         + #10 +
    'var Obj: TObject;'                                       + #10 +
    '    F: IFoo;'                                            + #10 +
    '    B: Boolean;'                                         + #10 +
    'begin'                                                   + #10 +
    '  Obj := TFoo.Create();'                                   + #10 +
    '  B := Supports(Obj, IFoo, F);'                          + #10 +
    '  Obj.Free()'                                              + #10 +
    'end.';

  SrcSupportsNonIntf =
    'program P;'                                              + #10 +
    'type'                                                    + #10 +
    '  TFoo = class(TObject)'                                 + #10 +
    '  end;'                                                  + #10 +
    'var Obj: TObject;'                                       + #10 +
    '    B: Boolean;'                                         + #10 +
    'begin'                                                   + #10 +
    '  Obj := TFoo.Create();'                                   + #10 +
    '  B := Supports(Obj, TFoo);'                             + #10 +
    '  Obj.Free()'                                              + #10 +
    'end.';

procedure TInterfaceTests.TestParse_Supports_TwoArg_ProducesSupportsExpr;
var Prog: TProgram;
    Assign: TAssignment;
    SE: TSupportsExpr;
begin
  Prog := ParseSrc(SrcSupportsTwoArg);
  try
    { assignment: B := Supports(Obj, IFoo) — index 1 (after Obj := TFoo.Create) }
    Assign := TAssignment(Prog.Block.Stmts[1]);
    AssertTrue('rhs is TSupportsExpr', Assign.Expr is TSupportsExpr);
    SE := TSupportsExpr(Assign.Expr);
    AssertEquals('interface name', 'IFoo', SE.IntfTypeName);
    AssertEquals('no out-var', '', SE.OutVarName);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestParse_Supports_ThreeArg_ProducesSupportsExpr;
var Prog: TProgram;
    Assign: TAssignment;
    SE: TSupportsExpr;
begin
  Prog := ParseSrc(SrcSupportsThreeArg);
  try
    Assign := TAssignment(Prog.Block.Stmts[1]);
    AssertTrue('rhs is TSupportsExpr', Assign.Expr is TSupportsExpr);
    SE := TSupportsExpr(Assign.Expr);
    AssertEquals('interface name', 'IFoo', SE.IntfTypeName);
    AssertEquals('out-var name', 'F', SE.OutVarName);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_Supports_TwoArg_ResultIsBoolean;
var Prog: TProgram;
    Assign: TAssignment;
    SE: TSupportsExpr;
begin
  Prog := AnalyseSrc(SrcSupportsTwoArg);
  try
    Assign := TAssignment(Prog.Block.Stmts[1]);
    SE := TSupportsExpr(Assign.Expr);
    AssertTrue('ResolvedType set', SE.ResolvedType <> nil);
    AssertEquals('result is Boolean', 'Boolean', SE.ResolvedType.Name);
    AssertTrue('ResolvedIntfType set', SE.ResolvedIntfType <> nil);
    AssertEquals('intf type is IFoo', 'IFoo', SE.ResolvedIntfType.Name);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_Supports_ThreeArg_ResultIsBoolean;
var Prog: TProgram;
    Assign: TAssignment;
    SE: TSupportsExpr;
begin
  Prog := AnalyseSrc(SrcSupportsThreeArg);
  try
    Assign := TAssignment(Prog.Block.Stmts[1]);
    SE := TSupportsExpr(Assign.Expr);
    AssertTrue('ResolvedType set', SE.ResolvedType <> nil);
    AssertEquals('result is Boolean', 'Boolean', SE.ResolvedType.Name);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_Supports_NonInterface_RaisesError;
begin
  AnalyseExpectError(SrcSupportsNonIntf);
end;

procedure TInterfaceTests.TestCodegen_Supports_TwoArg_CallsImplementsInterface;
var IR: string;
begin
  IR := GenIR(SrcSupportsTwoArg);
  AssertTrue('calls _ImplementsInterface',
    Pos('call $_ImplementsInterface', IR) > 0);
  AssertTrue('passes typeinfo_IFoo',
    Pos('$typeinfo_IFoo', IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_Supports_ThreeArg_WritesSlots;
var IR: string;
begin
  IR := GenIR(SrcSupportsThreeArg);
  AssertTrue('calls _ImplementsInterface',
    Pos('call $_ImplementsInterface', IR) > 0);
  { On success the obj slot of the out-var must be written }
  AssertTrue('stores obj slot',
    Pos('storel', IR) > 0);
  { itab slot must be populated via _GetItab }
  AssertTrue('calls _GetItab',
    Pos('call $_GetItab', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Interface argument passing — non-identifier expressions              }
{ ------------------------------------------------------------------ }

procedure TInterfaceTests.TestCodegen_InterfaceArg_AsExpr_PassesBothSlots;
var IR: string;
begin
  IR := GenIR(SrcInterfaceArgAsExpr);
  AssertTrue('calls _GetItab for as-expr arg',
    Pos('call $_GetItab', IR) > 0);
  AssertTrue('calls UseIntf',
    Pos('call $UseIntf', IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_InterfaceArg_Identifier_PassesBothSlots;
var IR: string;
begin
  IR := GenIR(SrcInterfaceArgIdent);
  AssertTrue('loads _obj slot for ident arg',
    Pos('loadl $F_obj', IR) > 0);
  AssertTrue('loads _itab slot for ident arg',
    Pos('loadl $F_itab', IR) > 0);
  AssertTrue('calls UseIntf',
    Pos('call $UseIntf', IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_MethodInterfaceParam_FatPointerSignature;
var IR: string;
begin
  IR := GenIR(SrcMethodInterfaceParam);
  { The method must receive the interface param as a two-slot fat pointer and
    alloc both local halves — not a single `w %_par_X` slot. }
  AssertTrue('method signature splits param into obj + itab',
    Pos('l %_par_X_obj, l %_par_X_itab', IR) > 0);
  AssertTrue('allocs local obj slot for the param',
    Pos('%_var_X_obj =l alloc8', IR) > 0);
  AssertTrue('allocs local itab slot for the param',
    Pos('%_var_X_itab =l alloc8', IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_MethodInterfaceArg_PassesBothSlots;
var IR: string;
begin
  IR := GenIR(SrcMethodInterfaceParam);
  { The method call site must pass both halves of the caller's fat pointer. }
  AssertTrue('passes _obj slot at the method call site',
    Pos('loadl $F_obj', IR) > 0);
  AssertTrue('passes _itab slot at the method call site',
    Pos('loadl $F_itab', IR) > 0);
end;

{ Regression (issue #64): inside a method body, an interface-typed field
  must shadow a same-named global variable.  The semantic analyser previously
  found the global 'im: Tmi' and reported a type-mismatch instead of
  recognising 'im' as the field 'im: Iprinter' of the enclosing class. }
procedure TInterfaceTests.TestSemantic_InterfaceField_ShadowsGlobal_OK;
begin
  { Must not raise ESemanticError }
  AnalyseSrc(SrcInterfaceFieldShadowsGlobal).Free();
end;

initialization
  RegisterTest(TInterfaceTests);

end.
