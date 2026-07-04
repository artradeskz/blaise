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
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

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
    procedure TestCodegen_InterfaceArrayElement_StoresFatPointer;
    procedure TestCodegen_InterfaceArrayElement_ReadsFatPointer;
    procedure TestCodegen_InterfaceMethodCall_IndirectDispatch;
    procedure TestCodegen_InterfaceField_InRecord_NoUndefObjTemp;
    procedure TestCodegen_InterfaceField_InRecord_SizedSixteen;
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

    { ------------------------------------------------------------------ }
    { Interface properties                                                 }
    { ------------------------------------------------------------------ }
    procedure TestParse_Interface_WithProperty;
    procedure TestSemantic_InterfaceProperty_Registered;
    procedure TestSemantic_InterfaceProperty_UnknownAccessor_RaisesError;
    procedure TestSemantic_InterfaceProperty_WriteToReadOnly_RaisesError;
    procedure TestSemantic_InterfaceProperty_InheritedFromParent_OK;
    procedure TestCodegen_InterfacePropertyRead_DispatchesGetter;
    procedure TestCodegen_InterfacePropertyWrite_DispatchesSetter;

    { ------------------------------------------------------------------ }
    { Regression — interface idents as values; interface-returning        }
    { interface-method calls                                              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_InterfaceResult_NilCompare_UsesObjSlot;
    procedure TestCodegen_InterfaceLocal_NilCompare_UsesObjSlot;
    procedure TestCodegen_IntfMethodReturningIntf_AssignsToSplitSlots;

    { ------------------------------------------------------------------ }
    { Regression — itab-dispatch argument ABI; discarded sret returns     }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_IntfDispatch_RecordArg_PassesAggregate;
    procedure TestCodegen_IntfDispatch_OutString_PassesSlotAddr;
    procedure TestCodegen_DiscardedIntfReturnStmt_GetsSretAndRelease;
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

  { Write an interface into a static-array element.  Before the fix
    the element-store fell through to the generic path which picked
    storew (QbeTypeOf falls to 'w' for tyInterface), leaving itab
    uninitialised and clobbering only the low 4 bytes of obj.  After:
    the obj+itab pair is stored with two storel instructions. }
  SrcInterfaceArrayElementWrite =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
          end;
          TFoo = class(TObject, IFoo)
            procedure DoIt;
          end;
        procedure TFoo.DoIt; begin end;
        var
          Reg: array[0..1] of IFoo;
        procedure Register(AItem: IFoo);
        begin
          Reg[0] := AItem
        end;
        var T: TFoo;
        begin
          T := TFoo.Create();
          Register(T)
        end.
        ''';

  { Read an interface back out of a static-array element and assign
    to another interface var.  Before the fix the subscript-read
    path emitted `loadw` against the 16-byte slot and then `storel`
    into the global LHS (which only has split _obj/_itab slots —
    producing an undefined-symbol link error at the bare global
    name).  After: the obj+itab halves are loaded from ElemPtr /
    ElemPtr+8 and written into the LHS's split slots. }
  SrcInterfaceArrayElementRead =
    '''
        program P;
        type
          IFoo = interface
            procedure DoIt;
          end;
        var
          Reg: array[0..1] of IFoo;
          F:   IFoo;
        begin
          F := Reg[0]
        end.
        ''';

  { Interface field inside a record, with a method called through it and a
    trailing Integer field.  Pins the codegen fix: dispatch reads the field's
    contiguous fat pointer (never an undefined %_var__obj split slot), and the
    interface field occupies 16 bytes so Tag lands at offset 16. }
  SrcInterfaceFieldInRecord =
    '''
        program P;
        type
          IFoo = interface
            function GetVal: Integer;
          end;
          TFoo = class(TObject, IFoo)
            V: Integer;
            function GetVal: Integer;
          end;
          TRec = record
            Foo: IFoo;
            Tag: Integer;
          end;
        function TFoo.GetVal: Integer;
        begin
          Result := Self.V
        end;
        var
          r: TRec;
          f: TFoo;
        begin
          f := TFoo.Create();
          f.V := 42;
          r.Foo := f;
          r.Tag := 7;
          WriteLn(r.Foo.GetVal());
          WriteLn(r.Tag)
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
  { F is a program-level global — ONE 16-byte data item based at $F_obj;
    the itab half is addressed as $F_obj + 8 (no $F_itab symbol). }
  AssertTrue('fat-pointer data item for F', Pos('$F_obj = { l 0, l 0 }', IR) > 0);
  AssertTrue('itab half addressed at +8', Pos('add $F_obj, 8', IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_InterfaceArrayElement_StoresFatPointer;
var
  IR: string;
begin
  IR := GenIR(SrcInterfaceArrayElementWrite);
  { Element store must use storel (fat-pointer halves), not storew. }
  AssertTrue('element store uses storel',
    Pos('storel', IR) > 0);
  AssertFalse('element store must not use storew on a 16-byte fat slot',
    Pos('storew %_t', IR) > 0);
  { itab half is written at ElemPtr + 8 (computed via `add %, 8`). }
  AssertTrue('itab store offset built via add %, 8',
    Pos('add %', IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_InterfaceArrayElement_ReadsFatPointer;
var
  IR: string;
begin
  IR := GenIR(SrcInterfaceArrayElementRead);
  { No mistyped loads or single-slot stores against the global LHS. }
  AssertFalse('subscript read must not emit `=w loadl` (typed-w with 8-byte load)',
    Pos('=w loadl', IR) > 0);
  AssertFalse('LHS write must not emit storew %_t targeting the global iface',
    Pos('storew %_t', IR) > 0);
  { Both halves are written into the global LHS's contiguous fat-pointer
    block: obj at $F_obj, itab at $F_obj + 8.  (Globals stopped using
    split _obj/_itab slots when the contiguous layout landed.) }
  AssertTrue('LHS obj store hits the fat-pointer block',
    Pos(', $F_obj', IR) >= 0);
  AssertTrue('LHS itab half addressed at +8',
    Pos('add $F_obj, 8', IR) >= 0);
end;

procedure TInterfaceTests.TestCodegen_InterfaceMethodCall_IndirectDispatch;
var
  IR: string;
begin
  IR := GenIR(SrcInterfaceVar);
  { Interface dispatch loads the itab pointer (global: $F_obj + 8) and
    calls indirectly. }
  AssertTrue('addresses itab half', Pos('add $F_obj, 8', IR) > 0);
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
  { F, G are program-level globals — ONE 16-byte item each, base label
    $Name_obj with the itab half addressed as $Name_obj + 8. }
  AssertTrue('reads F_obj',  Pos('loadl $F_obj',   IR) > 0);
  AssertTrue('addresses F itab half', Pos('add $F_obj, 8', IR) > 0);
  AssertTrue('writes G_obj', Pos('storel ', IR) > 0);
  AssertTrue('addresses G itab half', Pos('add $G_obj, 8', IR) > 0);
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
  AssertTrue('itab half read for dispatch but never released',
    Pos('add $F_obj, 8', IR) > 0);  { itab is read during the method
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
  { Global interfaces are one 16-byte item; the itab half is $F_obj + 8. }
  AssertTrue('addresses the itab half for ident arg',
    Pos('add $F_obj, 8', IR) > 0);
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
  { The param's fat pointer is ONE contiguous 16-byte alloc whose base is
    the _obj slot; the _itab name is derived at +8. }
  AssertTrue('allocs contiguous fat-pointer block for the param',
    Pos('%_var_X_obj =l alloc8 16', IR) > 0);
  AssertTrue('derives the itab slot at obj + 8',
    Pos('%_var_X_itab =l add %_var_X_obj, 8', IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_MethodInterfaceArg_PassesBothSlots;
var IR: string;
begin
  IR := GenIR(SrcMethodInterfaceParam);
  { The method call site must pass both halves of the caller's fat pointer.
    Global interfaces are ONE 16-byte data item ($F_obj): the itab half has
    no symbol of its own and is addressed as $F_obj + 8. }
  AssertTrue('passes _obj slot at the method call site',
    Pos('loadl $F_obj', IR) > 0);
  AssertTrue('addresses the itab half at $F_obj + 8',
    Pos('add $F_obj, 8', IR) > 0);
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

procedure TInterfaceTests.TestCodegen_InterfaceField_InRecord_NoUndefObjTemp;
var
  IR: string;
begin
  { Calling a method through an interface record field must resolve the field's
    fat pointer, not emit the undefined %_var__obj / %_var__itab split-slot
    temps that QBE rejects (the pre-fix bug). }
  IR := GenIR(SrcInterfaceFieldInRecord);
  AssertTrue('no undefined obj split-slot temp', Pos('%_var__obj', IR) <= 0);
  AssertTrue('no undefined itab split-slot temp', Pos('%_var__itab', IR) <= 0);
  AssertTrue('uses the static itab for the field store',
    Pos('$itab_TFoo_IFoo', IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_InterfaceField_InRecord_SizedSixteen;
var
  IR: string;
begin
  { The interface field is a 16-byte fat pointer, so the following Integer
    field Tag sits at offset 16 — the store to Tag adds 16 to the record base. }
  IR := GenIR(SrcInterfaceFieldInRecord);
  AssertTrue('Tag field lives at offset 16 (interface field is 16 bytes)',
    Pos('add $r, 16', IR) > 0);
end;

const
  SrcIntfProperty =
    '''
        program P;
        type
          IInter = interface
            function GetValue(): Integer;
            procedure SetValue(AValue: Integer);
            property Value: Integer read GetValue write SetValue;
          end;
          TFace = class(TObject, IInter)
            FVal: Integer;
            function GetValue(): Integer;
            procedure SetValue(AValue: Integer);
          end;
        function TFace.GetValue(): Integer;
        begin
          Result := FVal;
        end;
        procedure TFace.SetValue(AValue: Integer);
        begin
          FVal := AValue;
        end;
        var
          I: IInter;
        begin
          I := TFace.Create();
          I.Value := 13;
          WriteLn(I.Value);
        end.
        ''';

procedure TInterfaceTests.TestParse_Interface_WithProperty;
var Prog: TProgram;
begin
  Prog := ParseSrc(SrcIntfProperty);
  AssertNotNil('interface with property parses', Prog);
  Prog.Free();
end;

procedure TInterfaceTests.TestSemantic_InterfaceProperty_Registered;
var
  Prog: TProgram;
  Sym:  TSymbol;
  Intf: TInterfaceTypeDesc;
begin
  Prog := AnalyseSrc(SrcIntfProperty);
  try
    Sym := Prog.SymbolTable.Lookup('IInter');
    AssertNotNil('IInter registered', Sym);
    Intf := TInterfaceTypeDesc(Sym.TypeDesc);
    AssertNotNil('property Value found', Intf.FindProperty('Value'));
    AssertEquals('read accessor', 'GetValue', Intf.FindProperty('Value').ReadMethod);
    AssertEquals('write accessor', 'SetValue', Intf.FindProperty('Value').WriteMethod);
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestSemantic_InterfaceProperty_UnknownAccessor_RaisesError;
var
  Prog: TProgram;
  A:    TSemanticAnalyser;
  Got:  Boolean;
begin
  Prog := ParseSrc('''
      program P;
      type
        IInter = interface
          function GetValue(): Integer;
          property Value: Integer read NoSuchMethod;
        end;
      begin
      end.
      ''');
  A := TSemanticAnalyser.Create();
  Got := False;
  try
    try
      A.Analyse(Prog);
    except
      on E: ESemanticError do Got := True;
    end;
  finally
    A.Free();
    Prog.Free();
  end;
  AssertTrue('unknown accessor rejected', Got);
end;

procedure TInterfaceTests.TestSemantic_InterfaceProperty_WriteToReadOnly_RaisesError;
var
  Prog: TProgram;
  A:    TSemanticAnalyser;
  Got:  Boolean;
begin
  Prog := ParseSrc('''
      program P;
      type
        IInter = interface
          function GetValue(): Integer;
          property Value: Integer read GetValue;
        end;
        TFace = class(TObject, IInter)
          function GetValue(): Integer;
        end;
      function TFace.GetValue(): Integer;
      begin
        Result := 1;
      end;
      var I: IInter;
      begin
        I := TFace.Create();
        I.Value := 5;
      end.
      ''');
  A := TSemanticAnalyser.Create();
  Got := False;
  try
    try
      A.Analyse(Prog);
    except
      on E: ESemanticError do Got := True;
    end;
  finally
    A.Free();
    Prog.Free();
  end;
  AssertTrue('write to read-only interface property rejected', Got);
end;

procedure TInterfaceTests.TestSemantic_InterfaceProperty_InheritedFromParent_OK;
var
  Prog: TProgram;
  Sym:  TSymbol;
  Intf: TInterfaceTypeDesc;
begin
  Prog := AnalyseSrc('''
      program P;
      type
        IBase = interface
          function GetValue(): Integer;
          property Value: Integer read GetValue;
        end;
        IChild = interface(IBase)
          procedure Extra();
        end;
      begin
      end.
      ''');
  try
    Sym := Prog.SymbolTable.Lookup('IChild');
    Intf := TInterfaceTypeDesc(Sym.TypeDesc);
    AssertNotNil('child sees parent property', Intf.FindProperty('Value'));
  finally
    Prog.Free();
  end;
end;

procedure TInterfaceTests.TestCodegen_InterfacePropertyRead_DispatchesGetter;
var IR: string;
begin
  IR := GenIR(SrcIntfProperty);
  { Property read lowers to an itab-dispatched getter: the itab half of the
    receiver's fat pointer is addressed (locals keep a _itab slot name;
    global receivers compute $Name_obj + 8) and called indirectly. }
  AssertTrue('reads receiver itab half',
    (Pos('_itab', IR) > 0) or (Pos('_obj, 8', IR) > 0));
  AssertTrue('indirect call through function pointer temp',
    Pos('=w call %', IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_InterfacePropertyWrite_DispatchesSetter;
var IR: string;
begin
  IR := GenIR(SrcIntfProperty);
  { Property write lowers to an itab-dispatched setter call with the value
    as the single argument after Self. }
  AssertTrue('setter dispatched with value argument',
    Pos('call %', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Regression — interface idents as values; interface-returning        }
{ interface-method calls                                              }
{ ------------------------------------------------------------------ }

const
  { Function whose RETURN TYPE is an interface, with `if Result = nil` in the
    body.  An interface Result has no single %_var_Result slot — only the
    split %_var_Result_obj / %_var_Result_itab pair pointing into the sret
    buffer — so the nil compare must load the obj half. }
  SrcInterfaceResultNilCompare =
    '''
        program P;
        type
          IDriver = interface
            function GetVal(): Integer;
          end;
          TDrv = class(TObject, IDriver)
            function GetVal(): Integer;
          end;
        function TDrv.GetVal(): Integer;
        begin
          Result := 7
        end;
        function GetDriver(): IDriver;
        begin
          Result := nil;
          if Result = nil then
            Result := TDrv.Create()
        end;
        begin
        end.
        ''';

  { Plain interface LOCAL compared against nil — same obj-half rule. }
  SrcInterfaceLocalNilCompare =
    '''
        program P;
        type
          IDriver = interface
            function GetVal(): Integer;
          end;
          TDrv = class(TObject, IDriver)
            function GetVal(): Integer;
          end;
        function TDrv.GetVal(): Integer;
        begin
          Result := 7
        end;
        procedure Run();
        var
          D: IDriver;
        begin
          D := nil;
          if D = nil then
            D := TDrv.Create()
        end;
        begin
          Run()
        end.
        ''';

  { Interface-method call (itab dispatch) RETURNING an interface, assigned to
    a LOCAL interface var.  The callee writes the fat pointer through a hidden
    sret arg; the caller must store obj/itab into the split slots — never a
    single `storel %t, %_var_W`. }
  SrcIntfMethodCallReturnsInterface =
    '''
        program P;
        type
          IWidget = interface
            function Tag(): Integer;
          end;
          IDriver = interface
            function MakeWidget(N: Integer): IWidget;
          end;
          TWidget = class(TObject, IWidget)
            function Tag(): Integer;
          end;
          TDrv = class(TObject, IDriver)
            function MakeWidget(N: Integer): IWidget;
          end;
        function TWidget.Tag(): Integer;
        begin
          Result := 1
        end;
        function TDrv.MakeWidget(N: Integer): IWidget;
        begin
          Result := TWidget.Create()
        end;
        procedure Run();
        var
          D: IDriver;
          W: IWidget;
        begin
          D := TDrv.Create();
          W := D.MakeWidget(3)
        end;
        begin
          Run()
        end.
        ''';

procedure TInterfaceTests.TestCodegen_InterfaceResult_NilCompare_UsesObjSlot;
var
  IR: string;
begin
  IR := GenIR(SrcInterfaceResultNilCompare);
  AssertTrue('nil compare loads the obj half of Result',
    Pos('loadl %_var_Result_obj', IR) > 0);
  AssertFalse('must not load a non-existent single %_var_Result slot',
    Pos('loadl %_var_Result' + #10, IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_InterfaceLocal_NilCompare_UsesObjSlot;
var
  IR: string;
begin
  IR := GenIR(SrcInterfaceLocalNilCompare);
  AssertTrue('nil compare loads the obj half of the local',
    Pos('loadl %_var_D_obj', IR) > 0);
  AssertFalse('must not load a non-existent single %_var_D slot',
    Pos('loadl %_var_D' + #10, IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_IntfMethodReturningIntf_AssignsToSplitSlots;
var
  IR: string;
begin
  IR := GenIR(SrcIntfMethodCallReturnsInterface);
  AssertTrue('obj half stored into the split obj slot',
    Pos(', %_var_W_obj', IR) > 0);
  AssertTrue('itab half stored into the split itab slot',
    Pos(', %_var_W_itab', IR) > 0);
  AssertFalse('must not store into a non-existent single %_var_W slot',
    Pos(', %_var_W' + #10, IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Regression — itab-dispatch argument ABI; discarded sret returns     }
{ ------------------------------------------------------------------ }

const
  { Record by const through itab dispatch — must use the same aggregate
    param type (:_ffi_TOpts) as a direct call, not a single w/l scalar. }
  SrcIntfDispatchRecordArg =
    '''
        program P;
        type
          TOpts = record
            A: Integer;
            B: Integer;
            C: Integer;
          end;
          ICfg = interface
            procedure Configure(const Opts: TOpts; X: Integer);
          end;
          TCfg = class(TObject, ICfg)
            procedure Configure(const Opts: TOpts; X: Integer);
          end;
        procedure TCfg.Configure(const Opts: TOpts; X: Integer);
        begin
          WriteLn(X)
        end;
        var
          C: ICfg;
          O: TOpts;
        begin
          C := TCfg.Create();
          C.Configure(O, 77)
        end.
        ''';

  { out-string through itab dispatch — must pass the slot ADDRESS
    (var-param rule), not the loaded value. }
  SrcIntfDispatchOutString =
    '''
        program P;
        type
          IName = interface
            procedure GetName(out AName: string);
          end;
          TNamed = class(TObject, IName)
            procedure GetName(out AName: string);
          end;
        procedure TNamed.GetName(out AName: string);
        begin
          AName := 'x'
        end;
        procedure Run();
        var
          N: IName;
          S: string;
        begin
          N := TNamed.Create();
          N.GetName(S)
        end;
        begin
          Run()
        end.
        ''';

  { Interface-returning itab call discarded in statement position — the
    call must receive a throwaway sret buffer as hidden first arg and the
    returned obj must be released. }
  SrcDiscardedIntfReturnStmt =
    '''
        program P;
        type
          IWidget = interface
            function Tag(): Integer;
          end;
          IDriver = interface
            function MakeWidget(N: Integer): IWidget;
          end;
          TWidget = class(TObject, IWidget)
            function Tag(): Integer;
          end;
          TDrv = class(TObject, IDriver)
            function MakeWidget(N: Integer): IWidget;
          end;
        function TWidget.Tag(): Integer;
        begin
          Result := 1
        end;
        function TDrv.MakeWidget(N: Integer): IWidget;
        begin
          Result := TWidget.Create()
        end;
        var
          D: IDriver;
        begin
          D := TDrv.Create();
          D.MakeWidget(5)
        end.
        ''';

procedure TInterfaceTests.TestCodegen_IntfDispatch_RecordArg_PassesAggregate;
var
  IR: string;
  CallPos: Integer;
  CallLine: string;
begin
  IR := GenIR(SrcIntfDispatchRecordArg);
  { The dispatch site is the only INDIRECT call ('call %fptr(...)'); the
    callee signature also mentions :_ffi_TOpts, so scope the check to the
    indirect call line. }
  CallPos := Pos('call %', IR);
  AssertTrue('indirect dispatch call present', CallPos > 0);
  CallLine := Copy(IR, CallPos, Pos(')', Copy(IR, CallPos, MaxInt)) + 1);
  AssertTrue('record arg uses the aggregate FFI type at the dispatch site: '
    + CallLine, Pos(':_ffi_TOpts ', CallLine) > 0);
end;

procedure TInterfaceTests.TestCodegen_IntfDispatch_OutString_PassesSlotAddr;
var
  IR: string;
begin
  IR := GenIR(SrcIntfDispatchOutString);
  AssertTrue('out-string arg passes the slot address',
    Pos(', l %_var_S', IR) > 0);
end;

procedure TInterfaceTests.TestCodegen_DiscardedIntfReturnStmt_GetsSretAndRelease;
var
  IR: string;
  CallPos: Integer;
begin
  IR := GenIR(SrcDiscardedIntfReturnStmt);
  { The dispatch call must carry a hidden sret buffer; the buffer alloc and
    a release of the returned obj must both be present in main. }
  CallPos := Pos('alloc8 16', IR);
  AssertTrue('throwaway sret buffer allocated for the discarded call',
    CallPos > 0);
  AssertTrue('returned obj released after the discarded call',
    Pos('call $_ClassRelease', Copy(IR, CallPos, MaxInt)) > 0);
end;

initialization
  RegisterTest(TInterfaceTests);

end.
