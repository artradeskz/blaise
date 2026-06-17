{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.classof;

{ Tests for 'class of TFoo' metaclass type support — Step 11a. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

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

    { Metaclass-var dispatch: C.Create() emits _ClassCreate + indirect
      ctor call via vtable, not a static call to the base Create. }
    procedure TestSemantic_MetaclassVar_Create_Accepted;
    procedure TestCodegen_MetaclassVar_Create_IndirectCtor;
    procedure TestCodegen_MetaclassVar_Create_NoCtor_NoIndirectCall;
  end;

implementation

function TClassOfTests.ParseSrc(const ASrc: string): TProgram;
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

function TClassOfTests.AnalyseSrc(const ASrc: string): TProgram;
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

function TClassOfTests.GenIR(const ASrc: string): string;
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

procedure TClassOfTests.AnalyseExpectError(const ASrc: string);
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
{  Parser                                                             }
{ ------------------------------------------------------------------ }

procedure TClassOfTests.TestParse_ClassOf_AsAlias;
const
  Src =
    '''
        program P;
        type
          TBase = class(TObject) end;
          TBaseClass = class of TBase;
        begin end.
        ''';
var Prog: TProgram;
begin
  Prog := ParseSrc(Src);
  try
    AssertEquals('two type decls', 2, Prog.Block.TypeDecls.Count);
  finally
    Prog.Free();
  end;
end;

procedure TClassOfTests.TestParse_ClassOf_VarDecl;
const
  Src =
    '''
        program P;
        type
          TBase = class(TObject) end;
        var C: class of TBase;
        begin end.
        ''';
var Prog: TProgram;
begin
  Prog := ParseSrc(Src);
  try
    AssertEquals('one var decl', 1, Prog.Block.Decls.Count);
  finally
    Prog.Free();
  end;
end;

procedure TClassOfTests.TestParse_ClassOf_FieldType;
const
  Src =
    '''
        program P;
        type
          TBase = class(TObject) end;
          TWrap = class(TObject)
            Cls: class of TBase;
          end;
        begin end.
        ''';
var Prog: TProgram;
begin
  Prog := ParseSrc(Src);
  try
    AssertEquals('two type decls', 2, Prog.Block.TypeDecls.Count);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{  Semantic                                                            }
{ ------------------------------------------------------------------ }

procedure TClassOfTests.TestSemantic_ClassOf_TypeIsMetaClass;
const
  Src =
    '''
        program P;
        type
          TBase = class(TObject) end;
        var C: class of TBase;
        begin end.
        ''';
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
    Prog.Free();
  end;
end;

procedure TClassOfTests.TestSemantic_ClassOf_BaseClass;
const
  Src =
    '''
        program P;
        type
          TBase = class(TObject) end;
        var C: class of TBase;
        begin end.
        ''';
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
    Prog.Free();
  end;
end;

procedure TClassOfTests.TestSemantic_AssignClassIdent_ToMetaClass;
const
  Src =
    '''
        program P;
        type
          TBase = class(TObject) end;
        var C: class of TBase;
        begin
          C := TBase
        end.
        ''';
var Prog: TProgram;
begin
  { Should analyse without error. }
  Prog := AnalyseSrc(Src);
  try
    AssertEquals('one stmt', 1, Prog.Block.Stmts.Count);
  finally
    Prog.Free();
  end;
end;

procedure TClassOfTests.TestSemantic_AssignDescendant_ToBaseMetaClass;
const
  Src =
    '''
        program P;
        type
          TBase    = class(TObject) end;
          TDerived = class(TBase) end;
        var C: class of TBase;
        begin
          C := TDerived
        end.
        ''';
var Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertEquals('one stmt', 1, Prog.Block.Stmts.Count);
  finally
    Prog.Free();
  end;
end;

procedure TClassOfTests.TestSemantic_RejectUnrelatedClass_ToMetaClass;
const
  Src =
    '''
        program P;
        type
          TBase  = class(TObject) end;
          TOther = class(TObject) end;
        var C: class of TBase;
        begin
          C := TOther
        end.
        ''';
begin
  AnalyseExpectError(Src);
end;

procedure TClassOfTests.TestSemantic_RejectClassOf_Nonclass;
const
  Src =
    '''
        program P;
        type
          TInt = class of Integer;
        begin end.
        ''';
begin
  AnalyseExpectError(Src);
end;

procedure TClassOfTests.TestSemantic_MetaClass_AcceptedAsPointerArg;
const
  Src =
    '''
        program P;
        type
          TBase = class(TObject) end;
        procedure Take(const P: Pointer);
        begin end;
        begin
          Take(TBase)
        end.
        ''';
var Prog: TProgram;
begin
  { A metaclass-typed value passes through an untyped Pointer arg. }
  Prog := AnalyseSrc(Src);
  try
    AssertEquals('one stmt', 1, Prog.Block.Stmts.Count);
  finally
    Prog.Free();
  end;
end;

procedure TClassOfTests.TestSemantic_CompareTwoMetaClassValues;
const
  Src =
    '''
        program P;
        type
          TBase    = class(TObject) end;
          TDerived = class(TBase) end;
        var B: Boolean;
        begin
          B := TBase = TDerived
        end.
        ''';
var Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertEquals('one stmt', 1, Prog.Block.Stmts.Count);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{  Codegen                                                             }
{ ------------------------------------------------------------------ }

procedure TClassOfTests.TestCodegen_ClassIdent_EmitsTypeinfo;
const
  Src =
    '''
        program P;
        type
          TBase = class(TObject) end;
        var C: class of TBase;
        begin
          C := TBase
        end.
        ''';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('IR copies $typeinfo_TBase into a temp',
    Pos('copy $typeinfo_TBase', IR) > 0);
end;

procedure TClassOfTests.TestCodegen_MetaClassVar_StorelTypeinfo;
const
  Src =
    '''
        program P;
        type
          TBase = class(TObject) end;
        var C: class of TBase;
        begin
          C := TBase
        end.
        ''';
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
    '''
        program P;
        type
          TBase = class(TObject) end;
        var B: Boolean;
        begin
          B := TBase = TBase
        end.
        ''';
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
    '''
        program P;
        type TFoo = class(TObject) end;
        var F: TFoo;
        begin
          F := ClassCreate(F)
        end.
        '''
  );
end;

procedure TClassOfTests.TestCodegen_ClassCreate_EmitsAllocAndCtorCall;
const
  Src =
    '''
        program P;
        type
          TFoo = class(TObject)
            Value: Integer;
            constructor Create(N: Integer);
          end;
        constructor TFoo.Create(N: Integer);
        begin Self.Value := N end;
        var C: class of TFoo; F: TFoo;
        begin
          C := TFoo;
          F := ClassCreate(C, 7)
        end.
        ''';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('emits call to $_ClassCreate', Pos('call $_ClassCreate(', IR) > 0);
  AssertTrue('emits indirect ctor call via vtable (no static TFoo_Create call)',
    Pos('call $TFoo_Create(', IR) < 0);
end;

procedure TClassOfTests.TestCodegen_ClassCreate_NoCtor_OnlyAllocCalled;
const
  Src =
    '''
        program P;
        type TFoo = class(TObject) end;
        var C: class of TFoo; F: TFoo;
        begin
          C := TFoo;
          F := ClassCreate(C)
        end.
        ''';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('emits call to $_ClassCreate', Pos('call $_ClassCreate(', IR) > 0);
  AssertTrue('no constructor call emitted when class declares none',
    Pos('TFoo_Create', IR) < 0);
end;

{ ---------- Metaclass-var C.Create() dispatch tests ---------- }

procedure TClassOfTests.TestSemantic_MetaclassVar_Create_Accepted;
const Src = '''
    program P;
    type
      TFoo = class(TObject)
        constructor Create;
      end;
    constructor TFoo.Create; begin end;
    var C: class of TFoo; F: TFoo;
    begin
      C := TFoo;
      F := C.Create()
    end.
    ''';
begin
  AnalyseSrc(Src);
end;

procedure TClassOfTests.TestCodegen_MetaclassVar_Create_IndirectCtor;
const Src = '''
    program P;
    type
      TFoo = class(TObject)
        constructor Create;
      end;
    constructor TFoo.Create; begin end;
    var C: class of TFoo; F: TFoo;
    begin
      C := TFoo;
      F := C.Create()
    end.
    ''';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('emits _ClassCreate for runtime alloc',
    Pos('call $_ClassCreate(', IR) > 0);
  AssertTrue('emits indirect ctor call via vtable (loadl from vtable slot)',
    Pos('loadl', IR) > 0);
  AssertTrue('does NOT emit a static TFoo_Create call',
    Pos('call $TFoo_Create(', IR) < 0);
end;

procedure TClassOfTests.TestCodegen_MetaclassVar_Create_NoCtor_NoIndirectCall;
const Src = '''
    program P;
    type TFoo = class(TObject) end;
    var C: class of TFoo; F: TFoo;
    begin
      C := TFoo;
      F := C.Create()
    end.
    ''';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('emits _ClassCreate for runtime alloc',
    Pos('call $_ClassCreate(', IR) > 0);
  AssertTrue('no ctor call when class declares no Create',
    Pos('TFoo_Create', IR) < 0);
end;

initialization
  RegisterTest(TClassOfTests);
end.
