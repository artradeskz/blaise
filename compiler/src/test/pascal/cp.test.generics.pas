{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.generics;

{$mode objfpc}{$H+}

{ Tests for generic type monomorphization.
  Phase 3 scope: single type-parameter classes with inline method bodies;
  standalone generic method implementations are not supported yet. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TGenericsTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    function AnalyseUnit(const ASrc: string): TUnit;
    function GenUnitIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Parser — generic type declarations                                   }
    { ------------------------------------------------------------------ }
    procedure TestParse_Generic_TypeDecl_IsGenericTypeDef;
    procedure TestParse_Generic_ParamName;
    procedure TestParse_Generic_TwoParams;
    procedure TestParse_Generic_FieldUsesTypeParam;
    procedure TestParse_Generic_MethodReturnUsesTypeParam;
    procedure TestParse_Generic_MethodParamUsesTypeParam;

    { ------------------------------------------------------------------ }
    { Parser — generic type references                                     }
    { ------------------------------------------------------------------ }
    procedure TestParse_Generic_VarDeclTypeName;
    procedure TestParse_Generic_TwoArgVarDecl;
    procedure TestParse_Generic_ConstructorCallParsed;

    { ------------------------------------------------------------------ }
    { Semantic — generic registration and instantiation                    }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Generic_TemplateRegistered;
    procedure TestSemantic_Generic_TemplateNotExposedAsConcreteType;
    procedure TestSemantic_Generic_VarDecl_InstantiatesType;
    procedure TestSemantic_Generic_InstFieldType_Integer;
    procedure TestSemantic_Generic_InstFieldType_String;
    procedure TestSemantic_Generic_TwoParams_BothFieldsResolved;

    { ------------------------------------------------------------------ }
    { Semantic — unit-scope generic var declarations                        }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_UnitIntf_GenericVar_Resolves;
    procedure TestSemantic_UnitImpl_GenericVar_Resolves;

    { ------------------------------------------------------------------ }
    { Codegen — monomorphized types                                        }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_Generic_TypeInfoEmitted;
    procedure TestCodegen_Generic_ConstructorAllocsMemory;
    procedure TestCodegen_Generic_MethodEmitted;
    procedure TestCodegen_Generic_FieldAccessWorks;

    { ------------------------------------------------------------------ }
    { Codegen — unit-scope generic var                                     }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_UnitIntf_GenericVar_GlobalData;

    { ------------------------------------------------------------------ }
    { Multi-instance: same generic class with two different type args     }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Generic_TwoInstancesOfSameClass_Resolve;
    procedure TestSemantic_Generic_TwoInstances_PointerFieldDistinctTypes;
    procedure TestCodegen_Generic_TwoInstances_MethodCallsResolveToOwnInstance;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Source constants                                                     }
{ ------------------------------------------------------------------ }

const
  SrcGenericOneParam =
    '''
        program P;
        type
          TBox<T> = class
            FValue: T;
          end;
        begin
        end.
        ''';

  SrcGenericTwoParams =
    '''
        program P;
        type
          TPair<K, V> = class
            FKey: K;
            FVal: V;
          end;
        begin
        end.
        ''';

  SrcGenericWithMethod =
    '''
        program P;
        type
          TBox<T> = class
            FValue: T;
            function GetValue: T;
            procedure SetValue(AVal: T);
          end;
        begin
        end.
        ''';

  SrcGenericVarInteger =
    '''
        program P;
        type
          TBox<T> = class
            FValue: T;
          end;
        var B: TBox<Integer>;
        begin
        end.
        ''';

  SrcGenericVarString =
    '''
        program P;
        type
          TBox<T> = class
            FValue: T;
          end;
        var S: TBox<string>;
        begin
        end.
        ''';

  SrcGenericTwoParamVar =
    '''
        program P;
        type
          TPair<K, V> = class
            FKey: K;
            FVal: V;
          end;
        var P: TPair<string, Integer>;
        begin
        end.
        ''';

  SrcGenericUsage =
    '''
        program P;
        type
          TBox<T> = class
            FValue: T;
            function GetValue: T;
            begin
              Result := Self.FValue
            end;
            procedure SetValue(AVal: T);
            begin
              Self.FValue := AVal
            end;
          end;
        var B: TBox<Integer>;
        begin
          B := TBox<Integer>.Create;
          B.SetValue(42);
          WriteLn(B.GetValue())
        end.
        ''';

  SrcUnitIntfGenericVar =
    '''
        unit U;
        interface
        type
          TBox<T> = class
            FValue: T;
          end;
        var
          G: TBox<Integer>;
        implementation
        end.
        ''';

  SrcUnitImplGenericVar =
    '''
        unit U;
        interface
        type
          TBox<T> = class
            FValue: T;
          end;
        implementation
        var
          G: TBox<string>;
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TGenericsTests.ParseSrc(const ASrc: string): TProgram;
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

function TGenericsTests.AnalyseSrc(const ASrc: string): TProgram;
var
  SA: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  SA     := TSemanticAnalyser.Create;
  try
    SA.Analyse(Result);
  finally
    SA.Free;
  end;
end;

function TGenericsTests.GenIR(const ASrc: string): string;
var
  CG:   TCodeGenQBE;
  Prog: TProgram;
begin
  Prog := AnalyseSrc(ASrc);
  CG   := TCodeGenQBE.Create;
  try
    CG.Generate(Prog);
    Result := CG.GetOutput;
  finally
    CG.Free;
    Prog.Free;
  end;
end;

function TGenericsTests.AnalyseUnit(const ASrc: string): TUnit;
var
  L:  TLexer;
  P:  TParser;
  SA: TSemanticAnalyser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.ParseUnit;
  finally
    P.Free;
    L.Free;
  end;
  SA := TSemanticAnalyser.Create;
  try
    SA.AnalyseUnit(Result);
  finally
    SA.Free;
  end;
end;

function TGenericsTests.GenUnitIR(const ASrc: string): string;
var
  U:  TUnit;
  CG: TCodeGenQBE;
begin
  U := AnalyseUnit(ASrc);
  try
    CG := TCodeGenQBE.Create;
    try
      CG.GenerateUnit(U);
      Result := CG.GetOutput;
    finally
      CG.Free;
    end;
  finally
    U.Free;
  end;
end;

procedure TGenericsTests.AnalyseExpectError(const ASrc: string);
var
  Prog: TProgram;
  SA:   TSemanticAnalyser;
begin
  Prog := ParseSrc(ASrc);
  SA   := TSemanticAnalyser.Create;
  try
    try
      SA.Analyse(Prog);
      Fail('Expected ESemanticError but none was raised');
    except
      on E: ESemanticError do { expected };
    end;
  finally
    SA.Free;
    Prog.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser — generic type declarations                                   }
{ ------------------------------------------------------------------ }

procedure TGenericsTests.TestParse_Generic_TypeDecl_IsGenericTypeDef;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(SrcGenericOneParam);
  try
    AssertEquals('one type decl', 1, Prog.Block.TypeDecls.Count);
    TD := TTypeDecl(Prog.Block.TypeDecls[0]);
    AssertEquals('name is TBox', 'TBox', TD.Name);
    AssertTrue('def is TGenericTypeDef', TD.Def is TGenericTypeDef);
  finally
    Prog.Free;
  end;
end;

procedure TGenericsTests.TestParse_Generic_ParamName;
var
  Prog: TProgram;
  GD:   TGenericTypeDef;
begin
  Prog := ParseSrc(SrcGenericOneParam);
  try
    GD := TGenericTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('one param', 1, GD.ParamNames.Count);
    AssertEquals('param name is T', 'T', GD.ParamNames[0]);
  finally
    Prog.Free;
  end;
end;

procedure TGenericsTests.TestParse_Generic_TwoParams;
var
  Prog: TProgram;
  GD:   TGenericTypeDef;
begin
  Prog := ParseSrc(SrcGenericTwoParams);
  try
    GD := TGenericTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('two params', 2, GD.ParamNames.Count);
    AssertEquals('first param K', 'K', GD.ParamNames[0]);
    AssertEquals('second param V', 'V', GD.ParamNames[1]);
  finally
    Prog.Free;
  end;
end;

procedure TGenericsTests.TestParse_Generic_FieldUsesTypeParam;
var
  Prog: TProgram;
  GD:   TGenericTypeDef;
  FD:   TFieldDecl;
begin
  Prog := ParseSrc(SrcGenericOneParam);
  try
    GD := TGenericTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('one field', 1, GD.ClassDef.Fields.Count);
    FD := TFieldDecl(GD.ClassDef.Fields[0]);
    AssertEquals('field type is T', 'T', FD.TypeName);
  finally
    Prog.Free;
  end;
end;

procedure TGenericsTests.TestParse_Generic_MethodReturnUsesTypeParam;
var
  Prog: TProgram;
  GD:   TGenericTypeDef;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcGenericWithMethod);
  try
    GD := TGenericTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MD := TMethodDecl(GD.ClassDef.Methods[0]);  { GetValue }
    AssertEquals('return type is T', 'T', MD.ReturnTypeName);
  finally
    Prog.Free;
  end;
end;

procedure TGenericsTests.TestParse_Generic_MethodParamUsesTypeParam;
var
  Prog: TProgram;
  GD:   TGenericTypeDef;
  MD:   TMethodDecl;
  Par:  TMethodParam;
begin
  Prog := ParseSrc(SrcGenericWithMethod);
  try
    GD  := TGenericTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    MD  := TMethodDecl(GD.ClassDef.Methods[1]);  { SetValue }
    Par := TMethodParam(MD.Params[0]);
    AssertEquals('param type is T', 'T', Par.TypeName);
  finally
    Prog.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser — generic type references                                     }
{ ------------------------------------------------------------------ }

procedure TGenericsTests.TestParse_Generic_VarDeclTypeName;
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := ParseSrc(SrcGenericVarInteger);
  try
    AssertEquals('one var decl', 1, Prog.Block.Decls.Count);
    VD := TVarDecl(Prog.Block.Decls[0]);
    AssertEquals('var type is TBox<Integer>', 'TBox<Integer>', VD.TypeName);
  finally
    Prog.Free;
  end;
end;

procedure TGenericsTests.TestParse_Generic_TwoArgVarDecl;
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := ParseSrc(SrcGenericTwoParamVar);
  try
    VD := TVarDecl(Prog.Block.Decls[0]);
    AssertEquals('var type is TPair<string,Integer>',
      'TPair<string,Integer>', VD.TypeName);
  finally
    Prog.Free;
  end;
end;

procedure TGenericsTests.TestParse_Generic_ConstructorCallParsed;
var
  Prog:   TProgram;
  Assign: TAssignment;
  Expr:   TFieldAccessExpr;
begin
  Prog := ParseSrc(SrcGenericUsage);
  try
    { Stmt[0] = B := TBox<Integer>.Create }
    AssertTrue('stmt 0 is assignment', Prog.Block.Stmts[0] is TAssignment);
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertTrue('rhs is TFieldAccessExpr', Assign.Expr is TFieldAccessExpr);
    Expr := TFieldAccessExpr(Assign.Expr);
    AssertEquals('record name is TBox<Integer>', 'TBox<Integer>', Expr.RecordName);
    AssertEquals('field is Create', 'Create', Expr.FieldName);
  finally
    Prog.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic — generic registration and instantiation                    }
{ ------------------------------------------------------------------ }

procedure TGenericsTests.TestSemantic_Generic_TemplateRegistered;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcGenericOneParam);
  try
    AssertNotNull('TBox template registered',
      Prog.SymbolTable.FindGeneric('TBox'));
  finally
    Prog.Free;
  end;
end;

procedure TGenericsTests.TestSemantic_Generic_TemplateNotExposedAsConcreteType;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcGenericOneParam);
  try
    AssertNull('TBox not a concrete type',
      Prog.SymbolTable.FindType('TBox'));
  finally
    Prog.Free;
  end;
end;

procedure TGenericsTests.TestSemantic_Generic_VarDecl_InstantiatesType;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcGenericVarInteger);
  try
    AssertNotNull('TBox<Integer> instantiated',
      Prog.SymbolTable.FindType('TBox<Integer>'));
  finally
    Prog.Free;
  end;
end;

procedure TGenericsTests.TestSemantic_Generic_InstFieldType_Integer;
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
  FI:   TFieldInfo;
begin
  Prog := AnalyseSrc(SrcGenericVarInteger);
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TBox<Integer>'));
    FI := RT.FindField('FValue');
    AssertNotNull('FValue field exists', FI);
    AssertEquals('FValue type is tyInteger', Ord(tyInteger), Ord(FI.TypeDesc.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TGenericsTests.TestSemantic_Generic_InstFieldType_String;
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
  FI:   TFieldInfo;
begin
  Prog := AnalyseSrc(SrcGenericVarString);
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TBox<string>'));
    AssertNotNull('TBox<string> instantiated', RT);
    FI := RT.FindField('FValue');
    AssertNotNull('FValue field exists', FI);
    AssertTrue('FValue type is string', FI.TypeDesc.IsString);
  finally
    Prog.Free;
  end;
end;

procedure TGenericsTests.TestSemantic_Generic_TwoParams_BothFieldsResolved;
var
  Prog:  TProgram;
  RT:    TRecordTypeDesc;
  FKey:  TFieldInfo;
  FVal:  TFieldInfo;
begin
  Prog := AnalyseSrc(SrcGenericTwoParamVar);
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TPair<string,Integer>'));
    AssertNotNull('TPair<string,Integer> instantiated', RT);
    FKey := RT.FindField('FKey');
    FVal := RT.FindField('FVal');
    AssertNotNull('FKey field', FKey);
    AssertNotNull('FVal field', FVal);
    AssertTrue('FKey is string', FKey.TypeDesc.IsString);
    AssertEquals('FVal is tyInteger', Ord(tyInteger), Ord(FVal.TypeDesc.Kind));
  finally
    Prog.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Codegen — monomorphized types                                        }
{ ------------------------------------------------------------------ }

procedure TGenericsTests.TestCodegen_Generic_TypeInfoEmitted;
var
  IR: string;
begin
  IR := GenIR(SrcGenericUsage);
  AssertTrue('typeinfo for TBox_Integer emitted',
    Pos('$typeinfo_TBox_Integer', IR) > 0);
end;

procedure TGenericsTests.TestCodegen_Generic_ConstructorAllocsMemory;
var
  IR: string;
begin
  IR := GenIR(SrcGenericUsage);
  AssertTrue('constructor calls _ClassAlloc',
    Pos('call $_ClassAlloc', IR) > 0);
end;

procedure TGenericsTests.TestCodegen_Generic_MethodEmitted;
var
  IR: string;
begin
  IR := GenIR(SrcGenericUsage);
  AssertTrue('GetValue method emitted',
    Pos('TBox_Integer_GetValue', IR) > 0);
  AssertTrue('SetValue method emitted',
    Pos('TBox_Integer_SetValue', IR) > 0);
end;

procedure TGenericsTests.TestCodegen_Generic_FieldAccessWorks;
var
  IR: string;
begin
  IR := GenIR(SrcGenericUsage);
  { SetValue stores into FValue; verify a store instruction is emitted }
  AssertTrue('method bodies emitted with stores', Pos('storew', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Semantic — unit-scope generic var declarations                        }
{ ------------------------------------------------------------------ }

procedure TGenericsTests.TestSemantic_UnitIntf_GenericVar_Resolves;
var
  U: TUnit;
begin
  U := AnalyseUnit(SrcUnitIntfGenericVar);
  try
    AssertEquals('interface var count', 1, U.IntfBlock.Decls.Count);
    AssertTrue('resolved type not nil',
      TVarDecl(U.IntfBlock.Decls.Items[0]).ResolvedType <> nil);
    AssertEquals('resolved type name', 'TBox<Integer>',
      TVarDecl(U.IntfBlock.Decls.Items[0]).ResolvedType.Name);
  finally
    U.Free;
  end;
end;

procedure TGenericsTests.TestSemantic_UnitImpl_GenericVar_Resolves;
var
  U: TUnit;
begin
  U := AnalyseUnit(SrcUnitImplGenericVar);
  try
    AssertEquals('impl var count', 1, U.ImplBlock.Decls.Count);
    AssertTrue('resolved type not nil',
      TVarDecl(U.ImplBlock.Decls.Items[0]).ResolvedType <> nil);
    AssertEquals('resolved type name', 'TBox<string>',
      TVarDecl(U.ImplBlock.Decls.Items[0]).ResolvedType.Name);
  finally
    U.Free;
  end;
end;

procedure TGenericsTests.TestCodegen_UnitIntf_GenericVar_GlobalData;
var
  IR: string;
begin
  IR := GenUnitIR(SrcUnitIntfGenericVar);
  AssertTrue('global data slot for G emitted',
    Pos('data $G', IR) > 0);
  AssertTrue('typeinfo for TBox_Integer emitted',
    Pos('$typeinfo_TBox_Integer', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Multi-instance: same generic class with two different type args     }
{ ------------------------------------------------------------------ }

const
  { Two var decls of the same generic class with different type args.
    Used to fail with 'Type mismatch: expected ''^T'' but got ''^TObject'''
    because '^T' was cached globally under the unsubstituted name after
    the first instantiation, and the unsubstituted constructor-call
    receiver name '<T>' got mutated to '<String>' on the first analysis
    and then incorrectly re-used on the second. }
  SrcTwoInstancesSameGeneric =
    '''
        program P;
        type
          TBox<T> = class
            FValue: T;
            procedure SetIt(V: T);
            begin
              Self.FValue := V
            end;
          end;
        var
          A: TBox<Integer>;
          B: TBox<String>;
        begin end.
        ''';

  SrcTwoInstancesPointerField =
    '''
        program P;
        type
          TCell<T> = class
            FData: ^T;
            procedure SetData(P: ^T);
            begin
              Self.FData := P
            end;
          end;
        var
          CI: TCell<Integer>;
          CS: TCell<String>;
        begin end.
        ''';

procedure TGenericsTests.TestSemantic_Generic_TwoInstancesOfSameClass_Resolve;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcTwoInstancesSameGeneric);
  try
    AssertNotNull('TBox<Integer> instantiated',
      Prog.SymbolTable.FindType('TBox<Integer>'));
    AssertNotNull('TBox<string> instantiated',
      Prog.SymbolTable.FindType('TBox<string>'));
  finally
    Prog.Free;
  end;
end;

const
  { Two instances of the same generic class; one method calls another method
    on the same class.  If the method body is shared across instances without
    re-analysis, the inner Self.SetValue call will resolve to the same
    instance for both — so TBox_String_Init would emit
      call $TBox_Integer_SetValue
    instead of $TBox_String_SetValue.  Per-instance AST body cloning ensures
    each instance has its own analysed body and the correct call targets. }
  SrcTwoInstancesMethodCallsOwn =
    '''
        program P;
        type
          TBox<T> = class
            FValue: T;
            procedure SetValue(V: T);
            begin
              Self.FValue := V
            end;
            procedure Init(V: T);
            begin
              Self.SetValue(V)
            end;
          end;
        var
          A: TBox<Integer>;
          B: TBox<String>;
        begin end.
        ''';

procedure TGenericsTests.TestSemantic_Generic_TwoInstances_PointerFieldDistinctTypes;
var
  Prog: TProgram;
  CI, CS: TRecordTypeDesc;
  FI, FS: TFieldInfo;
begin
  Prog := AnalyseSrc(SrcTwoInstancesPointerField);
  try
    CI := TRecordTypeDesc(Prog.SymbolTable.FindType('TCell<Integer>'));
    CS := TRecordTypeDesc(Prog.SymbolTable.FindType('TCell<string>'));
    AssertNotNull('TCell<Integer> instantiated', CI);
    AssertNotNull('TCell<string>  instantiated', CS);
    FI := CI.FindField('FData');
    FS := CS.FindField('FData');
    AssertNotNull('FData on TCell<Integer>', FI);
    AssertNotNull('FData on TCell<string>',  FS);
    { The two FData fields must resolve to distinct pointer types — '^T'
      must NOT be shared across instances. }
    AssertEquals('FData<Integer> base type',
      '^Integer', FI.TypeDesc.Name);
    AssertEquals('FData<string>  base type',
      '^string',  FS.TypeDesc.Name);
  finally
    Prog.Free;
  end;
end;

procedure TGenericsTests.TestCodegen_Generic_TwoInstances_MethodCallsResolveToOwnInstance;
var
  IR:        string;
  IntInit:   Integer;
  StrInit:   Integer;
  IntBody:   string;
  StrBody:   string;
begin
  IR := GenIR(SrcTwoInstancesMethodCallsOwn);

  { Locate the two Init function bodies in the IR. }
  IntInit := Pos('function $TBox_Integer_Init', IR);
  StrInit := Pos('function $TBox_String_Init', IR);
  AssertTrue('TBox_Integer_Init function emitted', IntInit > 0);
  AssertTrue('TBox_String_Init function emitted',  StrInit > 0);

  { Take a window from each function start until the next 'function ' marker
    (or end of string). }
  if IntInit < StrInit then
  begin
    IntBody := Copy(IR, IntInit, StrInit - IntInit);
    StrBody := Copy(IR, StrInit, Length(IR) - StrInit + 1);
  end
  else
  begin
    StrBody := Copy(IR, StrInit, IntInit - StrInit);
    IntBody := Copy(IR, IntInit, Length(IR) - IntInit + 1);
  end;

  AssertTrue('TBox_Integer_Init body calls $TBox_Integer_SetValue',
    Pos('call $TBox_Integer_SetValue', IntBody) > 0);
  AssertTrue('TBox_String_Init body calls $TBox_String_SetValue',
    Pos('call $TBox_String_SetValue', StrBody) > 0);
end;

initialization
  RegisterTest(TGenericsTests);

end.
