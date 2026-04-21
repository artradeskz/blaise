unit cp.test.generics;

{$mode objfpc}{$H+}

{ Tests for generic type monomorphization.
  Phase 3 scope: single type-parameter classes with inline method bodies;
  standalone generic method implementations are not supported yet. }

interface

uses
  Classes, SysUtils, StrUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TGenericsTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
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
    { Codegen — monomorphized types                                        }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_Generic_TypeInfoEmitted;
    procedure TestCodegen_Generic_ConstructorAllocsMemory;
    procedure TestCodegen_Generic_MethodEmitted;
    procedure TestCodegen_Generic_FieldAccessWorks;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Source constants                                                     }
{ ------------------------------------------------------------------ }

const
  SrcGenericOneParam =
    'program P;'                        + LineEnding +
    'type'                              + LineEnding +
    '  TBox<T> = class'                 + LineEnding +
    '    FValue: T;'                    + LineEnding +
    '  end;'                            + LineEnding +
    'begin'                             + LineEnding +
    'end.';

  SrcGenericTwoParams =
    'program P;'                        + LineEnding +
    'type'                              + LineEnding +
    '  TPair<K, V> = class'             + LineEnding +
    '    FKey: K;'                      + LineEnding +
    '    FVal: V;'                      + LineEnding +
    '  end;'                            + LineEnding +
    'begin'                             + LineEnding +
    'end.';

  SrcGenericWithMethod =
    'program P;'                        + LineEnding +
    'type'                              + LineEnding +
    '  TBox<T> = class'                 + LineEnding +
    '    FValue: T;'                    + LineEnding +
    '    function GetValue: T;'         + LineEnding +
    '    procedure SetValue(AVal: T);'  + LineEnding +
    '  end;'                            + LineEnding +
    'begin'                             + LineEnding +
    'end.';

  SrcGenericVarInteger =
    'program P;'                        + LineEnding +
    'type'                              + LineEnding +
    '  TBox<T> = class'                 + LineEnding +
    '    FValue: T;'                    + LineEnding +
    '  end;'                            + LineEnding +
    'var B: TBox<Integer>;'             + LineEnding +
    'begin'                             + LineEnding +
    'end.';

  SrcGenericVarString =
    'program P;'                        + LineEnding +
    'type'                              + LineEnding +
    '  TBox<T> = class'                 + LineEnding +
    '    FValue: T;'                    + LineEnding +
    '  end;'                            + LineEnding +
    'var S: TBox<string>;'              + LineEnding +
    'begin'                             + LineEnding +
    'end.';

  SrcGenericTwoParamVar =
    'program P;'                        + LineEnding +
    'type'                              + LineEnding +
    '  TPair<K, V> = class'             + LineEnding +
    '    FKey: K;'                      + LineEnding +
    '    FVal: V;'                      + LineEnding +
    '  end;'                            + LineEnding +
    'var P: TPair<string, Integer>;'    + LineEnding +
    'begin'                             + LineEnding +
    'end.';

  SrcGenericUsage =
    'program P;'                                     + LineEnding +
    'type'                                           + LineEnding +
    '  TBox<T> = class'                              + LineEnding +
    '    FValue: T;'                                 + LineEnding +
    '    function GetValue: T;'                      + LineEnding +
    '    begin'                                      + LineEnding +
    '      Result := Self.FValue'                    + LineEnding +
    '    end;'                                       + LineEnding +
    '    procedure SetValue(AVal: T);'               + LineEnding +
    '    begin'                                      + LineEnding +
    '      Self.FValue := AVal'                      + LineEnding +
    '    end;'                                       + LineEnding +
    '  end;'                                         + LineEnding +
    'var B: TBox<Integer>;'                          + LineEnding +
    'begin'                                          + LineEnding +
    '  B := TBox<Integer>.Create;'                   + LineEnding +
    '  B.SetValue(42);'                              + LineEnding +
    '  WriteLn(B.GetValue())'                         + LineEnding +
    'end.';

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
  AssertTrue('constructor calls malloc', Pos('call $malloc', IR) > 0);
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

initialization
  RegisterTest(TGenericsTests);

end.
