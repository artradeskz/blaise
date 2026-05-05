{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.properties;

{$mode objfpc}{$H+}

{ Tests for Pascal property declarations — field-backed and method-backed.
  Properties are transparent syntactic sugar: reads and writes redirect to
  a backing field or method accessor. }

interface

uses
  Classes, SysUtils, StrUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TPropertyTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_Property_FieldBackedReadOnly;
    procedure TestParse_Property_FieldBackedReadWrite;
    procedure TestParse_Property_MethodBackedRead;
    procedure TestParse_Property_MethodBackedReadWrite;
    procedure TestParse_Property_CountInClassDef;

    { ------------------------------------------------------------------ }
    { Semantic — field-backed                                              }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Property_FieldBacked_OK;
    procedure TestSemantic_Property_FieldBacked_TypeResolved;
    procedure TestSemantic_Property_ReadOnly_WriteRaisesError;
    procedure TestSemantic_Property_ReadWrite_OK;

    { ------------------------------------------------------------------ }
    { Semantic — method-backed                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Property_MethodBacked_OK;
    procedure TestSemantic_Property_MethodBacked_TypeResolved;

    { ------------------------------------------------------------------ }
    { Codegen — field-backed                                               }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_Property_FieldBacked_Read_EmitsLoad;
    procedure TestCodegen_Property_FieldBacked_Write_EmitsStore;

    { ------------------------------------------------------------------ }
    { Codegen — method-backed                                              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_Property_MethodBacked_Read_EmitsCall;

    { ------------------------------------------------------------------ }
    { Indexed properties                                                   }
    { ------------------------------------------------------------------ }
    procedure TestParse_IndexedProperty_ParamNameAndType;
    procedure TestSemantic_IndexedProperty_Read_OK;
    procedure TestSemantic_IndexedProperty_Write_OK;
    procedure TestSemantic_IndexedProperty_MissingIndex_RaisesError;
    procedure TestCodegen_IndexedProperty_Read_EmitsGetterWithIndex;
    procedure TestCodegen_IndexedProperty_Write_EmitsSetterWithIndex;

    { Regression: 'Outer.Inner.Indexed[Variable]' — chained base + indexed
      property read with a variable index.  Previously crashed the codegen
      because the analyser skipped AnalyseExpr on PropIndexExpr in the
      Base<>nil branch, leaving its ResolvedType nil. }
    procedure TestCodegen_IndexedProperty_ChainedBase_VarIndex_Compiles;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Source constants                                                     }
{ ------------------------------------------------------------------ }

const
  SrcFieldBackedReadOnly =
    'program P;'                           + LineEnding +
    'type'                                 + LineEnding +
    '  TBox = class'                       + LineEnding +
    '    FCount: Integer;'                 + LineEnding +
    '    property Count: Integer read FCount;' + LineEnding +
    '  end;'                               + LineEnding +
    'begin'                                + LineEnding +
    'end.';

  SrcFieldBackedReadWrite =
    'program P;'                                          + LineEnding +
    'type'                                                + LineEnding +
    '  TBox = class'                                      + LineEnding +
    '    FValue: Integer;'                                + LineEnding +
    '    property Value: Integer read FValue write FValue;' + LineEnding +
    '  end;'                                              + LineEnding +
    'begin'                                               + LineEnding +
    'end.';

  SrcMethodBackedRead =
    'program P;'                               + LineEnding +
    'type'                                     + LineEnding +
    '  TBox = class'                           + LineEnding +
    '    FCount: Integer;'                     + LineEnding +
    '    function GetCount: Integer;'          + LineEnding +
    '    begin'                                + LineEnding +
    '      Result := Self.FCount'              + LineEnding +
    '    end;'                                 + LineEnding +
    '    property Count: Integer read GetCount;' + LineEnding +
    '  end;'                                   + LineEnding +
    'begin'                                    + LineEnding +
    'end.';

  SrcMethodBackedReadWrite =
    'program P;'                                            + LineEnding +
    'type'                                                  + LineEnding +
    '  TBox = class'                                        + LineEnding +
    '    FValue: Integer;'                                  + LineEnding +
    '    function GetValue: Integer;'                       + LineEnding +
    '    begin'                                             + LineEnding +
    '      Result := Self.FValue'                           + LineEnding +
    '    end;'                                              + LineEnding +
    '    procedure SetValue(AVal: Integer);'                + LineEnding +
    '    begin'                                             + LineEnding +
    '      Self.FValue := AVal'                             + LineEnding +
    '    end;'                                              + LineEnding +
    '    property Value: Integer read GetValue write SetValue;' + LineEnding +
    '  end;'                                                + LineEnding +
    'begin'                                                 + LineEnding +
    'end.';

  SrcFieldBackedUsage =
    'program P;'                                          + LineEnding +
    'type'                                                + LineEnding +
    '  TBox = class'                                      + LineEnding +
    '    FValue: Integer;'                                + LineEnding +
    '    property Value: Integer read FValue write FValue;' + LineEnding +
    '  end;'                                              + LineEnding +
    'var B: TBox;'                                        + LineEnding +
    'begin'                                               + LineEnding +
    '  B := TBox.Create;'                                 + LineEnding +
    '  B.Value := 42;'                                    + LineEnding +
    '  WriteLn(B.Value)'                                  + LineEnding +
    'end.';

  SrcMethodBackedReadUsage =
    'program P;'                               + LineEnding +
    'type'                                     + LineEnding +
    '  TBox = class'                           + LineEnding +
    '    FCount: Integer;'                     + LineEnding +
    '    function GetCount: Integer;'          + LineEnding +
    '    begin'                                + LineEnding +
    '      Result := Self.FCount'              + LineEnding +
    '    end;'                                 + LineEnding +
    '    property Count: Integer read GetCount;' + LineEnding +
    '  end;'                                   + LineEnding +
    'var B: TBox;'                             + LineEnding +
    'begin'                                    + LineEnding +
    '  B := TBox.Create;'                      + LineEnding +
    '  WriteLn(B.Count)'                       + LineEnding +
    'end.';

  SrcIndexedPropDecl =
    'program P;'                                                   + LineEnding +
    'type'                                                         + LineEnding +
    '  TList = class'                                              + LineEnding +
    '    function Get(AIndex: Integer): Integer;'                  + LineEnding +
    '    begin'                                                    + LineEnding +
    '      Result := AIndex'                                       + LineEnding +
    '    end;'                                                     + LineEnding +
    '    procedure Put(AIndex: Integer; AValue: Integer);'         + LineEnding +
    '    begin'                                                    + LineEnding +
    '    end;'                                                     + LineEnding +
    '    property Items[Index: Integer]: Integer read Get write Put;' + LineEnding +
    '  end;'                                                       + LineEnding +
    'begin'                                                        + LineEnding +
    'end.';

  SrcIndexedPropReadUsage =
    'program P;'                                                   + LineEnding +
    'type'                                                         + LineEnding +
    '  TList = class'                                              + LineEnding +
    '    function Get(AIndex: Integer): Integer;'                  + LineEnding +
    '    begin'                                                    + LineEnding +
    '      Result := AIndex'                                       + LineEnding +
    '    end;'                                                     + LineEnding +
    '    property Items[Index: Integer]: Integer read Get;'        + LineEnding +
    '  end;'                                                       + LineEnding +
    'var L: TList; V: Integer;'                                    + LineEnding +
    'begin'                                                        + LineEnding +
    '  L := TList.Create;'                                         + LineEnding +
    '  V := L.Items[3];'                                           + LineEnding +
    '  WriteLn(V)'                                                 + LineEnding +
    'end.';

  SrcIndexedPropWriteUsage =
    'program P;'                                                   + LineEnding +
    'type'                                                         + LineEnding +
    '  TList = class'                                              + LineEnding +
    '    FValue: Integer;'                                         + LineEnding +
    '    function Get(AIndex: Integer): Integer;'                  + LineEnding +
    '    begin'                                                    + LineEnding +
    '      Result := AIndex'                                       + LineEnding +
    '    end;'                                                     + LineEnding +
    '    procedure Put(AIndex: Integer; AValue: Integer);'         + LineEnding +
    '    begin'                                                    + LineEnding +
    '      Self.FValue := AValue'                                  + LineEnding +
    '    end;'                                                     + LineEnding +
    '    property Items[Index: Integer]: Integer read Get write Put;' + LineEnding +
    '  end;'                                                       + LineEnding +
    'var L: TList;'                                                + LineEnding +
    'begin'                                                        + LineEnding +
    '  L := TList.Create;'                                         + LineEnding +
    '  L.Items[2] := 42'                                           + LineEnding +
    'end.';

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TPropertyTests.ParseSrc(const ASrc: string): TProgram;
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

function TPropertyTests.AnalyseSrc(const ASrc: string): TProgram;
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

function TPropertyTests.GenIR(const ASrc: string): string;
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

procedure TPropertyTests.AnalyseExpectError(const ASrc: string);
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
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TPropertyTests.TestParse_Property_FieldBackedReadOnly;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  PD:   TPropertyDecl;
begin
  Prog := ParseSrc(SrcFieldBackedReadOnly);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('one property', 1, CD.Properties.Count);
    PD := TPropertyDecl(CD.Properties[0]);
    AssertEquals('property name', 'Count', PD.Name);
    AssertEquals('type name', 'Integer', PD.TypeName);
    AssertEquals('read name', 'FCount', PD.ReadName);
    AssertEquals('write name empty', '', PD.WriteName);
  finally
    Prog.Free;
  end;
end;

procedure TPropertyTests.TestParse_Property_FieldBackedReadWrite;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  PD:   TPropertyDecl;
begin
  Prog := ParseSrc(SrcFieldBackedReadWrite);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    PD := TPropertyDecl(CD.Properties[0]);
    AssertEquals('property name', 'Value', PD.Name);
    AssertEquals('read name', 'FValue', PD.ReadName);
    AssertEquals('write name', 'FValue', PD.WriteName);
  finally
    Prog.Free;
  end;
end;

procedure TPropertyTests.TestParse_Property_MethodBackedRead;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  PD:   TPropertyDecl;
begin
  Prog := ParseSrc(SrcMethodBackedRead);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('one property', 1, CD.Properties.Count);
    PD := TPropertyDecl(CD.Properties[0]);
    AssertEquals('property name', 'Count', PD.Name);
    AssertEquals('read name', 'GetCount', PD.ReadName);
    AssertEquals('write name empty', '', PD.WriteName);
  finally
    Prog.Free;
  end;
end;

procedure TPropertyTests.TestParse_Property_MethodBackedReadWrite;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  PD:   TPropertyDecl;
begin
  Prog := ParseSrc(SrcMethodBackedReadWrite);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    PD := TPropertyDecl(CD.Properties[0]);
    AssertEquals('read name', 'GetValue', PD.ReadName);
    AssertEquals('write name', 'SetValue', PD.WriteName);
  finally
    Prog.Free;
  end;
end;

procedure TPropertyTests.TestParse_Property_CountInClassDef;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(SrcMethodBackedReadWrite);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('one field', 1, CD.Fields.Count);
    AssertEquals('two methods', 2, CD.Methods.Count);
    AssertEquals('one property', 1, CD.Properties.Count);
  finally
    Prog.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic — field-backed                                              }
{ ------------------------------------------------------------------ }

procedure TPropertyTests.TestSemantic_Property_FieldBacked_OK;
begin
  AnalyseSrc(SrcFieldBackedReadWrite).Free;
end;

procedure TPropertyTests.TestSemantic_Property_FieldBacked_TypeResolved;
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
  PI:   TPropertyInfo;
begin
  Prog := AnalyseSrc(SrcFieldBackedReadWrite);
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TBox'));
    AssertNotNull('TBox found', RT);
    PI := RT.FindProperty('Value');
    AssertNotNull('Value property found', PI);
    AssertEquals('type is tyInteger', Ord(tyInteger), Ord(PI.TypeDesc.Kind));
    AssertEquals('read field is FValue', 'FValue', PI.ReadField);
    AssertEquals('write field is FValue', 'FValue', PI.WriteField);
  finally
    Prog.Free;
  end;
end;

procedure TPropertyTests.TestSemantic_Property_ReadOnly_WriteRaisesError;
begin
  AnalyseExpectError(
    'program P;'                                  + LineEnding +
    'type TBox = class'                           + LineEnding +
    '  FCount: Integer;'                          + LineEnding +
    '  property Count: Integer read FCount;'      + LineEnding +
    'end;'                                        + LineEnding +
    'var B: TBox;'                                + LineEnding +
    'begin B := TBox.Create; B.Count := 5 end.'
  );
end;

procedure TPropertyTests.TestSemantic_Property_ReadWrite_OK;
begin
  AnalyseSrc(SrcFieldBackedUsage).Free;
end;

{ ------------------------------------------------------------------ }
{ Semantic — method-backed                                             }
{ ------------------------------------------------------------------ }

procedure TPropertyTests.TestSemantic_Property_MethodBacked_OK;
begin
  AnalyseSrc(SrcMethodBackedReadUsage).Free;
end;

procedure TPropertyTests.TestSemantic_Property_MethodBacked_TypeResolved;
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
  PI:   TPropertyInfo;
begin
  Prog := AnalyseSrc(SrcMethodBackedRead);
  try
    RT := TRecordTypeDesc(Prog.SymbolTable.FindType('TBox'));
    PI := RT.FindProperty('Count');
    AssertNotNull('Count property found', PI);
    AssertEquals('type is tyInteger', Ord(tyInteger), Ord(PI.TypeDesc.Kind));
    AssertEquals('read field empty', '', PI.ReadField);
    AssertEquals('read method is GetCount', 'GetCount', PI.ReadMethod);
  finally
    Prog.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Codegen — field-backed                                               }
{ ------------------------------------------------------------------ }

procedure TPropertyTests.TestCodegen_Property_FieldBacked_Read_EmitsLoad;
var
  IR: string;
begin
  IR := GenIR(SrcFieldBackedUsage);
  { B.Value read → loads FValue field (offset=8, after vptr) }
  AssertTrue('IR emitted for field-backed read', Pos('loadw', IR) > 0);
end;

procedure TPropertyTests.TestCodegen_Property_FieldBacked_Write_EmitsStore;
var
  IR: string;
begin
  IR := GenIR(SrcFieldBackedUsage);
  { B.Value := 42 → stores to FValue field }
  AssertTrue('IR emitted for field-backed write', Pos('storew', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Codegen — method-backed                                              }
{ ------------------------------------------------------------------ }

procedure TPropertyTests.TestCodegen_Property_MethodBacked_Read_EmitsCall;
var
  IR: string;
begin
  IR := GenIR(SrcMethodBackedReadUsage);
  { B.Count → calls $TBox_GetCount }
  AssertTrue('method-backed read emits call to GetCount',
    Pos('TBox_GetCount', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Indexed properties                                                   }
{ ------------------------------------------------------------------ }

procedure TPropertyTests.TestParse_IndexedProperty_ParamNameAndType;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
  PD:   TPropertyDecl;
begin
  Prog := ParseSrc(SrcIndexedPropDecl);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('one property', 1, CD.Properties.Count);
    PD := TPropertyDecl(CD.Properties[0]);
    AssertEquals('property name', 'Items', PD.Name);
    AssertEquals('index param name', 'Index', PD.IndexParamName);
    AssertEquals('index type name', 'Integer', PD.IndexTypeName);
    AssertEquals('read name', 'Get', PD.ReadName);
    AssertEquals('write name', 'Put', PD.WriteName);
  finally
    Prog.Free;
  end;
end;

procedure TPropertyTests.TestSemantic_IndexedProperty_Read_OK;
begin
  AnalyseSrc(SrcIndexedPropReadUsage).Free;
end;

procedure TPropertyTests.TestSemantic_IndexedProperty_Write_OK;
begin
  AnalyseSrc(SrcIndexedPropWriteUsage).Free;
end;

procedure TPropertyTests.TestSemantic_IndexedProperty_MissingIndex_RaisesError;
begin
  AnalyseExpectError(
    'program P;'                                              + LineEnding +
    'type TList = class'                                      + LineEnding +
    '  function Get(AIndex: Integer): Integer;'               + LineEnding +
    '  begin Result := AIndex end;'                           + LineEnding +
    '  property Items[Index: Integer]: Integer read Get;'     + LineEnding +
    'end;'                                                    + LineEnding +
    'var L: TList; V: Integer;'                               + LineEnding +
    'begin L := TList.Create; V := L.Items; WriteLn(V) end.'
  );
end;

procedure TPropertyTests.TestCodegen_IndexedProperty_Read_EmitsGetterWithIndex;
var
  IR: string;
begin
  IR := GenIR(SrcIndexedPropReadUsage);
  AssertTrue('indexed read emits getter call', Pos('call $TList_Get', IR) > 0);
end;

procedure TPropertyTests.TestCodegen_IndexedProperty_Write_EmitsSetterWithIndex;
var
  IR: string;
begin
  IR := GenIR(SrcIndexedPropWriteUsage);
  AssertTrue('indexed write emits setter call', Pos('call $TList_Put', IR) > 0);
end;

procedure TPropertyTests.TestCodegen_IndexedProperty_ChainedBase_VarIndex_Compiles;
const
  Src =
    'program P;'                                                    + LineEnding +
    'type'                                                          + LineEnding +
    '  TItems = class'                                              + LineEnding +
    '    function Get(AIndex: Integer): Integer;'                   + LineEnding +
    '    begin Result := AIndex end;'                               + LineEnding +
    '    property Strings[Index: Integer]: Integer read Get;'       + LineEnding +
    '  end;'                                                        + LineEnding +
    '  TOuter = class'                                              + LineEnding +
    '    FInner: TItems;'                                           + LineEnding +
    '    property Inner: TItems read FInner;'                       + LineEnding +
    '  end;'                                                        + LineEnding +
    'var'                                                           + LineEnding +
    '  O: TOuter;'                                                  + LineEnding +
    '  I, V: Integer;'                                              + LineEnding +
    'begin'                                                         + LineEnding +
    '  O := TOuter.Create;'                                         + LineEnding +
    '  O.FInner := TItems.Create;'                                  + LineEnding +
    '  I := 7;'                                                     + LineEnding +
    '  V := O.Inner.Strings[I];'                                    + LineEnding +
    '  WriteLn(V)'                                                  + LineEnding +
    'end.';
var
  IR: string;
begin
  IR := GenIR(Src);
  { The fix routes both segments through method-backed property reads.
    Inner is field-backed (read FInner) so the inner step is a load; the
    outer Strings[Index] is method-backed and must emit a call to Get
    threaded with the variable I. }
  AssertTrue('outer indexed getter emitted', Pos('call $TItems_Get', IR) > 0);
end;

initialization
  RegisterTest(TPropertyTests);

end.
