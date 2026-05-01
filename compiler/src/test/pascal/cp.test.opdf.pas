{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

unit cp.test.opdf;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSemantic, uDebugOPDF;

type
  TOPDFTests = class(TTestCase)
  private
    function GenOPDF(const ASrc: string): string;
    function Contains(const AText, AFragment: string): Boolean;
  published
    procedure TestOPDF_SectionDeclaration;
    procedure TestOPDF_HeaderMagic;
    procedure TestOPDF_HeaderVersion;
    procedure TestOPDF_TotalRecordsPatched;
    procedure TestOPDF_Primitive_Integer;
    procedure TestOPDF_Primitive_Boolean;
    procedure TestOPDF_Primitive_Int64;
    procedure TestOPDF_AnsiStr_Record;
    procedure TestOPDF_GlobalVar_QuadLabel;
    procedure TestOPDF_GlobalVar_RecType;
    procedure TestOPDF_Enum_RecType;
    procedure TestOPDF_Enum_MemberName;
    procedure TestOPDF_Class_RecType;
    procedure TestOPDF_Class_VtableRef;
    procedure TestOPDF_FunctionScope_RecType;
    procedure TestOPDF_FunctionScope_LowPC;
    procedure TestOPDF_Parameter_RecType;
    procedure TestOPDF_LocalVar_RecType;
    procedure TestOPDF_LocalVar_RBPOffset;
    procedure TestOPDF_LineInfo_RecType;
    procedure TestOPDF_LineInfo_FileName;
    procedure TestOPDF_LineInfo_LineNumber;
    procedure TestOPDF_MainScope_RecType;
    procedure TestOPDF_MainScope_LowPC;
    procedure TestOPDF_MainScope_LineInfo;
    { Step 6c }
    procedure TestOPDF_Pointer_RecType;
    procedure TestOPDF_Array_Static_RecType;
    procedure TestOPDF_Array_Static_IsDynamic;
    procedure TestOPDF_Set_RecType;
    procedure TestOPDF_Set_SizeInBytes;
    procedure TestOPDF_Property_RecType;
    procedure TestOPDF_Interface_RecType;
    procedure TestOPDF_Constant_OrdRecord;
    procedure TestOPDF_Constant_OrdValue;
    procedure TestOPDF_Constant_StrRecord;
    procedure TestOPDF_UnitDir_Present;
    procedure TestOPDF_UnitDir_UnitCount;
  end;

implementation

function TOPDFTests.GenOPDF(const ASrc: string): string;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  E:  TOPDFEmitter;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse;
  A  := TSemanticAnalyser.Create;
  try
    A.Analyse(Pr);
    E := TOPDFEmitter.Create(Pr, 'test.pas');
    try
      Result := E.GetOutput;
    finally
      E.Free;
    end;
  finally
    A.Free;
    Pr.Free;
    P.Free;
    L.Free;
  end;
end;

function TOPDFTests.Contains(const AText, AFragment: string): Boolean;
begin
  Result := Pos(AFragment, AText) > 0;
end;

{ ------------------------------------------------------------------ }

procedure TOPDFTests.TestOPDF_SectionDeclaration;
var
  Out: string;
begin
  Out := GenOPDF('program P; begin end.');
  AssertTrue('section directive present', Contains(Out, '.section .opdf'));
end;

procedure TOPDFTests.TestOPDF_HeaderMagic;
var
  Out: string;
begin
  Out := GenOPDF('program P; begin end.');
  AssertTrue('OPDF magic bytes present', Contains(Out, '.byte 79, 80, 68, 70'));
end;

procedure TOPDFTests.TestOPDF_HeaderVersion;
var
  Out: string;
begin
  Out := GenOPDF('program P; begin end.');
  AssertTrue('version word present', Contains(Out, '.word 1'));
end;

procedure TOPDFTests.TestOPDF_TotalRecordsPatched;
var
  Out: string;
begin
  Out := GenOPDF('program P; var X: Integer; begin end.');
  AssertFalse('TotalRecords not still zero placeholder',
    Contains(Out, '.int  0                        # TotalRecords'));
end;

procedure TOPDFTests.TestOPDF_Primitive_Integer;
var
  Out: string;
begin
  Out := GenOPDF('program P; var X: Integer; begin end.');
  AssertTrue('recPrimitive Integer comment', Contains(Out, '# recPrimitive: Integer'));
  AssertTrue('Integer name emitted', Contains(Out, '.ascii "Integer"'));
end;

procedure TOPDFTests.TestOPDF_Primitive_Boolean;
var
  Out: string;
begin
  Out := GenOPDF('program P; begin end.');
  AssertTrue('recPrimitive Boolean present', Contains(Out, '# recPrimitive: Boolean'));
end;

procedure TOPDFTests.TestOPDF_Primitive_Int64;
var
  Out: string;
begin
  Out := GenOPDF('program P; begin end.');
  AssertTrue('recPrimitive Int64 present', Contains(Out, '# recPrimitive: Int64'));
end;

procedure TOPDFTests.TestOPDF_AnsiStr_Record;
var
  Out: string;
begin
  Out := GenOPDF('program P; begin end.');
  AssertTrue('recAnsiStr present', Contains(Out, '# recAnsiStr'));
  AssertTrue('AnsiString name emitted', Contains(Out, '.ascii "AnsiString"'));
end;

procedure TOPDFTests.TestOPDF_GlobalVar_QuadLabel;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'      + LineEnding +
    'var MyVar: Integer;' + LineEnding +
    'begin end.');
  AssertTrue('global var .quad label', Contains(Out, '.quad MyVar'));
end;

procedure TOPDFTests.TestOPDF_GlobalVar_RecType;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'      + LineEnding +
    'var MyVar: Integer;' + LineEnding +
    'begin end.');
  AssertTrue('recGlobalVar comment', Contains(Out, '# recGlobalVar: MyVar'));
end;

procedure TOPDFTests.TestOPDF_Enum_RecType;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'                              + LineEnding +
    'type TColor = (clRed, clGreen, clBlue);' + LineEnding +
    'begin end.');
  AssertTrue('recEnum comment', Contains(Out, '# recEnum: TColor'));
end;

procedure TOPDFTests.TestOPDF_Enum_MemberName;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'                              + LineEnding +
    'type TColor = (clRed, clGreen, clBlue);' + LineEnding +
    'begin end.');
  AssertTrue('enum member name in output', Contains(Out, '.ascii "clRed"'));
  AssertTrue('second member', Contains(Out, '.ascii "clBlue"'));
end;

procedure TOPDFTests.TestOPDF_Class_RecType;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'              + LineEnding +
    'type'                    + LineEnding +
    '  TDog = class'          + LineEnding +
    '    FName: string;'      + LineEnding +
    '  end;'                  + LineEnding +
    'begin end.');
  AssertTrue('recClass comment', Contains(Out, '# recClass: TDog'));
end;

procedure TOPDFTests.TestOPDF_Class_VtableRef;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'              + LineEnding +
    'type'                    + LineEnding +
    '  TDog = class'          + LineEnding +
    '    FName: string;'      + LineEnding +
    '  end;'                  + LineEnding +
    'begin end.');
  AssertTrue('vtable reference in class record', Contains(Out, 'vtable_TDog'));
end;

procedure TOPDFTests.TestOPDF_FunctionScope_RecType;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'                + LineEnding +
    'procedure Greet;'          + LineEnding +
    'begin end;'                + LineEnding +
    'begin end.');
  AssertTrue('recFunctionScope comment', Contains(Out, '# recFunctionScope: Greet'));
end;

procedure TOPDFTests.TestOPDF_FunctionScope_LowPC;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'                + LineEnding +
    'procedure Greet;'          + LineEnding +
    'begin end;'                + LineEnding +
    'begin end.');
  AssertTrue('LowPC label reference', Contains(Out, '.quad Greet'));
end;

procedure TOPDFTests.TestOPDF_Parameter_RecType;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'                          + LineEnding +
    'procedure Greet(Name: string);'      + LineEnding +
    'begin end;'                          + LineEnding +
    'begin end.');
  AssertTrue('recParameter comment', Contains(Out, '# recParameter: Name'));
end;

procedure TOPDFTests.TestOPDF_LocalVar_RecType;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'                  + LineEnding +
    'procedure Compute;'          + LineEnding +
    'var Total: Integer;'         + LineEnding +
    'begin end;'                  + LineEnding +
    'begin end.');
  AssertTrue('recLocalVar comment', Contains(Out, '# recLocalVar: Total'));
end;

procedure TOPDFTests.TestOPDF_LocalVar_RBPOffset;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'                  + LineEnding +
    'procedure Compute;'          + LineEnding +
    'var Total: Integer;'         + LineEnding +
    'begin end;'                  + LineEnding +
    'begin end.');
  AssertTrue('RBP offset line present', Contains(Out, '# LocationData (RBP offset)'));
end;

procedure TOPDFTests.TestOPDF_LineInfo_RecType;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'              + LineEnding +
    'procedure Work;'         + LineEnding +
    'var X: Integer;'         + LineEnding +
    'begin'                   + LineEnding +
    '  X := 1;'               + LineEnding +
    'end;'                    + LineEnding +
    'begin end.');
  AssertTrue('recLineInfo record present', Contains(Out, '# recLineInfo'));
end;

procedure TOPDFTests.TestOPDF_LineInfo_FileName;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'              + LineEnding +
    'procedure Work;'         + LineEnding +
    'var X: Integer;'         + LineEnding +
    'begin'                   + LineEnding +
    '  X := 1;'               + LineEnding +
    'end;'                    + LineEnding +
    'begin end.');
  AssertTrue('source filename in line info', Contains(Out, '.ascii "test.pas"'));
end;

procedure TOPDFTests.TestOPDF_LineInfo_LineNumber;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'              + LineEnding +
    'procedure Work;'         + LineEnding +
    'var X: Integer;'         + LineEnding +
    'begin'                   + LineEnding +
    '  X := 1;'               + LineEnding +
    'end;'                    + LineEnding +
    'begin end.');
  AssertTrue('line 5 recorded', Contains(Out, '.int  5  # LineNumber'));
end;

procedure TOPDFTests.TestOPDF_MainScope_RecType;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'      + LineEnding +
    'var X: Integer;' + LineEnding +
    'begin'           + LineEnding +
    '  X := 1;'       + LineEnding +
    'end.');
  AssertTrue('recFunctionScope for main', Contains(Out, '# recFunctionScope: P'));
end;

procedure TOPDFTests.TestOPDF_MainScope_LowPC;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'      + LineEnding +
    'var X: Integer;' + LineEnding +
    'begin'           + LineEnding +
    '  X := 1;'       + LineEnding +
    'end.');
  AssertTrue('main LowPC label', Contains(Out, '.quad main'));
end;

procedure TOPDFTests.TestOPDF_MainScope_LineInfo;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'      + LineEnding +
    'var X: Integer;' + LineEnding +
    'begin'           + LineEnding +
    '  X := 1;'       + LineEnding +
    'end.');
  AssertTrue('line 4 in main body recorded', Contains(Out, '.int  4  # LineNumber'));
end;

procedure TOPDFTests.TestOPDF_Pointer_RecType;
var
  Out: string;
begin
  { Use ^Integer as a class field type — inline pointer types work
    in field/var positions even though 'type T = ^Foo' in the type
    section is not yet parsed }
  Out := GenOPDF(
    'program P;'              + LineEnding +
    'type TFoo = class'       + LineEnding +
    '  FNext: ^Integer;'      + LineEnding +
    'end;'                    + LineEnding +
    'begin end.');
  AssertTrue('recPointer comment', Contains(Out, '# recPointer: ^Integer'));
end;

procedure TOPDFTests.TestOPDF_Array_Static_RecType;
var
  Out: string;
begin
  { Inline array type in global var — type section array decls not yet parsed }
  Out := GenOPDF(
    'program P;'                           + LineEnding +
    'var A: array[1..5] of Integer;'       + LineEnding +
    'begin end.');
  AssertTrue('recArray comment',
    Contains(Out, '# recArray (static): array[1..5] of Integer'));
end;

procedure TOPDFTests.TestOPDF_Array_Static_IsDynamic;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'                           + LineEnding +
    'var A: array[1..5] of Integer;'       + LineEnding +
    'begin end.');
  AssertTrue('IsDynamic=0 for static array', Contains(Out, '.byte 0  # IsDynamic'));
end;

procedure TOPDFTests.TestOPDF_Set_RecType;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'                                   + LineEnding +
    'type'                                         + LineEnding +
    '  TDays = (Mon, Tue, Wed);'                   + LineEnding +
    '  TDaySet = set of TDays;'                    + LineEnding +
    'var S: TDaySet;'                              + LineEnding +
    'begin end.');
  AssertTrue('recSet comment', Contains(Out, '# recSet: TDaySet'));
end;

procedure TOPDFTests.TestOPDF_Set_SizeInBytes;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'                                   + LineEnding +
    'type'                                         + LineEnding +
    '  TDays = (Mon, Tue, Wed);'                   + LineEnding +
    '  TDaySet = set of TDays;'                    + LineEnding +
    'var S: TDaySet;'                              + LineEnding +
    'begin end.');
  AssertTrue('SizeInBytes=4 for small set', Contains(Out, '.byte 4  # SizeInBytes'));
end;

procedure TOPDFTests.TestOPDF_Property_RecType;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'                                      + LineEnding +
    'type TFoo = class'                               + LineEnding +
    '  FVal: Integer;'                                + LineEnding +
    '  property Val: Integer read FVal write FVal;'  + LineEnding +
    'end;'                                            + LineEnding +
    'begin end.');
  AssertTrue('recProperty comment', Contains(Out, '# recProperty: Val'));
end;

procedure TOPDFTests.TestOPDF_Interface_RecType;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'                    + LineEnding +
    'type IGreeter = interface'     + LineEnding +
    '  procedure Greet;'            + LineEnding +
    'end;'                          + LineEnding +
    'begin end.');
  AssertTrue('recInterface comment', Contains(Out, '# recInterface: IGreeter'));
end;

procedure TOPDFTests.TestOPDF_Constant_OrdRecord;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'       + LineEnding +
    'const MaxVal = 100;' + LineEnding +
    'begin end.');
  AssertTrue('recConstant for integer', Contains(Out, '# recConstant: MaxVal'));
end;

procedure TOPDFTests.TestOPDF_Constant_OrdValue;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'          + LineEnding +
    'const MaxVal = 100;' + LineEnding +
    'begin end.');
  AssertTrue('constant value embedded', Contains(Out, '.quad 100  # Value'));
end;

procedure TOPDFTests.TestOPDF_Constant_StrRecord;
var
  Out: string;
begin
  Out := GenOPDF(
    'program P;'                  + LineEnding +
    'const Greeting = ''Hello'';' + LineEnding +
    'begin end.');
  AssertTrue('recConstant for string', Contains(Out, '# recConstant: Greeting'));
end;

procedure TOPDFTests.TestOPDF_UnitDir_Present;
var
  Out: string;
begin
  Out := GenOPDF('program P; begin end.');
  AssertTrue('recUnitDirectory present', Contains(Out, '# recUnitDirectory'));
end;

procedure TOPDFTests.TestOPDF_UnitDir_UnitCount;
var
  Out: string;
begin
  Out := GenOPDF('program P; begin end.');
  AssertTrue('unit count is 1', Contains(Out, '.int  1  # UnitCount'));
end;

initialization
  RegisterTest(TOPDFTests);

end.
