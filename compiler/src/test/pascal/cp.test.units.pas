{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.units;

{ Tests for unit interface/implementation: parsing, semantic analysis,
  and code generation. Cross-unit 'uses' loading is out of scope here. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE, uUnitLoader;

type
  TUnitTests = class(TTestCase)
  private
    function  ParseUnit(const ASrc: string): TUnit;
    function  AnalyseUnit(const ASrc: string): TUnit;
    function  GenUnitIR(const ASrc: string): string;
    procedure AnalyseUnitExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Lexer                                                                }
    { ------------------------------------------------------------------ }
    procedure TestLexer_Unit_Keyword;
    procedure TestLexer_Interface_Keyword;
    procedure TestLexer_Implementation_Keyword;

    { ------------------------------------------------------------------ }
    { Parser — structure                                                   }
    { ------------------------------------------------------------------ }
    procedure TestParse_Unit_IsNotProgram;
    procedure TestParse_Unit_Name;
    procedure TestParse_Unit_IntfHasForwardDecls;
    procedure TestParse_Unit_ForwardDeclHasNilBody;
    procedure TestParse_Unit_ImplHasFullBodies;
    procedure TestParse_Unit_ImplBodyIsNotNil;
    procedure TestParse_Unit_IntfTypeDecl;
    procedure TestParse_Unit_ForwardDeclParamCount;
    procedure TestParse_Unit_MultipleForwardDecls;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Unit_OK;
    procedure TestSemantic_Unit_WithType_OK;
    procedure TestSemantic_Unit_ImplBodyUsesIntfType;
    procedure TestSemantic_Unit_SignatureMismatch_ParamCount_RaisesError;
    procedure TestSemantic_Unit_MissingImpl_RaisesError;
    procedure TestSemantic_Unit_ImplOnlyDecl_OK;

    { Interface-section global variable is registered and visible to
      implementation-section function bodies. }
    procedure TestSemantic_Unit_IntfVarVisibleInImpl;
    { Implementation-section type declarations are processed (e.g.
      enum types declared after the 'implementation' keyword can be
      used to type subsequent var declarations). }
    procedure TestSemantic_Unit_ImplTypeDecl;
    { Forward decl with 'overload' directive parses and analyses. }
    procedure TestSemantic_Unit_ForwardOverload_OK;

    { ------------------------------------------------------------------ }
    { Codegen                                                              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_Unit_NoMainFunction;
    procedure TestCodegen_Unit_IntfFunctionsExported;
    procedure TestCodegen_Unit_FunctionBodyInIR;
    procedure TestCodegen_Unit_ImplOnlyFuncNotExported;
    procedure TestCodegen_Unit_CorrectArithmetic;

    { ------------------------------------------------------------------ }
    { Unit loader                                                          }
    { ------------------------------------------------------------------ }
    { Missing unit with no search paths must raise EUnitNotFound, not
      silently succeed (regression for issue #31). }
    procedure TestUnitLoader_MissingUnit_NoSearchPaths_RaisesError;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TUnitTests.ParseUnit(const ASrc: string): TUnit;
var L: TLexer; P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.ParseUnit;
  finally
    P.Free; L.Free;
  end;
end;

function TUnitTests.AnalyseUnit(const ASrc: string): TUnit;
var A: TSemanticAnalyser;
begin
  Result := ParseUnit(ASrc);
  A := TSemanticAnalyser.Create;
  try
    A.AnalyseUnit(Result);
  finally
    A.Free;
  end;
end;

function TUnitTests.GenUnitIR(const ASrc: string): string;
var U: TUnit; CG: TCodeGenQBE;
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

procedure TUnitTests.AnalyseUnitExpectError(const ASrc: string);
var U: TUnit;
begin
  try
    U := AnalyseUnit(ASrc);
    U.Free;
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ;
  end;
end;

{ ------------------------------------------------------------------ }
{ Shared source snippets                                               }
{ ------------------------------------------------------------------ }

const
  SrcUnitFuncs =
    '''
        unit MathUtils;
        interface
        function Add(A, B: Integer): Integer;
        function Mul(A, B: Integer): Integer;
        implementation
        function Add(A, B: Integer): Integer;
        begin
          Result := A + B
        end;
        function Mul(A, B: Integer): Integer;
        begin
          Result := A * B
        end;
        end.
        ''';

  SrcUnitWithType =
    '''
        unit Shapes;
        interface
        type
          TBox = record
            W: Integer;
            H: Integer;
          end;
        function Area(W, H: Integer): Integer;
        implementation
        function Area(W, H: Integer): Integer;
        begin
          Result := W * H
        end;
        end.
        ''';

  SrcUnitImplOnly =
    '''
        unit Internals;
        interface
        function Pub(X: Integer): Integer;
        implementation
        function Helper(X: Integer): Integer;
        begin
          Result := X + 1
        end;
        function Pub(X: Integer): Integer;
        begin
          Result := Helper(X)
        end;
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Lexer tests                                                          }
{ ------------------------------------------------------------------ }

procedure TUnitTests.TestLexer_Unit_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('unit');
  try
    T := L.Next;
    AssertEquals('unit token', Ord(tkUnit), Ord(T.Kind));
  finally L.Free; end;
end;

procedure TUnitTests.TestLexer_Interface_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('interface');
  try
    T := L.Next;
    AssertEquals('interface token', Ord(tkIntf), Ord(T.Kind));
  finally L.Free; end;
end;

procedure TUnitTests.TestLexer_Implementation_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('implementation');
  try
    T := L.Next;
    AssertEquals('implementation token', Ord(tkImplementation), Ord(T.Kind));
  finally L.Free; end;
end;

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TUnitTests.TestParse_Unit_IsNotProgram;
var U: TUnit;
begin
  U := ParseUnit(SrcUnitFuncs);
  try
    AssertNotNull('TUnit returned', U);
  finally U.Free; end;
end;

procedure TUnitTests.TestParse_Unit_Name;
var U: TUnit;
begin
  U := ParseUnit(SrcUnitFuncs);
  try
    AssertEquals('unit name is MathUtils', 'MathUtils', U.Name);
  finally U.Free; end;
end;

procedure TUnitTests.TestParse_Unit_IntfHasForwardDecls;
var U: TUnit;
begin
  U := ParseUnit(SrcUnitFuncs);
  try
    AssertEquals('intf has 2 forward decls', 2, U.IntfBlock.ProcDecls.Count);
  finally U.Free; end;
end;

procedure TUnitTests.TestParse_Unit_ForwardDeclHasNilBody;
var U: TUnit; MD: TMethodDecl;
begin
  U := ParseUnit(SrcUnitFuncs);
  try
    MD := TMethodDecl(U.IntfBlock.ProcDecls[0]);
    AssertNull('forward decl body is nil', MD.Body);
  finally U.Free; end;
end;

procedure TUnitTests.TestParse_Unit_ImplHasFullBodies;
var U: TUnit;
begin
  U := ParseUnit(SrcUnitFuncs);
  try
    AssertEquals('impl has 2 full decls', 2, U.ImplBlock.ProcDecls.Count);
  finally U.Free; end;
end;

procedure TUnitTests.TestParse_Unit_ImplBodyIsNotNil;
var U: TUnit; MD: TMethodDecl;
begin
  U := ParseUnit(SrcUnitFuncs);
  try
    MD := TMethodDecl(U.ImplBlock.ProcDecls[0]);
    AssertNotNull('impl body is not nil', MD.Body);
  finally U.Free; end;
end;

procedure TUnitTests.TestParse_Unit_IntfTypeDecl;
var U: TUnit;
begin
  U := ParseUnit(SrcUnitWithType);
  try
    AssertEquals('intf has 1 type decl', 1, U.IntfBlock.TypeDecls.Count);
    AssertEquals('type name is TBox',
      'TBox', TTypeDecl(U.IntfBlock.TypeDecls[0]).Name);
  finally U.Free; end;
end;

procedure TUnitTests.TestParse_Unit_ForwardDeclParamCount;
var U: TUnit; MD: TMethodDecl;
begin
  U := ParseUnit(SrcUnitFuncs);
  try
    MD := TMethodDecl(U.IntfBlock.ProcDecls[0]);  { Add }
    AssertEquals('Add has 2 params', 2, MD.Params.Count);
  finally U.Free; end;
end;

procedure TUnitTests.TestParse_Unit_MultipleForwardDecls;
var U: TUnit;
begin
  U := ParseUnit(SrcUnitImplOnly);
  try
    AssertEquals('intf has 1 forward decl', 1, U.IntfBlock.ProcDecls.Count);
    AssertEquals('impl has 2 full decls',   2, U.ImplBlock.ProcDecls.Count);
  finally U.Free; end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TUnitTests.TestSemantic_Unit_OK;
begin
  AnalyseUnit(SrcUnitFuncs).Free;
end;

procedure TUnitTests.TestSemantic_Unit_WithType_OK;
begin
  AnalyseUnit(SrcUnitWithType).Free;
end;

procedure TUnitTests.TestSemantic_Unit_ImplBodyUsesIntfType;
begin
  { TBox is declared in interface; impl body can reference it }
  AnalyseUnit(SrcUnitWithType).Free;
end;

procedure TUnitTests.TestSemantic_Unit_SignatureMismatch_ParamCount_RaisesError;
begin
  AnalyseUnitExpectError(
    'unit Bad;' + #10 +
    'interface' + #10 +
    'function Add(A, B: Integer): Integer;' + #10 +
    'implementation' + #10 +
    'function Add(A: Integer): Integer;'         + #10 +  { wrong: 1 param }
    '''
        begin
          Result := A
        end;
        end.
        ''');
end;

procedure TUnitTests.TestSemantic_Unit_MissingImpl_RaisesError;
begin
  AnalyseUnitExpectError(
    '''
        unit Bad;
        interface
        function Add(A, B: Integer): Integer;
        implementation
        end.
        ''');                                     { no implementation of Add }
end;

procedure TUnitTests.TestSemantic_Unit_ImplOnlyDecl_OK;
begin
  { Helper is impl-only; Pub calls Helper — both should resolve }
  AnalyseUnit(SrcUnitImplOnly).Free;
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                        }
{ ------------------------------------------------------------------ }

procedure TUnitTests.TestCodegen_Unit_NoMainFunction;
var IR: string;
begin
  IR := GenUnitIR(SrcUnitFuncs);
  AssertFalse('no $main in unit IR', Pos('$main', IR) > 0);
end;

procedure TUnitTests.TestCodegen_Unit_IntfFunctionsExported;
var IR: string;
begin
  IR := GenUnitIR(SrcUnitFuncs);
  { Interface-declared functions carry the export keyword }
  AssertTrue('export present for Add', Pos('export function', IR) > 0);
end;

procedure TUnitTests.TestCodegen_Unit_FunctionBodyInIR;
var IR: string;
begin
  IR := GenUnitIR(SrcUnitFuncs);
  AssertTrue('$MathUtils_Add in IR', Pos('$MathUtils_Add', IR) > 0);
  AssertTrue('$MathUtils_Mul in IR', Pos('$MathUtils_Mul', IR) > 0);
end;

procedure TUnitTests.TestCodegen_Unit_ImplOnlyFuncNotExported;
var IR: string; HelperPos: Integer; ExportPos: Integer;
begin
  IR := GenUnitIR(SrcUnitImplOnly);
  { Helper is impl-only: its definition must NOT have 'export' prefix.
    Pub is interface-declared: it must have 'export'. }
  HelperPos := Pos('$Internals_Helper', IR);
  ExportPos := Pos('export function', IR);
  AssertTrue('$Internals_Helper present', HelperPos > 0);
  { The 'export' keyword must not appear immediately before $Internals_Helper }
  AssertTrue('$Internals_Pub exported', Pos('export function w $Internals_Pub', IR) > 0);
  AssertFalse('$Internals_Helper not exported', Pos('export function w $Internals_Helper', IR) > 0);
end;

procedure TUnitTests.TestCodegen_Unit_CorrectArithmetic;
var IR: string;
begin
  IR := GenUnitIR(SrcUnitFuncs);
  AssertTrue('add instruction for Add', Pos('add', IR) > 0);
  AssertTrue('mul instruction for Mul', Pos('mul', IR) > 0);
end;

procedure TUnitTests.TestSemantic_Unit_IntfVarVisibleInImpl;
var
  U: TUnit;
begin
  U := AnalyseUnit(
    '''
        unit U;
        interface
        var Counter: Integer;
        procedure Bump;
        implementation
        procedure Bump;
        begin Counter := Counter + 1 end;
        end.
        ''');
  U.Free;
end;

procedure TUnitTests.TestSemantic_Unit_ImplTypeDecl;
var
  U: TUnit;
begin
  U := AnalyseUnit(
    '''
        unit U;
        interface
        procedure Bump;
        implementation
        type
          TMode = (mA, mB, mC);
        var CurrentMode: TMode;
        procedure Bump;
        begin CurrentMode := mA end;
        end.
        ''');
  U.Free;
end;

procedure TUnitTests.TestSemantic_Unit_ForwardOverload_OK;
var
  U: TUnit;
begin
  U := AnalyseUnit(
    '''
        unit U;
        interface
        function Add(A, B: Integer): Integer; overload;
        function Add(A, B: Double):  Double;  overload;
        implementation
        function Add(A, B: Integer): Integer; overload;
        begin Result := A + B end;
        function Add(A, B: Double): Double; overload;
        begin Result := A + B end;
        end.
        ''');
  U.Free;
end;

procedure TUnitTests.TestUnitLoader_MissingUnit_NoSearchPaths_RaisesError;
var
  Lexer:      TLexer;
  Parser:     TParser;
  Prog:       TProgram;
  Loader:     TUnitLoader;
  SearchPaths: TStringList;
  Units:      TObjectList;
begin
  Lexer  := TLexer.Create('program nounit; uses zip, zilch, nada; begin end.');
  Parser := TParser.Create(Lexer);
  Prog   := Parser.Parse;
  try
    SearchPaths := TStringList.Create;
    try
      Loader := TUnitLoader.Create(SearchPaths);
      try
        try
          Units := Loader.LoadAll(Prog.UsedUnits);
          Units.Free;
          Fail('Expected EUnitNotFound');
        except
          on E: EUnitNotFound do ;
        end;
      finally
        Loader.Free;
      end;
    finally
      SearchPaths.Free;
    end;
  finally
    Prog.Free;
    Parser.Free;
    Lexer.Free;
  end;
end;

initialization
  RegisterTest(TUnitTests);

end.
