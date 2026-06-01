{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.multifile;

{ Tests for multi-file compilation: TUnitLoader (search, cycle detection,
  dependency ordering), TSemanticAnalyser.AnalyseUnitForExport (cross-unit
  symbol visibility), and combined code generation via AppendUnit/AppendProgram. }

interface

uses
  Classes, SysUtils, Contnrs, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE,
  uUnitLoader;

type
  TMultifileTests = class(TTestCase)
  private
    FTmpDir: string;
    procedure WriteUnit(const AName, ASrc: string);
    function  MakeSearchPaths: TStringList;
    function  ParseProg(const ASrc: string): TProgram;
    function  ParseUnitSrc(const ASrc: string): TUnit;
  protected
    procedure SetUp; override;
    procedure TearDown; override;
  published
    { ------------------------------------------------------------------ }
    { TUnitLoader                                                          }
    { ------------------------------------------------------------------ }
    procedure TestUnitLoader_LocatesUnitInSearchPath;
    procedure TestUnitLoader_RaisesOnMissingUnit;
    procedure TestUnitLoader_DetectsCycle;
    procedure TestUnitLoader_DependencyOrder;
    { ------------------------------------------------------------------ }
    { AnalyseUnitForExport                                                 }
    { ------------------------------------------------------------------ }
    procedure TestSemanticAnalyser_ExportedTypeVisibleInProgram;
    procedure TestSemanticAnalyser_ExportedFuncVisibleInProgram;
    { ------------------------------------------------------------------ }
    { Combined code generation                                             }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_TwoFileCompile_UnitFuncExported;
    procedure TestCodegen_TwoFileCompile_MainPresent;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

procedure TMultifileTests.SetUp;
begin
  FTmpDir := GetTempDir + 'blaise_mf_' + IntToStr(GetProcessID);
  ForceDirectories(FTmpDir);
end;

procedure TMultifileTests.TearDown;
begin
  { Temp .pas files are left; just attempt to remove the dir. }
  RemoveDir(FTmpDir);
end;

procedure TMultifileTests.WriteUnit(const AName, ASrc: string);
var
  F: TStringList;
begin
  F := TStringList.Create;
  try
    F.Text := ASrc;
    F.SaveToFile(FTmpDir + '/' + AName + '.pas');
  finally
    F.Free;
  end;
end;

function TMultifileTests.MakeSearchPaths: TStringList;
begin
  Result := TStringList.Create;
  Result.Add(FTmpDir);
end;

function TMultifileTests.ParseProg(const ASrc: string): TProgram;
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

function TMultifileTests.ParseUnitSrc(const ASrc: string): TUnit;
var
  L: TLexer;
  P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.ParseUnit;
  finally
    P.Free;
    L.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ TUnitLoader tests                                                    }
{ ------------------------------------------------------------------ }

procedure TMultifileTests.TestUnitLoader_LocatesUnitInSearchPath;
const
  Src =
    '''
        unit MathUtils;
        interface
        function Add(A, B: Integer): Integer;
        implementation
        function Add(A, B: Integer): Integer;
        begin
          Result := A + B
        end;
        end.
        ''';
var
  Paths:  TStringList;
  Loader: TUnitLoader;
  Names:  TStringList;
  Units:  TObjectList;
begin
  WriteUnit('MathUtils', Src);

  Paths  := MakeSearchPaths;
  Loader := TUnitLoader.Create(Paths);
  Names  := TStringList.Create;
  try
    Names.Add('MathUtils');
    Units := Loader.LoadAll(Names);
    try
      AssertEquals('one unit loaded', 1, Units.Count);
      AssertEquals('unit name', 'MathUtils', TUnit(Units.Items[0]).Name);
    finally
      Units.Free;
    end;
  finally
    Names.Free;
    Loader.Free;
    Paths.Free;
  end;
end;

procedure TMultifileTests.TestUnitLoader_RaisesOnMissingUnit;
var
  Paths:  TStringList;
  Loader: TUnitLoader;
  Names:  TStringList;
  Units:  TObjectList;
begin
  Paths  := MakeSearchPaths;
  Loader := TUnitLoader.Create(Paths);
  Names  := TStringList.Create;
  try
    Names.Add('NoSuchUnit');
    try
      Units := Loader.LoadAll(Names);
      Units.Free;
      Fail('Expected EUnitNotFound');
    except
      on E: EUnitNotFound do ;  { expected }
    end;
  finally
    Names.Free;
    Loader.Free;
    Paths.Free;
  end;
end;

procedure TMultifileTests.TestUnitLoader_DetectsCycle;
const
  SrcA =
    '''
        unit CycleA;
        interface
        uses CycleB;
        implementation
        end.
        ''';
  SrcB =
    '''
        unit CycleB;
        interface
        uses CycleA;
        implementation
        end.
        ''';
var
  Paths:  TStringList;
  Loader: TUnitLoader;
  Names:  TStringList;
  Units:  TObjectList;
begin
  WriteUnit('CycleA', SrcA);
  WriteUnit('CycleB', SrcB);

  Paths  := MakeSearchPaths;
  Loader := TUnitLoader.Create(Paths);
  Names  := TStringList.Create;
  try
    Names.Add('CycleA');
    try
      Units := Loader.LoadAll(Names);
      Units.Free;
      Fail('Expected ECircularDependency');
    except
      on E: ECircularDependency do ;  { expected }
    end;
  finally
    Names.Free;
    Loader.Free;
    Paths.Free;
  end;
end;

procedure TMultifileTests.TestUnitLoader_DependencyOrder;
const
  SrcC =
    '''
        unit DepC;
        interface
        implementation
        end.
        ''';
  SrcB =
    '''
        unit DepB;
        interface
        uses DepC;
        implementation
        end.
        ''';
  SrcA =
    '''
        unit DepA;
        interface
        uses DepB;
        implementation
        end.
        ''';
var
  Paths:  TStringList;
  Loader: TUnitLoader;
  Names:  TStringList;
  Units:  TObjectList;
begin
  WriteUnit('DepC', SrcC);
  WriteUnit('DepB', SrcB);
  WriteUnit('DepA', SrcA);

  Paths  := MakeSearchPaths;
  Loader := TUnitLoader.Create(Paths);
  Names  := TStringList.Create;
  try
    Names.Add('DepA');
    Units := Loader.LoadAll(Names);
    try
      AssertEquals('three units loaded', 3, Units.Count);
      AssertEquals('first is leaf DepC', 'DepC', TUnit(Units.Items[0]).Name);
      AssertEquals('second is DepB',     'DepB', TUnit(Units.Items[1]).Name);
      AssertEquals('third is DepA',      'DepA', TUnit(Units.Items[2]).Name);
    finally
      Units.Free;
    end;
  finally
    Names.Free;
    Loader.Free;
    Paths.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ AnalyseUnitForExport tests                                           }
{ ------------------------------------------------------------------ }

procedure TMultifileTests.TestSemanticAnalyser_ExportedTypeVisibleInProgram;
const
  UnitSrc =
    '''
        unit Shapes;
        interface
        type
          TPoint = record
            X: Integer;
            Y: Integer;
          end;
        implementation
        end.
        ''';
  ProgSrc =
    '''
        program TestP;
        uses Shapes;
        var p: TPoint;
        begin
          p.X := 1
        end.
        ''';
var
  U:    TUnit;
  Prog: TProgram;
  SA:   TSemanticAnalyser;
begin
  U    := ParseUnitSrc(UnitSrc);
  Prog := ParseProg(ProgSrc);
  SA   := TSemanticAnalyser.Create;
  try
    SA.AnalyseUnitForExport(U);
    { If TPoint is not in global scope, Analyse will raise ESemanticError }
    SA.Analyse(Prog);
    AssertNotNull('prog analysed', Prog.SymbolTable);
  finally
    SA.Free;
    Prog.Free;
    U.Free;
  end;
end;

procedure TMultifileTests.TestSemanticAnalyser_ExportedFuncVisibleInProgram;
const
  UnitSrc =
    '''
        unit MathU;
        interface
        function Add(A, B: Integer): Integer;
        implementation
        function Add(A, B: Integer): Integer;
        begin
          Result := A + B
        end;
        end.
        ''';
  ProgSrc =
    '''
        program TestP;
        uses MathU;
        var r: Integer;
        begin
          r := Add(1, 2)
        end.
        ''';
var
  U:    TUnit;
  Prog: TProgram;
  SA:   TSemanticAnalyser;
begin
  U    := ParseUnitSrc(UnitSrc);
  Prog := ParseProg(ProgSrc);
  SA   := TSemanticAnalyser.Create;
  try
    SA.AnalyseUnitForExport(U);
    SA.Analyse(Prog);
    AssertNotNull('prog analysed', Prog.SymbolTable);
  finally
    SA.Free;
    Prog.Free;
    U.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Combined code generation tests                                       }
{ ------------------------------------------------------------------ }

procedure TMultifileTests.TestCodegen_TwoFileCompile_UnitFuncExported;
const
  UnitSrc =
    '''
        unit MathU;
        interface
        function Add(A, B: Integer): Integer;
        implementation
        function Add(A, B: Integer): Integer;
        begin
          Result := A + B
        end;
        end.
        ''';
  ProgSrc =
    '''
        program TestP;
        uses MathU;
        var r: Integer;
        begin
          r := Add(1, 2)
        end.
        ''';
var
  U:    TUnit;
  Prog: TProgram;
  SA:   TSemanticAnalyser;
  CG:   TCodeGenQBE;
  IR:   string;
begin
  U    := ParseUnitSrc(UnitSrc);
  Prog := ParseProg(ProgSrc);
  SA   := TSemanticAnalyser.Create;
  CG   := TCodeGenQBE.Create;
  try
    SA.AnalyseUnitForExport(U);
    SA.Analyse(Prog);
    CG.AppendUnit(U);
    CG.AppendProgram(Prog);
    IR := CG.GetOutput;
    AssertTrue('unit func exported',
      (Pos('export function', IR) > 0) and (Pos('$MathU_Add', IR) > 0));
  finally
    CG.Free;
    SA.Free;
    Prog.Free;
    U.Free;
  end;
end;

procedure TMultifileTests.TestCodegen_TwoFileCompile_MainPresent;
const
  UnitSrc =
    '''
        unit MathU;
        interface
        function Add(A, B: Integer): Integer;
        implementation
        function Add(A, B: Integer): Integer;
        begin
          Result := A + B
        end;
        end.
        ''';
  ProgSrc =
    '''
        program TestP;
        uses MathU;
        var r: Integer;
        begin
          r := Add(1, 2)
        end.
        ''';
var
  U:    TUnit;
  Prog: TProgram;
  SA:   TSemanticAnalyser;
  CG:   TCodeGenQBE;
  IR:   string;
begin
  U    := ParseUnitSrc(UnitSrc);
  Prog := ParseProg(ProgSrc);
  SA   := TSemanticAnalyser.Create;
  CG   := TCodeGenQBE.Create;
  try
    SA.AnalyseUnitForExport(U);
    SA.Analyse(Prog);
    CG.AppendUnit(U);
    CG.AppendProgram(Prog);
    IR := CG.GetOutput;
    AssertTrue('main function present',
      (Pos('export function', IR) > 0) and (Pos('$main', IR) > 0));
  finally
    CG.Free;
    SA.Free;
    Prog.Free;
    U.Free;
  end;
end;

initialization
  RegisterTest(TMultifileTests);
end.
