{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.constants;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSemantic, uCodeGenQBE;

type
  TConstTests = class(TTestCase)
  private
    function GenIR(const ASrc: string): string;
    function ParseUnit(const ASrc: string): TUnit;
    function IRContains(const AIR, AFragment: string): Boolean;
  published
    { Exported interface constant is visible in importing program }
    procedure TestExportedConstVisibleInProgram;
    { Integer constant in program scope }
    procedure TestIntConstInProgramScope;
    { Negative integer constant }
    procedure TestNegativeIntConst;
    { String constant in program scope }
    procedure TestStringConst;
    { Integer constant in unit interface section is parsed }
    procedure TestIntConstInUnitInterface;
    { Integer constant in unit implementation section is parsed }
    procedure TestIntConstInUnitImpl;
    { Implementation-section constant is usable in a method body in that unit }
    procedure TestImplConstUsableInMethodBody;
    { Constant used in assignment }
    procedure TestConstUsedInAssignment;
    { Constant used as WriteLn argument }
    procedure TestConstUsedInWriteLn;
    { Multiple constants in one const block }
    procedure TestMultipleConstsInBlock;
    { Two const blocks in same scope }
    procedure TestTwoConstBlocks;
    { Local constant inside a standalone procedure }
    procedure TestLocalConstInProcedure;
    { Local constant inside a standalone function }
    procedure TestLocalConstInFunction;
    { Local constant inside a class method }
    procedure TestLocalConstInMethod;
    { Constant in a class declaration section (class-level constant) }
    procedure TestConstInClassDeclaration;

    { Typed constants — const Name: Type = Value }
    procedure TestTypedConst_Integer;
    procedure TestTypedConst_Int64;
    procedure TestTypedConst_Double;
    procedure TestTypedConst_Single;
    procedure TestTypedConst_Boolean;
    procedure TestTypedConst_String;
    procedure TestTypedConst_TypeAnnotationPreserved;
    procedure TestTypedConst_NegativeDouble;
    procedure TestTypedConst_NegativeInteger;
    procedure TestTypedConst_InUnit;
    procedure TestTypedConst_UsedInExpression;

    { Array-of-enum typed constants }
    procedure TestArrayConst_StringElements_Parses;
    procedure TestArrayConst_IntElements_Parses;
    procedure TestArrayConst_StringElements_InIR;
    procedure TestArrayConst_IntElements_InIR;
    procedure TestArrayConst_IndexedByEnumVar;
    procedure TestArrayConst_WrongElementCount_Error;
    procedure TestArrayConst_InUnit;

    { Range-indexed array constants: array[Low..High] of T = (...) }
    procedure TestArrayConst_RangeIndexed_Parses;
    procedure TestArrayConst_RangeIndexed_InIR;
    procedure TestArrayConst_RangeIndexed_StringElements;
    procedure TestArrayConst_RangeIndexed_WrongCount_Error;
    procedure TestArrayConst_RangeIndexed_IndexedByVar;

    { Class-level array constants }
    procedure TestClassArrayConst_RangeIndexed_InIR;
    procedure TestClassArrayConst_EnumIndexed_InIR;

    { Function-local typed array constants — must emit a data item in the
      data section, not just reference $Name from the function body. }
    procedure TestArrayConst_LocalInFunction_EmitsDataItem;
    procedure TestArrayConst_LocalInProcedure_EmitsDataItem;
    procedure TestArrayConst_LocalInMethod_EmitsDataItem;
  end;

implementation

function TConstTests.GenIR(const ASrc: string): string;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  CG: TCodeGenQBE;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse;
  A  := TSemanticAnalyser.Create;
  try
    A.Analyse(Pr);
  finally
    A.Free;
  end;
  CG := TCodeGenQBE.Create;
  try
    CG.Generate(Pr);
    Result := CG.GetOutput;
  finally
    CG.Free;
    Pr.Free;
    P.Free;
    L.Free;
  end;
end;

function TConstTests.ParseUnit(const ASrc: string): TUnit;
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

function TConstTests.IRContains(const AIR, AFragment: string): Boolean;
begin
  Result := Pos(AFragment, AIR) > 0;
end;

procedure TConstTests.TestExportedConstVisibleInProgram;
const
  UnitSrc =
    '''
        unit MyConsts;
        interface
        const
          dupAccept = 0;
          dupIgnore = 1;
          dupError  = 2;
        implementation
        end.
        ''';
  ProgSrc =
    '''
        program TestP;
        uses MyConsts;
        var x: Integer;
        begin
          x := dupIgnore
        end.
        ''';
var
  U:    TUnit;
  Prog: TProgram;
  SA:   TSemanticAnalyser;
  L:    TLexer;
  P:    TParser;
begin
  L := TLexer.Create(UnitSrc);
  P := TParser.Create(L);
  U := P.ParseUnit;
  P.Free; L.Free;

  L := TLexer.Create(ProgSrc);
  P := TParser.Create(L);
  Prog := P.Parse;
  P.Free; L.Free;

  SA := TSemanticAnalyser.Create;
  try
    SA.AnalyseUnitForExport(U);
    { If dupIgnore is not in global scope, Analyse will raise ESemanticError }
    SA.Analyse(Prog);
    AssertNotNull('Program should analyse without error', Prog.SymbolTable);
  finally
    SA.Free;
    Prog.Free;
    U.Free;
  end;
end;

procedure TConstTests.TestIntConstInProgramScope;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        const MaxItems = 10;
        var x: Integer;
        begin
          x := MaxItems;
        end.
        '''
  );
  AssertTrue('IR should be non-empty for program with integer const', IR <> '');
end;

procedure TConstTests.TestNegativeIntConst;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        const MinVal = -1;
        var x: Integer;
        begin
          x := MinVal;
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('Negative const should fold to -1', IRContains(IR, '-1'));
end;

procedure TConstTests.TestStringConst;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        const AppName = 'MyApp';
        begin
          WriteLn(AppName);
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('String const value should appear in IR', IRContains(IR, 'MyApp'));
end;

procedure TConstTests.TestIntConstInUnitInterface;
var
  U: TUnit;
begin
  U := ParseUnit(
    '''
        unit MyConsts;
        interface
        const
          dupAccept = 0;
          dupIgnore = 1;
          dupError  = 2;
        implementation
        end.
        '''
  );
  try
    AssertEquals('Interface const block should have 3 entries',
      3, U.IntfBlock.ConstDecls.Count);
    AssertEquals('First const name', 'dupAccept',
      TConstDecl(U.IntfBlock.ConstDecls.Items[0]).Name);
    AssertEquals('First const value', 0,
      TConstDecl(U.IntfBlock.ConstDecls.Items[0]).IntVal);
    AssertEquals('Second const name', 'dupIgnore',
      TConstDecl(U.IntfBlock.ConstDecls.Items[1]).Name);
    AssertEquals('Third const name', 'dupError',
      TConstDecl(U.IntfBlock.ConstDecls.Items[2]).Name);
    AssertEquals('Third const value', 2,
      TConstDecl(U.IntfBlock.ConstDecls.Items[2]).IntVal);
  finally
    U.Free;
  end;
end;

procedure TConstTests.TestIntConstInUnitImpl;
var
  U: TUnit;
begin
  U := ParseUnit(
    '''
        unit MyConsts;
        interface
        implementation
        const
          InternalVal = 42;
        end.
        '''
  );
  try
    AssertEquals('Impl const block should have 1 entry',
      1, U.ImplBlock.ConstDecls.Count);
    AssertEquals('Impl const name', 'InternalVal',
      TConstDecl(U.ImplBlock.ConstDecls.Items[0]).Name);
    AssertEquals('Impl const value', 42,
      TConstDecl(U.ImplBlock.ConstDecls.Items[0]).IntVal);
  finally
    U.Free;
  end;
end;

procedure TConstTests.TestImplConstUsableInMethodBody;
const
  UnitSrc =
    '''
        unit Checker;
        interface
        function GetLimit: Integer;
        implementation
        const
          Limit = 99;
        function GetLimit: Integer;
        begin
          Result := Limit
        end;
        end.
        ''';
var
  U:  TUnit;
  SA: TSemanticAnalyser;
begin
  U  := ParseUnit(UnitSrc);
  SA := TSemanticAnalyser.Create;
  try
    { AnalyseUnitForExport raises ESemanticError if Limit is not resolved }
    SA.AnalyseUnitForExport(U);
    AssertNotNull('Unit should analyse without error', U);
  finally
    SA.Free;
    U.Free;
  end;
end;

procedure TConstTests.TestConstUsedInAssignment;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        const Limit = 5;
        var x: Integer;
        begin
          x := Limit;
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('Const value should appear in IR', IRContains(IR, '5'));
end;

procedure TConstTests.TestConstUsedInWriteLn;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        const ErrCode = 42;
        begin
          WriteLn(ErrCode);
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('Constant value should appear in IR', IRContains(IR, '42'));
end;

procedure TConstTests.TestMultipleConstsInBlock;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        const
          A = 1;
          B = 2;
          C = 3;
        var x: Integer;
        begin
          x := A;
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
end;

procedure TConstTests.TestTwoConstBlocks;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        const First = 10;
        var x: Integer;
        const Second = 20;
        begin
          x := First + Second;
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
end;

procedure TConstTests.TestLocalConstInProcedure;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        procedure DoWork;
        const Threshold = 7;
        var x: Integer;
        begin
          x := Threshold
        end;
        begin
          DoWork
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('Local const value should appear in IR', IRContains(IR, '7'));
end;

procedure TConstTests.TestLocalConstInFunction;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        function Compute: Integer;
        const Base = 100;
        begin
          Result := Base
        end;
        var r: Integer;
        begin
          r := Compute
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('Local const value should appear in IR', IRContains(IR, '100'));
end;

procedure TConstTests.TestLocalConstInMethod;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        type
          TFoo = class
            function Bar: Integer;
          end;
        function TFoo.Bar: Integer;
        const Magic = 55;
        begin
          Result := Magic
        end;
        var f: TFoo;
        begin
          f := TFoo.Create;
          WriteLn(f.Bar);
          f.Free
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('Local const value should appear in IR', IRContains(IR, '55'));
end;

procedure TConstTests.TestConstInClassDeclaration;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        type
          TFoo = class
          const
            MaxItems = 100;
          var
            FCount: Integer;
          end;
        var x: Integer;
        begin
          x := TFoo.MaxItems
        end.
        '''
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('Class const value should appear in IR', IRContains(IR, '100'));
end;

{ ------------------------------------------------------------------ }
{ Typed constants                                                      }
{ ------------------------------------------------------------------ }

procedure TConstTests.TestTypedConst_Integer;
var IR: string;
begin
  IR := GenIR(
    '''
    program Test;
    const MaxItems: Integer = 100;
    var x: Integer;
    begin x := MaxItems end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('value in IR', IRContains(IR, '100'));
end;

procedure TConstTests.TestTypedConst_Int64;
var IR: string;
begin
  IR := GenIR(
    '''
    program Test;
    const BigVal: Int64 = 1000000000;
    var x: Int64;
    begin x := BigVal end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('value in IR', IRContains(IR, '1000000000'));
end;

procedure TConstTests.TestTypedConst_Double;
var IR: string;
begin
  IR := GenIR(
    '''
    program Test;
    const Pi: Double = 3.14159;
    var x: Double;
    begin x := Pi end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('value in IR', IRContains(IR, '3.14159'));
end;

procedure TConstTests.TestTypedConst_Single;
var IR: string;
begin
  IR := GenIR(
    '''
    program Test;
    const E: Single = 2.71828;
    var x: Single;
    begin x := E end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('value in IR', IRContains(IR, '2.71828'));
end;

procedure TConstTests.TestTypedConst_Boolean;
var IR: string;
begin
  IR := GenIR(
    '''
    program Test;
    const Flag: Boolean = True;
    var b: Boolean;
    begin b := Flag end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
end;

procedure TConstTests.TestTypedConst_String;
var IR: string;
begin
  IR := GenIR(
    '''
    program Test;
    const Greeting: string = 'hello';
    begin WriteLn(Greeting) end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('value in IR', IRContains(IR, 'hello'));
end;

procedure TConstTests.TestTypedConst_TypeAnnotationPreserved;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  SA: TSemanticAnalyser;
  Sym: TSymbol;
begin
  L  := TLexer.Create('program Test; const Pi: Double = 3.14; begin end.');
  P  := TParser.Create(L);
  Pr := P.Parse;
  SA := TSemanticAnalyser.Create;
  try
    SA.Analyse(Pr);
    Sym := Pr.SymbolTable.Lookup('Pi');
    AssertNotNil('Pi symbol exists', Sym);
    AssertEquals('Pi is Double', 'Double', Sym.TypeDesc.Name);
  finally
    SA.Free; Pr.Free; P.Free; L.Free;
  end;
end;

procedure TConstTests.TestTypedConst_NegativeDouble;
var IR: string;
begin
  IR := GenIR(
    '''
    program Test;
    const NegPi: Double = -3.14159;
    var x: Double;
    begin x := NegPi end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('negative value in IR', IRContains(IR, '-3.14159'));
end;

procedure TConstTests.TestTypedConst_NegativeInteger;
var IR: string;
begin
  IR := GenIR(
    '''
    program Test;
    const MinVal: Integer = -42;
    var x: Integer;
    begin x := MinVal end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('negative value in IR', IRContains(IR, '-42'));
end;

procedure TConstTests.TestTypedConst_InUnit;
var
  U: TUnit;
begin
  U := ParseUnit(
    '''
    unit MyMath;
    interface
    const Pi: Double = 3.14159265358979;
    implementation
    end.
    ''');
  AssertNotNull('unit parsed', U);
  AssertEquals('one const decl', 1, U.IntfBlock.ConstDecls.Count);
  U.Free;
end;

procedure TConstTests.TestTypedConst_UsedInExpression;
var IR: string;
begin
  IR := GenIR(
    '''
    program Test;
    const Scale: Double = 2.5;
    var x, y: Double;
    begin
      x := 4.0;
      y := x * Scale
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Scale value in IR', IRContains(IR, '2.5'));
end;

{ ------------------------------------------------------------------ }
{ Array-of-enum typed constants                                        }
{ ------------------------------------------------------------------ }

procedure TConstTests.TestArrayConst_StringElements_Parses;
var U: TUnit;
begin
  U := ParseUnit(
    '''
    unit W;
    interface
    type TWeather = (wtSunny, wtCloudy, wtRainy);
    const WeatherNames: array[TWeather] of string = ('Sunny', 'Cloudy', 'Rainy');
    implementation
    end.
    ''');
  AssertNotNull('unit parsed', U);
  AssertEquals('one const decl', 1, U.IntfBlock.ConstDecls.Count);
  U.Free;
end;

procedure TConstTests.TestArrayConst_IntElements_Parses;
var U: TUnit;
begin
  U := ParseUnit(
    '''
    unit W;
    interface
    type TDir = (dNorth, dSouth, dEast, dWest);
    const DirCost: array[TDir] of Integer = (1, 1, 2, 2);
    implementation
    end.
    ''');
  AssertNotNull('unit parsed', U);
  AssertEquals('one const decl', 1, U.IntfBlock.ConstDecls.Count);
  U.Free;
end;

procedure TConstTests.TestArrayConst_StringElements_InIR;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    type TWeather = (wtSunny, wtCloudy, wtRainy);
    const WeatherNames: array[TWeather] of string = ('Sunny', 'Cloudy', 'Rainy');
    begin
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Sunny in IR', IRContains(IR, 'Sunny'));
  AssertTrue('Cloudy in IR', IRContains(IR, 'Cloudy'));
  AssertTrue('Rainy in IR', IRContains(IR, 'Rainy'));
  AssertTrue('WeatherNames in IR', IRContains(IR, 'WeatherNames'));
end;

procedure TConstTests.TestArrayConst_IntElements_InIR;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    type TDir = (dNorth, dSouth, dEast, dWest);
    const DirCost: array[TDir] of Integer = (1, 1, 2, 2);
    begin
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('DirCost in IR', IRContains(IR, 'DirCost'));
end;

procedure TConstTests.TestArrayConst_IndexedByEnumVar;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    type TWeather = (wtSunny, wtCloudy, wtRainy);
    const WeatherNames: array[TWeather] of string = ('Sunny', 'Cloudy', 'Rainy');
    var W: TWeather; S: string;
    begin
      W := wtCloudy;
      S := WeatherNames[W]
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('WeatherNames in IR', IRContains(IR, 'WeatherNames'));
end;

procedure TConstTests.TestArrayConst_WrongElementCount_Error;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  SA: TSemanticAnalyser;
  GotError: Boolean;
begin
  GotError := False;
  L  := TLexer.Create(
    '''
    program P;
    type TWeather = (wtSunny, wtCloudy, wtRainy);
    const WeatherNames: array[TWeather] of string = ('Sunny', 'Cloudy');
    begin end.
    ''');
  P  := TParser.Create(L);
  Pr := P.Parse;
  SA := TSemanticAnalyser.Create;
  try
    try
      SA.Analyse(Pr);
    except
      on E: ESemanticError do GotError := True;
    end;
  finally
    SA.Free; Pr.Free; P.Free; L.Free;
  end;
  AssertTrue('wrong count raises error', GotError);
end;

procedure TConstTests.TestArrayConst_InUnit;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    type TWeather = (wtSunny, wtCloudy, wtRainy);
    const WeatherNames: array[TWeather] of string = ('Sunny', 'Cloudy', 'Rainy');
    var W: TWeather; S: string;
    begin
      W := wtRainy;
      S := WeatherNames[W];
      WriteLn(S)
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Rainy in IR', IRContains(IR, 'Rainy'));
end;

procedure TConstTests.TestArrayConst_RangeIndexed_Parses;
var U: TUnit;
begin
  U := ParseUnit(
    '''
    unit W;
    interface
    const Days: array[0..6] of string = ('Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat');
    implementation
    end.
    ''');
  AssertNotNull('unit parsed', U);
  AssertEquals('one const decl', 1, U.IntfBlock.ConstDecls.Count);
  U.Free;
end;

procedure TConstTests.TestArrayConst_RangeIndexed_InIR;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const Vals: array[0..3] of Integer = (10, 20, 30, 40);
    begin
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Vals in IR', IRContains(IR, 'Vals'));
end;

procedure TConstTests.TestArrayConst_RangeIndexed_StringElements;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const Days: array[0..2] of string = ('Mon', 'Tue', 'Wed');
    begin
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Mon in IR', IRContains(IR, 'Mon'));
  AssertTrue('Tue in IR', IRContains(IR, 'Tue'));
  AssertTrue('Wed in IR', IRContains(IR, 'Wed'));
end;

procedure TConstTests.TestArrayConst_RangeIndexed_WrongCount_Error;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  SA: TSemanticAnalyser;
  GotError: Boolean;
begin
  GotError := False;
  L  := TLexer.Create(
    '''
    program P;
    const Vals: array[0..3] of Integer = (10, 20);
    begin end.
    ''');
  P  := TParser.Create(L);
  Pr := P.Parse;
  SA := TSemanticAnalyser.Create;
  try
    try
      SA.Analyse(Pr);
    except
      on E: ESemanticError do GotError := True;
    end;
  finally
    SA.Free; Pr.Free; P.Free; L.Free;
  end;
  AssertTrue('wrong count raises error', GotError);
end;

procedure TConstTests.TestArrayConst_RangeIndexed_IndexedByVar;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    const Days: array[0..2] of string = ('Mon', 'Tue', 'Wed');
    var I: Integer; S: string;
    begin
      I := 1;
      S := Days[I]
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Days in IR', IRContains(IR, 'Days'));
end;

procedure TConstTests.TestClassArrayConst_RangeIndexed_InIR;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    type
      TMyClass = class
      public
        const Items: array[0..2] of string = ('A', 'B', 'C');
      end;
    var T: TMyClass;
    begin
      T := TMyClass.Create;
      WriteLn(T.Items[1]);
      T.Free
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Items in IR', IRContains(IR, 'Items'));
end;

procedure TConstTests.TestClassArrayConst_EnumIndexed_InIR;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    type
      TColor = (Red, Green, Blue);
      TPalette = class
      public
        const Names: array[TColor] of string = ('Red', 'Green', 'Blue');
      end;
    var P2: TPalette;
    begin
      P2 := TPalette.Create;
      WriteLn(P2.Names[0]);
      P2.Free
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('Names in IR', IRContains(IR, 'Names'));
end;

{ Regression: a typed array constant declared inside a function body
  was referenced as `$Days` from the function code but no
  `data $Days = ...` item was emitted, so the linker failed with
  `undefined reference to Days`. EmitGlobalConstData was only called on
  the top-level program/unit blocks and never recursed into method
  bodies. }
procedure TConstTests.TestArrayConst_LocalInFunction_EmitsDataItem;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    function DaysInMonth(M: Integer): Integer;
    const
      Days: array[1..12] of Integer = (31,28,31,30,31,30,31,31,30,31,30,31);
    begin
      Result := Days[M]
    end;
    begin
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('$Days data item emitted',
    Pos('data $Days =', IR) >= 0);
  AssertTrue('Days[M] reference present',
    Pos('add $Days', IR) >= 0);
end;

procedure TConstTests.TestArrayConst_LocalInProcedure_EmitsDataItem;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    procedure Dump;
    const
      Tbl: array[0..2] of Integer = (10, 20, 30);
    begin
      WriteLn(Tbl[0])
    end;
    begin
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('$Tbl data item emitted',
    Pos('data $Tbl =', IR) >= 0);
end;

procedure TConstTests.TestArrayConst_LocalInMethod_EmitsDataItem;
var IR: string;
begin
  IR := GenIR(
    '''
    program P;
    type
      TFoo = class
      public
        function Lookup(I: Integer): Integer;
      end;
    function TFoo.Lookup(I: Integer): Integer;
    const
      Vals: array[0..3] of Integer = (7, 8, 9, 10);
    begin
      Result := Vals[I]
    end;
    var F: TFoo;
    begin
      F := TFoo.Create;
      WriteLn(F.Lookup(0));
      F.Free
    end.
    ''');
  AssertTrue('IR non-empty', IR <> '');
  AssertTrue('$Vals data item emitted',
    Pos('data $Vals =', IR) >= 0);
end;

initialization
  RegisterTest(TConstTests);

end.
