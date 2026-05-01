{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

unit cp.test.constants;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
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
    { Constant used in assignment }
    procedure TestConstUsedInAssignment;
    { Constant used as WriteLn argument }
    procedure TestConstUsedInWriteLn;
    { Multiple constants in one const block }
    procedure TestMultipleConstsInBlock;
    { Two const blocks in same scope }
    procedure TestTwoConstBlocks;
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
    'unit MyConsts;'               + LineEnding +
    'interface'                    + LineEnding +
    'const'                        + LineEnding +
    '  dupAccept = 0;'             + LineEnding +
    '  dupIgnore = 1;'             + LineEnding +
    '  dupError  = 2;'             + LineEnding +
    'implementation'               + LineEnding +
    'end.';
  ProgSrc =
    'program TestP;'               + LineEnding +
    'uses MyConsts;'               + LineEnding +
    'var x: Integer;'              + LineEnding +
    'begin'                        + LineEnding +
    '  x := dupIgnore'             + LineEnding +
    'end.';
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
    'program Test;'                + LineEnding +
    'const MaxItems = 10;'         + LineEnding +
    'var x: Integer;'              + LineEnding +
    'begin'                        + LineEnding +
    '  x := MaxItems;'             + LineEnding +
    'end.'
  );
  AssertTrue('IR should be non-empty for program with integer const', IR <> '');
end;

procedure TConstTests.TestNegativeIntConst;
var
  IR: string;
begin
  IR := GenIR(
    'program Test;'                + LineEnding +
    'const MinVal = -1;'           + LineEnding +
    'var x: Integer;'              + LineEnding +
    'begin'                        + LineEnding +
    '  x := MinVal;'               + LineEnding +
    'end.'
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('Negative const should fold to -1', IRContains(IR, '-1'));
end;

procedure TConstTests.TestStringConst;
var
  IR: string;
begin
  IR := GenIR(
    'program Test;'                    + LineEnding +
    'const AppName = ''MyApp'';'       + LineEnding +
    'begin'                            + LineEnding +
    '  WriteLn(AppName);'              + LineEnding +
    'end.'
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('String const value should appear in IR', IRContains(IR, 'MyApp'));
end;

procedure TConstTests.TestIntConstInUnitInterface;
var
  U: TUnit;
begin
  U := ParseUnit(
    'unit MyConsts;'               + LineEnding +
    'interface'                    + LineEnding +
    'const'                        + LineEnding +
    '  dupAccept = 0;'             + LineEnding +
    '  dupIgnore = 1;'             + LineEnding +
    '  dupError  = 2;'             + LineEnding +
    'implementation'               + LineEnding +
    'end.'
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
    'unit MyConsts;'               + LineEnding +
    'interface'                    + LineEnding +
    'implementation'               + LineEnding +
    'const'                        + LineEnding +
    '  InternalVal = 42;'          + LineEnding +
    'end.'
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

procedure TConstTests.TestConstUsedInAssignment;
var
  IR: string;
begin
  IR := GenIR(
    'program Test;'                + LineEnding +
    'const Limit = 5;'             + LineEnding +
    'var x: Integer;'              + LineEnding +
    'begin'                        + LineEnding +
    '  x := Limit;'                + LineEnding +
    'end.'
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('Const value should appear in IR', IRContains(IR, '5'));
end;

procedure TConstTests.TestConstUsedInWriteLn;
var
  IR: string;
begin
  IR := GenIR(
    'program Test;'                + LineEnding +
    'const ErrCode = 42;'          + LineEnding +
    'begin'                        + LineEnding +
    '  WriteLn(ErrCode);'          + LineEnding +
    'end.'
  );
  AssertTrue('IR should be non-empty', IR <> '');
  AssertTrue('Constant value should appear in IR', IRContains(IR, '42'));
end;

procedure TConstTests.TestMultipleConstsInBlock;
var
  IR: string;
begin
  IR := GenIR(
    'program Test;'                + LineEnding +
    'const'                        + LineEnding +
    '  A = 1;'                     + LineEnding +
    '  B = 2;'                     + LineEnding +
    '  C = 3;'                     + LineEnding +
    'var x: Integer;'              + LineEnding +
    'begin'                        + LineEnding +
    '  x := A;'                    + LineEnding +
    'end.'
  );
  AssertTrue('IR should be non-empty', IR <> '');
end;

procedure TConstTests.TestTwoConstBlocks;
var
  IR: string;
begin
  IR := GenIR(
    'program Test;'                + LineEnding +
    'const First = 10;'            + LineEnding +
    'var x: Integer;'              + LineEnding +
    'const Second = 20;'           + LineEnding +
    'begin'                        + LineEnding +
    '  x := First + Second;'       + LineEnding +
    'end.'
  );
  AssertTrue('IR should be non-empty', IR <> '');
end;

initialization
  RegisterTest(TConstTests);

end.
