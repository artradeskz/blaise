{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.overload;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TOverloadTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { Phase A — arity-distinct standalone overloading }

    { Parser: 'overload' directive sets the IsOverload flag on TMethodDecl }
    procedure TestParse_OverloadDirective_SetsFlag;

    { Semantic: two same-named procs with 'overload' both keep their decls }
    procedure TestSemantic_TwoArities_BothRegistered;

    { Semantic: duplicate name without 'overload' is rejected }
    procedure TestSemantic_DuplicateWithoutOverload_RaisesError;

    { Semantic: mixing 'overload' with non-'overload' is rejected }
    procedure TestSemantic_MixingOverloadAndPlain_RaisesError;

    { Semantic: call site with no matching arity raises error }
    procedure TestSemantic_NoMatchingArity_RaisesError;

    { Codegen: each overload gets a distinct mangled QBE name }
    procedure TestCodegen_TwoArities_DistinctQBENames;

    { Codegen: call sites resolve to the correct mangled name based on arg count }
    procedure TestCodegen_CallSite_ResolvesByArity;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TOverloadTests.ParseSrc(const ASrc: string): TProgram;
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

function TOverloadTests.AnalyseSrc(const ASrc: string): TProgram;
var
  A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create;
  try
    A.Analyse(Result);
  finally
    A.Free;
  end;
end;

function TOverloadTests.GenIR(const ASrc: string): string;
var
  Prog: TProgram;
  CG:   TCodeGenQBE;
begin
  Prog := AnalyseSrc(ASrc);
  try
    CG := TCodeGenQBE.Create;
    try
      CG.Generate(Prog);
      Result := CG.GetOutput;
    finally
      CG.Free;
    end;
  finally
    Prog.Free;
  end;
end;

procedure TOverloadTests.AnalyseExpectError(const ASrc: string);
var
  Prog: TProgram;
begin
  try
    Prog := AnalyseSrc(ASrc);
    Prog.Free;
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ;
  end;
end;

{ ------------------------------------------------------------------ }
{ Shared sources                                                      }
{ ------------------------------------------------------------------ }

const
  SrcTwoArities =
    'program P;'                                            + LineEnding +
    'procedure Greet; overload;'                            + LineEnding +
    'begin'                                                 + LineEnding +
    '  WriteLn(''hello'')'                                  + LineEnding +
    'end;'                                                  + LineEnding +
    'procedure Greet(N: Integer); overload;'                + LineEnding +
    'begin'                                                 + LineEnding +
    '  WriteLn(N)'                                          + LineEnding +
    'end;'                                                  + LineEnding +
    'begin'                                                 + LineEnding +
    '  Greet;'                                              + LineEnding +
    '  Greet(42)'                                           + LineEnding +
    'end.';

  SrcDupNoOverload =
    'program P;'                                            + LineEnding +
    'procedure Greet;'                                      + LineEnding +
    'begin'                                                 + LineEnding +
    'end;'                                                  + LineEnding +
    'procedure Greet(N: Integer);'                          + LineEnding +
    'begin'                                                 + LineEnding +
    'end;'                                                  + LineEnding +
    'begin'                                                 + LineEnding +
    'end.';

  SrcMixedOverloadFlag =
    'program P;'                                            + LineEnding +
    'procedure Greet; overload;'                            + LineEnding +
    'begin'                                                 + LineEnding +
    'end;'                                                  + LineEnding +
    'procedure Greet(N: Integer);'                          + LineEnding +
    'begin'                                                 + LineEnding +
    'end;'                                                  + LineEnding +
    'begin'                                                 + LineEnding +
    'end.';

  SrcNoMatchingArity =
    'program P;'                                            + LineEnding +
    'procedure Greet; overload;'                            + LineEnding +
    'begin'                                                 + LineEnding +
    'end;'                                                  + LineEnding +
    'procedure Greet(N: Integer); overload;'                + LineEnding +
    'begin'                                                 + LineEnding +
    'end;'                                                  + LineEnding +
    'begin'                                                 + LineEnding +
    '  Greet(1, 2)'                                         + LineEnding +
    'end.';

{ ------------------------------------------------------------------ }
{ Tests                                                               }
{ ------------------------------------------------------------------ }

procedure TOverloadTests.TestParse_OverloadDirective_SetsFlag;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcTwoArities);
  try
    AssertEquals('two procs parsed', 2, Prog.Block.ProcDecls.Count);
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertTrue('first proc has IsOverload=True', MD.IsOverload);
    MD := TMethodDecl(Prog.Block.ProcDecls[1]);
    AssertTrue('second proc has IsOverload=True', MD.IsOverload);
  finally
    Prog.Free;
  end;
end;

procedure TOverloadTests.TestSemantic_TwoArities_BothRegistered;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcTwoArities);
  try
    AssertEquals('both proc decls survive', 2, Prog.Block.ProcDecls.Count);
  finally
    Prog.Free;
  end;
end;

procedure TOverloadTests.TestSemantic_DuplicateWithoutOverload_RaisesError;
begin
  AnalyseExpectError(SrcDupNoOverload);
end;

procedure TOverloadTests.TestSemantic_MixingOverloadAndPlain_RaisesError;
begin
  AnalyseExpectError(SrcMixedOverloadFlag);
end;

procedure TOverloadTests.TestSemantic_NoMatchingArity_RaisesError;
begin
  AnalyseExpectError(SrcNoMatchingArity);
end;

procedure TOverloadTests.TestCodegen_TwoArities_DistinctQBENames;
var
  IR: string;
begin
  IR := GenIR(SrcTwoArities);
  { Each overload must produce its own QBE function definition. The exact
    mangling scheme is a Phase A internal detail (arity-suffixed for now,
    type-coded later). We assert distinctness via the suffix presence. }
  AssertTrue('arity-0 overload defined',
    Pos('function $Greet$N0(', IR) > 0);
  AssertTrue('arity-1 overload defined',
    Pos('function $Greet$N1(', IR) > 0);
end;

procedure TOverloadTests.TestCodegen_CallSite_ResolvesByArity;
var
  IR: string;
begin
  IR := GenIR(SrcTwoArities);
  AssertTrue('arity-0 call site mangled',
    Pos('call $Greet$N0(', IR) > 0);
  AssertTrue('arity-1 call site mangled',
    Pos('call $Greet$N1(', IR) > 0);
end;

initialization
  RegisterTest(TOverloadTests);

end.
