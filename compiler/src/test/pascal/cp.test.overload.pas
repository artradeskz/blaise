{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.overload;

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

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

    { Phase B — type-distinct resolution }

    { Two same-arity overloads distinguished only by parameter type }
    procedure TestSemantic_TypeDistinct_BothRegistered;

    { Codegen: per-type mangled names use the type-code scheme }
    procedure TestCodegen_TypeDistinct_DistinctQBENames;

    { Resolution: exact-type match preferred over widening (Integer
      argument selects Integer overload, not Double overload) }
    procedure TestCodegen_ExactMatch_BeatsWidening;

    { Resolution: when no exact match, widening is taken (Integer argument
      selects Double overload when no Integer overload exists) }
    procedure TestCodegen_WideningMatch_Used;

    { Two same-arity overloads where the argument is an exact match for
      neither but a widening match for both — must be flagged ambiguous }
    procedure TestSemantic_AmbiguousOverload_RaisesError;

    { Phase C — class method overloading }

    { Two methods sharing a name but distinguished by parameter type }
    procedure TestSemantic_ClassOverload_BothRegistered;
    procedure TestCodegen_ClassOverload_DistinctQBENames;
    procedure TestCodegen_ClassOverload_CallSitesMangled;

    { Class method dup without 'overload' rejected }
    procedure TestSemantic_ClassDupNoOverload_RaisesError;

    { virtual + overload base; override + overload descendant }
    procedure TestCodegen_VirtualOverload_DistinctVTableSlots;

    { Overload resolution in implicit-self expression context: a 3-arg call
      to a method that has a 3-param and a 4-param (open-array) overload
      must resolve to the 3-param overload, not fail with arity mismatch. }
    procedure TestSemantic_ImplicitSelf_ExprCtx_PicksCorrectOverload;

    { Constructor call site must use overload resolution.  When a class
      declares two same-named constructors and the higher-arity overload
      is indexed first, FindMethodDecl alone would pick it and then
      AppendDefaultArgs would fail on the unfilled parameter that has no
      default. }
    procedure TestSemantic_ConstructorOverload_PicksCorrectArity;
    procedure TestCodegen_ConstructorOverload_PicksCorrectArity;
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
    Result := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
end;

function TOverloadTests.AnalyseSrc(const ASrc: string): TProgram;
var
  A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Result);
  finally
    A.Free();
  end;
end;

function TOverloadTests.GenIR(const ASrc: string): string;
var
  Prog: TProgram;
  CG:   TCodeGenQBE;
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

procedure TOverloadTests.AnalyseExpectError(const ASrc: string);
var
  Prog: TProgram;
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
{ Shared sources                                                      }
{ ------------------------------------------------------------------ }

const
  SrcTwoArities =
    '''
        program P;
        procedure Greet; overload;
        begin
          WriteLn('hello')
        end;
        procedure Greet(N: Integer); overload;
        begin
          WriteLn(N)
        end;
        begin
          Greet;
          Greet(42)
        end.
        ''';

  SrcDupNoOverload =
    '''
        program P;
        procedure Greet;
        begin
        end;
        procedure Greet(N: Integer);
        begin
        end;
        begin
        end.
        ''';

  SrcMixedOverloadFlag =
    '''
        program P;
        procedure Greet; overload;
        begin
        end;
        procedure Greet(N: Integer);
        begin
        end;
        begin
        end.
        ''';

  SrcNoMatchingArity =
    '''
        program P;
        procedure Greet; overload;
        begin
        end;
        procedure Greet(N: Integer); overload;
        begin
        end;
        begin
          Greet(1, 2)
        end.
        ''';

  SrcTypeDistinct =
    '''
        program P;
        procedure Show(N: Integer); overload;
        begin
          WriteLn(N)
        end;
        procedure Show(S: string); overload;
        begin
          WriteLn(S)
        end;
        begin
          Show(42);
          Show('hi')
        end.
        ''';

  { Two same-arity overloads — Integer + Double.  Calling with an
    Integer literal must pick the Integer overload (exact match). }
  SrcExactBeatsWidening =
    '''
        program P;
        procedure F(N: Integer); overload;
        begin
          WriteLn(N)
        end;
        procedure F(D: Double); overload;
        begin
          WriteLn(DoubleToStr(D))
        end;
        begin
          F(42)
        end.
        ''';

  { Single Double overload, called with Integer — widening succeeds. }
  SrcWideningUsed =
    '''
        program P;
        procedure F(D: Double); overload;
        begin
          WriteLn(DoubleToStr(D))
        end;
        begin
          F(42)
        end.
        ''';

  SrcClassOverload =
    '''
        program P;
        type
          TFoo = class
            procedure Show(N: Integer); overload;
            procedure Show(S: string); overload;
          end;
          procedure TFoo.Show(N: Integer); overload;
          begin WriteLn(N) end;
          procedure TFoo.Show(S: string); overload;
          begin WriteLn(S) end;
        var F: TFoo;
        begin
          F := TFoo.Create();
          F.Show(42);
          F.Show('hi')
        end.
        ''';

  SrcClassDupNoOverload =
    '''
        program P;
        type
          TFoo = class
            procedure Show(N: Integer);
            procedure Show(S: string);
          end;
          procedure TFoo.Show(N: Integer);
          begin end;
          procedure TFoo.Show(S: string);
          begin end;
        begin end.
        ''';

  SrcVirtualOverload =
    '''
        program P;
        type
          TBase = class
            procedure Greet(N: Integer); overload; virtual;
            procedure Greet(S: string);  overload; virtual;
          end;
          TChild = class(TBase)
            procedure Greet(N: Integer); overload; override;
            procedure Greet(S: string);  overload; override;
          end;
          procedure TBase.Greet(N: Integer); overload;
          begin WriteLn('base int ', N) end;
          procedure TBase.Greet(S: string); overload;
          begin WriteLn('base str ', S) end;
          procedure TChild.Greet(N: Integer); overload;
          begin WriteLn('child int ', N) end;
          procedure TChild.Greet(S: string); overload;
          begin WriteLn('child str ', S) end;
        begin end.
        ''';

  { Method overload where one variant takes an open-array 4th param and
    another has only 3 params.  A 3-arg call in expression context (result
    assigned) must resolve to the 3-param overload, not the 4-param one. }
  SrcImplicitSelfOverloadExprCtx =
    '''
        program P;
        type
          THelper = class
            function Run(const S: string; out R: string; out N: Integer;
                         const Args: array of string): Boolean; overload;
            function Run(const S: string; out R: string;
                         out N: Integer): Boolean; overload;
          end;
          function THelper.Run(const S: string; out R: string; out N: Integer;
                               const Args: array of string): Boolean;
          begin R := 'with-args'; N := 1; Result := True; end;
          function THelper.Run(const S: string; out R: string;
                               out N: Integer): Boolean;
          begin R := 'no-args'; N := 0; Result := True; end;
          type TOwner = class
            FHelper: THelper;
            procedure DoIt;
          end;
          procedure TOwner.DoIt;
          var S: string; N: Integer; Ok: Boolean;
          begin
            { implicit-self expression context — was broken: picked 4-param overload }
            Ok := FHelper.Run('x', S, N);
          end;
        begin end.
        ''';

  { Two same-arity overloads — Double + Single — both reachable from an
    integer literal only by widening, with equal score → ambiguous. }
  { Constructor overload where the 2-arg variant is declared first — so
    FindMethodDecl would return it for the 1-arg call site.  Without
    overload resolution at the constructor call, AppendDefaultArgs would
    fail because parameter B of the 2-arg Create has no default. }
  SrcCtorOverload =
    '''
        program P;
        type
          TFoo = class
            constructor Create(A: Integer; B: Integer); overload;
            constructor Create(A: Integer); overload;
          end;
          constructor TFoo.Create(A: Integer; B: Integer);
          begin end;
          constructor TFoo.Create(A: Integer);
          begin end;
        var F: TFoo;
        begin
          F := TFoo.Create(42);
          F.Free()
        end.
        ''';

  SrcAmbiguousOverload =
    'program P;'                                            + LineEnding +
    'procedure F(D: Double); overload;'                     + LineEnding +
    'begin'                                                 + LineEnding +
    'end;'                                                  + LineEnding +
    'procedure F(S: Single); overload;'                     + LineEnding +
    'begin'                                                 + LineEnding +
    'end;'                                                  + LineEnding +
    'begin'                                                 + LineEnding +
    '  F(42)'                                               + LineEnding +
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
    Prog.Free();
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
    Prog.Free();
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
  { Type-code mangling: '$' in the resolved name is escaped to '_D_' in QBE
    symbols (QBE allows '$' inside identifiers, but other downstream tools
    do not).  Zero-arg overload is '_D_' (empty signature), Integer overload
    is '_D_i'. }
  AssertTrue('zero-arg overload defined',
    Pos('function $Greet_D_(', IR) > 0);
  AssertTrue('Integer overload defined',
    Pos('function $Greet_D_i(', IR) > 0);
end;

procedure TOverloadTests.TestCodegen_CallSite_ResolvesByArity;
var
  IR: string;
begin
  IR := GenIR(SrcTwoArities);
  AssertTrue('zero-arg call site mangled',
    Pos('call $Greet_D_(', IR) > 0);
  AssertTrue('Integer call site mangled',
    Pos('call $Greet_D_i(', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Phase B — type-distinct resolution                                  }
{ ------------------------------------------------------------------ }

procedure TOverloadTests.TestSemantic_TypeDistinct_BothRegistered;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcTypeDistinct);
  try
    AssertEquals('both proc decls survive', 2, Prog.Block.ProcDecls.Count);
  finally
    Prog.Free();
  end;
end;

procedure TOverloadTests.TestCodegen_TypeDistinct_DistinctQBENames;
var
  IR: string;
begin
  IR := GenIR(SrcTypeDistinct);
  AssertTrue('Integer-typed overload uses ''i'' suffix',
    Pos('function $Show_D_i(', IR) > 0);
  AssertTrue('string-typed overload uses ''S'' suffix',
    Pos('function $Show_D_S(', IR) > 0);
  AssertTrue('Integer call site mangled',
    Pos('call $Show_D_i(', IR) > 0);
  AssertTrue('string call site mangled',
    Pos('call $Show_D_S(', IR) > 0);
end;

procedure TOverloadTests.TestCodegen_ExactMatch_BeatsWidening;
var
  IR: string;
begin
  IR := GenIR(SrcExactBeatsWidening);
  AssertTrue('exact-match overload selected (Integer)',
    Pos('call $F_D_i(', IR) > 0);
  AssertFalse('widening overload not selected (Double)',
    Pos('call $F_D_d(', IR) > 0);
end;

procedure TOverloadTests.TestCodegen_WideningMatch_Used;
var
  IR: string;
begin
  IR := GenIR(SrcWideningUsed);
  AssertTrue('widening overload selected (Double)',
    Pos('call $F_D_d(', IR) > 0);
end;

procedure TOverloadTests.TestSemantic_AmbiguousOverload_RaisesError;
begin
  AnalyseExpectError(SrcAmbiguousOverload);
end;

{ ------------------------------------------------------------------ }
{ Phase C — class method overloading                                  }
{ ------------------------------------------------------------------ }

procedure TOverloadTests.TestSemantic_ClassOverload_BothRegistered;
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := AnalyseSrc(SrcClassOverload);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('TFoo has two Show methods', 2, CD.Methods.Count);
  finally
    Prog.Free();
  end;
end;

procedure TOverloadTests.TestCodegen_ClassOverload_DistinctQBENames;
var
  IR: string;
begin
  IR := GenIR(SrcClassOverload);
  AssertTrue('Integer overload defined as $TFoo_Show_D_i',
    Pos('function $TFoo_Show_D_i(', IR) > 0);
  AssertTrue('string overload defined as $TFoo_Show_D_S',
    Pos('function $TFoo_Show_D_S(', IR) > 0);
end;

procedure TOverloadTests.TestCodegen_ClassOverload_CallSitesMangled;
var
  IR: string;
begin
  IR := GenIR(SrcClassOverload);
  AssertTrue('Integer call site mangled',
    Pos('call $TFoo_Show_D_i(', IR) > 0);
  AssertTrue('string call site mangled',
    Pos('call $TFoo_Show_D_S(', IR) > 0);
end;

procedure TOverloadTests.TestSemantic_ClassDupNoOverload_RaisesError;
begin
  AnalyseExpectError(SrcClassDupNoOverload);
end;

procedure TOverloadTests.TestCodegen_VirtualOverload_DistinctVTableSlots;
var
  IR: string;
begin
  IR := GenIR(SrcVirtualOverload);
  { Each (name, signature) pair gets its own vtable slot.  The TBase
    typeinfo data record carries one entry per slot pointing to the
    matching base implementation; TChild carries overrides keyed by
    the same mangled signatures. }
  AssertTrue('TBase Integer slot',
    Pos('$TBase_Greet_D_i', IR) > 0);
  AssertTrue('TBase string slot',
    Pos('$TBase_Greet_D_S', IR) > 0);
  AssertTrue('TChild Integer override',
    Pos('$TChild_Greet_D_i', IR) > 0);
  AssertTrue('TChild string override',
    Pos('$TChild_Greet_D_S', IR) > 0);
end;

procedure TOverloadTests.TestSemantic_ImplicitSelf_ExprCtx_PicksCorrectOverload;
var
  IR: string;
begin
  { Must compile without error — previously raised
    "Method expects 4 argument(s) but got 3" }
  IR := GenIR(SrcImplicitSelfOverloadExprCtx);
  { The 3-param overload (no-args) must be called, not the 4-param one.
    Mangled name: Run(const S; out R: string; out N: Integer) }
  AssertTrue('calls 3-param overload',
    Pos('call $THelper_Run_D_S_V_S_V_i(', IR) > 0);
end;

procedure TOverloadTests.TestSemantic_ConstructorOverload_PicksCorrectArity;
var
  Prog: TProgram;
begin
  { Must analyse without error.  Previously raised:
    "No default value for parameter 'B' of 'Create'" because the
    constructor call site used FindMethodDecl, which picked the 2-arg
    overload (indexed first) and then failed to fill parameter B. }
  Prog := AnalyseSrc(SrcCtorOverload);
  Prog.Free();
end;

procedure TOverloadTests.TestCodegen_ConstructorOverload_PicksCorrectArity;
var
  IR: string;
begin
  IR := GenIR(SrcCtorOverload);
  { The 1-arg constructor must be called, not the 2-arg one.
    Mangled name for Create(A: Integer) is $TFoo_Create_D_i. }
  AssertTrue('calls 1-arg constructor overload',
    Pos('call $TFoo_Create_D_i(', IR) > 0);
  AssertFalse('does not call 2-arg constructor overload',
    Pos('call $TFoo_Create_D_i_i(', IR) > 0);
end;

initialization
  RegisterTest(TOverloadTests);

end.
