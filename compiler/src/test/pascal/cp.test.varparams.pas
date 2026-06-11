{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.varparams;

{ Tests for var parameters: pass-by-reference semantics across
  lexer, parser, semantic analysis, and code generation. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

type
  TVarParamTests = class(TTestCase)
  private
    function  ParseSrc(const ASrc: string): TProgram;
    function  AnalyseSrc(const ASrc: string): TProgram;
    function  GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_VarParam_IsVarParam;
    procedure TestParse_VarParam_MultiInGroup;
    procedure TestParse_VarParam_Mixed_VarAndValue;
    procedure TestParse_VarParam_ValueParam_IsNotVar;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_VarParam_OK;
    procedure TestSemantic_VarParam_NonVariable_RaisesError;
    procedure TestSemantic_VarParam_TypeMismatch_RaisesError;

    { ------------------------------------------------------------------ }
    { Codegen                                                              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_VarParam_SignatureUsesPointerType;
    procedure TestCodegen_VarParam_CallPassesAddress;
    procedure TestCodegen_VarParam_WriteStoresThroughPointer;
    procedure TestCodegen_VarParam_ReadDereferencesPointer;
    procedure TestCodegen_VarParam_Swap;
    { Var-param forwarding: passing a var param directly to another var param }
    procedure TestCodegen_VarParam_ForwardToProc;
    procedure TestCodegen_VarParam_ForwardToMethod;

    { L-value var args beyond simple identifiers: a record-field access
      (R.F) and a pointer-deref-then-field (P^.F) must both be accepted
      where the parameter is var-typed. }
    procedure TestSemantic_VarParam_FieldAccess_OK;
    procedure TestSemantic_VarParam_DerefField_OK;

    { Var-param call where the actual argument is a CLASS field
      (C.Field where C is a class reference, not a record).  The address
      must be computed as (loadl C) + offset, not (&C + offset), because
      the variable holding the class reference stores a pointer to the
      heap object — adding the offset to the variable's address points
      at unrelated memory.  See BUG-001 in bugs.txt. }
    procedure TestCodegen_VarParam_ClassFieldLeaf_LoadsObjectPointer;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TVarParamTests.ParseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free(); L.Free();
  end;
end;

function TVarParamTests.AnalyseSrc(const ASrc: string): TProgram;
var A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Result);
  finally
    A.Free();
  end;
end;

function TVarParamTests.GenIR(const ASrc: string): string;
var P: TProgram; CG: TCodeGenQBE;
begin
  P := AnalyseSrc(ASrc);
  try
    CG := TCodeGenQBE.Create();
    try
      CG.Generate(P);
      Result := CG.GetOutput();
    finally
      CG.Free();
    end;
  finally
    P.Free();
  end;
end;

procedure TVarParamTests.AnalyseExpectError(const ASrc: string);
var P: TProgram;
begin
  try
    P := AnalyseSrc(ASrc);
    P.Free();
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ;
  end;
end;

{ ------------------------------------------------------------------ }
{ Shared source snippets                                               }
{ ------------------------------------------------------------------ }

const
  SrcVarSet =
    '''
        program VarTest;
        procedure SetVal(var X: Integer);
        begin
          X := 42
        end;
        var V: Integer;
        begin
          V := 0;
          SetVal(V)
        end.
        ''';

  SrcVarSwap =
    '''
        program SwapTest;
        procedure Swap(var A, B: Integer);
        var T: Integer;
        begin
          T := A;
          A := B;
          B := T
        end;
        var X, Y: Integer;
        begin
          X := 1;
          Y := 2;
          Swap(X, Y)
        end.
        ''';

  SrcMixed =
    '''
        program MixedTest;
        procedure P(var A: Integer; B: Integer);
        begin
          A := B
        end;
        var X: Integer;
        begin
          P(X, 5)
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TVarParamTests.TestParse_VarParam_IsVarParam;
var P: TProgram; MD: TMethodDecl; Par: TMethodParam;
begin
  P := ParseSrc(SrcVarSet);
  try
    MD  := TMethodDecl(P.Block.ProcDecls[0]);  { SetVal }
    Par := TMethodParam(MD.Params[0]);         { var X }
    AssertTrue('X is var param', Par.IsVarParam);
  finally P.Free(); end;
end;

procedure TVarParamTests.TestParse_VarParam_MultiInGroup;
var P: TProgram; MD: TMethodDecl;
begin
  P := ParseSrc(SrcVarSwap);
  try
    MD := TMethodDecl(P.Block.ProcDecls[0]);  { Swap }
    AssertTrue('A is var param', TMethodParam(MD.Params[0]).IsVarParam);
    AssertTrue('B is var param', TMethodParam(MD.Params[1]).IsVarParam);
  finally P.Free(); end;
end;

procedure TVarParamTests.TestParse_VarParam_Mixed_VarAndValue;
var P: TProgram; MD: TMethodDecl;
begin
  P := ParseSrc(SrcMixed);
  try
    MD := TMethodDecl(P.Block.ProcDecls[0]);  { P(var A; B) }
    AssertTrue('A is var param',    TMethodParam(MD.Params[0]).IsVarParam);
    AssertFalse('B is value param', TMethodParam(MD.Params[1]).IsVarParam);
  finally P.Free(); end;
end;

procedure TVarParamTests.TestParse_VarParam_ValueParam_IsNotVar;
var P: TProgram; MD: TMethodDecl;
begin
  P := ParseSrc(
    '''
        program T;
        procedure Q(X: Integer);
        begin end;
        begin end.
        ''');
  try
    MD := TMethodDecl(P.Block.ProcDecls[0]);
    AssertFalse('X is not var param', TMethodParam(MD.Params[0]).IsVarParam);
  finally P.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TVarParamTests.TestSemantic_VarParam_OK;
begin
  AnalyseSrc(SrcVarSet).Free();
end;

procedure TVarParamTests.TestSemantic_VarParam_NonVariable_RaisesError;
begin
  AnalyseExpectError(
    'program Bad;' + #10 +
    'procedure Inc(var X: Integer);' + #10 +
    'begin X := X + 1 end;' + #10 +
    'begin' + #10 +
    '  Inc(42)'                                     + #10 +  { literal, not a variable }
    'end.');
end;

procedure TVarParamTests.TestSemantic_VarParam_TypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    'program Bad;' + #10 +
    'procedure SetI(var X: Integer);' + #10 +
    'begin X := 1 end;' + #10 +
    'var B: Boolean;' + #10 +
    'begin' + #10 +
    '  SetI(B)'                                     + #10 +  { wrong type }
    'end.');
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                        }
{ ------------------------------------------------------------------ }

procedure TVarParamTests.TestCodegen_VarParam_SignatureUsesPointerType;
var IR: string;
begin
  IR := GenIR(SrcVarSet);
  { var X: Integer → pointer param, QBE type l }
  AssertTrue('var param uses l type', Pos('l %_par_X', IR) > 0);
end;

procedure TVarParamTests.TestCodegen_VarParam_CallPassesAddress;
var IR: string;
begin
  IR := GenIR(SrcVarSet);
  { SetVal(V) must pass the address of V — V is a global so address is $V }
  AssertTrue('call passes address of V', Pos('call $SetVal(l $V)', IR) > 0);
end;

procedure TVarParamTests.TestCodegen_VarParam_WriteStoresThroughPointer;
var IR: string;
begin
  IR := GenIR(SrcVarSet);
  { X := 42 inside SetVal must load the pointer then store through it }
  AssertTrue('loads pointer for write', Pos('loadl %_var_X', IR) > 0);
  AssertTrue('storew used for Integer write', Pos('storew', IR) > 0);
end;

procedure TVarParamTests.TestCodegen_VarParam_ReadDereferencesPointer;
var IR: string;
begin
  IR := GenIR(SrcVarSwap);
  { T := A inside Swap must load the pointer then load through it }
  AssertTrue('loads pointer for read', Pos('loadl %_var_A', IR) > 0);
end;

procedure TVarParamTests.TestCodegen_VarParam_Swap;
var IR: string;
begin
  IR := GenIR(SrcVarSwap);
  { Both X and Y addresses passed to Swap — X and Y are globals so addresses are $X, $Y }
  AssertTrue('passes address of X', Pos('l $X', IR) > 0);
  AssertTrue('passes address of Y', Pos('l $Y', IR) > 0);
end;

procedure TVarParamTests.TestCodegen_VarParam_ForwardToProc;
var IR: string;
begin
  { A var param forwarded directly to another procedure's var param.
    SetViaCaller(var N) calls SetToFive(N) — N is a var param, so the codegen
    must emit  loadl %_var_N  to get the original caller's address, then pass
    that value.  Passing %_var_N directly (the slot address) is wrong. }
  IR := GenIR(
    '''
        program FwdTest;
        procedure SetToFive(var N: Integer);
        begin N := 5 end;
        procedure SetViaCaller(var N: Integer);
        begin SetToFive(N) end;
        var V: Integer;
        begin V := 0; SetViaCaller(V) end.
        ''');
  AssertTrue('SetViaCaller must loadl %_var_N to obtain original pointer',
    Pos('loadl %_var_N', IR) > 0);
  AssertFalse('must NOT pass slot address directly',
    Pos('call $SetToFive(l %_var_N)', IR) > 0);
end;

procedure TVarParamTests.TestCodegen_VarParam_ForwardToMethod;
const
  SrcMethodFwd =
    '''
        program MethodFwd;
        type
          THelper = class
            procedure SetVal(var N: Integer);
          end;
        procedure THelper.SetVal(var N: Integer);
        begin N := 7 end;
        procedure Wrapper(H: THelper; var N: Integer);
        begin H.SetVal(N) end;
        var H: THelper; V: Integer;
        begin
          H := THelper.Create();
          V := 0;
          Wrapper(H, V);
          H.Free()
        end.
        ''';
var IR: string;
begin
  { Wrapper(H: THelper; var N: Integer) calls H.SetVal(N).
    N is a var param so the codegen must emit loadl %_var_N and pass the
    result, not %_var_N itself (which is only the pointer's storage slot). }
  IR := GenIR(SrcMethodFwd);
  AssertTrue('Wrapper must loadl %_var_N for method forwarding',
    Pos('loadl %_var_N', IR) > 0);
  AssertFalse('must NOT pass slot address directly to SetVal',
    Pos('call $THelper_SetVal(l %_var_N)', IR) > 0);
end;

procedure TVarParamTests.TestSemantic_VarParam_FieldAccess_OK;
var
  Prog: TProgram;
begin
  { Pass R.Count (a field access expression) as a var argument.
    Must analyse without error — field accesses are L-values. }
  Prog := AnalyseSrc(
    '''
        program Prg;
        type
          TRec = record Count: Integer; end;
        procedure Bump(var N: Integer);
        begin Inc(N) end;
        var R: TRec;
        begin
          R.Count := 0;
          Bump(R.Count)
        end.
        ''');
  Prog.Free();
end;

procedure TVarParamTests.TestSemantic_VarParam_DerefField_OK;
var
  Prog: TProgram;
begin
  { Pass P^.Count (pointer deref + field) as a var argument. }
  Prog := AnalyseSrc(
    '''
        program Prg;
        type
          TRec = record Count: Integer; end;
          PRec = ^TRec;
        procedure Bump(var N: Integer);
        begin Inc(N) end;
        var P: PRec; R: TRec;
        begin
          P := @R;
          P^.Count := 0;
          Bump(P^.Count)
        end.
        ''');
  Prog.Free();
end;

procedure TVarParamTests.TestCodegen_VarParam_ClassFieldLeaf_LoadsObjectPointer;
const
  SrcClassFieldVarArg =
    '''
        program ClassFieldVar;
        procedure Fill(var V: Integer);
        begin V := 4096 end;
        type
          TNode = class
            Pad:   Integer;
            Value: Integer;
          end;
        var N: TNode;
        begin
          N := TNode.Create();
          Fill(N.Value)
        end.
        ''';
var
  IR: string;
begin
  IR := GenIR(SrcClassFieldVarArg);
  { N is a global class reference, so the slot is $N and stores a pointer
    to the heap object.  Computing the address of N.Value must first load
    that pointer; `add $N, <offset>` would point at unrelated memory. }
  AssertTrue('loads the class pointer from $N before offsetting',
    Pos('loadl $N', IR) > 0);
  AssertFalse('must NOT add a field offset to $N (the slot address)',
    Pos('add $N,', IR) > 0);
end;

initialization
  RegisterTest(TVarParamTests);

end.
