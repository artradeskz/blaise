{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.proctypes;

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSemantic, uSymbolTable, blaise.codegen.qbe;

type
  TProcTypesTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    function IRContains(const AIR, AFragment: string): Boolean;
    function FindTypeDecl(AProg: TProgram; const AName: string): TTypeDecl;
  published
    { Parser — bare procedural type declarations }
    procedure TestParse_NoArgFunc_KindIsProcedural;
    procedure TestParse_NoArgFunc_ReturnTypeIsInteger;
    procedure TestParse_FuncWithParams_ParamCount;
    procedure TestParse_FuncWithParams_FirstParamName;
    procedure TestParse_FuncWithParams_ConstParamFlag;
    procedure TestParse_NoArgProc_KindIsProcedural;
    procedure TestParse_NoArgProc_NoReturnType;
    procedure TestParse_ProcWithVarParam_VarParamFlag;

    { Semantic — type assignability }
    procedure TestSemantic_AssignCompatibleFunc_OK;
    procedure TestSemantic_AssignWrongReturnType_Fails;
    procedure TestSemantic_AssignWrongParamCount_Fails;

    { Semantic — indirect-call argument type checking.
      Calls through a procedural-typed variable must validate each
      argument's type against the signature, not just the arg count. }
    procedure TestSemantic_IndirectCallStmt_WrongArgType_Fails;
    procedure TestSemantic_IndirectCallExpr_WrongArgType_Fails;

    { Codegen — emission }
    procedure TestCodegen_ProceduralVar_AllocatedAsPointer;
    procedure TestCodegen_AddrOfFunc_EmitsFunctionLabel;
    procedure TestCodegen_IndirectCall_UsesTempNotName;
  end;

implementation

function TProcTypesTests.ParseSrc(const ASrc: string): TProgram;
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

function TProcTypesTests.GenIR(const ASrc: string): string;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  CG: TCodeGenQBE;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
  finally
    A.Free();
  end;
  CG := TCodeGenQBE.Create();
  try
    CG.Generate(Pr);
    Result := CG.GetOutput();
  finally
    CG.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

function TProcTypesTests.IRContains(const AIR, AFragment: string): Boolean;
begin
  Result := Pos(AFragment, AIR) > 0;
end;

function TProcTypesTests.FindTypeDecl(AProg: TProgram; const AName: string): TTypeDecl;
var
  I: Integer;
  TD: TTypeDecl;
begin
  Result := nil;
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if SameText(TD.Name, AName) then
    begin
      Result := TD;
      Exit;
    end;
  end;
end;

{ ── Parser tests ─────────────────────────────────────────────────────────── }

procedure TProcTypesTests.TestParse_NoArgFunc_KindIsProcedural;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TIntFn = function: Integer;
        begin
        end.
        '''
  );
  try
    TD := FindTypeDecl(Prog, 'TIntFn');
    AssertNotNull('Should find type decl TIntFn', TD);
    AssertTrue('Def should be a TProceduralTypeDef',
      TD.Def is TProceduralTypeDef);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_NoArgFunc_ReturnTypeIsInteger;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TIntFn = function: Integer;
        begin
        end.
        '''
  );
  try
    TD  := FindTypeDecl(Prog, 'TIntFn');
    Def := TProceduralTypeDef(TD.Def);
    AssertEquals('IsFunction should be True', True, Def.IsFunction);
    AssertEquals('ReturnTypeName should be Integer', 'Integer', Def.ReturnTypeName);
    AssertEquals('Should have 0 params', 0, Def.Params.Count);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_FuncWithParams_ParamCount;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TBinFn = function(A: Integer; B: Integer): Integer;
        begin
        end.
        '''
  );
  try
    TD  := FindTypeDecl(Prog, 'TBinFn');
    Def := TProceduralTypeDef(TD.Def);
    AssertEquals('Should have 2 params', 2, Def.Params.Count);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_FuncWithParams_FirstParamName;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
  P1:   TMethodParam;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TBinFn = function(A: Integer; B: Integer): Integer;
        begin
        end.
        '''
  );
  try
    TD  := FindTypeDecl(Prog, 'TBinFn');
    Def := TProceduralTypeDef(TD.Def);
    P1  := TMethodParam(Def.Params.Items[0]);
    AssertEquals('First param name', 'A', P1.ParamName);
    AssertEquals('First param type', 'Integer', P1.TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_FuncWithParams_ConstParamFlag;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
  P1:   TMethodParam;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TStrFn = function(const S: string): Integer;
        begin
        end.
        '''
  );
  try
    TD  := FindTypeDecl(Prog, 'TStrFn');
    Def := TProceduralTypeDef(TD.Def);
    P1  := TMethodParam(Def.Params.Items[0]);
    AssertEquals('Param name', 'S', P1.ParamName);
    AssertTrue('IsConstParam should be True', P1.IsConstParam);
    AssertFalse('IsVarParam should be False', P1.IsVarParam);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_NoArgProc_KindIsProcedural;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TVoidProc = procedure;
        begin
        end.
        '''
  );
  try
    TD := FindTypeDecl(Prog, 'TVoidProc');
    AssertNotNull('Should find type decl TVoidProc', TD);
    AssertTrue('Def should be a TProceduralTypeDef',
      TD.Def is TProceduralTypeDef);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_NoArgProc_NoReturnType;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TVoidProc = procedure;
        begin
        end.
        '''
  );
  try
    TD  := FindTypeDecl(Prog, 'TVoidProc');
    Def := TProceduralTypeDef(TD.Def);
    AssertEquals('IsFunction should be False', False, Def.IsFunction);
    AssertEquals('ReturnTypeName should be empty', '', Def.ReturnTypeName);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_ProcWithVarParam_VarParamFlag;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
  P1:   TMethodParam;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TIncProc = procedure(var X: Integer);
        begin
        end.
        '''
  );
  try
    TD  := FindTypeDecl(Prog, 'TIncProc');
    Def := TProceduralTypeDef(TD.Def);
    P1  := TMethodParam(Def.Params.Items[0]);
    AssertTrue('IsVarParam should be True', P1.IsVarParam);
    AssertFalse('IsConstParam should be False', P1.IsConstParam);
  finally
    Prog.Free();
  end;
end;

{ ── Semantic tests ───────────────────────────────────────────────────────── }

procedure TProcTypesTests.TestSemantic_AssignCompatibleFunc_OK;
var
  IR: string;
begin
  { Should not raise. Assigning @MyFn to a TIntFn variable type-checks. }
  IR := GenIR(
    '''
        program Test;
        type
          TIntFn = function: Integer;
        function MyFn: Integer;
        begin
          Result := 42;
        end;
        var F: TIntFn;
        begin
          F := @MyFn;
        end.
        '''
  );
  AssertTrue('IR should be non-empty', Length(IR) > 0);
end;

procedure TProcTypesTests.TestSemantic_AssignWrongReturnType_Fails;
var
  Raised: Boolean;
begin
  Raised := False;
  try
    GenIR(
      '''
          program Test;
          type
            TIntFn = function: Integer;
          function MyFn: string;
          begin
            Result := 'nope';
          end;
          var F: TIntFn;
          begin
            F := @MyFn;
          end.
          '''
    );
  except
    Raised := True;
  end;
  AssertTrue('Should raise on incompatible return type', Raised);
end;

procedure TProcTypesTests.TestSemantic_AssignWrongParamCount_Fails;
var
  Raised: Boolean;
begin
  Raised := False;
  try
    GenIR(
      '''
          program Test;
          type
            TIntFn = function: Integer;
          function MyFn(X: Integer): Integer;
          begin
            Result := X;
          end;
          var F: TIntFn;
          begin
            F := @MyFn;
          end.
          '''
    );
  except
    Raised := True;
  end;
  AssertTrue('Should raise on incompatible param count', Raised);
end;

procedure TProcTypesTests.TestSemantic_IndirectCallStmt_WrongArgType_Fails;
var
  Raised: Boolean;
begin
  { Statement-form indirect call: H('s') where H expects Integer must
    be rejected at semantic time, not silently miscompiled. }
  Raised := False;
  try
    GenIR(
      '''
          program Test;
          type
            THandler = procedure(N: Integer);
          procedure DoIt(N: Integer);
          begin
          end;
          var H: THandler;
          begin
            H := @DoIt;
            H('oops')
          end.
          '''
    );
  except
    Raised := True;
  end;
  AssertTrue(
    'Indirect call statement should reject string where Integer expected',
    Raised);
end;

procedure TProcTypesTests.TestSemantic_IndirectCallExpr_WrongArgType_Fails;
var
  Raised: Boolean;
begin
  { Expression-form indirect call: R := F('s') where F expects Integer
    must also be rejected at semantic time. }
  Raised := False;
  try
    GenIR(
      '''
          program Test;
          type
            TIntFn = function(N: Integer): Integer;
          function Square(N: Integer): Integer;
          begin
            Result := N * N
          end;
          var F: TIntFn; R: Integer;
          begin
            F := @Square;
            R := F('oops')
          end.
          '''
    );
  except
    Raised := True;
  end;
  AssertTrue(
    'Indirect call expression should reject string where Integer expected',
    Raised);
end;

{ ── Codegen tests ────────────────────────────────────────────────────────── }

procedure TProcTypesTests.TestCodegen_ProceduralVar_AllocatedAsPointer;
var
  IR: string;
begin
  { Inside a function body, a procedural variable is stack-allocated as
    a single pointer slot (alloc8 1).  At program scope it would land in
    the data section, which is also a pointer slot; this test pins the
    stack-allocation path. }
  IR := GenIR(
    '''
        program Test;
        type
          TIntFn = function: Integer;
        procedure UseFn;
        var
          F: TIntFn;
        begin
        end;
        begin
          UseFn;
        end.
        '''
  );
  AssertTrue('IR should contain alloc8 for procedural var',
    IRContains(IR, 'alloc8'));
end;

procedure TProcTypesTests.TestCodegen_AddrOfFunc_EmitsFunctionLabel;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        type
          TIntFn = function: Integer;
        function MyFn: Integer;
        begin
          Result := 42;
        end;
        var F: TIntFn;
        begin
          F := @MyFn;
        end.
        '''
  );
  { Storing @MyFn into F should put the address $MyFn into the variable. }
  AssertTrue('IR should reference $MyFn as an address',
    IRContains(IR, '$MyFn'));
end;

procedure TProcTypesTests.TestCodegen_IndirectCall_UsesTempNotName;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        type
          TIntFn = function: Integer;
        function MyFn: Integer;
        begin
          Result := 42;
        end;
        var
          F: TIntFn;
          X: Integer;
        begin
          F := @MyFn;
          X := F();
        end.
        '''
  );
  { An indirect call through F() must NOT emit 'call $MyFn(' — that would be a
    direct call.  It should call through a temp, e.g. 'call %tmp(' where the
    temp was loaded from F. }
  AssertFalse('Indirect call must not be a direct call to $MyFn',
    IRContains(IR, 'call $MyFn('));
end;

initialization
  RegisterTest(TProcTypesTests);

end.
