{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.sizeof;

{ Unit + e2e tests for the SizeOf intrinsic.

  Coverage:
    - SizeOf(TypeName) folds to a literal byte size.
    - SizeOf(variable) folds to the byte size of the variable's type.
    - SizeOf(record-field-access) folds to the field type's byte size.
    - End-to-end WriteLn(SizeOf(var)) prints the expected size. }

interface

uses
  blaise.testing, cp.test.e2e.base,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TSizeOfTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
  published
    procedure TestSemantic_SizeOf_IntegerVar_Folds4;
    procedure TestSemantic_SizeOf_ByteVar_Folds1;
    procedure TestSemantic_SizeOf_Int64Var_Folds8;
    procedure TestSemantic_SizeOf_RecordVar_FoldsRecordSize;
    procedure TestSemantic_SizeOf_RecordFieldAccess_FoldsFieldSize;
  end;

  [Threaded]
  TSizeOfE2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_SizeOf_Variable_PrintsTypeSize;
  end;

implementation

const
  LE = #10;

{ -------------- helpers -------------- }

function TSizeOfTests.AnalyseSrc(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
  A: TSemanticAnalyser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Result);
  finally
    A.Free();
  end;
end;

function TSizeOfTests.GenIR(const ASrc: string): string;
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

{ -------------- semantic / IR tests -------------- }

procedure TSizeOfTests.TestSemantic_SizeOf_IntegerVar_Folds4;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var X: Integer; N: Integer;
        begin
          N := SizeOf(X)
        end.
        ''');
  AssertTrue('SizeOf(IntegerVar) folds to 4', Pos('copy 4', IR) > 0);
end;

procedure TSizeOfTests.TestSemantic_SizeOf_ByteVar_Folds1;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var B: Byte; N: Integer;
        begin
          N := SizeOf(B)
        end.
        ''');
  AssertTrue('SizeOf(ByteVar) folds to 1', Pos('copy 1', IR) > 0);
end;

procedure TSizeOfTests.TestSemantic_SizeOf_Int64Var_Folds8;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var Q: Int64; N: Integer;
        begin
          N := SizeOf(Q)
        end.
        ''');
  AssertTrue('SizeOf(Int64Var) folds to 8', Pos('copy 8', IR) > 0);
end;

procedure TSizeOfTests.TestSemantic_SizeOf_RecordVar_FoldsRecordSize;
var
  IR: string;
begin
  { Trec: Integer(4) + Byte(1) + padding + UInt32(4), aligned to 4 = 12 bytes. }
  IR := GenIR(
    '''
        program P;
        type Trec = record a: Integer; b: Byte; c: UInt32; end;
        var T: Trec; N: Integer;
        begin
          N := SizeOf(T)
        end.
        ''');
  AssertTrue('SizeOf(RecordVar) folds to record byte size',
    (Pos('copy 12', IR) > 0) or (Pos('copy 9', IR) > 0));
end;

procedure TSizeOfTests.TestSemantic_SizeOf_RecordFieldAccess_FoldsFieldSize;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type Trec = record a: Integer; b: Byte; end;
        var T: Trec; N: Integer;
        begin
          N := SizeOf(T.b)
        end.
        ''');
  AssertTrue('SizeOf(record-field) folds to field size', Pos('copy 1', IR) > 0);
end;

{ -------------- e2e tests -------------- }

procedure TSizeOfE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-sizeof');
end;

procedure TSizeOfE2ETests.TestRun_SizeOf_Variable_PrintsTypeSize;
const
  Src =
    '''
        program P;
        var X: Integer; B: Byte;
        begin
          WriteLn(SizeOf(X));
          WriteLn(SizeOf(B))
        end.
        ''';
var
  Output: string;
  RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('SizeOf(X)=4 then SizeOf(B)=1', '4' + LE + '1' + LE, Output);
end;

initialization
  RegisterTest(TSizeOfTests);
  RegisterTest(TSizeOfE2ETests);

end.
