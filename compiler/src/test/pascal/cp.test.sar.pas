{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.sar;

{ Unit + e2e tests for the `sar` (arithmetic shift right) operator.

  Background: in Pascal, `shr` is a *logical* right shift (zero-fill) —
  it discards the sign bit.  When the programmer wants sign-preserving
  right shift on a signed integer (for example, dividing a negative
  number by a power of two), Blaise provides a distinct `sar` operator
  that maps to QBE's `sar` instruction.

  Coverage:
    - `sar` is a recognised binary operator at the term-level precedence.
    - Codegen emits QBE `sar` (not `shr`) for Int64, UInt64, and 32-bit
      integer types.
    - End-to-end: a negative Int64 sar 1 keeps its sign; a positive
      value matches the shr result. }

interface

uses
  blaise.testing, cp.test.e2e.base,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TSarTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
  published
    procedure TestCodegen_Int64_Sar_EmitsSar;
    procedure TestCodegen_UInt64_Sar_EmitsSar;
    procedure TestCodegen_Integer_Sar_EmitsSar;
    procedure TestCodegen_Shr_StillEmitsShr;
  end;

  [Threaded]
  TSarE2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_NegativeInt64_Sar_PreservesSign;
    procedure TestRun_NegativeInt64_Shr_DiscardsSign;
    procedure TestRun_PositiveInteger_Sar_MatchesShr;
  end;

implementation

{ -------------- helpers -------------- }

function TSarTests.AnalyseSrc(const ASrc: string): TProgram;
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

function TSarTests.GenIR(const ASrc: string): string;
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

{ -------------- codegen -------------- }

procedure TSarTests.TestCodegen_Int64_Sar_EmitsSar;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var A, B: Int64;
        begin
          B := A sar 1
        end.
        ''');
  AssertTrue('Int64 sar emits sar', Pos(' sar ', IR) > 0);
end;

procedure TSarTests.TestCodegen_UInt64_Sar_EmitsSar;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var A, B: UInt64;
        begin
          B := A sar 1
        end.
        ''');
  AssertTrue('UInt64 sar emits sar', Pos(' sar ', IR) > 0);
end;

procedure TSarTests.TestCodegen_Integer_Sar_EmitsSar;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var A, B: Integer;
        begin
          B := A sar 1
        end.
        ''');
  AssertTrue('Integer sar emits sar', Pos(' sar ', IR) > 0);
end;

procedure TSarTests.TestCodegen_Shr_StillEmitsShr;
var
  IR: string;
begin
  { Regression: `shr` must continue to map to QBE `shr`, not `sar`.
    A unit test for this is cheap insurance against accidental
    cross-wiring of the two operators. }
  IR := GenIR(
    '''
        program P;
        var A, B: Int64;
        begin
          B := A shr 1
        end.
        ''');
  AssertTrue('Int64 shr emits shr', Pos(' shr ', IR) > 0);
  AssertFalse('Int64 shr does not emit sar', Pos(' sar ', IR) > 0);
end;

{ -------------- e2e -------------- }

procedure TSarE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-sar');
end;

const
  LE = #10;

  SrcNegInt64Sar =
    '''
    program P;
    var A, B: Int64;
    begin
      A := -16;
      B := A sar 2;
      WriteLn(B)
    end.
    ''';

  SrcNegInt64Shr =
    '''
    program P;
    var A, B: Int64;
    begin
      A := -16;
      B := A shr 2;
      WriteLn(B)
    end.
    ''';

  SrcPosIntSar =
    '''
    program P;
    var A, B: Integer;
    begin
      A := 64;
      B := A sar 2;
      WriteLn(B)
    end.
    ''';

procedure TSarE2ETests.TestRun_NegativeInt64_Sar_PreservesSign;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcNegInt64Sar, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  { -16 sar 2 = -4 (sign preserved) }
  AssertEquals('-16 sar 2 = -4', '-4' + LE, Output);
end;

procedure TSarE2ETests.TestRun_NegativeInt64_Shr_DiscardsSign;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcNegInt64Shr, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  { -16 shr 2 = ((2^64 - 16) >> 2) = 2^62 - 4 = 4611686018427387900 }
  AssertEquals('-16 shr 2 = 4611686018427387900',
    '4611686018427387900' + LE, Output);
end;

procedure TSarE2ETests.TestRun_PositiveInteger_Sar_MatchesShr;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcPosIntSar, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  { 64 sar 2 = 16 (positive numbers behave identically) }
  AssertEquals('64 sar 2 = 16', '16' + LE, Output);
end;

initialization
  RegisterTest(TSarTests);
  RegisterTest(TSarE2ETests);

end.
