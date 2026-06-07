{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.highlow;

{ Unit + e2e tests for High/Low on ordinal types.

  Coverage:
    - High/Low of type names: Integer, Byte, Word, SmallInt, UInt32, Int64,
      UInt64, Boolean, and enums.
    - High/Low of variables of ordinal types (resolves to the var's type).
    - Result type matches the argument type (e.g. High(Int64) is Int64).
    - Targeted error message when the argument is a floating-point type. }

interface

uses
  blaise.testing, cp.test.e2e.base,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  THighLowTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string; const AExpectFragment: string);
  published
    { Type-name arguments }
    procedure TestSemantic_HighInteger_Folds2147483647;
    procedure TestSemantic_LowInteger_FoldsNeg2147483648;
    procedure TestSemantic_HighByte_Folds255;
    procedure TestSemantic_LowByte_Folds0;
    procedure TestSemantic_HighWord_Folds65535;
    procedure TestSemantic_HighSmallInt_Folds32767;
    procedure TestSemantic_LowSmallInt_FoldsNeg32768;
    procedure TestSemantic_HighBoolean_Folds1;
    procedure TestSemantic_LowBoolean_Folds0;
    procedure TestSemantic_HighUInt32_Folds4294967295;
    procedure TestSemantic_HighInt64_FoldsLLong;
    procedure TestSemantic_HighUInt64_FoldsULLong;
    procedure TestSemantic_HighEnum_FoldsLastOrdinal;
    procedure TestSemantic_LowEnum_Folds0;

    { Variable arguments resolve to the var's type bounds }
    procedure TestSemantic_HighIntegerVar_Folds2147483647;
    procedure TestSemantic_HighByteVar_Folds255;
    procedure TestSemantic_HighInt64Var_FoldsLLong;

    { Error path for floats }
    procedure TestSemantic_HighDouble_RaisesTargetedError;
    procedure TestSemantic_LowSingle_RaisesTargetedError;
  end;

  [Threaded]
  THighLowE2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_HighInteger_PrintsMaxInt;
    procedure TestRun_HighByte_Prints255;
    procedure TestRun_HighEnum_PrintsLastOrdinal;
    procedure TestRun_LowHighIntegerLoopBound;
  end;

implementation

const
  LE = #10;

{ -------------- helpers -------------- }

function THighLowTests.AnalyseSrc(const ASrc: string): TProgram;
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

function THighLowTests.GenIR(const ASrc: string): string;
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

procedure THighLowTests.AnalyseExpectError(const ASrc: string;
  const AExpectFragment: string);
var
  Threw: Boolean;
  Msg:   string;
begin
  Threw := False;
  Msg := '';
  try
    AnalyseSrc(ASrc);
  except
    on E: Exception do
    begin
      Threw := True;
      Msg := E.Message;
    end;
  end;
  AssertTrue('expected semantic error', Threw);
  AssertTrue(Format('error must mention "%s", got: %s', [AExpectFragment, Msg]),
    Pos(AExpectFragment, Msg) > 0);
end;

{ -------------- semantic / IR tests on type names -------------- }

procedure THighLowTests.TestSemantic_HighInteger_Folds2147483647;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var N: Integer;
        begin N := High(Integer) end.
        ''');
  AssertTrue('=w copy 2147483647', Pos('=w copy 2147483647', IR) > 0);
end;

procedure THighLowTests.TestSemantic_LowInteger_FoldsNeg2147483648;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var N: Integer;
        begin N := Low(Integer) end.
        ''');
  AssertTrue('=w copy -2147483648', Pos('=w copy -2147483648', IR) > 0);
end;

procedure THighLowTests.TestSemantic_HighByte_Folds255;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var B: Byte;
        begin B := High(Byte) end.
        ''');
  AssertTrue('copy 255', Pos('copy 255', IR) > 0);
end;

procedure THighLowTests.TestSemantic_LowByte_Folds0;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var B: Byte;
        begin B := Low(Byte) end.
        ''');
  AssertTrue('copy 0', Pos('copy 0', IR) > 0);
end;

procedure THighLowTests.TestSemantic_HighWord_Folds65535;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var W: Word;
        begin W := High(Word) end.
        ''');
  AssertTrue('copy 65535', Pos('copy 65535', IR) > 0);
end;

procedure THighLowTests.TestSemantic_HighSmallInt_Folds32767;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var S: SmallInt;
        begin S := High(SmallInt) end.
        ''');
  AssertTrue('copy 32767', Pos('copy 32767', IR) > 0);
end;

procedure THighLowTests.TestSemantic_LowSmallInt_FoldsNeg32768;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var S: SmallInt;
        begin S := Low(SmallInt) end.
        ''');
  AssertTrue('copy -32768', Pos('copy -32768', IR) > 0);
end;

procedure THighLowTests.TestSemantic_HighBoolean_Folds1;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var B: Boolean;
        begin B := High(Boolean) end.
        ''');
  AssertTrue('copy 1', Pos('copy 1', IR) > 0);
end;

procedure THighLowTests.TestSemantic_LowBoolean_Folds0;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var B: Boolean;
        begin B := Low(Boolean) end.
        ''');
  AssertTrue('copy 0', Pos('copy 0', IR) > 0);
end;

procedure THighLowTests.TestSemantic_HighUInt32_Folds4294967295;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var U: UInt32;
        begin U := High(UInt32) end.
        ''');
  AssertTrue('copy 4294967295', Pos('copy 4294967295', IR) > 0);
end;

procedure THighLowTests.TestSemantic_HighInt64_FoldsLLong;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var Q: Int64;
        begin Q := High(Int64) end.
        ''');
  AssertTrue('=l copy 9223372036854775807',
    Pos('=l copy 9223372036854775807', IR) > 0);
end;

procedure THighLowTests.TestSemantic_HighUInt64_FoldsULLong;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var Q: UInt64;
        begin Q := High(UInt64) end.
        ''');
  AssertTrue('=l copy 18446744073709551615',
    Pos('=l copy 18446744073709551615', IR) > 0);
end;

procedure THighLowTests.TestSemantic_HighEnum_FoldsLastOrdinal;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TColour = (Red, Green, Blue);
        var N: Integer;
        begin N := Ord(High(TColour)) end.
        ''');
  AssertTrue('=w copy 2', Pos('=w copy 2', IR) > 0);
end;

procedure THighLowTests.TestSemantic_LowEnum_Folds0;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TColour = (Red, Green, Blue);
        var N: Integer;
        begin N := Ord(Low(TColour)) end.
        ''');
  AssertTrue('=w copy 0', Pos('=w copy 0', IR) > 0);
end;

{ -------------- variable arguments -------------- }

procedure THighLowTests.TestSemantic_HighIntegerVar_Folds2147483647;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var X, N: Integer;
        begin N := High(X) end.
        ''');
  AssertTrue('=w copy 2147483647', Pos('=w copy 2147483647', IR) > 0);
end;

procedure THighLowTests.TestSemantic_HighByteVar_Folds255;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var B: Byte;
        begin B := High(B) end.
        ''');
  AssertTrue('copy 255', Pos('copy 255', IR) > 0);
end;

procedure THighLowTests.TestSemantic_HighInt64Var_FoldsLLong;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var Q: Int64;
        begin Q := High(Q) end.
        ''');
  AssertTrue('=l copy 9223372036854775807',
    Pos('=l copy 9223372036854775807', IR) > 0);
end;

{ -------------- error path -------------- }

procedure THighLowTests.TestSemantic_HighDouble_RaisesTargetedError;
begin
  AnalyseExpectError(
    '''
        program P;
        var D: Double;
        begin D := High(D) end.
        ''',
    'floating-point');
end;

procedure THighLowTests.TestSemantic_LowSingle_RaisesTargetedError;
begin
  AnalyseExpectError(
    '''
        program P;
        var S: Single;
        begin S := Low(S) end.
        ''',
    'floating-point');
end;

{ -------------- e2e tests -------------- }

procedure THighLowE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-highlow');
end;

procedure THighLowE2ETests.TestRun_HighInteger_PrintsMaxInt;
const
  Src =
    '''
        program P;
        begin
          WriteLn(High(Integer));
          WriteLn(Low(Integer))
        end.
        ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Integer bounds',
    '2147483647' + LE + '-2147483648' + LE, Output);
end;

procedure THighLowE2ETests.TestRun_HighByte_Prints255;
const
  Src =
    '''
        program P;
        var B: Byte;
        begin
          B := High(Byte);
          WriteLn(B)
        end.
        ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Byte high', '255' + LE, Output);
end;

procedure THighLowE2ETests.TestRun_HighEnum_PrintsLastOrdinal;
const
  Src =
    '''
        program P;
        type TColour = (Red, Green, Blue);
        begin
          WriteLn(Ord(High(TColour)));
          WriteLn(Ord(Low(TColour)))
        end.
        ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('enum bounds', '2' + LE + '0' + LE, Output);
end;

procedure THighLowE2ETests.TestRun_LowHighIntegerLoopBound;
const
  { Smoke test: using High/Low as loop literal sentinels. }
  Src =
    '''
        program P;
        var I, N: Integer;
        begin
          N := 0;
          for I := 1 to 5 do
            N := N + I;
          if N < High(Integer) then
            WriteLn(N);
          if N > Low(Integer) then
            WriteLn('ok')
        end.
        ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('loop guard', '15' + LE + 'ok' + LE, Output);
end;

initialization
  RegisterTest(THighLowTests);
  RegisterTest(THighLowE2ETests);

end.
