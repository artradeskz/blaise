{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.uint64;

{ Unit + e2e tests for the UInt64 / QWord type.

  Coverage:
    - UInt64 and QWord both resolve to the same type descriptor.
    - SizeOf(UInt64) = SizeOf(QWord) = 8.
    - Mixing Int64 and UInt64 in an expression is a type error.
    - Comparisons use unsigned QBE comparison instructions (cugtl, cultl, ...).
    - Arithmetic uses udiv/urem for division/modulo.
    - Decimal literal in the (2^63, 2^64-1) range parses as UInt64.
    - End-to-end WriteLn / IntToStr / UInt64ToStr round-trip. }

interface

uses
  blaise.testing, cp.test.e2e.base,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

type
  TUInt64Tests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    procedure TestSemantic_UInt64_TypeRegistered;
    procedure TestSemantic_QWord_TypeRegistered;
    procedure TestSemantic_QWordIsAliasOfUInt64;
    procedure TestSemantic_SizeOf_UInt64_Is8;
    procedure TestSemantic_SizeOf_QWord_Is8;
    procedure TestSemantic_PtrUInt_IsUInt64;
    procedure TestSemantic_UInt64_Plus_Int64_IsError;
    procedure TestSemantic_LargeLiteralResolvesAsUInt64;
    procedure TestCodegen_UInt64_Less_UsesUnsignedCmp;
    procedure TestCodegen_UInt64_Greater_UsesUnsignedCmp;
    procedure TestCodegen_UInt64_Div_UsesUdiv;
    procedure TestCodegen_UInt64_Mod_UsesUrem;
    procedure TestCodegen_WriteLn_UInt64_CallsSysWriteUInt64;
    procedure TestCodegen_IntToStr_UInt64_CallsUInt64ToStr;
  end;

  [Threaded]
  TUInt64E2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_UInt64_RoundTrip;
    procedure TestRun_QWord_Alias;
    procedure TestRun_UInt64_LargeLiteral;
    procedure TestRun_UInt64_Arithmetic;
    procedure TestRun_UInt64_UnsignedCompare;
    procedure TestRun_Int64_MinValue;
  end;

implementation

{ -------------- helpers -------------- }

function TUInt64Tests.AnalyseSrc(const ASrc: string): TProgram;
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

function TUInt64Tests.GenIR(const ASrc: string): string;
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

procedure TUInt64Tests.AnalyseExpectError(const ASrc: string);
var
  Prog: TProgram;
begin
  try
    Prog := AnalyseSrc(ASrc);
    Prog.Free();
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ; { expected }
  end;
end;

{ -------------- semantic -------------- }

procedure TUInt64Tests.TestSemantic_UInt64_TypeRegistered;
const
  Src =
    '''
        program P;
        var X: UInt64;
        begin end.
        ''';
var
  Prog: TProgram;
  T:    TTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    T := TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType;
    AssertTrue('UInt64 resolves',     T <> nil);
    AssertEquals('Kind = tyUInt64', Ord(tyUInt64), Ord(T.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TUInt64Tests.TestSemantic_QWord_TypeRegistered;
const
  Src =
    '''
        program P;
        var X: QWord;
        begin end.
        ''';
var
  Prog: TProgram;
  T:    TTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    T := TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType;
    AssertTrue('QWord resolves',      T <> nil);
    AssertEquals('Kind = tyUInt64', Ord(tyUInt64), Ord(T.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TUInt64Tests.TestSemantic_QWordIsAliasOfUInt64;
const
  Src =
    '''
        program P;
        var A: UInt64;
        var B: QWord;
        begin end.
        ''';
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertSame('UInt64 and QWord share one descriptor',
      TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType,
      TVarDecl(Prog.Block.Decls.Items[1]).ResolvedType);
  finally
    Prog.Free();
  end;
end;

procedure TUInt64Tests.TestSemantic_SizeOf_UInt64_Is8;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var N: Integer;
        begin
          N := SizeOf(UInt64)
        end.
        ''');
  AssertTrue('SizeOf(UInt64) is 8', Pos('copy 8', IR) > 0);
end;

procedure TUInt64Tests.TestSemantic_SizeOf_QWord_Is8;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var N: Integer;
        begin
          N := SizeOf(QWord)
        end.
        ''');
  AssertTrue('SizeOf(QWord) is 8', Pos('copy 8', IR) > 0);
end;

procedure TUInt64Tests.TestSemantic_PtrUInt_IsUInt64;
const
  Src =
    '''
        program P;
        var P1: PtrUInt;
        begin end.
        ''';
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertEquals('PtrUInt has Kind=tyUInt64', Ord(tyUInt64),
      Ord(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TUInt64Tests.TestSemantic_UInt64_Plus_Int64_IsError;
begin
  AnalyseExpectError(
    '''
        program P;
        var U: UInt64;
        var I: Int64;
        begin
          U := U + I
        end.
        ''');
end;

procedure TUInt64Tests.TestSemantic_LargeLiteralResolvesAsUInt64;
const
  { 18000000000000000000 is larger than MaxInt64 (9223372036854775807) but
    fits in UInt64. }
  Src =
    '''
        program P;
        var U: UInt64;
        begin
          U := 18000000000000000000
        end.
        ''';
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  Prog.Free();
end;

{ -------------- codegen -------------- }

procedure TUInt64Tests.TestCodegen_UInt64_Less_UsesUnsignedCmp;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var A, B: UInt64;
        var R: Boolean;
        begin
          R := A < B
        end.
        ''');
  AssertTrue('UInt64 < uses cultl', Pos('cultl', IR) > 0);
  AssertFalse('no signed csltl',     Pos('csltl', IR) > 0);
end;

procedure TUInt64Tests.TestCodegen_UInt64_Greater_UsesUnsignedCmp;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var A, B: UInt64;
        var R: Boolean;
        begin
          R := A > B
        end.
        ''');
  AssertTrue('UInt64 > uses cugtl', Pos('cugtl', IR) > 0);
end;

procedure TUInt64Tests.TestCodegen_UInt64_Div_UsesUdiv;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var A, B, C: UInt64;
        begin
          C := A div B
        end.
        ''');
  AssertTrue('UInt64 div uses udiv', Pos('udiv', IR) > 0);
end;

procedure TUInt64Tests.TestCodegen_UInt64_Mod_UsesUrem;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var A, B, C: UInt64;
        begin
          C := A mod B
        end.
        ''');
  AssertTrue('UInt64 mod uses urem', Pos('urem', IR) > 0);
end;

procedure TUInt64Tests.TestCodegen_WriteLn_UInt64_CallsSysWriteUInt64;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var U: UInt64;
        begin
          WriteLn(U)
        end.
        ''');
  AssertTrue('WriteLn(UInt64) calls _SysWriteUInt64',
    Pos('$_SysWriteUInt64', IR) > 0);
end;

procedure TUInt64Tests.TestCodegen_IntToStr_UInt64_CallsUInt64ToStr;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program P;
        var U: UInt64;
        var S: string;
        begin
          S := IntToStr(U)
        end.
        ''');
  AssertTrue('IntToStr(UInt64) routes to _UInt64ToStr',
    Pos('$_UInt64ToStr', IR) > 0);
end;

{ -------------- e2e -------------- }

procedure TUInt64E2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-uint64');
end;

const
  LE = #10;

  SrcUInt64RoundTrip =
    '''
    program P;
    var U: UInt64;
    begin
      U := 42;
      WriteLn(U)
    end.
    ''';

  SrcQWordAlias =
    '''
    program P;
    var Q: QWord;
    begin
      Q := 100;
      WriteLn(Q)
    end.
    ''';

  SrcUInt64LargeLiteral =
    '''
    program P;
    var U: UInt64;
    begin
      U := 18000000000000000000;
      WriteLn(U)
    end.
    ''';

  SrcUInt64Arithmetic =
    '''
    program P;
    var A, B, S: UInt64;
    begin
      A := 1000000;
      B := 2000003;
      S := A + B;
      WriteLn(S);
      WriteLn(B div A);
      WriteLn(B mod A)
    end.
    ''';

  SrcUInt64UnsignedCompare =
    '''
    program P;
    var A, B: UInt64;
    begin
      { 17000000000000000000 > MaxInt64 — must be treated as unsigned. }
      A := 17000000000000000000;
      B := 1;
      if A > B then WriteLn('yes') else WriteLn('no')
    end.
    ''';

  { Low(Int64) = -9223372036854775808 has no positive counterpart, so a
    naive negate-then-extract-digits path overflows and prints only '-'.
    WriteDecimal must handle the most-negative value correctly. }
  SrcInt64MinValue =
    '''
    program P;
    var N: Int64;
    begin
      N := Int64(1) shl 63;
      WriteLn(N)
    end.
    ''';

procedure TUInt64E2ETests.TestRun_UInt64_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcUInt64RoundTrip, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('42', '42' + LE, Output);
end;

procedure TUInt64E2ETests.TestRun_QWord_Alias;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcQWordAlias, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('100', '100' + LE, Output);
end;

procedure TUInt64E2ETests.TestRun_UInt64_LargeLiteral;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcUInt64LargeLiteral, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('large literal round-trips',
    '18000000000000000000' + LE, Output);
end;

procedure TUInt64E2ETests.TestRun_UInt64_Arithmetic;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcUInt64Arithmetic, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('sum, div, mod',
    '3000003' + LE + '2' + LE + '3' + LE, Output);
end;

procedure TUInt64E2ETests.TestRun_UInt64_UnsignedCompare;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcUInt64UnsignedCompare, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('17e18 > 1 unsigned',
    'yes' + LE, Output);
end;

procedure TUInt64E2ETests.TestRun_Int64_MinValue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInt64MinValue, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Low(Int64) prints in full',
    '-9223372036854775808' + LE, Output);
end;

initialization
  RegisterTest(TUInt64Tests);
  RegisterTest(TUInt64E2ETests);

end.
