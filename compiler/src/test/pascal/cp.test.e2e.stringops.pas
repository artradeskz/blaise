{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.stringops;

{ E2E tests for string operations, Int64 formatting, and string subscripting. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EStringOpsTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_StringOps_Length;
    procedure TestRun_StringOps_Pos;
    procedure TestRun_StringOps_Copy;
    procedure TestRun_StringOps_UpperCase;
    procedure TestRun_StringOps_SameText;
    procedure TestRun_StringOps_IntToStr;
    procedure TestRun_StringOps_StrToInt;
    procedure TestRun_StringOps_StrToInt_Hex;
    procedure TestRun_StringOps_Copy_MaxIntCount;
    procedure TestRun_Int64_PositiveAboveInt32_FormatsCorrectly;
    procedure TestRun_StringOps_Format_IntArg;
    procedure TestRun_StringOps_Format_StrArg;
    procedure TestRun_StringOps_Format_MixedArgs;
    procedure TestRun_StringSubscript_ReadByte;
    procedure TestRun_StringConcat_TwoStrings;
    procedure TestRun_StringConcat_WithInt;
    procedure TestRun_StringDelete_Modifies;
    procedure TestRun_StringSetLength_Truncates;
    procedure TestRun_Int64_ArithmeticOverInt32;
    procedure TestRun_Int64_Comparison;
    procedure TestRun_Int64_ForLoop;
  end;

implementation

procedure TE2EStringOpsTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-stringops');
end;

const
  LE = #10;

  SrcStringLength =
    '''
        program P;
        var s: string;
        var n: Integer;
        begin
          s := 'hello';
          n := Length(s);
          WriteLn(n)
        end.
        ''';

  SrcStringPos =
    '''
        program P;
        var s, sub: string;
        var n: Integer;
        begin
          s   := 'hello world';
          sub := 'world';
          n   := Pos(sub, s);
          WriteLn(n)
        end.
        ''';

  SrcStringCopy =
    '''
        program P;
        var s, t: string;
        begin
          s := 'hello';
          t := Copy(s, 1, 3);
          WriteLn(t)
        end.
        ''';

  SrcStringUpperCase =
    '''
        program P;
        var s, t: string;
        begin
          s := 'hello';
          t := UpperCase(s);
          WriteLn(t)
        end.
        ''';

  SrcStringSameText =
    '''
        program P;
        var s, t: string;
        var b: Boolean;
        begin
          s := 'Hello';
          t := 'hello';
          b := SameText(s, t);
          WriteLn(b)
        end.
        ''';

  SrcStringIntToStr =
    '''
        program P;
        var n: Integer;
        var s: string;
        begin
          n := 42;
          s := IntToStr(n);
          WriteLn(s)
        end.
        ''';

  SrcStringStrToInt =
    '''
        program P;
        var s: string;
        var n: Integer;
        begin
          s := '123';
          n := StrToInt(s);
          WriteLn(n)
        end.
        ''';

  SrcStringStrToIntHex =
    '''
        program P;
        var n: Integer;
        begin
          n := StrToInt('$FF');
          WriteLn(n)
        end.
        ''';

  SrcStringCopyMaxIntCount =
    '''
        program P;
        var s: string;
        begin
          s := Copy('^Integer', 1, MaxInt);
          WriteLn(s)
        end.
        ''';

  SrcInt64PositiveAboveInt32 =
    '''
        program P;
        var v: Int64;
        begin
          v := 1000000000;
          v := v + v + 166136261;
          if v < 0 then WriteLn('neg')
                  else WriteLn('pos');
          WriteLn(IntToStr(v))
        end.
        ''';

  SrcFormatIntArg =
    '''
        program P;
        var n: Integer;
        var s: string;
        begin
          n := 42;
          s := Format('val=%d', n);
          WriteLn(s)
        end.
        ''';

  SrcFormatStrArg =
    '''
        program P;
        var t: string;
        var s: string;
        begin
          t := 'world';
          s := Format('hello %s', t);
          WriteLn(s)
        end.
        ''';

  SrcFormatMixedArgs =
    '''
        program P;
        var name: string;
        var age: Integer;
        var s: string;
        begin
          name := 'Alice';
          age  := 30;
          s := Format('%s=%d', name, age);
          WriteLn(s)
        end.
        ''';

  SrcStringSubscript = '''
    program P;
    var S: string;
    begin
      S := 'ABC';
      WriteLn(S[0]);
      WriteLn(S[1]);
      WriteLn(S[2])
    end.
    ''';

  SrcStringConcatStr = '''
    program P;
    var A, B, C: string;
    begin
      A := 'foo';
      B := 'bar';
      C := A + B;
      WriteLn(C)
    end.
    ''';

  SrcStringDelete = '''
    program P;
    var S: string;
    begin
      S := 'Hello World';
      Delete(S, 5, 6);
      WriteLn(S)
    end.
    ''';

  SrcStringSetLength = '''
    program P;
    var S: string;
    begin
      S := 'Hello';
      SetLength(S, 3);
      WriteLn(S)
    end.
    ''';

  SrcInt64Arith = '''
    program P;
    var A, B: Int64;
    begin
      A := 3000000000;
      B := A * 2;
      WriteLn(B)
    end.
    ''';

  SrcInt64Compare = '''
    program P;
    var A: Int64;
    begin
      A := 5000000000;
      if A > 4000000000 then WriteLn('big');
      if A < 6000000000 then WriteLn('small')
    end.
    ''';

  SrcInt64ForLoop = '''
    program P;
    var I: Int64; S: Int64;
    begin
      S := 0;
      for I := 1 to 5 do
        S := S + I;
      WriteLn(S)
    end.
    ''';

procedure TE2EStringOpsTests.TestRun_StringOps_Length;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringLength, Output, RCode));
  AssertEquals('Length(''hello'') = 5', '5', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_Pos;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringPos, Output, RCode));
  AssertEquals('Pos(''world'', ''hello world'') = 6', '6', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_Copy;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringCopy, Output, RCode));
  AssertEquals('Copy(''hello'', 1, 3) = ''ell''', 'ell', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_UpperCase;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringUpperCase, Output, RCode));
  AssertEquals('UpperCase(''hello'') = ''HELLO''', 'HELLO', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_SameText;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringSameText, Output, RCode));
  AssertEquals('SameText(''Hello'', ''hello'') = True', 'True', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_IntToStr;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringIntToStr, Output, RCode));
  AssertEquals('IntToStr(42) = ''42''', '42', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_StrToInt;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringStrToInt, Output, RCode));
  AssertEquals('StrToInt(''123'') = 123', '123', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_StrToInt_Hex;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringStrToIntHex, Output, RCode));
  AssertEquals('StrToInt(''$FF'') = 255', '255', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_Copy_MaxIntCount;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringCopyMaxIntCount, Output, RCode));
  AssertEquals('Copy(''^Integer'', 1, MaxInt) = ''Integer''', 'Integer', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_Int64_PositiveAboveInt32_FormatsCorrectly;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInt64PositiveAboveInt32, Output, RCode));
  AssertEquals('Int64=2166136261 compares as positive and formats correctly',
    'pos' + LE + '2166136261', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_Format_IntArg;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcFormatIntArg, Output, RCode));
  AssertEquals('Format int arg', 'val=42', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_Format_StrArg;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcFormatStrArg, Output, RCode));
  AssertEquals('Format str arg', 'hello world', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringOps_Format_MixedArgs;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcFormatMixedArgs, Output, RCode));
  AssertEquals('Format mixed args', 'Alice=30', Trim(Output));
end;

procedure TE2EStringOpsTests.TestRun_StringSubscript_ReadByte;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringSubscript, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('65 66 67', '65' + LE + '66' + LE + '67' + LE, Output);
end;

procedure TE2EStringOpsTests.TestRun_StringConcat_TwoStrings;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringConcatStr, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('foobar', 'foobar' + LE, Output);
end;

procedure TE2EStringOpsTests.TestRun_StringConcat_WithInt;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun('program P; begin WriteLn(''x='' + IntToStr(7)) end.',
                  Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('x=7', 'x=7' + LE, Output);
end;

procedure TE2EStringOpsTests.TestRun_StringDelete_Modifies;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringDelete, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Hello', 'Hello' + LE, Output);
end;

procedure TE2EStringOpsTests.TestRun_StringSetLength_Truncates;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcStringSetLength, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Hel', 'Hel' + LE, Output);
end;

procedure TE2EStringOpsTests.TestRun_Int64_ArithmeticOverInt32;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInt64Arith, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('6000000000', '6000000000' + LE, Output);
end;

procedure TE2EStringOpsTests.TestRun_Int64_Comparison;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInt64Compare, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('big small', 'big' + LE + 'small' + LE, Output);
end;

procedure TE2EStringOpsTests.TestRun_Int64_ForLoop;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInt64ForLoop, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('15', '15' + LE, Output);
end;

initialization
  RegisterTest(TE2EStringOpsTests);

end.
