{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.records;

{ E2E tests for record types: field read/write, pass by value, pass by var,
  string fields under ARC, and nested records. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ERecordsTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_Record_FieldReadWrite;
    procedure TestRun_Record_PassByValue;
    procedure TestRun_Record_PassByVar;
    procedure TestRun_Record_AssignToVarParam;
    procedure TestRun_Record_StringField_ARC;
    procedure TestRun_Record_NestedRecord;
    procedure TestRun_Record_FourByteFields_PackedAndRoundTrip;
    procedure TestRun_Record_ByteThenInteger_RoundTrip;
  end;

implementation

procedure TE2ERecordsTests.SetUp;
begin
  inherited SetUp;
  SetUpScratch('compiler/target/test-e2e-records');
end;

const
  LE = #10;

  SrcRecordFieldRW = '''
    program P;
    type TPoint = record X, Y: Integer; end;
    var P1: TPoint;
    begin
      P1.X := 3;
      P1.Y := 7;
      WriteLn(P1.X + P1.Y)
    end.
    ''';

  SrcRecordPassByValue = '''
    program P;
    type TPoint = record X, Y: Integer; end;
    procedure Print(Pt: TPoint);
    begin
      WriteLn(Pt.X);
      WriteLn(Pt.Y)
    end;
    var P1: TPoint;
    begin
      P1.X := 5;
      P1.Y := 9;
      Print(P1)
    end.
    ''';

  SrcRecordPassByVar = '''
    program P;
    type TPoint = record X, Y: Integer; end;
    procedure Scale(var Pt: TPoint);
    begin
      Pt.X := Pt.X * 2;
      Pt.Y := Pt.Y * 2
    end;
    var P1: TPoint;
    begin
      P1.X := 3;
      P1.Y := 4;
      Scale(P1);
      WriteLn(P1.X);
      WriteLn(P1.Y)
    end.
    ''';

  { Regression: whole-record assignment to a var/out record parameter.
    Previously the IsVarParam path had no tyRecord case, so `Dst := L` (or
    `Dst := Func`) fell through to a single-word store and wrote garbage back
    to the caller.  Covers both a local-record RHS (var) and a record-returning
    function RHS (out). }
  SrcRecordAssignToVarParam = '''
    program P;
    type TPoint = record X, Y: Integer; end;
    function Make(AX, AY: Integer): TPoint;
    begin
      Result.X := AX;
      Result.Y := AY
    end;
    procedure FillFromLocal(var Dst: TPoint);
    var L: TPoint;
    begin
      L.X := 11;
      L.Y := 22;
      Dst := L
    end;
    procedure FillFromCall(out Dst: TPoint);
    begin
      Dst := Make(33, 44)
    end;
    var A, B: TPoint;
    begin
      FillFromLocal(A);
      FillFromCall(B);
      WriteLn(A.X);
      WriteLn(A.Y);
      WriteLn(B.X);
      WriteLn(B.Y)
    end.
    ''';

  SrcRecordStringField = '''
    program P;
    type TName = record First, Last: string; end;
    var N: TName;
    begin
      N.First := 'Ada';
      N.Last  := 'Lovelace';
      WriteLn(N.First + ' ' + N.Last)
    end.
    ''';

  SrcRecordNested = '''
    program P;
    type
      TInner = record V: Integer; end;
      TOuter = record A, B: TInner; end;
    var O: TOuter;
    begin
      O.A.V := 10;
      O.B.V := 20;
      WriteLn(O.A.V + O.B.V)
    end.
    ''';

  SrcRecordFourBytes = '''
    program P;
    type
      TFourBytes = record
        A: Byte;
        B: Byte;
        C: Byte;
        D: Byte;
      end;
    var R: TFourBytes;
    begin
      R.A := 1;
      R.B := 2;
      R.C := 3;
      R.D := 4;
      WriteLn(SizeOf(TFourBytes));
      WriteLn(R.A);
      WriteLn(R.B);
      WriteLn(R.C);
      WriteLn(R.D)
    end.
    ''';

  SrcRecordByteThenInteger = '''
    program P;
    type
      TMixed = record
        Tag: Byte;
        Value: Integer;
      end;
    var R: TMixed;
    begin
      R.Tag := 7;
      R.Value := 12345;
      WriteLn(R.Tag);
      WriteLn(R.Value);
      WriteLn(SizeOf(TMixed))
    end.
    ''';

procedure TE2ERecordsTests.TestRun_Record_FieldReadWrite;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordFieldRW, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('3 + 7 = 10', '10' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_PassByValue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordPassByValue, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('5 then 9', '5' + LE + '9' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_PassByVar;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordPassByVar, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('6 then 8', '6' + LE + '8' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_AssignToVarParam;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordAssignToVarParam, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('11 22 33 44',
    '11' + LE + '22' + LE + '33' + LE + '44' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_StringField_ARC;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordStringField, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Ada Lovelace', 'Ada Lovelace' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_NestedRecord;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordNested, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('10 + 20 = 30', '30' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_FourByteFields_PackedAndRoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordFourBytes, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('size 4, fields 1..4',
    '4' + LE + '1' + LE + '2' + LE + '3' + LE + '4' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_ByteThenInteger_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordByteThenInteger, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('tag=7, value=12345, size=8',
    '7' + LE + '12345' + LE + '8' + LE, Output);
end;

initialization
  RegisterTest(TE2ERecordsTests);

end.
