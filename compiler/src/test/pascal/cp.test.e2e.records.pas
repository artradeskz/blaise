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
    procedure TestRun_Record_NestedFieldAssign_MethodCall;
    procedure TestRun_Record_StmtMethodCall_Local;
    procedure TestRun_Record_StmtMethodCall_ImplicitSelf;
    procedure TestRun_Record_StmtMethodCall_Result;
    procedure TestRun_Record_AddrOfImplicitSelf;
    procedure TestRun_Record_PointerDerefFieldAccess;
    procedure TestRun_Record_DynArrayField_ReturnByValue_NoLeak;
    procedure TestRun_Class_RecordField_NestedClass_FullCleanup;
    procedure TestRun_Record_InterfaceField_AssignCallAndCopy;
  end;

implementation

procedure TE2ERecordsTests.SetUp;
begin
  inherited SetUp();
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

  SrcRecordStmtMethodCallLocal = '''
    program P;
    type
      TCounter = record
        Value: Integer;
        procedure Inc;
        function GetValue: Integer;
      end;
    procedure TCounter.Inc;
    begin
      Value := Value + 1
    end;
    function TCounter.GetValue: Integer;
    begin
      Result := Value
    end;
    var
      C: TCounter;
    begin
      C.Value := 0;
      C.Inc();
      C.Inc();
      C.Inc();
      WriteLn(C.GetValue())
    end.
    ''';

  SrcRecordStmtMethodCallImplicitSelf = '''
    program P;
    type
      TCounter = record
        Value: Integer;
        procedure Inc;
      end;
      TApp = class
        FC: TCounter;
        procedure Run;
      end;
    procedure TCounter.Inc;
    begin
      Value := Value + 1
    end;
    procedure TApp.Run;
    begin
      FC.Inc();
      FC.Inc();
      FC.Inc();
      WriteLn(FC.Value)
    end;
    var
      A: TApp;
    begin
      A := TApp.Create();
      A.Run()
    end.
    ''';

  SrcRecordStmtMethodCallResult = '''
    program P;
    type
      TPoint = record
        X, Y: Integer;
        procedure SetXY(AX, AY: Integer);
      end;
    procedure TPoint.SetXY(AX, AY: Integer);
    begin
      X := AX;
      Y := AY
    end;
    function MakePoint(AX, AY: Integer): TPoint;
    begin
      Result.SetXY(AX, AY)
    end;
    var
      P: TPoint;
    begin
      P := MakePoint(5, 8);
      WriteLn(P.X);
      WriteLn(P.Y)
    end.
    ''';

  SrcRecordAddrOfImplicitSelf = '''
    program P;
    type
      TPoint = record
        X, Y: Integer;
      end;
      TApp = class
        Pt: TPoint;
        procedure Run;
      end;
    procedure TApp.Run;
    var PP: ^TPoint;
    begin
      Pt.X := 10;
      Pt.Y := 20;
      PP := @Pt;
      WriteLn(PP^.X);
      WriteLn(PP^.Y)
    end;
    var
      A: TApp;
    begin
      A := TApp.Create();
      A.Run()
    end.
    ''';

  SrcRecordPointerDerefFieldAccess = '''
    program P;
    type
      TPoint = record X, Y: Integer; end;
    var
      Pt: TPoint;
      PP: ^TPoint;
    begin
      Pt.X := 42;
      Pt.Y := 99;
      PP := @Pt;
      WriteLn(PP^.X);
      WriteLn(PP^.Y)
    end.
    ''';

  { Regression: a record whose field is a dynamic array, returned by value
    in a loop.  Before the dyn-array ARC fix, every iteration leaked the
    array buffer because EmitRecordCopy/EmitRecordReleaseFields did not
    refcount tyDynArray fields.  After the fix, the per-iter delta is one
    AddRef + one Release on the buffer header — net zero — and the final
    assertion of the buffer contents proves the data was not freed under
    the function's feet. }
  { Regression: a class whose field is a record whose field is another class
    whose field is another record whose field is a leaf class.  Each Create
    increments a global AliveCount; each Destroy decrements it.  After the
    outermost instance is released, AliveCount must be 0 — proving that
    _FieldCleanup for a class with a record field recurses through that
    record's class sub-fields all the way down.

    Before the fix, _FieldCleanup_<T> skipped record-typed fields entirely,
    so the chain leaked TMid and TLeaf instances every iteration. }
  SrcClassRecordFieldNestedCleanup = '''
    program P;
    type
      TLeaf = class
        Tag: Integer;
        constructor Create();
        destructor Destroy(); override;
      end;
      TMidRec = record
        Leaf:  TLeaf;
        Extra: Integer;
      end;
      TMid = class
        Inner: TMidRec;
        constructor Create();
        destructor Destroy(); override;
      end;
      TOuterRec = record
        Mid:  TMid;
        Note: Integer;
      end;
      TOuter = class
        Wrap: TOuterRec;
        constructor Create();
        destructor Destroy(); override;
      end;
    var
      AliveCount: Integer;
    constructor TLeaf.Create();
    begin
      AliveCount := AliveCount + 1;
      Self.Tag := 1
    end;
    destructor TLeaf.Destroy();
    begin
      AliveCount := AliveCount - 1
    end;
    constructor TMid.Create();
    begin
      AliveCount := AliveCount + 1;
      Self.Inner.Leaf  := TLeaf.Create();
      Self.Inner.Extra := 7
    end;
    destructor TMid.Destroy();
    begin
      AliveCount := AliveCount - 1
    end;
    constructor TOuter.Create();
    begin
      AliveCount := AliveCount + 1;
      Self.Wrap.Mid  := TMid.Create();
      Self.Wrap.Note := 99
    end;
    destructor TOuter.Destroy();
    begin
      AliveCount := AliveCount - 1
    end;
    procedure RunOnce();
    var
      O: TOuter;
    begin
      O := TOuter.Create();
      if O.Wrap.Mid.Inner.Leaf.Tag <> 1 then
        WriteLn('chain broken')
    end;
    var
      i: Integer;
    begin
      AliveCount := 0;
      for i := 0 to 99 do
        RunOnce();
      WriteLn(AliveCount)
    end.
    ''';

  SrcRecordDynArrayReturnByValueNoLeak = '''
    program P;
    type
      TBuf = record
        Arr: array of Integer;
      end;
    function MakeBuf: TBuf;
    var
      tmp: TBuf;
      a:   array of Integer;
    begin
      SetLength(a, 8);
      a[0] := 1;
      a[7] := 70;
      tmp.Arr := a;
      Result := tmp
    end;
    var
      i:   Integer;
      r:   TBuf;
    begin
      for i := 0 to 4999 do
        r := MakeBuf();
      WriteLn(r.Arr[0]);
      WriteLn(r.Arr[7])
    end.
    ''';

  { Interface-typed field inside a record: exercises (1) assigning a class into
    an interface record field (r.Foo := f → obj+itab fat-pointer store with
    ARC), (2) calling a method through an interface record field
    (r.Foo.GetVal() → dispatch via the field's contiguous fat pointer), (3)
    record copy carrying the interface field (b := a) and (4) the 16-byte field
    size so Tag sits at offset 16, not 8.  Before the fix the field was sized 8
    bytes and the method dispatch emitted an undefined %_var__obj temp that QBE
    rejected. }
  SrcRecordInterfaceFieldAssignCallCopy = '''
    program P;
    type
      IFoo = interface
        function GetVal: Integer;
      end;
      TFoo = class(TObject, IFoo)
        V: Integer;
        function GetVal: Integer;
      end;
      TRec = record
        Foo: IFoo;
        Tag: Integer;
      end;
    function TFoo.GetVal: Integer;
    begin
      Result := Self.V
    end;
    function MakeRec(n: Integer): TRec;
    var
      r: TRec;
      f: TFoo;
    begin
      f := TFoo.Create();
      f.V := n;
      r.Foo := f;
      r.Tag := n * 10;
      Result := r
    end;
    var
      a: TRec;
      b: TRec;
    begin
      a := MakeRec(5);
      b := a;
      WriteLn(b.Foo.GetVal());
      WriteLn(a.Tag)
    end.
    ''';

  SrcRecordNestedFieldAssignMethodCall = '''
    program P;
    type
      TDate = record
        Year: Integer;
        Month: Integer;
        Day: Integer;
        function ToString: string;
      end;
      TDateTime = record
        Date: TDate;
        Hour: Integer;
      end;
    function TDate.ToString: string;
    begin
      Result := IntToStr(Self.Year) + '-' + IntToStr(Self.Month) + '-' + IntToStr(Self.Day)
    end;
    var
      DT: TDateTime;
      D: TDate;
    begin
      DT.Date.Year := 2026;
      DT.Date.Month := 6;
      DT.Date.Day := 5;
      DT.Hour := 14;
      D := DT.Date;
      WriteLn(D.ToString());
      WriteLn(DT.Date.ToString())
    end.
    ''';

procedure TE2ERecordsTests.TestRun_Record_FieldReadWrite;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordFieldRW, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('3 + 7 = 10', '10' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_PassByValue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordPassByValue, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('5 then 9', '5' + LE + '9' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_PassByVar;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordPassByVar, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('6 then 8', '6' + LE + '8' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_AssignToVarParam;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordAssignToVarParam, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('11 22 33 44',
    '11' + LE + '22' + LE + '33' + LE + '44' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_StringField_ARC;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordStringField, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Ada Lovelace', 'Ada Lovelace' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_NestedRecord;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordNested, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('10 + 20 = 30', '30' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_FourByteFields_PackedAndRoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordFourBytes, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('size 4, fields 1..4',
    '4' + LE + '1' + LE + '2' + LE + '3' + LE + '4' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_ByteThenInteger_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordByteThenInteger, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('tag=7, value=12345, size=8',
    '7' + LE + '12345' + LE + '8' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_NestedFieldAssign_MethodCall;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRecordNestedFieldAssignMethodCall, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('nested field assign + method call',
    '2026-6-5' + LE + '2026-6-5' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_StmtMethodCall_Local;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcRecordStmtMethodCallLocal, '3' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_Record_StmtMethodCall_ImplicitSelf;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcRecordStmtMethodCallImplicitSelf, '3' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_Record_StmtMethodCall_Result;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcRecordStmtMethodCallResult, '5' + LE + '8' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_Record_AddrOfImplicitSelf;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcRecordAddrOfImplicitSelf, '10' + LE + '20' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_Record_PointerDerefFieldAccess;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnBoth(SrcRecordPointerDerefFieldAccess, '42' + LE + '99' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_Class_RecordField_NestedClass_FullCleanup;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcClassRecordFieldNestedCleanup, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('all 3 layers fully released across 100 iterations',
    '0' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_DynArrayField_ReturnByValue_NoLeak;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcRecordDynArrayReturnByValueNoLeak, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('first and last element survive 5000 iterations',
    '1' + LE + '70' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_InterfaceField_AssignCallAndCopy;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcRecordInterfaceFieldAssignCallCopy, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('method dispatch through interface field + 16-byte field layout',
    '5' + LE + '50' + LE, Output);
end;

initialization
  RegisterTest(TE2ERecordsTests);

end.
