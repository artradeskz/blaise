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
    procedure TestRun_Record_ByValParam_StringField_HeapARC;
    procedure TestRun_Record_ByValArg_InlineCallResult_NestedManaged_NoLeak;
    procedure TestRun_DynArrayRecordElem_FieldAssignAndRead;
    procedure TestRun_DynArrayRecordElem_CopyNoAlias;
    procedure TestRun_StaticArrayRecordElem_FieldAssignAndRead;
    procedure TestRun_DynArrayClassElem_MethodCallStmt;
    procedure TestRun_RecordField_DynArrayElemWrite;
    procedure TestRun_ClassField_DynArrayElemWrite_AllReceiverShapes;
    procedure TestRun_NestedChain_DynArrayElemWrite;
    procedure TestRun_SubscriptChain_FieldElemWrite;
    procedure TestRun_RecordField_StaticArrayElemWrite;
    procedure TestRun_RecordField_DynArrayOfString_ElemWrite_ARC;
    procedure TestRun_RecordCallResult_IntoArrayElement;
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
    program Prg;
    type TPoint = record X, Y: Integer; end;
    var P1: TPoint;
    begin
      P1.X := 3;
      P1.Y := 7;
      WriteLn(P1.X + P1.Y)
    end.
    ''';

  SrcRecordPassByValue = '''
    program Prg;
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
    program Prg;
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
    program Prg;
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
    program Prg;
    type TName = record First, Last: string; end;
    var N: TName;
    begin
      N.First := 'Ada';
      N.Last  := 'Lovelace';
      WriteLn(N.First + ' ' + N.Last)
    end.
    ''';

  SrcRecordNested = '''
    program Prg;
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
    program Prg;
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
    program Prg;
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
    program Prg;
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
    program Prg;
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
    program Prg;
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
    program Prg;
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
    program Prg;
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
    program Prg;
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

  { Regression: a record with a managed (string) field passed by value
    to a callee that REASSIGNS the field used to free the caller's
    heap-allocated string and then return.  The caller's subsequent
    read of the field was a use-after-free that often crashed on exit.
    A literal-only test wouldn't trip the bug because string literals
    have a sentinel refcount of -1 (Release is a no-op); we force a
    real heap refcount via 'heap-' + 'allocated'. }
  SrcRecordByValParam_StringField_HeapARC = '''
    program Prg;
    type TR = record S: string; end;
    procedure Mutate(R: TR);
    begin R.S := 'callee-replacement' end;
    var W: TR;
    begin
      W.S := 'heap-' + 'allocated';
      WriteLn('before: ', W.S);
      Mutate(W);
      WriteLn('after:  ', W.S)
    end.
    ''';

  { Caller-side cleanup of an inline call result used as a by-value
    record arg: Consume(MakeOuter()) where TOuter has a string field
    AND a nested TInner whose own field is a string.  Before the fix
    the temporary's two heap strings leaked once per Driver call; over
    many iterations the process either OOMs or the allocator's free
    list ages noticeably.  Successful run prints both fields once and
    exits 0; we drive the pattern in a tight loop so a leak would
    show up under stress. }
  SrcRecordByValArg_InlineNestedManaged = '''
    program Prg;
    type
      TInner = record N: string; end;
      TOuter = record S: string; Inner: TInner; end;
    function MakeOuter: TOuter;
    begin
      Result.S := 'outer-' + 'heap';
      Result.Inner.N := 'inner-' + 'heap'
    end;
    procedure Consume(R: TOuter);
    begin
      WriteLn(R.S, '|', R.Inner.N)
    end;
    procedure Driver;
    begin
      Consume(MakeOuter())
    end;
    var i: Integer;
    begin
      for i := 1 to 1000 do Driver()
    end.
    ''';

  SrcRecordDynArrayReturnByValueNoLeak = '''
    program Prg;
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
    program Prg;
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
    program Prg;
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
  AssertRunsOnAll(SrcRecordStmtMethodCallLocal, '3' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_Record_StmtMethodCall_ImplicitSelf;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordStmtMethodCallImplicitSelf, '3' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_Record_StmtMethodCall_Result;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordStmtMethodCallResult, '5' + LE + '8' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_Record_AddrOfImplicitSelf;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordAddrOfImplicitSelf, '10' + LE + '20' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_Record_PointerDerefFieldAccess;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordPointerDerefFieldAccess, '42' + LE + '99' + LE, 0);
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

procedure TE2ERecordsTests.TestRun_Record_ByValParam_StringField_HeapARC;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcRecordByValParam_StringField_HeapARC, Output, RCode));
  AssertEquals('exit code 0 (no use-after-free crash)', 0, RCode);
  AssertEquals('caller string survives callee whole-string reassignment',
    'before: heap-allocated' + LE + 'after:  heap-allocated' + LE, Output);
end;

procedure TE2ERecordsTests.TestRun_Record_ByValArg_InlineCallResult_NestedManaged_NoLeak;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcRecordByValArg_InlineNestedManaged, Output, RCode));
  AssertEquals('exit code 0 over 1000 inline-temp iterations', 0, RCode);
  AssertTrue('Driver printed nested strings',
    Pos('outer-heap|inner-heap' + LE, Output) >= 0);
end;

const
  SrcDynRecElemFieldAssign = '''
    program Prg;
    type
      TInner = record N: Integer; end;
      TRec = record
        Name: String;
        Number: Integer;
        Inner: TInner;
      end;
    var
      r1, r2: TRec;
      a: array of TRec;
    begin
      SetLength(a, 2);
      r1.Name := 'First';  r1.Number := 1;
      r2.Name := 'Second'; r2.Number := 2;
      a[0] := r1;
      a[1] := r2;
      writeln(a[0].Name);
      a[0].Name := 'Patched';
      a[0].Number := 10;
      a[0].Inner.N := 7;
      writeln(a[0].Name);
      writeln(a[1].Name);
      writeln(a[0].Number);
      writeln(a[1].Number);
      writeln(a[0].Inner.N);
      writeln(r1.Name);
    end.
    ''';

  SrcDynRecElemCopyNoAlias = '''
    program Prg;
    type TRec = record Name: String; Number: Integer; end;
    var
      r: TRec;
      a: array of TRec;
    begin
      SetLength(a, 1);
      r.Name := 'one';
      r.Number := 1;
      a[0] := r;
      r.Name := 'two';
      r.Number := 2;
      writeln(a[0].Name);
      writeln(a[0].Number);
      r := a[0];
      a[0].Name := 'three';
      writeln(r.Name);
      writeln(r.Number);
      writeln(a[0].Name);
    end.
    ''';

  SrcStaticRecElemFieldAssign = '''
    program Prg;
    type TRec = record Name: String; Number: Integer; end;
    var
      r1, r2: TRec;
      sa: array[0..1] of TRec;
    begin
      r1.Name := 'First';  r1.Number := 1;
      r2.Name := 'Second'; r2.Number := 2;
      sa[0] := r1;
      sa[1] := r2;
      sa[0].Name := 'Patched';
      sa[0].Number := 10;
      writeln(sa[0].Name);
      writeln(sa[1].Name);
      writeln(sa[0].Number);
      writeln(sa[1].Number);
      writeln(r1.Name);
    end.
    ''';

  SrcDynClassElemMethodCall = '''
    program Prg;
    type
      TC = class
        V: Integer;
        procedure Bump;
      end;
    procedure TC.Bump;
    begin
      V := V + 1;
    end;
    var
      a: array of TC;
    begin
      SetLength(a, 1);
      a[0] := TC.Create();
      a[0].Bump;
      a[0].Bump();
      writeln(a[0].V);
    end.
    ''';

procedure TE2ERecordsTests.TestRun_DynArrayRecordElem_FieldAssignAndRead;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDynRecElemFieldAssign,
    'First' + LE + 'Patched' + LE + 'Second' + LE + '10' + LE + '2' + LE +
    '7' + LE + 'First' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_DynArrayRecordElem_CopyNoAlias;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDynRecElemCopyNoAlias,
    'one' + LE + '1' + LE + 'one' + LE + '1' + LE + 'three' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_StaticArrayRecordElem_FieldAssignAndRead;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStaticRecElemFieldAssign,
    'Patched' + LE + 'Second' + LE + '10' + LE + '2' + LE + 'First' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_DynArrayClassElem_MethodCallStmt;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDynClassElemMethodCall, '2' + LE, 0);
end;

const
  SrcRecFieldDynElemWrite = '''
    program Prg;
    type
      TIA = array of Integer;
      TR  = record A: TIA; end;
    var r: TR;
    begin
      SetLength(r.A, 3);
      r.A[0] := 10;
      r.A[1] := 20;
      r.A[2] := r.A[0] + r.A[1];
      writeln(r.A[0]);
      writeln(r.A[1]);
      writeln(r.A[2]);
    end.
    ''';

  SrcClassFieldDynElemWrite = '''
    program Prg;
    type
      TIA = array of Integer;
      TC = class
        A: TIA;
        procedure Fill;
      end;
    procedure TC.Fill;
    begin
      SetLength(A, 3);
      A[0] := 42;
      Self.A[1] := 43;
      A[2] := A[0] + Self.A[1];
    end;
    var c: TC;
    begin
      c := TC.Create();
      c.Fill;
      writeln(c.A[0]);
      writeln(c.A[1]);
      writeln(c.A[2]);
      c.A[0] := 7;
      writeln(c.A[0]);
    end.
    ''';

  SrcNestedChainDynElemWrite = '''
    program Prg;
    type
      TIA    = array of Integer;
      TInner = record A: TIA; end;
      TC     = class N: TInner; end;
    var c: TC;
    begin
      c := TC.Create();
      SetLength(c.N.A, 3);
      c.N.A[0] := 7;
      c.N.A[1] := 8;
      writeln(c.N.A[0]);
      writeln(c.N.A[1]);
    end.
    ''';

  SrcSubscriptChainFieldElemWrite = '''
    program Prg;
    type
      TIA = array of Integer;
      TR  = record A: TIA; end;
    var
      rs: array of TR;
    begin
      SetLength(rs, 2);
      SetLength(rs[1].A, 3);
      rs[1].A[2] := 99;
      writeln(rs[1].A[2]);
    end.
    ''';

  SrcRecFieldStaticElemWrite = '''
    program Prg;
    type
      TR = record S: array[0..2] of Integer; end;
    var r: TR;
    begin
      r.S[0] := 5;
      r.S[1] := 6;
      r.S[2] := r.S[0] + r.S[1];
      writeln(r.S[0]);
      writeln(r.S[1]);
      writeln(r.S[2]);
    end.
    ''';

  SrcRecFieldDynStrElemWrite = '''
    program Prg;
    type
      TSA = array of String;
      TR  = record N: TSA; end;
    var
      r: TR;
      s: String;
    begin
      SetLength(r.N, 2);
      s := 'wor';
      r.N[0] := 'hello';
      r.N[1] := s + 'ld';
      r.N[0] := 'bye';
      writeln(r.N[0]);
      writeln(r.N[1]);
    end.
    ''';

procedure TE2ERecordsTests.TestRun_RecordField_DynArrayElemWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecFieldDynElemWrite,
    '10' + LE + '20' + LE + '30' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_ClassField_DynArrayElemWrite_AllReceiverShapes;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcClassFieldDynElemWrite,
    '42' + LE + '43' + LE + '85' + LE + '7' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_NestedChain_DynArrayElemWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcNestedChainDynElemWrite, '7' + LE + '8' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_SubscriptChain_FieldElemWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSubscriptChainFieldElemWrite, '99' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_RecordField_StaticArrayElemWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecFieldStaticElemWrite,
    '5' + LE + '6' + LE + '11' + LE, 0);
end;

procedure TE2ERecordsTests.TestRun_RecordField_DynArrayOfString_ElemWrite_ARC;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecFieldDynStrElemWrite,
    'bye' + LE + 'world' + LE, 0);
end;

const
  SrcRecordCallIntoElem = '''
    program Prg;
    type
      TTok = record
        Kind: Integer;
        Text: String;
      end;
      TLex = class
        FN: Integer;
        function Next(): TTok;
      end;
    function TLex.Next(): TTok;
    begin
      FN := FN + 1;
      Result.Kind := FN;
      Result.Text := 'tok' + IntToStr(FN);
    end;
    var
      L: TLex;
      A: array[0..2] of TTok;
      D: array of TTok;
      I: Integer;
    begin
      L := TLex.Create();
      for I := 0 to 2 do
        A[I] := L.Next();
      writeln(A[0].Kind, ' ', A[0].Text);
      writeln(A[2].Kind, ' ', A[2].Text);
      SetLength(D, 2);
      D[1] := L.Next();
      writeln(D[1].Kind, ' ', D[1].Text);
    end.
    ''';

procedure TE2ERecordsTests.TestRun_RecordCallResult_IntoArrayElement;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordCallIntoElem,
    '1 tok1' + LE + '3 tok3' + LE + '4 tok4' + LE, 0);
end;

initialization
  RegisterTest(TE2ERecordsTests);

end.
