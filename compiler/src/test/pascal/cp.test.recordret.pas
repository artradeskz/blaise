{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.recordret;

{ IR-shape coverage for QBE record-by-value return.

  Verifies that ClassifyRecordReturn picks rcInt1 for single-field
  non-managed-integer-class records, with matching callee/caller shape
  (typed `function w/l`, typed call with capture-and-store), and that
  records containing managed fields or more than one field stay on
  sret (hidden `l %_par__sret` first param, void function, plain ret). }

interface

uses
  blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe,
  blaise.codegen.target;

type
  TRecordReturnTests = class(TTestCase)
  private
    function GenIR(const ASrc: string): string;
  published
    { rcInt1: one-field POD records return typed }
    procedure TestCodegen_OneIntegerField_ReturnsW;
    procedure TestCodegen_OnePointerField_ReturnsL;
    procedure TestCodegen_OneByteField_ReturnsW;
    procedure TestCodegen_OneEnumField_ReturnsW;

    { rcInt1 caller side: capture + store back }
    procedure TestCodegen_OneIntegerField_CallerStoresW;
    procedure TestCodegen_OneByteField_CallerStoresB;

    { Managed field → sret stays (string/class/interface/dynarray) }
    procedure TestCodegen_StringField_StaysOnSret;
    procedure TestCodegen_ClassField_StaysOnSret;
    procedure TestCodegen_DynArrayField_StaysOnSret;

    { rcInt1 widened: multi-field one-eightbyte records }
    procedure TestCodegen_TwoIntegerFields_UsesRegReturnL;
    procedure TestCodegen_TwoSmallIntFields_UsesRegReturnW;
    procedure TestCodegen_TwoByteFields_UsesStoreH;
    procedure TestCodegen_IntegerPlusSmallInt_UsesRegReturnL;
    procedure TestCodegen_OddSizedRecord_StaysOnSret;

    { Nested-record fields: POD nested -> qualifies; managed nested -> sret. }
    procedure TestCodegen_NestedAllPodRecord_QualifiesRegReturn;
    procedure TestCodegen_NestedWithStringField_StaysOnSret;
    procedure TestCodegen_NestedWithClassField_StaysOnSret;
    procedure TestCodegen_DeeplyNestedPod_QualifiesRegReturn;

    { rcInt2: 9..16-byte integer-class records use rax:rdx via QBE aggregate }
    procedure TestCodegen_TwoInt64Fields_UsesAggregateReturn;
    procedure TestCodegen_TwoInt64Fields_CallerMemcpy;
    procedure TestCodegen_IntegerPlusInt64_UsesAggregate;
    procedure TestCodegen_TwoInt64WithManagedFieldElsewhere_NotApplicable;

    { rcSSE1: single Double field uses xmm0 (`function d`) }
    procedure TestCodegen_OneDoubleField_UsesSSE1;
    { rcSSE2: two-Double record uses xmm0:xmm1 via QBE aggregate }
    procedure TestCodegen_TwoDoubleFields_UsesSSE2;
    procedure TestCodegen_TwoDoubleFields_CallerMemcpy;
    { tySingle reg-return: single Single, 2-Single, Single + Double }
    procedure TestCodegen_OneSingleField_UsesSSE1S;
    procedure TestCodegen_TwoSingleFields_UsesSSE1D;
    procedure TestCodegen_SinglePlusDouble_UsesSSE2;
    { rcIntSSE / rcSSEInt — mixed Int + Double via QBE aggregate }
    procedure TestCodegen_IntegerPlusDouble_UsesIntSSE;
    procedure TestCodegen_DoublePlusInt64_UsesSSEInt;
    procedure TestCodegen_Int64PlusDouble_UsesIntSSE;
  end;

implementation

uses
  SysUtils;

function TRecordReturnTests.GenIR(const ASrc: string): string;
var
  L:    TLexer;
  P:    TParser;
  Prog: TProgram;
  A:    TSemanticAnalyser;
  CG:   TCodeGenQBE;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Prog := P.Parse();
  finally
    P.Free();
  end;
  try
    A := TSemanticAnalyser.Create();
    try
      A.Analyse(Prog);
    finally
      A.Free();
    end;
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

{ --- rcInt1 callee shape --- }

procedure TRecordReturnTests.TestCodegen_OneIntegerField_ReturnsW;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TI = record X: Integer; end;
        function MakeIt(): TI;
        begin
          Result.X := 42
        end;
        begin
        end.
        ''');
  AssertContains('function w', IR);
  AssertContains('$MakeIt', IR);
end;

procedure TRecordReturnTests.TestCodegen_OnePointerField_ReturnsL;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TP = record Q: Pointer; end;
        function MakeIt(): TP;
        begin
          Result.Q := nil
        end;
        begin
        end.
        ''');
  AssertContains('function l $MakeIt', IR);
end;

procedure TRecordReturnTests.TestCodegen_OneByteField_ReturnsW;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TB = record C: Byte; end;
        function MakeIt(): TB;
        begin
          Result.C := 7
        end;
        begin
        end.
        ''');
  AssertContains('function w $MakeIt', IR);
  AssertContains('loadub', IR);
end;

procedure TRecordReturnTests.TestCodegen_OneEnumField_ReturnsW;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TColor = (cRed, cGreen, cBlue);
          TE = record K: TColor; end;
        function MakeIt(): TE;
        begin
          Result.K := cGreen
        end;
        begin
        end.
        ''');
  AssertContains('function w $MakeIt', IR);
end;

{ --- rcInt1 caller shape --- }

procedure TRecordReturnTests.TestCodegen_OneIntegerField_CallerStoresW;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TI = record X: Integer; end;
        function MakeIt(): TI;
        begin
          Result.X := 1
        end;
        var R: TI;
        begin
          R := MakeIt()
        end.
        ''');
  { rcInt1: caller has `%t =w call $MakeIt()` and `storew %t, %_var_R`. }
  AssertContains('=w call $MakeIt', IR);
  AssertContains('storew', IR);
  { No hidden sret param in the call. }
  AssertFalse('caller passes sret', Pos('call $MakeIt(l', IR) <> -1);
end;

procedure TRecordReturnTests.TestCodegen_OneByteField_CallerStoresB;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TB = record C: Byte; end;
        function MakeIt(): TB;
        begin
          Result.C := 9
        end;
        var R: TB;
        begin
          R := MakeIt()
        end.
        ''');
  AssertContains('=w call $MakeIt', IR);
  AssertContains('storeb', IR);
end;

{ --- managed-field records stay on sret --- }

procedure TRecordReturnTests.TestCodegen_StringField_StaysOnSret;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TS = record S: string; end;
        function MakeIt(): TS;
        begin
          Result.S := 'x'
        end;
        var R: TS;
        begin
          R := MakeIt()
        end.
        ''');
  { Callee: hidden sret param, void function. }
  AssertContains('function $MakeIt(l %_par__sret', IR);
  { No `function w $MakeIt` or `function l $MakeIt` — that would be reg-return. }
  AssertFalse('would-be reg-return for managed record',
    (Pos('function w $MakeIt', IR) <> -1) or
    (Pos('function l $MakeIt', IR) <> -1));
end;

procedure TRecordReturnTests.TestCodegen_ClassField_StaysOnSret;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TThing = class end;
          TC = record T: TThing; end;
        function MakeIt(): TC;
        begin
          Result.T := nil
        end;
        var R: TC;
        begin
          R := MakeIt()
        end.
        ''');
  AssertContains('function $MakeIt(l %_par__sret', IR);
  AssertFalse('class field forced reg-return',
    Pos('=l call $MakeIt', IR) <> -1);
end;

procedure TRecordReturnTests.TestCodegen_DynArrayField_StaysOnSret;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TD = record A: array of Integer; end;
        function MakeIt(): TD;
        begin
        end;
        var R: TD;
        begin
          R := MakeIt()
        end.
        ''');
  AssertContains('function $MakeIt(l %_par__sret', IR);
end;

{ --- rcInt1 widened to multi-field one-eightbyte records --- }

procedure TRecordReturnTests.TestCodegen_TwoIntegerFields_UsesRegReturnL;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type T2 = record X, Y: Integer; end;
        function MakeIt(): T2;
        begin
          Result.X := 1;
          Result.Y := 2
        end;
        var R: T2;
        begin
          R := MakeIt()
        end.
        ''');
  { 8 bytes = one l-eightbyte → return as l. }
  AssertContains('function l $MakeIt', IR);
  AssertContains('=l call $MakeIt', IR);
  AssertContains('storel', IR);
  AssertContains('loadl %_var_Result', IR);
end;

procedure TRecordReturnTests.TestCodegen_TwoSmallIntFields_UsesRegReturnW;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type T2 = record A, B: SmallInt; end;
        function MakeIt(): T2;
        begin
          Result.A := 1;
          Result.B := 2
        end;
        var R: T2;
        begin
          R := MakeIt()
        end.
        ''');
  { 4 bytes total — fits in w. }
  AssertContains('function w $MakeIt', IR);
  AssertContains('storew', IR);
end;

procedure TRecordReturnTests.TestCodegen_TwoByteFields_UsesStoreH;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type T2 = record A, B: Byte; end;
        function MakeIt(): T2;
        begin
          Result.A := 1;
          Result.B := 2
        end;
        var R: T2;
        begin
          R := MakeIt()
        end.
        ''');
  { 2 bytes total — loaduh / storeh pair. }
  AssertContains('function w $MakeIt', IR);
  AssertContains('loaduh %_var_Result', IR);
  AssertContains('storeh', IR);
end;

procedure TRecordReturnTests.TestCodegen_IntegerPlusSmallInt_UsesRegReturnL;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TS = record A: Integer; B: SmallInt; end;
        function MakeIt(): TS;
        begin
          Result.A := 1;
          Result.B := 2
        end;
        begin
        end.
        ''');
  { Natural alignment pads to 8 bytes — one l-eightbyte. }
  AssertContains('function l $MakeIt', IR);
end;

procedure TRecordReturnTests.TestCodegen_OddSizedRecord_StaysOnSret;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type T3 = record A, B, C: Byte; end;
        function MakeIt(): T3;
        begin
          Result.A := 1
        end;
        begin
        end.
        ''');
  { TotalSize = 3 — not in [1,2,4,8], falls through to sret. }
  AssertContains('function $MakeIt(l %_par__sret', IR);
end;

{ --- nested-record qualification via IsRecordManagedClean --- }

procedure TRecordReturnTests.TestCodegen_NestedAllPodRecord_QualifiesRegReturn;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TInner = record A: Integer; end;
          TOuter = record I: TInner; end;
        function MakeIt(): TOuter;
        begin
          Result.I.A := 42
        end;
        begin
        end.
        ''');
  { Outer is 4 bytes, all leaves int -> rcInt1 w. }
  AssertContains('function w $MakeIt', IR);
  AssertFalse('outer with POD nested forced sret',
    Pos('%_par__sret', IR) <> -1);
end;

procedure TRecordReturnTests.TestCodegen_NestedWithStringField_StaysOnSret;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TInner = record S: string; end;
          TOuter = record I: TInner; end;
        function MakeIt(): TOuter;
        begin
          Result.I.S := 'x'
        end;
        begin
        end.
        ''');
  { IsRecordManagedClean recurses into TInner, finds the string,
    forces TOuter to sret. }
  AssertContains('function $MakeIt(l %_par__sret', IR);
end;

procedure TRecordReturnTests.TestCodegen_NestedWithClassField_StaysOnSret;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TThing = class end;
          TInner = record T: TThing; end;
          TOuter = record I: TInner; end;
        function MakeIt(): TOuter;
        begin
          Result.I.T := nil
        end;
        begin
        end.
        ''');
  AssertContains('function $MakeIt(l %_par__sret', IR);
end;

procedure TRecordReturnTests.TestCodegen_DeeplyNestedPod_QualifiesRegReturn;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type
          TLeaf  = record A: Integer; end;
          TMid   = record L: TLeaf; end;
          TOuter = record M: TMid; end;
        function MakeIt(): TOuter;
        begin
          Result.M.L.A := 7
        end;
        begin
        end.
        ''');
  { Three levels deep, all-POD -> recursion still finds rcInt1. }
  AssertContains('function w $MakeIt', IR);
end;

{ --- rcInt2: aggregate-return for 9..16-byte integer-class records --- }

procedure TRecordReturnTests.TestCodegen_TwoInt64Fields_UsesAggregateReturn;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type T2 = record A, B: Int64; end;
        function MakeIt(): T2;
        begin
          Result.A := 1;
          Result.B := 2
        end;
        begin
        end.
        ''');
  { Callee declared with QBE aggregate return type and no hidden sret param. }
  AssertContains('function :_ffi_T2 $MakeIt', IR);
  { Aggregate type declaration emitted in the data section. }
  AssertContains('type :_ffi_T2 = align 8', IR);
  AssertContains('ret %_var_Result', IR);
  AssertFalse('would-be sret param',
    Pos('%_par__sret', IR) <> -1);
end;

procedure TRecordReturnTests.TestCodegen_TwoInt64Fields_CallerMemcpy;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type T2 = record A, B: Int64; end;
        function MakeIt(): T2;
        begin
          Result.A := 1;
          Result.B := 2
        end;
        var R: T2;
        begin
          R := MakeIt()
        end.
        ''');
  { Caller: aggregate-typed call result, then memcpy 16 bytes to dest. }
  AssertContains('=:_ffi_T2 call $MakeIt', IR);
  AssertContains('call $memcpy(', IR);
end;

procedure TRecordReturnTests.TestCodegen_IntegerPlusInt64_UsesAggregate;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type T3 = record A: Integer; B: Int64; end;
        function MakeIt(): T3;
        begin
          Result.A := 1;
          Result.B := 2
        end;
        begin
        end.
        ''');
  { TotalSize = 16 (4 + 4 pad + 8), all integer-class → rcInt2. }
  AssertContains('function :_ffi_T3 $MakeIt', IR);
end;

procedure TRecordReturnTests.TestCodegen_TwoInt64WithManagedFieldElsewhere_NotApplicable;
var IR: string;
begin
  { Sanity: a 24-byte record (over 16) stays on sret regardless of field types. }
  IR := GenIR(
    '''
        program P;
        type T3 = record A, B, C: Int64; end;
        function MakeIt(): T3;
        begin
          Result.A := 1
        end;
        begin
        end.
        ''');
  AssertContains('function $MakeIt(l %_par__sret', IR);
end;

{ --- rcSSE1 / rcSSE2: Double-leaved records --- }

procedure TRecordReturnTests.TestCodegen_OneDoubleField_UsesSSE1;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TF = record V: Double; end;
        function MakeIt(): TF;
        begin
          Result.V := 1.5
        end;
        var R: TF;
        begin
          R := MakeIt()
        end.
        ''');
  AssertContains('function d $MakeIt', IR);
  AssertContains('loadd %_var_Result', IR);
  AssertContains('=d call $MakeIt', IR);
  AssertContains('stored', IR);
end;

procedure TRecordReturnTests.TestCodegen_TwoDoubleFields_UsesSSE2;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type T2D = record A, B: Double; end;
        function MakeIt(): T2D;
        begin
          Result.A := 1.0;
          Result.B := 2.0
        end;
        begin
        end.
        ''');
  AssertContains('function :_ffi_T2D $MakeIt', IR);
  AssertContains('type :_ffi_T2D = align 8 { d, d }', IR);
  AssertContains('ret %_var_Result', IR);
end;

procedure TRecordReturnTests.TestCodegen_TwoDoubleFields_CallerMemcpy;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type T2D = record A, B: Double; end;
        function MakeIt(): T2D;
        begin
          Result.A := 1.0;
          Result.B := 2.0
        end;
        var R: T2D;
        begin
          R := MakeIt()
        end.
        ''');
  AssertContains('=:_ffi_T2D call $MakeIt', IR);
  AssertContains('call $memcpy(', IR);
end;

procedure TRecordReturnTests.TestCodegen_OneSingleField_UsesSSE1S;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TF = record V: Single; end;
        function MakeIt(): TF;
        begin
          Result.V := 1.5
        end;
        var R: TF;
        begin
          R := MakeIt()
        end.
        ''');
  { 4-byte single-Single record returns in xmm0 as `s`. }
  AssertContains('function s $MakeIt', IR);
  AssertContains('loads %_var_Result', IR);
  AssertContains('=s call $MakeIt', IR);
  AssertContains('stores', IR);
end;

procedure TRecordReturnTests.TestCodegen_TwoSingleFields_UsesSSE1D;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type T2S = record A, B: Single; end;
        function MakeIt(): T2S;
        begin
          Result.A := 1.0;
          Result.B := 2.0
        end;
        var R: T2S;
        begin
          R := MakeIt()
        end.
        ''');
  { 8-byte all-Single record packs into one SSE eightbyte; the bytes
    round-trip through xmm0 as opaque `d`. }
  AssertContains('function d $MakeIt', IR);
  AssertContains('loadd %_var_Result', IR);
  AssertContains('stored', IR);
end;

procedure TRecordReturnTests.TestCodegen_SinglePlusDouble_UsesSSE2;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TM = record S: Single; D: Double; end;
        function MakeIt(): TM;
        begin
          Result.S := 1.0;
          Result.D := 2.0
        end;
        begin
        end.
        ''');
  { 16 bytes, all-float — rcSSE2 with aggregate [ s, d ]. }
  AssertContains('function :_ffi_TM $MakeIt', IR);
  AssertContains('type :_ffi_TM = align 8 { s, d }', IR);
end;

procedure TRecordReturnTests.TestCodegen_IntegerPlusDouble_UsesIntSSE;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TM = record I: Integer; D: Double; end;
        function MakeIt(): TM;
        begin
          Result.I := 1;
          Result.D := 2.0
        end;
        var R: TM;
        begin
          R := MakeIt()
        end.
        ''');
  { Eightbyte 0 = Integer + 4B pad -> INTEGER class.
    Eightbyte 1 = Double -> SSE class.
    QBE returns in (rax, xmm0). }
  AssertContains('function :_ffi_TM $MakeIt', IR);
  AssertContains('type :_ffi_TM = align 8 { w, d }', IR);
  AssertContains('=:_ffi_TM call $MakeIt', IR);
  AssertContains('call $memcpy(', IR);
end;

procedure TRecordReturnTests.TestCodegen_DoublePlusInt64_UsesSSEInt;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TM = record D: Double; I: Int64; end;
        function MakeIt(): TM;
        begin
          Result.D := 1.0;
          Result.I := 2
        end;
        begin
        end.
        ''');
  { Eightbyte 0 = Double -> SSE; eightbyte 1 = Int64 -> INTEGER.
    QBE returns in (xmm0, rax). }
  AssertContains('function :_ffi_TM $MakeIt', IR);
  AssertContains('type :_ffi_TM = align 8 { d, l }', IR);
end;

procedure TRecordReturnTests.TestCodegen_Int64PlusDouble_UsesIntSSE;
var IR: string;
begin
  IR := GenIR(
    '''
        program P;
        type TM = record I: Int64; D: Double; end;
        function MakeIt(): TM;
        begin
          Result.I := 1;
          Result.D := 2.0
        end;
        begin
        end.
        ''');
  AssertContains('function :_ffi_TM $MakeIt', IR);
  AssertContains('type :_ffi_TM = align 8 { l, d }', IR);
end;

initialization
  RegisterTest(TRecordReturnTests);

end.
