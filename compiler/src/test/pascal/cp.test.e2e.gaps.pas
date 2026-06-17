{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.gaps;

{ E2E tests to close coverage gaps found during the IR-emit audit:
  packed records, sar (arithmetic shift right), UInt64 operations,
  and [Unretained] attribute.  All run on both backends. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EGapTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { Boolean xor (GitHub #123) }
    procedure TestRun_BoolXor_TrueXorTrue_IsFalse;
    procedure TestRun_BoolXor_AllCombinations;

    { Packed records }
    procedure TestRun_PackedRecord_ByteIntOffsets;
    procedure TestRun_PackedRecord_SizeOfPacked;

    { Arithmetic shift right (sar) }
    procedure TestRun_Sar_NegativeInt64_PreservesSign;
    procedure TestRun_Shr_NegativeInt64_ZeroExtends;
    procedure TestRun_Sar_PositiveInteger;

    { UInt64 operations }
    procedure TestRun_UInt64_RoundTrip;
    procedure TestRun_UInt64_LargeLiteral;
    procedure TestRun_UInt64_UnsignedCompare;
    procedure TestRun_UInt64_Arithmetic;

    { [Unretained] attribute }
    procedure TestRun_Unretained_BackRef_NoLeak;
    procedure TestRun_Unretained_AssignAndReadBack;

    { Generic records }
    procedure TestRun_GenericRecord_FieldAccess;
    procedure TestRun_GenericRecord_MethodCall;

    { TDictionary default property d[key] }
    procedure TestRun_TDictionary_DefaultProp_IntKeys;
    procedure TestRun_TDictionary_DefaultProp_StringKeys;
    procedure TestRun_TDictionary_DefaultProp_Update;

    { Published RTTI + MethodAddress }
    procedure TestRun_PublishedRTTI_MethodAddress;

    { Multi-arg WriteLn }
    procedure TestRun_WriteLn_MultipleArgs_MixedTypes;
  end;

implementation

procedure TE2EGapTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-gaps');
end;

{ ---- Boolean xor ---- }

procedure TE2EGapTests.TestRun_BoolXor_TrueXorTrue_IsFalse;
const Src = '''
    program T;
    var A, B: Boolean;
    begin
      A := True;
      B := True;
      WriteLn(A xor B)
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'False' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_BoolXor_AllCombinations;
const Src = '''
    program T;
    var A, B: Boolean;
    begin
      A := False; B := False; WriteLn(A xor B);
      A := False; B := True;  WriteLn(A xor B);
      A := True;  B := False; WriteLn(A xor B);
      A := True;  B := True;  WriteLn(A xor B)
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'False' + Chr(10) + 'True' + Chr(10) +
                       'True' + Chr(10) + 'False' + Chr(10), 0);
end;

{ ---- Packed records ---- }

procedure TE2EGapTests.TestRun_PackedRecord_ByteIntOffsets;
const Src = '''
    program T;
    type
      TPacked = packed record
        A: Byte;
        B: Integer;
      end;
    var R: TPacked;
    begin
      R.A := 1;
      R.B := 1000;
      WriteLn(R.A);
      WriteLn(R.B)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '1' + Chr(10) + '1000' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_PackedRecord_SizeOfPacked;
const Src = '''
    program T;
    type
      TPacked = packed record
        A: Byte;
        B: Integer;
      end;
      TNormal = record
        A: Byte;
        B: Integer;
      end;
    begin
      WriteLn(SizeOf(TPacked));
      WriteLn(SizeOf(TNormal))
    end.
    ''';
begin
  AssertRunsOnAll(Src, '5' + Chr(10) + '8' + Chr(10), 0);
end;

{ ---- Arithmetic shift right ---- }

procedure TE2EGapTests.TestRun_Sar_NegativeInt64_PreservesSign;
const Src = '''
    program T;
    var V: Int64;
    begin
      V := -16;
      WriteLn(V sar 2)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '-4' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_Shr_NegativeInt64_ZeroExtends;
const Src = '''
    program T;
    var V: Int64;
    begin
      V := -1;
      { shr on Int64 zero-extends: -1 shr 63 = 1 (not -1) }
      WriteLn(V shr 63)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '1' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_Sar_PositiveInteger;
const Src = '''
    program T;
    var V: Integer;
    begin
      V := 100;
      WriteLn(V sar 2)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '25' + Chr(10), 0);
end;

{ ---- UInt64 operations ---- }

procedure TE2EGapTests.TestRun_UInt64_RoundTrip;
const Src = '''
    program T;
    var U: UInt64;
    begin
      U := 42;
      WriteLn(U)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '42' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_UInt64_LargeLiteral;
const Src = '''
    program T;
    var U: UInt64;
    begin
      U := 18446744073709551615;
      if U > 0 then
        WriteLn('positive')
      else
        WriteLn('BUG')
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'positive' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_UInt64_UnsignedCompare;
const Src = '''
    program T;
    var A, B: UInt64;
    begin
      A := 18446744073709551615;
      B := 1;
      if A > B then
        WriteLn('ok')
      else
        WriteLn('BUG')
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'ok' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_UInt64_Arithmetic;
const Src = '''
    program T;
    var U: UInt64;
    begin
      U := 10;
      WriteLn(U * 3);
      WriteLn(U div 3);
      WriteLn(U mod 3)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '30' + Chr(10) + '3' + Chr(10) + '1' + Chr(10), 0);
end;

{ ---- [Unretained] attribute ---- }

procedure TE2EGapTests.TestRun_Unretained_BackRef_NoLeak;
const Src = '''
    program T;
    type
      TOwner = class(TObject)
        Name: string;
      end;
      TChild = class(TObject)
        [Unretained] Owner: TOwner;
      end;
    var
      O: TOwner;
      C: TChild;
    begin
      O := TOwner.Create();
      O.Name := 'parent';
      C := TChild.Create();
      C.Owner := O;
      WriteLn(C.Owner.Name);
      C.Free();
      O.Free();
      WriteLn('done')
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'parent' + Chr(10) + 'done' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_Unretained_AssignAndReadBack;
const Src = '''
    program T;
    type
      TNode = class(TObject)
        Value: Integer;
        [Unretained] Next: TNode;
      end;
    var
      A, B: TNode;
    begin
      A := TNode.Create();
      A.Value := 1;
      B := TNode.Create();
      B.Value := 2;
      A.Next := B;
      WriteLn(A.Next.Value);
      B.Free();
      A.Free();
      WriteLn('ok')
    end.
    ''';
begin
  AssertRunsOnAll(Src, '2' + Chr(10) + 'ok' + Chr(10), 0);
end;

{ ---- TDictionary default property ---- }

procedure TE2EGapTests.TestRun_TDictionary_DefaultProp_IntKeys;
const Src = '''
    program T;
    type
      TMap<K, V> = class
        FKeys:     ^K;
        FValues:   ^V;
        FCount:    Integer;
        FCapacity: Integer;
        procedure Grow;
        function  FindKey(Key: K): Integer;
        procedure Add(Key: K; Value: V);
        function  GetItem(Key: K): V;
        procedure SetItem(Key: K; Value: V);
        property Items[Key: K]: V read GetItem write SetItem; default;
      end;
    procedure TMap<K, V>.Grow;
    var NewCap: Integer;
    begin
      if Self.FCapacity = 0 then NewCap := 8
      else NewCap := Self.FCapacity * 2;
      Self.FKeys   := ReallocMem(Self.FKeys,   NewCap * SizeOf(K));
      Self.FValues := ReallocMem(Self.FValues, NewCap * SizeOf(V));
      Self.FCapacity := NewCap
    end;
    function TMap<K, V>.FindKey(Key: K): Integer;
    var I: Integer; Ptr: ^K;
    begin
      Result := -1;
      I := 0;
      while I < Self.FCount do
      begin
        Ptr := Self.FKeys + I * SizeOf(K);
        if Ptr^ = Key then begin Result := I; I := Self.FCount end
        else I := I + 1
      end
    end;
    procedure TMap<K, V>.Add(Key: K; Value: V);
    var Idx: Integer; KPtr: ^K; VPtr: ^V;
    begin
      Idx := Self.FindKey(Key);
      if Idx >= 0 then
      begin VPtr := Self.FValues + Idx * SizeOf(V); VPtr^ := Value end
      else begin
        if Self.FCount = Self.FCapacity then Self.Grow();
        KPtr := Self.FKeys + Self.FCount * SizeOf(K);
        VPtr := Self.FValues + Self.FCount * SizeOf(V);
        KPtr^ := Key; VPtr^ := Value;
        Self.FCount := Self.FCount + 1
      end
    end;
    function TMap<K, V>.GetItem(Key: K): V;
    var Idx: Integer; VPtr: ^V;
    begin
      Idx := Self.FindKey(Key);
      if Idx >= 0 then
      begin VPtr := Self.FValues + Idx * SizeOf(V); Result := VPtr^ end
      else Halt(1)
    end;
    procedure TMap<K, V>.SetItem(Key: K; Value: V);
    begin Self.Add(Key, Value) end;
    var D: TMap<Integer, Integer>;
    begin
      D := TMap<Integer, Integer>.Create();
      D[1] := 100;
      D[2] := 200;
      WriteLn(D[1]);
      WriteLn(D[2]);
      D.Free()
    end.
    ''';
begin
  AssertRunsOnAll(Src, '100' + Chr(10) + '200' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_TDictionary_DefaultProp_StringKeys;
const Src = '''
    program T;
    type
      TMap<K, V> = class
        FKeys:     ^K;
        FValues:   ^V;
        FCount:    Integer;
        FCapacity: Integer;
        procedure Grow;
        function  FindKey(Key: K): Integer;
        procedure Add(Key: K; Value: V);
        function  GetItem(Key: K): V;
        procedure SetItem(Key: K; Value: V);
        property Items[Key: K]: V read GetItem write SetItem; default;
      end;
    procedure TMap<K, V>.Grow;
    var NewCap: Integer;
    begin
      if Self.FCapacity = 0 then NewCap := 8
      else NewCap := Self.FCapacity * 2;
      Self.FKeys   := ReallocMem(Self.FKeys,   NewCap * SizeOf(K));
      Self.FValues := ReallocMem(Self.FValues, NewCap * SizeOf(V));
      Self.FCapacity := NewCap
    end;
    function TMap<K, V>.FindKey(Key: K): Integer;
    var I: Integer; Ptr: ^K;
    begin
      Result := -1;
      I := 0;
      while I < Self.FCount do
      begin
        Ptr := Self.FKeys + I * SizeOf(K);
        if Ptr^ = Key then begin Result := I; I := Self.FCount end
        else I := I + 1
      end
    end;
    procedure TMap<K, V>.Add(Key: K; Value: V);
    var Idx: Integer; KPtr: ^K; VPtr: ^V;
    begin
      Idx := Self.FindKey(Key);
      if Idx >= 0 then
      begin VPtr := Self.FValues + Idx * SizeOf(V); VPtr^ := Value end
      else begin
        if Self.FCount = Self.FCapacity then Self.Grow();
        KPtr := Self.FKeys + Self.FCount * SizeOf(K);
        VPtr := Self.FValues + Self.FCount * SizeOf(V);
        KPtr^ := Key; VPtr^ := Value;
        Self.FCount := Self.FCount + 1
      end
    end;
    function TMap<K, V>.GetItem(Key: K): V;
    var Idx: Integer; VPtr: ^V;
    begin
      Idx := Self.FindKey(Key);
      if Idx >= 0 then
      begin VPtr := Self.FValues + Idx * SizeOf(V); Result := VPtr^ end
      else Halt(1)
    end;
    procedure TMap<K, V>.SetItem(Key: K; Value: V);
    begin Self.Add(Key, Value) end;
    var D: TMap<string, Integer>;
    begin
      D := TMap<string, Integer>.Create();
      D['one'] := 1;
      D['two'] := 2;
      WriteLn(D['one']);
      WriteLn(D['two']);
      D.Free()
    end.
    ''';
begin
  AssertRunsOnAll(Src, '1' + Chr(10) + '2' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_TDictionary_DefaultProp_Update;
const Src = '''
    program T;
    type
      TMap<K, V> = class
        FKeys:     ^K;
        FValues:   ^V;
        FCount:    Integer;
        FCapacity: Integer;
        procedure Grow;
        function  FindKey(Key: K): Integer;
        procedure Add(Key: K; Value: V);
        function  GetItem(Key: K): V;
        procedure SetItem(Key: K; Value: V);
        property Items[Key: K]: V read GetItem write SetItem; default;
      end;
    procedure TMap<K, V>.Grow;
    var NewCap: Integer;
    begin
      if Self.FCapacity = 0 then NewCap := 8
      else NewCap := Self.FCapacity * 2;
      Self.FKeys   := ReallocMem(Self.FKeys,   NewCap * SizeOf(K));
      Self.FValues := ReallocMem(Self.FValues, NewCap * SizeOf(V));
      Self.FCapacity := NewCap
    end;
    function TMap<K, V>.FindKey(Key: K): Integer;
    var I: Integer; Ptr: ^K;
    begin
      Result := -1;
      I := 0;
      while I < Self.FCount do
      begin
        Ptr := Self.FKeys + I * SizeOf(K);
        if Ptr^ = Key then begin Result := I; I := Self.FCount end
        else I := I + 1
      end
    end;
    procedure TMap<K, V>.Add(Key: K; Value: V);
    var Idx: Integer; KPtr: ^K; VPtr: ^V;
    begin
      Idx := Self.FindKey(Key);
      if Idx >= 0 then
      begin VPtr := Self.FValues + Idx * SizeOf(V); VPtr^ := Value end
      else begin
        if Self.FCount = Self.FCapacity then Self.Grow();
        KPtr := Self.FKeys + Self.FCount * SizeOf(K);
        VPtr := Self.FValues + Self.FCount * SizeOf(V);
        KPtr^ := Key; VPtr^ := Value;
        Self.FCount := Self.FCount + 1
      end
    end;
    function TMap<K, V>.GetItem(Key: K): V;
    var Idx: Integer; VPtr: ^V;
    begin
      Idx := Self.FindKey(Key);
      if Idx >= 0 then
      begin VPtr := Self.FValues + Idx * SizeOf(V); Result := VPtr^ end
      else Halt(1)
    end;
    procedure TMap<K, V>.SetItem(Key: K; Value: V);
    begin Self.Add(Key, Value) end;
    var D: TMap<string, Integer>;
    begin
      D := TMap<string, Integer>.Create();
      D['x'] := 10;
      D['x'] := 42;
      WriteLn(D['x']);
      D.Free()
    end.
    ''';
begin
  AssertRunsOnAll(Src, '42' + Chr(10), 0);
end;

{ ---- Generic records ---- }

procedure TE2EGapTests.TestRun_GenericRecord_FieldAccess;
const Src = '''
    program T;
    type
      TPair<K, V> = record
        Key: K;
        Value: V;
      end;
    var P: TPair<Integer, string>;
    begin
      P.Key := 42;
      P.Value := 'hello';
      WriteLn(P.Key);
      WriteLn(P.Value)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '42' + Chr(10) + 'hello' + Chr(10), 0);
end;

procedure TE2EGapTests.TestRun_GenericRecord_MethodCall;
const Src = '''
    program T;
    type
      TBox<T> = record
        Data: T;
        function GetData: T;
      end;
    function TBox<T>.GetData: T;
    begin
      Result := Self.Data
    end;
    var B: TBox<Integer>;
    begin
      B.Data := 99;
      WriteLn(B.GetData())
    end.
    ''';
begin
  AssertRunsOnAll(Src, '99' + Chr(10), 0);
end;

{ ---- Published RTTI + MethodAddress ---- }

procedure TE2EGapTests.TestRun_PublishedRTTI_MethodAddress;
const Src = '''
    program T;
    type
      TMyObj = class(TObject)
      published
        procedure Greet;
      end;
    procedure TMyObj.Greet;
    begin
      WriteLn('hello from published')
    end;
    var
      Obj: TMyObj;
      Addr: Pointer;
    begin
      Obj := TMyObj.Create();
      Addr := MethodAddress(Obj, 'Greet');
      if Addr <> nil then
        WriteLn('found')
      else
        WriteLn('BUG');
      Obj.Free()
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'found' + Chr(10), 0);
end;

{ ---- Multi-arg WriteLn ---- }

procedure TE2EGapTests.TestRun_WriteLn_MultipleArgs_MixedTypes;
const Src = '''
    program T;
    var
      S: string;
      I: Integer;
      B: Boolean;
    begin
      S := 'val';
      I := 42;
      B := True;
      WriteLn(S, '=', I);
      WriteLn('ok:', B)
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'val=42' + Chr(10) + 'ok:True' + Chr(10), 0);
end;

initialization
  RegisterTest(TE2EGapTests);

end.
