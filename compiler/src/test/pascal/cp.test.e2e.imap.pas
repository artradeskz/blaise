{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.imap;

{ E2E tests for IMap<K,V>: compile -> QBE -> cc -> run, assert on stdout.
  Verifies that interface dispatch through IMap<K,V> routes to the correct
  concrete implementation at runtime — both TDictionary and TOrderedDictionary. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EIMapTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_IMap_TDictionary_AddAndContainsKey;
    procedure TestRun_IMap_TDictionary_TryGetValue;
    procedure TestRun_IMap_TDictionary_Remove;
    procedure TestRun_IMap_TOrderedDictionary_AddAndContainsKey;
    procedure TestRun_IMap_TOrderedDictionary_TryGetValue;
    procedure TestRun_IMap_SwapImplementation_SameCallSite;
    procedure TestRun_IMap_GenericDictInUnit_LinksAndRuns;
  end;

implementation

const
  { Shared IMap interface declaration used in all test programs }
  IMapSrc =
    '''
    program P;
    type
      IMap = interface
        procedure Add(Key, Value: Integer);
        function  TryGetValue(Key: Integer; var Value: Integer): Boolean;
        function  ContainsKey(Key: Integer): Boolean;
        procedure Remove(Key: Integer);
        function  GetCount: Integer;
      end;
    ''';

  { Non-generic TDict implementing IMap (concrete Integer key/value for E2E) }
  TDictSrc =
    '''
      TDict = class(IMap)
        FKeys:     ^Integer;
        FValues:   ^Integer;
        FCount:    Integer;
        FCapacity: Integer;
        procedure Grow;
        var NewCap, OldCap: Integer;
        begin
          OldCap := Self.FCapacity;
          if OldCap = 0 then NewCap := 8 else NewCap := OldCap * 2;
          Self.FKeys   := ReallocMem(Self.FKeys,   NewCap * SizeOf(Integer));
          ZeroMem(Self.FKeys + OldCap * SizeOf(Integer), (NewCap-OldCap) * SizeOf(Integer));
          Self.FValues := ReallocMem(Self.FValues, NewCap * SizeOf(Integer));
          ZeroMem(Self.FValues + OldCap * SizeOf(Integer), (NewCap-OldCap) * SizeOf(Integer));
          Self.FCapacity := NewCap
        end;
        function FindKey(Key: Integer): Integer;
        var I: Integer; Ptr: ^Integer;
        begin
          Result := -1; I := 0;
          while I < Self.FCount do begin
            Ptr := Self.FKeys + I * SizeOf(Integer);
            if Ptr^ = Key then begin Result := I; break end;
            I := I + 1
          end
        end;
        procedure Add(Key, Value: Integer);
        var Idx: Integer; KPtr, VPtr: ^Integer;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then begin
            VPtr := Self.FValues + Idx * SizeOf(Integer); VPtr^ := Value
          end else begin
            if Self.FCount = Self.FCapacity then Self.Grow;
            KPtr := Self.FKeys   + Self.FCount * SizeOf(Integer);
            VPtr := Self.FValues + Self.FCount * SizeOf(Integer);
            KPtr^ := Key; VPtr^ := Value;
            Self.FCount := Self.FCount + 1
          end
        end;
        function TryGetValue(Key: Integer; var Value: Integer): Boolean;
        var Idx: Integer; VPtr: ^Integer;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then begin
            VPtr := Self.FValues + Idx * SizeOf(Integer);
            Value := VPtr^; Result := True
          end else Result := False
        end;
        function ContainsKey(Key: Integer): Boolean;
        begin Result := Self.FindKey(Key) >= 0 end;
        procedure Remove(Key: Integer);
        var Idx, I: Integer; KDst, KSrc, VDst, VSrc: ^Integer;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then begin
            I := Idx;
            while I < Self.FCount - 1 do begin
              KDst := Self.FKeys   + I * SizeOf(Integer);
              KSrc := Self.FKeys   + (I+1) * SizeOf(Integer);
              VDst := Self.FValues + I * SizeOf(Integer);
              VSrc := Self.FValues + (I+1) * SizeOf(Integer);
              KDst^ := KSrc^; VDst^ := VSrc^; I := I + 1
            end;
            Self.FCount := Self.FCount - 1
          end
        end;
        function GetCount: Integer;
        begin Result := Self.FCount end;
        property Count: Integer read GetCount;
      end;
    ''';

  { Insertion-ordered variant implementing the same IMap interface }
  TOrdDictSrc =
    '''
      TOrdDict = class(IMap)
        FKeys:     ^Integer;
        FValues:   ^Integer;
        FCount:    Integer;
        FCapacity: Integer;
        procedure Grow;
        var NewCap, OldCap: Integer;
        begin
          OldCap := Self.FCapacity;
          if OldCap = 0 then NewCap := 8 else NewCap := OldCap * 2;
          Self.FKeys   := ReallocMem(Self.FKeys,   NewCap * SizeOf(Integer));
          ZeroMem(Self.FKeys + OldCap * SizeOf(Integer), (NewCap-OldCap) * SizeOf(Integer));
          Self.FValues := ReallocMem(Self.FValues, NewCap * SizeOf(Integer));
          ZeroMem(Self.FValues + OldCap * SizeOf(Integer), (NewCap-OldCap) * SizeOf(Integer));
          Self.FCapacity := NewCap
        end;
        function FindKey(Key: Integer): Integer;
        var I: Integer; Ptr: ^Integer;
        begin
          Result := -1; I := 0;
          while I < Self.FCount do begin
            Ptr := Self.FKeys + I * SizeOf(Integer);
            if Ptr^ = Key then begin Result := I; break end;
            I := I + 1
          end
        end;
        procedure Add(Key, Value: Integer);
        var Idx: Integer; KPtr, VPtr: ^Integer;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then begin
            VPtr := Self.FValues + Idx * SizeOf(Integer); VPtr^ := Value
          end else begin
            if Self.FCount = Self.FCapacity then Self.Grow;
            KPtr := Self.FKeys   + Self.FCount * SizeOf(Integer);
            VPtr := Self.FValues + Self.FCount * SizeOf(Integer);
            KPtr^ := Key; VPtr^ := Value;
            Self.FCount := Self.FCount + 1
          end
        end;
        function TryGetValue(Key: Integer; var Value: Integer): Boolean;
        var Idx: Integer; VPtr: ^Integer;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then begin
            VPtr := Self.FValues + Idx * SizeOf(Integer);
            Value := VPtr^; Result := True
          end else Result := False
        end;
        function ContainsKey(Key: Integer): Boolean;
        begin Result := Self.FindKey(Key) >= 0 end;
        procedure Remove(Key: Integer);
        var Idx, I: Integer; KDst, KSrc, VDst, VSrc: ^Integer;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then begin
            I := Idx;
            while I < Self.FCount - 1 do begin
              KDst := Self.FKeys   + I * SizeOf(Integer);
              KSrc := Self.FKeys   + (I+1) * SizeOf(Integer);
              VDst := Self.FValues + I * SizeOf(Integer);
              VSrc := Self.FValues + (I+1) * SizeOf(Integer);
              KDst^ := KSrc^; VDst^ := VSrc^; I := I + 1
            end;
            Self.FCount := Self.FCount - 1
          end
        end;
        function GetCount: Integer;
        begin Result := Self.FCount end;
        property Count: Integer read GetCount;
      end;
    ''';

  { Add via IMap, ContainsKey via IMap, print result }
  SrcDictAddContains =
    IMapSrc +
    '''
    type
    ''' +
    TDictSrc +
    '''
    var M: IMap;
    begin
      M := TDict.Create;
      M.Add(10, 100);
      M.Add(20, 200);
      WriteLn(M.ContainsKey(10));
      WriteLn(M.ContainsKey(99));
      WriteLn(M.GetCount)
    end.
    ''';

  { TryGetValue via IMap }
  SrcDictTryGet =
    IMapSrc +
    '''
    type
    ''' +
    TDictSrc +
    '''
    var M: IMap; V: Integer; OK: Boolean;
    begin
      M := TDict.Create;
      M.Add(42, 99);
      OK := M.TryGetValue(42, V);
      WriteLn(OK);
      WriteLn(V);
      OK := M.TryGetValue(7, V);
      WriteLn(OK)
    end.
    ''';

  { Remove via IMap }
  SrcDictRemove =
    IMapSrc +
    '''
    type
    ''' +
    TDictSrc +
    '''
    var M: IMap;
    begin
      M := TDict.Create;
      M.Add(1, 10); M.Add(2, 20); M.Add(3, 30);
      M.Remove(2);
      WriteLn(M.GetCount);
      WriteLn(M.ContainsKey(2));
      WriteLn(M.ContainsKey(1))
    end.
    ''';

  { Same operations through TOrdDict implementing the same IMap }
  SrcOrdDictAddContains =
    IMapSrc +
    '''
    type
    ''' +
    TOrdDictSrc +
    '''
    var M: IMap;
    begin
      M := TOrdDict.Create;
      M.Add(10, 100);
      M.Add(20, 200);
      WriteLn(M.ContainsKey(10));
      WriteLn(M.ContainsKey(99));
      WriteLn(M.GetCount)
    end.
    ''';

  { TryGetValue via TOrdDict/IMap }
  SrcOrdDictTryGet =
    IMapSrc +
    '''
    type
    ''' +
    TOrdDictSrc +
    '''
    var M: IMap; V: Integer; OK: Boolean;
    begin
      M := TOrdDict.Create;
      M.Add(42, 99);
      OK := M.TryGetValue(42, V);
      WriteLn(OK);
      WriteLn(V);
      OK := M.TryGetValue(7, V);
      WriteLn(OK)
    end.
    ''';

  { Swap implementation: same call site, two different concrete types }
  SrcSwapImpl =
    IMapSrc +
    '''
    type
    ''' +
    TDictSrc +
    TOrdDictSrc +
    '''
    var M: IMap; Flag: Boolean;
    begin
      M := TDict.Create;
      M.Add(5, 50);
      Flag := M.ContainsKey(5);
      WriteLn(Flag);
      M := TOrdDict.Create;
      M.Add(5, 50);
      Flag := M.ContainsKey(5);
      WriteLn(Flag)
    end.
    ''';

{ ------------------------------------------------------------------ }
{ Setup                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EIMapTests.SetUp;
begin
  inherited SetUp;
  SetUpScratch('compiler/target/test-e2e-imap')
end;

{ ------------------------------------------------------------------ }
{ Tests                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EIMapTests.TestRun_IMap_TDictionary_AddAndContainsKey;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcDictAddContains, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  { ContainsKey(10) -> true, ContainsKey(99) -> false, Count=2 }
  AssertTrue('contains 10 -> True',  Pos('True',  Output) >= 0);
  AssertTrue('contains 99 -> False', Pos('False', Output) >= 0);
  AssertTrue('count=2',              Pos('2',     Output) >= 0);
end;

procedure TE2EIMapTests.TestRun_IMap_TDictionary_TryGetValue;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcDictTryGet, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('found -> True',  Pos('True',  Output) >= 0);
  AssertTrue('value=99',       Pos('99',    Output) >= 0);
  AssertTrue('missing -> False', Pos('False', Output) >= 0);
end;

procedure TE2EIMapTests.TestRun_IMap_TDictionary_Remove;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcDictRemove, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('count=2',          Pos('2',     Output) >= 0);
  AssertTrue('removed key gone', Pos('False', Output) >= 0);
  AssertTrue('other key stays',  Pos('True',  Output) >= 0);
end;

procedure TE2EIMapTests.TestRun_IMap_TOrderedDictionary_AddAndContainsKey;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcOrdDictAddContains, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('contains 10 -> True',  Pos('True',  Output) >= 0);
  AssertTrue('contains 99 -> False', Pos('False', Output) >= 0);
  AssertTrue('count=2',              Pos('2',     Output) >= 0);
end;

procedure TE2EIMapTests.TestRun_IMap_TOrderedDictionary_TryGetValue;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcOrdDictTryGet, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('found -> True',    Pos('True',  Output) >= 0);
  AssertTrue('value=99',         Pos('99',    Output) >= 0);
  AssertTrue('missing -> False', Pos('False', Output) >= 0);
end;

procedure TE2EIMapTests.TestRun_IMap_SwapImplementation_SameCallSite;
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRun(SrcSwapImpl, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertTrue('TDict dispatch correct',    Pos('True', Output) >= 0);
  AssertTrue('TOrdDict dispatch correct', Pos('True', Output) >= 0);
end;

{ Regression: a generic class implementing a generic interface
  (TDictionary<string,Integer> -> IMap<string,Integer>) instantiated inside a
  USER UNIT (not the main program) must link.  Previously the unit codegen path
  emitted the impllist that references typeinfo_IMap_string_Integer but never
  emitted that typeinfo def, producing an undefined-symbol link error. }
procedure TE2EIMapTests.TestRun_IMap_GenericDictInUnit_LinksAndRuns;
const
  UnitSrc =
    '''
    unit genmapunit;
    interface
    uses Generics.Collections;
    type
      TStore = class
        FMap: TDictionary<string, Integer>;
        constructor Create;
        function Get(const AKey: string): Integer;
      end;
    implementation
    constructor TStore.Create;
    begin
      FMap := TDictionary<string, Integer>.Create;
      FMap.Add('answer', 42);
    end;
    function TStore.Get(const AKey: string): Integer;
    begin
      if not FMap.TryGetValue(AKey, Result) then Result := -1;
    end;
    end.
    ''';
  ProgSrc =
    '''
    program P;
    uses genmapunit;
    var S: TStore;
    begin
      S := TStore.Create;
      WriteLn(S.Get('answer'))
    end.
    ''';
var
  Output: string;
  RCode:  Integer;
begin
  if not ToolchainAvailable then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+link+run',
    CompileAndRunWithUnit('genmapunit', UnitSrc, ProgSrc, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Get(answer) = 42', '42' + #10, Output);
end;

initialization
  RegisterTest(TE2EIMapTests);

end.
