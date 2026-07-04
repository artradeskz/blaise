{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.collections2;

{ E2E tests for TObjectList and TStringList collection classes. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ECollections2Tests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_TObjectList_AddGetCount;
    procedure TestRun_TObjectList_Delete;
    procedure TestRun_Collections_Valgrind;
    procedure TestRun_TwoDictInstancesInUnit_BothLink;
    procedure TestRun_IntfFreeFunc_GenericReturn_Compiles;
  end;

implementation

procedure TE2ECollections2Tests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-collections2');
end;

const
  // Note: uses //-style comment here because the text contains curly braces.
  SrcTObjectListAddGetCount = '''
    program P;
    type
      TObjectList = class
        FData:     ^Pointer;
        FCount:    Integer;
        FCapacity: Integer;
        procedure Grow;
        var OldCap, NewCap: Integer;
        begin
          OldCap := Self.FCapacity;
          if OldCap = 0 then NewCap := 4
          else NewCap := OldCap * 2;
          Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(Pointer));
          Self.FCapacity := NewCap
        end;
        function Add(AObject: Pointer): Integer;
        var Dest: ^Pointer;
        begin
          if Self.FCount = Self.FCapacity then Self.Grow();
          Dest        := Self.FData + Self.FCount * SizeOf(Pointer);
          Dest^       := AObject;
          Self.FCount := Self.FCount + 1;
          Result      := Self.FCount - 1
        end;
        function Get(AIndex: Integer): Pointer;
        var Src: ^Pointer;
        begin
          Src    := Self.FData + AIndex * SizeOf(Pointer);
          Result := Src^
        end;
        procedure Delete(AIndex: Integer);
        var I: Integer; Dst, Src: ^Pointer;
        begin
          I := AIndex;
          while I < Self.FCount - 1 do
          begin
            Dst  := Self.FData + I * SizeOf(Pointer);
            Src  := Self.FData + (I + 1) * SizeOf(Pointer);
            Dst^ := Src^;
            I    := I + 1
          end;
          Self.FCount := Self.FCount - 1
        end;
        property Count: Integer read FCount;
      end;
    var
      L:  TObjectList;
      P1, P2: Pointer;
    begin
      L  := TObjectList.Create();
      P1 := GetMem(1);
      P2 := GetMem(1);
      L.Add(P1);
      L.Add(P2);
      L.Add(nil);
      WriteLn(L.Count);
      WriteLn(L.Get(0) = P1);
      WriteLn(L.Get(1) = P2)
    end.
    ''';

  SrcTObjectListDelete = '''
    program P;
    type
      TObjectList = class
        FData:     ^Pointer;
        FCount:    Integer;
        FCapacity: Integer;
        procedure Grow;
        var OldCap, NewCap: Integer;
        begin
          OldCap := Self.FCapacity;
          if OldCap = 0 then NewCap := 4
          else NewCap := OldCap * 2;
          Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(Pointer));
          Self.FCapacity := NewCap
        end;
        function Add(AObject: Pointer): Integer;
        var Dest: ^Pointer;
        begin
          if Self.FCount = Self.FCapacity then Self.Grow();
          Dest        := Self.FData + Self.FCount * SizeOf(Pointer);
          Dest^       := AObject;
          Self.FCount := Self.FCount + 1;
          Result      := Self.FCount - 1
        end;
        procedure Delete(AIndex: Integer);
        var I: Integer; Dst, Src: ^Pointer;
        begin
          I := AIndex;
          while I < Self.FCount - 1 do
          begin
            Dst  := Self.FData + I * SizeOf(Pointer);
            Src  := Self.FData + (I + 1) * SizeOf(Pointer);
            Dst^ := Src^;
            I    := I + 1
          end;
          Self.FCount := Self.FCount - 1
        end;
        property Count: Integer read FCount;
      end;
    var L: TObjectList;
    begin
      L := TObjectList.Create();
      L.Add(GetMem(1));
      L.Add(GetMem(1));
      L.Add(GetMem(1));
      L.Delete(1);
      WriteLn(L.Count)
    end.
    ''';

  SrcCollectionsValgrind =
    '''
        program P;
        type
          TObjectList = class
            FData: ^Pointer; FCount: Integer; FCapacity: Integer;
            procedure Grow;
            var OldCap, NewCap: Integer;
            begin
              OldCap := Self.FCapacity;
              if OldCap = 0 then NewCap := 4 else NewCap := OldCap * 2;
              Self.FData := ReallocMem(Self.FData, NewCap * SizeOf(Pointer));
              Self.FCapacity := NewCap
            end;
            function Add(AObject: Pointer): Integer;
            var Dest: ^Pointer;
            begin
              if Self.FCount = Self.FCapacity then Self.Grow();
              Dest := Self.FData + Self.FCount * SizeOf(Pointer);
              Dest^ := AObject;
              Self.FCount := Self.FCount + 1;
              Result := Self.FCount - 1
            end;
            procedure Destroy;
            begin
              FreeMem(Self.FData);
              Self.FData := nil; Self.FCount := 0; Self.FCapacity := 0
            end;
            property Count: Integer read FCount;
          end;
          TStringList = class
            FStrings: ^string; FObjects: ^Pointer;
            FCount: Integer; FCapacity: Integer;
            procedure Grow;
            var OldCap, NewCap: Integer;
            begin
              OldCap := Self.FCapacity;
              if OldCap = 0 then NewCap := 4 else NewCap := OldCap * 2;
              Self.FStrings := ReallocMem(Self.FStrings, NewCap * SizeOf(string));
              Self.FObjects := ReallocMem(Self.FObjects, NewCap * SizeOf(Pointer));
              ZeroMem(Self.FStrings + OldCap * SizeOf(string),
                      (NewCap - OldCap) * SizeOf(string));
              Self.FCapacity := NewCap
            end;
            procedure Destroy;
            var I: Integer; Ptr: ^string;
            begin
              I := 0;
              while I < Self.FCount do
              begin
                Ptr := Self.FStrings + I * SizeOf(string); Ptr^ := nil; I := I + 1
              end;
              FreeMem(Self.FStrings); FreeMem(Self.FObjects);
              Self.FStrings := nil; Self.FObjects := nil;
              Self.FCount := 0; Self.FCapacity := 0
            end;
            function Add(S: string): Integer;
            var StrP: ^string; ObjP: ^Pointer;
            begin
              if Self.FCount = Self.FCapacity then Self.Grow();
              StrP := Self.FStrings + Self.FCount * SizeOf(string);
              ObjP := Self.FObjects + Self.FCount * SizeOf(Pointer);
              StrP^ := S; ObjP^ := nil;
              Result := Self.FCount; Self.FCount := Self.FCount + 1
            end;
            function Get(AIndex: Integer): string;
            var Ptr: ^string;
            begin
              Ptr := Self.FStrings + AIndex * SizeOf(string); Result := Ptr^
            end;
            property Count: Integer read FCount;
          end;
        var OL: TObjectList; SL: TStringList;
        begin
          OL := TObjectList.Create();
          OL.Add(nil); OL.Add(nil);
          SL := TStringList.Create();
          SL.Add('hello'); SL.Add('world');
          WriteLn(OL.Count);
          WriteLn(SL.Get(0))
        end.
        ''';

procedure TE2ECollections2Tests.TestRun_TObjectList_AddGetCount;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTObjectListAddGetCount, Output, RCode));
  AssertEquals('count=3', '3', Trim(Copy(Output, 0, Pos(#10, Output))));
end;

procedure TE2ECollections2Tests.TestRun_TObjectList_Delete;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTObjectListDelete, Output, RCode));
  AssertEquals('count after delete=2', '2', Trim(Output));
end;

procedure TE2ECollections2Tests.TestRun_Collections_Valgrind;
var OK: Boolean; Log: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  if not ValgrindAvailable() then begin Ignore('valgrind not installed'); Exit; end;
  OK := RunUnderValgrind(SrcCollectionsValgrind, Log);
  if not OK then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('Collections Valgrind check failed:' + #10 + Log);
  end;
end;

{ Regression: a unit that holds two distinct instantiations of the same
  generic whose template inherits from a generic interface (TDictionary<K,V>
  derives from IMap<K,V>).  The first instantiation used to free the generic-
  template AST node it shares; the second lookup then saw a wrong-class object
  and silently mis-wired the instance — no TObject parent, no vtable — so the
  second instance's $vtable_... symbol was referenced but never emitted and the
  link failed.  Retaining templates in the symbol table fixes it.  Both
  instances must now compile, link and run. }
procedure TE2ECollections2Tests.TestRun_TwoDictInstancesInUnit_BothLink;
const
  UnitSrc = '''
    unit twodicts;
    interface
    uses Generics.Collections;
    type
      THolder = class
      public
        Ints:  TDictionary<string, Integer>;
        Bools: TDictionary<string, Boolean>;
        procedure Fill;
        function Total: Integer;
      end;
    implementation
    procedure THolder.Fill;
    begin
      Self.Ints  := TDictionary<string, Integer>.Create();
      Self.Bools := TDictionary<string, Boolean>.Create();
      Self.Ints.Add('a', 10);
      Self.Ints.Add('b', 20);
      Self.Bools.Add('x', True)
    end;
    function THolder.Total: Integer;
    begin
      Result := Self.Ints.Count + Self.Bools.Count
    end;
    end.
    ''';
  DrvSrc = '''
    program P;
    uses twodicts;
    var h: THolder;
    begin
      h := THolder.Create();
      h.Fill();
      WriteLn(h.Total());
      h.Free()
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+link+run',
    CompileAndRunWithUnit('twodicts', UnitSrc, DrvSrc, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Ints(2) + Bools(1) = 3', '3' + #10, Output);
end;

{ Regression: a unit's INTERFACE-section free function (not a class method)
  whose return type is a generic instantiation such as TList<string> used to
  fail semantic analysis with "Unknown return type 'TList<string>'".  The
  interface free-function path resolved the return type through a plain
  FindType lookup, which never attempts generic instantiation, whereas the
  class-method path goes through FindTypeOrInstantiate.  Switching the
  free-function path to FindTypeOrInstantiate fixes it.  The same generic
  return type as a class method, and as an impl-section free function, already
  worked — those must keep working. }
procedure TE2ECollections2Tests.TestRun_IntfFreeFunc_GenericReturn_Compiles;
const
  UnitSrc = '''
    unit freefunc;
    interface
    uses Generics.Collections;
    function MakeList: TList<string>;
    implementation
    function MakeList: TList<string>;
    begin
      Result := TList<string>.Create();
      Result.Add('a');
      Result.Add('b')
    end;
    end.
    ''';
  DrvSrc = '''
    program P;
    uses Generics.Collections, freefunc;
    var L: TList<string>;
    begin
      L := MakeList();
      WriteLn(L.Count);
      L.Free()
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+link+run',
    CompileAndRunWithUnit('freefunc', UnitSrc, DrvSrc, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('list count', '2' + #10, Output);
end;

initialization
  RegisterTest(TE2ECollections2Tests);

end.
