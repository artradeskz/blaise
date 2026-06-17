{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.genericintfs;

{ E2E tests for generic interfaces (IFoo<T>) and generic defaults
  (IEqualityComparer<T>, IComparer<T>).  Compile+run on both backends. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EGenericIntfTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { Generic interface: basic dispatch }
    procedure TestRun_GenericIntf_MethodDispatch;
    { Generic interface: two type params }
    procedure TestRun_GenericIntf_TwoTypeParams;
    { IEqualityComparer<Integer>: Equals dispatch }
    procedure TestRun_EqualityComparer_EqualsDispatch;
    { IEqualityComparer<Integer>: GetHashCode dispatch }
    procedure TestRun_EqualityComparer_GetHashCodeDispatch;
    { IComparer<Integer>: Compare dispatch }
    procedure TestRun_Comparer_CompareDispatch;
    { Generic interface with string type argument }
    procedure TestRun_GenericIntf_StringTypeArg;
    { Polymorphic: two classes implementing same generic interface }
    procedure TestRun_GenericIntf_PolymorphicDispatch;
  end;

implementation

procedure TE2EGenericIntfTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-genericintfs');
end;

procedure TE2EGenericIntfTests.TestRun_GenericIntf_MethodDispatch;
const Src = '''
    program T;
    type
      ITransform<T> = interface
        function Apply(V: T): T;
      end;
      TDoubler = class(ITransform<Integer>)
        function Apply(V: Integer): Integer;
        begin Result := V * 2 end;
      end;
    var
      Obj: TDoubler;
      Intf: ITransform<Integer>;
    begin
      Obj := TDoubler.Create();
      Intf := Obj;
      WriteLn(Intf.Apply(21))
    end.
    ''';
begin
  AssertRunsOnAll(Src, '42' + Chr(10), 0);
end;

procedure TE2EGenericIntfTests.TestRun_GenericIntf_TwoTypeParams;
const Src = '''
    program T;
    type
      IPair<K, V> = interface
        function GetKey: K;
        function GetValue: V;
      end;
      TIntPair = class(IPair<Integer, Integer>)
        FA: Integer;
        FB: Integer;
        constructor Create(A, B: Integer);
        function GetKey: Integer;
        function GetValue: Integer;
      end;
    constructor TIntPair.Create(A, B: Integer);
    begin
      Self.FA := A;
      Self.FB := B;
    end;
    function TIntPair.GetKey: Integer;
    begin Result := Self.FA end;
    function TIntPair.GetValue: Integer;
    begin Result := Self.FB end;
    var
      P: IPair<Integer, Integer>;
    begin
      P := TIntPair.Create(10, 20);
      WriteLn(P.GetKey());
      WriteLn(P.GetValue())
    end.
    ''';
begin
  AssertRunsOnAll(Src, '10' + Chr(10) + '20' + Chr(10), 0);
end;

procedure TE2EGenericIntfTests.TestRun_EqualityComparer_EqualsDispatch;
const Src = '''
    program T;
    type
      IEqualityComparer<T> = interface
        function Equals(A, B: T): Boolean;
        function GetHashCode(Value: T): Integer;
      end;
      TIntEqCmp = class(IEqualityComparer<Integer>)
        function Equals(A, B: Integer): Boolean;
        begin Result := A = B end;
        function GetHashCode(Value: Integer): Integer;
        begin Result := Value end;
      end;
    var
      C: IEqualityComparer<Integer>;
    begin
      C := TIntEqCmp.Create();
      if C.Equals(42, 42) then
        WriteLn('equal')
      else
        WriteLn('BUG');
      if C.Equals(1, 2) then
        WriteLn('BUG')
      else
        WriteLn('notequal')
    end.
    ''';
begin
  AssertRunsOnAll(Src, 'equal' + Chr(10) + 'notequal' + Chr(10), 0);
end;

procedure TE2EGenericIntfTests.TestRun_EqualityComparer_GetHashCodeDispatch;
const Src = '''
    program T;
    type
      IEqualityComparer<T> = interface
        function Equals(A, B: T): Boolean;
        function GetHashCode(Value: T): Integer;
      end;
      TIntEqCmp = class(IEqualityComparer<Integer>)
        function Equals(A, B: Integer): Boolean;
        begin Result := A = B end;
        function GetHashCode(Value: Integer): Integer;
        begin Result := Value end;
      end;
    var
      C: IEqualityComparer<Integer>;
    begin
      C := TIntEqCmp.Create();
      WriteLn(C.GetHashCode(99))
    end.
    ''';
begin
  AssertRunsOnAll(Src, '99' + Chr(10), 0);
end;

procedure TE2EGenericIntfTests.TestRun_Comparer_CompareDispatch;
const Src = '''
    program T;
    type
      IComparer<T> = interface
        function Compare(A, B: T): Integer;
      end;
      TIntCmp = class(IComparer<Integer>)
        function Compare(A, B: Integer): Integer;
        begin
          if A < B then
            Result := -1
          else if A > B then
            Result := 1
          else
            Result := 0
        end;
      end;
    var
      C: IComparer<Integer>;
    begin
      C := TIntCmp.Create();
      WriteLn(C.Compare(1, 2));
      WriteLn(C.Compare(5, 5));
      WriteLn(C.Compare(9, 3))
    end.
    ''';
begin
  AssertRunsOnAll(Src, '-1' + Chr(10) + '0' + Chr(10) + '1' + Chr(10), 0);
end;

procedure TE2EGenericIntfTests.TestRun_GenericIntf_StringTypeArg;
const Src = '''
    program T;
    type
      IFormatter<T> = interface
        function Format(V: T): string;
      end;
      TBracketWrap = class(IFormatter<string>)
        function Format(V: string): string;
        begin Result := '[' + V + ']' end;
      end;
    var
      F: IFormatter<string>;
    begin
      F := TBracketWrap.Create();
      WriteLn(F.Format('hello'))
    end.
    ''';
begin
  AssertRunsOnAll(Src, '[hello]' + Chr(10), 0);
end;

procedure TE2EGenericIntfTests.TestRun_GenericIntf_PolymorphicDispatch;
const Src = '''
    program T;
    type
      ITransform<T> = interface
        function Apply(V: T): T;
      end;
      TDoubler = class(ITransform<Integer>)
        function Apply(V: Integer): Integer;
        begin Result := V * 2 end;
      end;
      TTripler = class(ITransform<Integer>)
        function Apply(V: Integer): Integer;
        begin Result := V * 3 end;
      end;
    procedure PrintResult(Tr: ITransform<Integer>; V: Integer);
    begin
      WriteLn(Tr.Apply(V))
    end;
    var
      D: TDoubler;
      Tp: TTripler;
    begin
      D := TDoubler.Create();
      Tp := TTripler.Create();
      PrintResult(D, 5);
      PrintResult(Tp, 5)
    end.
    ''';
begin
  AssertRunsOnAll(Src, '10' + Chr(10) + '15' + Chr(10), 0);
end;

initialization
  RegisterTest(TE2EGenericIntfTests);

end.
