{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.inherit;

{ End-to-end tests for class inheritance — compile + run on BOTH backends.
  Grew out of the test-hardening sweep: cp.test.inherit.pas asserted only on
  generated QBE IR substrings and never fed the IR to QBE/native, so virtual
  dispatch, inherited calls, multi-level field layout, and destructor chaining
  were never proven to actually run.  Each test here runs the program on the
  QBE backend AND the native x86-64 backend and asserts on stdout. }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  TE2EInheritTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_ThreeLevelVirtualOverride;
    procedure TestRun_InheritedInOverride;
    procedure TestRun_CtorChainInherited;
    procedure TestRun_PolymorphicArrayDispatch;
    procedure TestRun_IsAsOperators;
    procedure TestRun_VirtualDispatchInCtor;
    procedure TestRun_FourLevelFieldInherit;
    procedure TestRun_DoubleDispatchInherited;
    procedure TestRun_VirtualDestructorChain;
    { A property whose getter/setter is virtual must dispatch through the
      vtable, exactly like a direct accessor call does. }
    procedure TestRun_VirtualPropertyGetter_Dispatches;
    procedure TestRun_VirtualPropertySetter_Dispatches;
  end;

implementation

const
  LE = #10;

procedure TE2EInheritTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-inherit');
end;

const
  { 3-level hierarchy: a non-virtual Describe in the root calls a virtual
    Name; the most-derived override must be reached regardless of the
    static (TA) variable type. }
  SrcThreeLevel = '''
    program P;
    type
      TA = class
        function Name: string; virtual; begin Result := 'A'; end;
        function Describe: string; begin Result := 'I am ' + Self.Name(); end;
      end;
      TB = class(TA)
        function Name: string; override; begin Result := 'B'; end;
      end;
      TC = class(TB)
        function Name: string; override; begin Result := 'C'; end;
      end;
    var a: TA;
    begin
      a := TC.Create; WriteLn(a.Describe()); a := nil;
      a := TB.Create; WriteLn(a.Describe()); a := nil;
    end.
    ''';

  SrcInheritedInOverride = '''
    program P;
    type
      TBase = class
        function Greet: string; virtual; begin Result := 'base'; end;
      end;
      TDerived = class(TBase)
        function Greet: string; override; begin Result := inherited Greet() + '+derived'; end;
      end;
    var d: TDerived;
    begin
      d := TDerived.Create; WriteLn(d.Greet()); d := nil;
    end.
    ''';

  SrcCtorChain = '''
    program P;
    type
      TBase = class
        FX: Integer;
        constructor Create(ax: Integer); begin FX := ax; end;
      end;
      TDerived = class(TBase)
        FY: Integer;
        constructor Create(ax, ay: Integer); begin inherited Create(ax); FY := ay; end;
      end;
    var d: TDerived;
    begin
      d := TDerived.Create(3, 7); WriteLn(d.FX + d.FY); d := nil;
    end.
    ''';

  { Polymorphism through a base-typed array: each element dispatches to its
    own override. }
  SrcPolyArray = '''
    program P;
    type
      TShape = class
        function Area: Integer; virtual; begin Result := 0; end;
      end;
      TSquare = class(TShape)
        FS: Integer;
        constructor Create(s: Integer); begin FS := s; end;
        function Area: Integer; override; begin Result := FS * FS; end;
      end;
      TRect = class(TShape)
        FW, FH: Integer;
        constructor Create(w, h: Integer); begin FW := w; FH := h; end;
        function Area: Integer; override; begin Result := FW * FH; end;
      end;
    var shapes: array[0..1] of TShape; i, total: Integer;
    begin
      shapes[0] := TSquare.Create(4);
      shapes[1] := TRect.Create(3, 5);
      total := 0;
      for i := 0 to 1 do total := total + shapes[i].Area();
      WriteLn(total);
      shapes[0] := nil; shapes[1] := nil;
    end.
    ''';

  SrcIsAs = '''
    program P;
    type
      TAnimal = class
        function Sound: string; virtual; begin Result := '?'; end;
      end;
      TDog = class(TAnimal)
        function Sound: string; override; begin Result := 'woof'; end;
        function Fetch: string; begin Result := 'fetching'; end;
      end;
    var a: TAnimal; d: TDog;
    begin
      a := TDog.Create;
      WriteLn(a.Sound());
      if a is TDog then WriteLn('is-dog');
      d := a as TDog;
      WriteLn(d.Fetch());
      a := nil;
    end.
    ''';

  { Template-method pattern: a base constructor calls a virtual that the
    derived class overrides — the override must be reached even though the
    object is still being constructed. }
  SrcVirtualInCtor = '''
    program P;
    type
      TBase = class
        FInit: Integer;
        constructor Create; begin FInit := Self.Compute(); end;
        function Compute: Integer; virtual; begin Result := 1; end;
      end;
      TDerived = class(TBase)
        function Compute: Integer; override; begin Result := 42; end;
      end;
    var b: TBase;
    begin
      b := TDerived.Create; WriteLn(b.FInit); b := nil;
    end.
    ''';

  { Four levels, each adding a field — checks that field offsets accumulate
    correctly down the hierarchy. }
  SrcFourLevelFields = '''
    program P;
    type
      T1 = class FA: Integer; end;
      T2 = class(T1) FB: Integer; end;
      T3 = class(T2) FC: Integer; end;
      T4 = class(T3) FD: Integer; end;
    var o: T4;
    begin
      o := T4.Create;
      o.FA := 1; o.FB := 2; o.FC := 3; o.FD := 4;
      WriteLn(o.FA + o.FB * 10 + o.FC * 100 + o.FD * 1000);
      o := nil;
    end.
    ''';

  { Double dispatch: an override calls inherited Wrap, which itself calls the
    virtual Tag — Tag must resolve to the derived override. }
  SrcDoubleDispatch = '''
    program P;
    type
      TA = class
        function Tag: string; virtual; begin Result := 'a'; end;
        function Wrap: string; virtual; begin Result := '[' + Self.Tag() + ']'; end;
      end;
      TB = class(TA)
        function Tag: string; override; begin Result := 'b'; end;
        function Wrap: string; override; begin Result := 'B' + inherited Wrap(); end;
      end;
    var a: TA;
    begin
      a := TB.Create; WriteLn(a.Wrap()); a := nil;
    end.
    ''';

  SrcDestructorChain = '''
    program P;
    type
      TBase = class
        destructor Destroy; override; begin WriteLn('base-destroy'); end;
      end;
      TDerived = class(TBase)
        destructor Destroy; override; begin WriteLn('derived-destroy'); inherited Destroy(); end;
      end;
    var d: TDerived;
    begin
      d := TDerived.Create;
      d.Free();
    end.
    ''';

  { A read property backed by a VIRTUAL getter: read through a base-typed
    variable holding a derived instance must reach the override (99), just as
    a direct b.GetVal() call does. }
  SrcVirtualGetter = '''
    program P;
    type
      TBase = class
        function GetVal: Integer; virtual; begin Result := 1; end;
        property Val: Integer read GetVal;
      end;
      TDerived = class(TBase)
        function GetVal: Integer; override; begin Result := 99; end;
      end;
    var b: TBase;
    begin
      b := TDerived.Create;
      WriteLn(b.Val);
      b := nil;
    end.
    ''';

  { A write property backed by a VIRTUAL setter: assigning through a base-typed
    variable must reach the override, which records double the value. }
  SrcVirtualSetter = '''
    program P;
    type
      TBase = class
        FStore: Integer;
        procedure SetVal(AValue: Integer); virtual; begin FStore := AValue; end;
        property Val: Integer write SetVal;
      end;
      TDerived = class(TBase)
        procedure SetVal(AValue: Integer); override; begin FStore := AValue * 2; end;
      end;
    var b: TBase;
    begin
      b := TDerived.Create;
      b.Val := 21;
      WriteLn(b.FStore);
      b := nil;
    end.
    ''';

procedure TE2EInheritTests.TestRun_ThreeLevelVirtualOverride;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcThreeLevel, 'I am C' + LE + 'I am B' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_InheritedInOverride;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInheritedInOverride, 'base+derived' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_CtorChainInherited;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcCtorChain, '10' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_PolymorphicArrayDispatch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcPolyArray, '31' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_IsAsOperators;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIsAs, 'woof' + LE + 'is-dog' + LE + 'fetching' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_VirtualDispatchInCtor;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVirtualInCtor, '42' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_FourLevelFieldInherit;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcFourLevelFields, '4321' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_DoubleDispatchInherited;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDoubleDispatch, 'B[b]' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_VirtualDestructorChain;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDestructorChain, 'derived-destroy' + LE + 'base-destroy' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_VirtualPropertyGetter_Dispatches;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVirtualGetter, '99' + LE, 0);
end;

procedure TE2EInheritTests.TestRun_VirtualPropertySetter_Dispatches;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVirtualSetter, '42' + LE, 0);
end;

initialization
  RegisterTest(TE2EInheritTests);

end.
