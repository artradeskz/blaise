{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.interfaces;

{ End-to-end tests for interfaces — compile + run on BOTH backends.  Grew
  out of the test-hardening sweep; the existing interface tests were
  IR/semantic-only, so the generated dispatch code was never exercised. }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  TE2EInterfaceTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_BasicDispatch;
    procedure TestRun_MethodWithArgs;
    procedure TestRun_PolymorphicThroughInterfaceVar;
    procedure TestRun_ClassImplementsTwoInterfaces;
    { Passing a class instance directly to an interface-typed parameter
      (implicit class->interface narrowing at the call site). }
    procedure TestRun_GlobalClassVar_ToInterfaceParam;
    procedure TestRun_LocalClassVar_ToInterfaceParam;
    procedure TestRun_ConstructorResult_ToInterfaceParam;
    procedure TestRun_ProcInterfaceParam;
    { Interface inheritance: a derived-interface value is assignable where the
      base interface is expected (assignment, parameter, multi-level chain). }
    procedure TestRun_DerivedInterface_ToBaseVar;
    procedure TestRun_DerivedInterface_ToBaseParam;
    procedure TestRun_ThreeLevelInterfaceChain;
    { A class implementing a DERIVED interface, narrowed directly to a BASE
      interface (needs the class to emit an itab for the inherited base). }
    procedure TestRun_ClassImplDerived_ToBaseVar;
    procedure TestRun_ClassImplDerived_ToBaseParam;
    { A class that INHERITS an interface from its ancestor (the ancestor
      declares the interface; the descendant does not re-list it).  The
      descendant must be assignable/passable as that interface, dispatching to
      its own overrides and to inherited (non-overridden) methods alike
      (issue #130 bug3). }
    procedure TestRun_InheritedInterface_DescendantToVar;
    procedure TestRun_InheritedInterface_OverrideAndInheritedMethod;
  end;

implementation

const
  LE = #10;

procedure TE2EInterfaceTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-interfaces');
end;

const
  SrcBasic = '''
    program Prg;
    type
      IGreeter = interface function Greet: string; end;
      TEng = class(IGreeter) function Greet: string; begin Result := 'hello' end; end;
    var g: IGreeter;
    begin g := TEng.Create(); WriteLn(g.Greet()) end.
    ''';

  SrcArgs = '''
    program Prg;
    type
      ICalc = interface function Add(A, B: Integer): Integer; end;
      TCalc = class(ICalc) function Add(A, B: Integer): Integer; begin Result := A + B end; end;
    var c: ICalc;
    begin c := TCalc.Create(); WriteLn(c.Add(15, 27)) end.
    ''';

  SrcPolymorphic = '''
    program Prg;
    type
      IShape = interface function Area: Integer; end;
      TSquare = class(IShape) FS: Integer; function Area: Integer; begin Result := FS * FS end; end;
      TRect = class(IShape) FW, FH: Integer; function Area: Integer; begin Result := FW * FH end; end;
    var s: IShape; total: Integer;
    begin
      total := 0;
      s := TSquare.Create(); TSquare(s).FS := 4; total := total + s.Area();
      s := TRect.Create(); TRect(s).FW := 3; TRect(s).FH := 5; total := total + s.Area();
      WriteLn(total)
    end.
    ''';

  SrcTwoIntfs = '''
    program Prg;
    type
      IA = interface function NA: Integer; end;
      IB = interface function NB: Integer; end;
      TBoth = class(IA, IB) function NA: Integer; begin Result := 1 end; function NB: Integer; begin Result := 2 end; end;
    var a: IA; b: IB; o: TBoth;
    begin o := TBoth.Create(); a := o; b := o; WriteLn(a.NA() + b.NB()) end.
    ''';

  SrcGlobalToParam = '''
    program Prg;
    type INamed = interface function Name: string; end;
      TThing = class(INamed) function Name: string; begin Result := 'thing' end; end;
    function Describe(N: INamed): string; begin Result := 'I am ' + N.Name() end;
    var t: TThing;
    begin t := TThing.Create(); WriteLn(Describe(t)) end.
    ''';

  SrcLocalToParam = '''
    program Prg;
    type INamed = interface function Name: string; end;
      TThing = class(INamed) function Name: string; begin Result := 'thing' end; end;
    function Describe(N: INamed): string; begin Result := 'I am ' + N.Name() end;
    procedure Run; var t: TThing; begin t := TThing.Create(); WriteLn(Describe(t)) end;
    begin Run() end.
    ''';

  SrcCtorToParam = '''
    program Prg;
    type INamed = interface function Name: string; end;
      TThing = class(INamed) function Name: string; begin Result := 'thing' end; end;
    function Describe(N: INamed): string; begin Result := 'I am ' + N.Name() end;
    begin WriteLn(Describe(TThing.Create())) end.
    ''';

  SrcProcParam = '''
    program Prg;
    type ILog = interface procedure Emit; end;
      TC = class(ILog) procedure Emit; begin WriteLn('emit') end; end;
    procedure Use(L: ILog); begin L.Emit() end;
    var c: TC;
    begin c := TC.Create(); Use(c) end.
    ''';

procedure TE2EInterfaceTests.TestRun_BasicDispatch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcBasic, 'hello' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_MethodWithArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcArgs, '42' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_PolymorphicThroughInterfaceVar;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcPolymorphic, '31' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_ClassImplementsTwoInterfaces;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcTwoIntfs, '3' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_GlobalClassVar_ToInterfaceParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcGlobalToParam, 'I am thing' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_LocalClassVar_ToInterfaceParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcLocalToParam, 'I am thing' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_ConstructorResult_ToInterfaceParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcCtorToParam, 'I am thing' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_ProcInterfaceParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcProcParam, 'emit' + LE, 0);
end;

const
  { IDog = interface(IAnimal): a derived-interface value is assignable where
    the base interface is expected. }
  SrcDerivedToBaseVar = '''
    program P;
    type
      IAnimal = interface function Name: string; end;
      IDog = interface(IAnimal) function Bark: string; end;
      TDog = class(IDog)
        function Name: string; begin Result := 'Rex' end;
        function Bark: string; begin Result := 'woof' end;
      end;
    var d: IDog; a: IAnimal;
    begin
      d := TDog.Create;
      a := d;
      WriteLn(a.Name());
      d := nil; a := nil
    end.
    ''';

  SrcDerivedToBaseParam = '''
    program P;
    type
      IAnimal = interface function Name: string; end;
      IDog = interface(IAnimal) function Bark: string; end;
      TDog = class(IDog)
        function Name: string; begin Result := 'Rex' end;
        function Bark: string; begin Result := 'woof' end;
      end;
    function Describe(a: IAnimal): string;
    begin Result := 'Animal: ' + a.Name() end;
    var d: IDog;
    begin
      d := TDog.Create;
      WriteLn(Describe(d));
      d := nil
    end.
    ''';

  SrcThreeLevelChain = '''
    program P;
    type
      IA = interface function A: Integer; end;
      IB = interface(IA) function B: Integer; end;
      IC = interface(IB) function C: Integer; end;
      TImpl = class(IC)
        function A: Integer; begin Result := 1 end;
        function B: Integer; begin Result := 2 end;
        function C: Integer; begin Result := 3 end;
      end;
    var c: IC; a: IA;
    begin
      c := TImpl.Create;
      a := c;
      WriteLn(a.A());
      c := nil; a := nil
    end.
    ''';

procedure TE2EInterfaceTests.TestRun_DerivedInterface_ToBaseVar;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDerivedToBaseVar, 'Rex' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_DerivedInterface_ToBaseParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDerivedToBaseParam, 'Animal: Rex' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_ThreeLevelInterfaceChain;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcThreeLevelChain, '1' + LE, 0);
end;

const
  { TDog implements IDog (derived); narrowing the INSTANCE directly to an
    IAnimal var/param needs the class to emit itab_TDog_IAnimal. }
  SrcClassImplDerivedToBaseVar = '''
    program P;
    type
      IAnimal = interface function Name: string; end;
      IDog = interface(IAnimal) function Bark: string; end;
      TDog = class(IDog)
        function Name: string; begin Result := 'Rex' end;
        function Bark: string; begin Result := 'woof' end;
      end;
    var a: IAnimal;
    begin
      a := TDog.Create;
      WriteLn(a.Name());
      a := nil
    end.
    ''';

  SrcClassImplDerivedToBaseParam = '''
    program P;
    type
      IAnimal = interface function Name: string; end;
      IDog = interface(IAnimal) function Bark: string; end;
      TDog = class(IDog)
        function Name: string; begin Result := 'Rex' end;
        function Bark: string; begin Result := 'woof' end;
      end;
    function Describe(a: IAnimal): string; begin Result := 'A:' + a.Name() end;
    begin
      WriteLn(Describe(TDog.Create))
    end.
    ''';

procedure TE2EInterfaceTests.TestRun_ClassImplDerived_ToBaseVar;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcClassImplDerivedToBaseVar, 'Rex' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_ClassImplDerived_ToBaseParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcClassImplDerivedToBaseParam, 'A:Rex' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InheritedInterface_DescendantToVar;
const
  { TLoud inherits IGreeter from TPerson; assigning a TLoud to an IGreeter var
    must work and dispatch to TLoud's override (issue #130 bug3 — the repro). }
  Src = '''
    program P;
    type
      IGreeter = interface function Greet: string; end;
      TPerson = class(IGreeter) function Greet: string; virtual; end;
      TLoud   = class(TPerson)  function Greet: string; override; end;
    function TPerson.Greet: string; begin Result := 'hi' end;
    function TLoud.Greet: string;   begin Result := 'HI' end;
    var g: IGreeter;
    begin
      g := TPerson.Create; WriteLn(g.Greet());
      g := TLoud.Create;   WriteLn(g.Greet());
      g := nil
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'hi' + LE + 'HI' + LE, 0);
end;

procedure TE2EInterfaceTests.TestRun_InheritedInterface_OverrideAndInheritedMethod;
const
  { Three-level chain through an interface parameter: each level's itab must
    resolve overridden methods to the level's own body and NON-overridden
    methods to the inherited ancestor body (Who is never overridden). }
  Src = '''
    program P;
    type
      IGreeter = interface
        function Greet: string;
        function Who: string;
      end;
      TPerson = class(IGreeter)
        function Greet: string; virtual;
        function Who: string; virtual;
      end;
      TLoud     = class(TPerson) function Greet: string; override; end;
      TVeryLoud = class(TLoud)   function Greet: string; override; end;
    function TPerson.Greet: string; begin Result := 'hi' end;
    function TPerson.Who: string;   begin Result := 'person' end;
    function TLoud.Greet: string;     begin Result := 'HI' end;
    function TVeryLoud.Greet: string; begin Result := 'HI!!!' end;
    procedure Use(g: IGreeter);
    begin WriteLn(g.Greet(), ' / ', g.Who()) end;
    var per: TPerson; lou: TLoud; vl: TVeryLoud;
    begin
      per := TPerson.Create; Use(per); per.Free;
      lou := TLoud.Create;   Use(lou); lou.Free;
      vl := TVeryLoud.Create; Use(vl); vl.Free
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'hi / person' + LE + 'HI / person' + LE + 'HI!!! / person' + LE, 0);
end;

initialization
  RegisterTest(TE2EInterfaceTests);

end.
