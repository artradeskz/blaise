{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.staticmembers;

{ E2E tests for `static` class/record members: static var, static method,
  static property, and the lazy-singleton pattern.  Each program is compiled
  and run on every backend (QBE + native).  Parser/semantic/IR tests live in
  cp.test.staticmembers.pas; these guard the codegen -> QBE -> run boundary
  the IR harness cannot see (data-slot emission, no-Self call ABI, qualified
  static reads). }

interface

uses
  classes, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EStaticMembersTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_StaticMethod_NoSelf;
    procedure TestRun_StaticVar_SharedAcrossCalls;
    procedure TestRun_StaticVar_QualifiedRead;
    procedure TestRun_StaticVar_QualifiedWrite_Scalar;
    procedure TestRun_StaticVar_QualifiedWrite_ClassARC;
    procedure TestRun_StaticVar_InterfaceStore;
    procedure TestRun_StaticVar_ChainedLValueBase;
    procedure TestRun_StaticProperty_QualifiedRead;
    procedure TestRun_Singleton_LazyGetInstance;
    procedure TestRun_StaticConst_OnClass;
    procedure TestRun_RecordStaticFactory;
  end;

implementation

procedure TE2EStaticMembersTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-staticmembers')
end;

procedure TE2EStaticMembersTests.TestRun_StaticMethod_NoSelf;
const Src =
  '''
  program P;
  type
    TMath = class
    public
      static function Square(X: Integer): Integer;
    end;
  static function TMath.Square(X: Integer): Integer;
  begin
    Result := X * X;
  end;
  begin
    WriteLn(TMath.Square(7))
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '49' + LineEnding, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticVar_SharedAcrossCalls;
const Src =
  '''
  program P;
  type
    TCounter = class
    private static var
      FN: Integer;
    public
      static function Next: Integer;
    end;
  static function TCounter.Next: Integer;
  begin
    FN := FN + 1;
    Result := FN;
  end;
  begin
    WriteLn(TCounter.Next());
    WriteLn(TCounter.Next());
    WriteLn(TCounter.Next())
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '1' + LE + '2' + LE + '3' + LE, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticVar_QualifiedRead;
const Src =
  '''
  program P;
  type
    TCounter = class
    public static var
      Total: Integer;
      static procedure Bump;
    end;
  static procedure TCounter.Bump;
  begin
    Total := Total + 10;
  end;
  begin
    TCounter.Bump();
    TCounter.Bump();
    WriteLn(TCounter.Total)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '20' + LineEnding, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticVar_QualifiedWrite_Scalar;
const Src =
  '''
  program P;
  type
    TFoo = class
    public static var
      GCount: Integer;
    end;
  begin
    TFoo.GCount := 5;
    TFoo.GCount := TFoo.GCount + 37;
    WriteLn(TFoo.GCount)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '42' + LineEnding, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticVar_QualifiedWrite_ClassARC;
const Src =
  '''
  program P;
  type
    TObj = class
    public
      V: Integer;
    end;
    THolder = class
    public static var
      GObj: TObj;
    end;
  var local: TObj;
  begin
    THolder.GObj := TObj.Create();
    local := THolder.GObj;
    local.V := 99;
    WriteLn(local.V);
    THolder.GObj := nil;
    if THolder.GObj = nil then WriteLn('released')
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '99' + LineEnding + 'released' + LineEnding, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticVar_InterfaceStore;
{ Interface-typed static var: the bare store inside a static method
  (FCache := X) must write BOTH slots of the 2-slot fat pointer (obj + itab)
  with correct ARC, and the bare read (Result := FCache) must reconstruct it.
  Regression for the static-call interface-arg leading-comma bug that made
  THolder.SetIt(T) emit an invalid QBE call and segfault native. }
const Src =
  '''
  program P;
  type
    IThing = interface
      procedure Speak;
    end;
    TThing = class(IThing)
    public
      Tag: Integer;
      procedure Speak;
    end;
    THolder = class
    public static var
      FCache: IThing;
      static procedure SetIt(X: IThing);
      static function GetIt: IThing;
    end;
  procedure TThing.Speak;
  begin
    WriteLn('thing ', Tag);
  end;
  static procedure THolder.SetIt(X: IThing);
  begin
    FCache := X;
  end;
  static function THolder.GetIt: IThing;
  begin
    Result := FCache;
  end;
  var
    T: TThing;
    Got: IThing;
  begin
    T := TThing.Create();
    T.Tag := 7;
    THolder.SetIt(T);
    Got := THolder.GetIt();
    Got.Speak();
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, 'thing 7' + LineEnding, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticVar_ChainedLValueBase;
{ A qualified static var of class type used as the BASE of a further l-value
  chain: 'TFoo.GObj.Field := V' (field write through the chained base) and
  'TFoo.GObj.Method()' (method call on the chained base).  The read form
  (TFoo.GObj.Field as an expression) already worked; the write/call receiver
  path through the chained base was unresolved ("Field access requires a record
  or class base, got 'class of TFoo'"). }
const Src =
  '''
  program P;
  type
    TObj = class
    public
      V: Integer;
      procedure Bump;
    end;
    THolder = class
    public static var
      GObj: TObj;
    end;
  procedure TObj.Bump;
  begin
    V := V + 1;
  end;
  begin
    THolder.GObj := TObj.Create();
    WriteLn(THolder.GObj.V);
    THolder.GObj.V := 5;
    WriteLn(THolder.GObj.V);
    THolder.GObj.Bump();
    WriteLn(THolder.GObj.V);
    THolder.GObj := nil
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '0' + LE + '5' + LE + '6' + LE, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticProperty_QualifiedRead;
const Src =
  '''
  program P;
  type
    TRegistry = class
    private static var
      FCounter: Integer;
    public
      static function NextId: Integer;
      static property Counter: Integer read NextId;
    end;
  static function TRegistry.NextId: Integer;
  begin
    FCounter := FCounter + 1;
    Result := FCounter;
  end;
  begin
    WriteLn(TRegistry.Counter);
    WriteLn(TRegistry.Counter)
  end.
  ''';
var LE: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll(Src, '1' + LE + '2' + LE, 0);
end;

procedure TE2EStaticMembersTests.TestRun_Singleton_LazyGetInstance;
const Src =
  '''
  program P;
  type
    TConfig = class
    private static var
      FInstance: TConfig;
    public
      FValue: Integer;
      static function Instance: TConfig;
    end;
  static function TConfig.Instance: TConfig;
  begin
    if FInstance = nil then
      FInstance := TConfig.Create();
    Result := FInstance;
  end;
  begin
    TConfig.Instance().FValue := 42;
    WriteLn(TConfig.Instance().FValue)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '42' + LineEnding, 0);
end;

procedure TE2EStaticMembersTests.TestRun_StaticConst_OnClass;
const Src =
  '''
  program P;
  type
    TLimits = class
    public static const
      MaxItems = 128;
    end;
  begin
    WriteLn(TLimits.MaxItems)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '128' + LineEnding, 0);
end;

procedure TE2EStaticMembersTests.TestRun_RecordStaticFactory;
const Src =
  '''
  program P;
  type
    TPoint = record
      X, Y: Integer;
      static function Make(AX, AY: Integer): TPoint;
    end;
  static function TPoint.Make(AX, AY: Integer): TPoint;
  begin
    Result.X := AX;
    Result.Y := AY;
  end;
  var Pt: TPoint;
  begin
    Pt := TPoint.Make(3, 4);
    WriteLn(Pt.X + Pt.Y)
  end.
  ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src, '7' + LineEnding, 0);
end;

initialization
  RegisterTest(TE2EStaticMembersTests);

end.
