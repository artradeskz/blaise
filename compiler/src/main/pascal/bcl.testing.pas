{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.

  Original work Copyright (c) the Free Pascal team — fpcunit.pp.
  Ported to Blaise by Graeme Geldenhuys, 2026.
}

{
  bcl.testing — minimum xUnit runtime surface for Blaise.

  Step 11d.  Direct port of the runtime surface of fpcunit.pp, scoped to the
  slice the 54 cp.test.*.pas regression units actually use.  The runner
  (text reporter) lives in a separate unit and is the subject of Step 11e.

  Departures from fpcunit:

    * No GUID on ITestListener — Blaise interfaces are GUID-free.
    * EAssertionFailed descends from TObject (not Exception) so the unit
      stays self-contained and avoids dragging SysUtils transitively.
      The unit follows the convention established by punit.pas in the
      RTL test tree.
    * AssertException / ExpectException are intentionally absent — no
      cp.test.*.pas unit currently relies on them.  Re-add when needed.
    * Test enumeration of a registered class via 'class of TTestCase' is
      deferred to Step 11e (the runner).  v0 only stores the registered
      classes for the runner to walk later.
}

unit bcl.testing;

{$mode objfpc}{$H+}

interface

uses
  Classes;

type
  { TRunMethod — type of a parameter-less method on any TObject descendant.
    Used as the cast target for the published-method dispatch trampoline:
    Code := MethodAddress(Self, FName); M.Code := Code; M.Data := Self;
    TRunMethod(M)(). }
  TRunMethod = procedure of object;

  { TTestResult is declared first so TTest.Run can name it without the
    forward-class-declaration form that Blaise does not yet support. }
  TTestResult = class(TObject)
  private
    FNumberOfTests:    Integer;
    FNumberOfFailures: Integer;
    FNumberOfErrors:   Integer;
    FFailureList:      TStringList;
    FErrorList:        TStringList;
  public
    constructor Create;
    destructor  Destroy; override;

    procedure StartTest (ATest: TObject);
    procedure EndTest   (ATest: TObject);
    procedure AddFailure(AName, AMessage: string);
    procedure AddError  (AName, AMessage: string);

    function  Summary: string;

    property  NumberOfTests:    Integer read FNumberOfTests;
    property  NumberOfFailures: Integer read FNumberOfFailures;
    property  NumberOfErrors:   Integer read FNumberOfErrors;
    property  Failures:         TStringList read FFailureList;
    property  Errors:           TStringList read FErrorList;
  end;

  { TTest — abstract root of the test hierarchy.  Concrete subclasses
    override Run and CountTestCases. }
  TTest = class(TObject)
  public
    procedure Run(AResult: TTestResult); virtual;
    function  CountTestCases: Integer; virtual;
  end;

  { TAssert — assertion helpers.  Implemented as instance methods rather
    than 'class procedure ... static' (Blaise does not yet parse 'class
    procedure').  Inside a published test method 'TFoo.TestX', a bare
    'AssertEquals(...)' call resolves through the inheritance chain to
    Self.AssertEquals, which is functionally equivalent. }
  TAssert = class(TTest)
  public
    procedure AssertTrue (ACondition: Boolean; AMsg: string = '');
    procedure AssertFalse(ACondition: Boolean; AMsg: string = '');

    procedure AssertEquals(AExpected, AActual: Integer; AMsg: string = ''); overload;
    procedure AssertEquals(AExpected, AActual: Int64;   AMsg: string = ''); overload;
    procedure AssertEquals(AExpected, AActual: string;  AMsg: string = ''); overload;
    procedure AssertEquals(AExpected, AActual: Pointer; AMsg: string = ''); overload;
    procedure AssertEquals(AExpected, AActual: Boolean; AMsg: string = ''); overload;

    procedure AssertNotNull(AObject: TObject; AMsg: string = '');
    procedure AssertNull   (AObject: TObject; AMsg: string = '');
    procedure AssertSame   (AExpected, AActual: TObject; AMsg: string = '');

    procedure Fail(AMsg: string);
  end;

  { TTestCase — base class for fixtures.  Each fixture class declares its
    test methods inside a 'published' visibility section; the hot path
    in RunTest looks them up via MethodAddress and dispatches via a
    procedure-of-object cast. }
  TTestCase = class(TAssert)
  private
    FName: string;
  protected
    procedure SetUp;    virtual;
    procedure TearDown; virtual;
  public
    constructor Create(AName: string);
    procedure   RunTest;            virtual;
    procedure   Run(AResult: TTestResult); override;
    function    CountTestCases: Integer; override;
    property    TestName: string read FName;
  end;

  { TTestCaseClass — class-of reference used by RegisterTest. }
  TTestCaseClass = class of TTestCase;

  { EAssertionFailed — raised by Fail / Assert* on failure.  Descends
    from TObject (not Exception) to keep this unit standalone. }
  EAssertionFailed = class(TObject)
  private
    FMessage: string;
  public
    constructor Create(AMessage: string);
    function    ToString: string; override;
    property    Message: string read FMessage;
  end;

{ Global test registry.  RegisterTest stores classes; the runner (Step
  11e) iterates over them, walks each class's published-method table to
  build per-method TTestCase instances, and runs each one. }
procedure RegisterTest(ATestClass: TTestCaseClass);
function  GetRegisteredTestCount: Integer;
function  GetRegisteredTest(AIndex: Integer): TTestCaseClass;

implementation

{ -----------------------------------------------------------------------
  Global registry storage
  ----------------------------------------------------------------------- }

var
  GRegistry: TStringList;  { Objects[i] holds the TTestCaseClass typeinfo ptr }

{ -----------------------------------------------------------------------
  TTest
  ----------------------------------------------------------------------- }

procedure TTest.Run(AResult: TTestResult);
begin
  { Abstract in spirit; concrete subclasses override. }
end;

function TTest.CountTestCases: Integer;
begin
  Result := 1;
end;

{ -----------------------------------------------------------------------
  TAssert
  ----------------------------------------------------------------------- }

procedure TAssert.AssertTrue(ACondition: Boolean; AMsg: string);
begin
  if not ACondition then
    Self.Fail(AMsg);
end;

procedure TAssert.AssertFalse(ACondition: Boolean; AMsg: string);
begin
  if ACondition then
    Self.Fail(AMsg);
end;

procedure TAssert.AssertEquals(AExpected, AActual: Integer; AMsg: string);
begin
  if AExpected <> AActual then
    Self.Fail(AMsg + ' Expected: ' + IntToStr(AExpected)
                   + '  Actual: '  + IntToStr(AActual));
end;

procedure TAssert.AssertEquals(AExpected, AActual: Int64; AMsg: string);
begin
  if AExpected <> AActual then
    Self.Fail(AMsg + ' Expected: ' + Int64ToStr(AExpected)
                   + '  Actual: '  + Int64ToStr(AActual));
end;

procedure TAssert.AssertEquals(AExpected, AActual: string; AMsg: string);
begin
  if AExpected <> AActual then
    Self.Fail(AMsg + ' Expected: "' + AExpected + '"  Actual: "' + AActual + '"');
end;

procedure TAssert.AssertEquals(AExpected, AActual: Pointer; AMsg: string);
begin
  if AExpected <> AActual then
    Self.Fail(AMsg + ' Expected and actual pointers differ');
end;

procedure TAssert.AssertEquals(AExpected, AActual: Boolean; AMsg: string);
var
  ExpStr, ActStr: string;
begin
  if AExpected <> AActual then
  begin
    if AExpected then ExpStr := 'True' else ExpStr := 'False';
    if AActual   then ActStr := 'True' else ActStr := 'False';
    Self.Fail(AMsg + ' Expected: ' + ExpStr + '  Actual: ' + ActStr);
  end;
end;

procedure TAssert.AssertNotNull(AObject: TObject; AMsg: string);
begin
  if AObject = nil then
    Self.Fail(AMsg + ' Expected non-nil object');
end;

procedure TAssert.AssertNull(AObject: TObject; AMsg: string);
begin
  if AObject <> nil then
    Self.Fail(AMsg + ' Expected nil object');
end;

procedure TAssert.AssertSame(AExpected, AActual: TObject; AMsg: string);
begin
  if AExpected <> AActual then
    Self.Fail(AMsg + ' Expected the same object instance');
end;

procedure TAssert.Fail(AMsg: string);
begin
  raise EAssertionFailed.Create(AMsg);
end;

{ -----------------------------------------------------------------------
  TTestCase
  ----------------------------------------------------------------------- }

constructor TTestCase.Create(AName: string);
begin
  inherited Create;
  Self.FName := AName;
end;

procedure TTestCase.SetUp;
begin
end;

procedure TTestCase.TearDown;
begin
end;

function TTestCase.CountTestCases: Integer;
begin
  Result := 1;
end;

{ Hot path: dispatch via published-method address.  This is the line
  that motivated Steps 11a/b/c. }
procedure TTestCase.RunTest;
var
  M:    TMethod;
  Code: Pointer;
  Run:  TRunMethod;
begin
  Code := MethodAddress(Self, Self.FName);
  if Code = nil then
    Self.Fail('Method ' + Self.FName + ' not found in published section');
  M.Code := Code;
  M.Data := Self;
  Run    := TRunMethod(M);
  Run;
end;

procedure TTestCase.Run(AResult: TTestResult);
begin
  AResult.StartTest(Self);
  try
    Self.SetUp;
    try
      try
        Self.RunTest;
      except
        on E: EAssertionFailed do
          AResult.AddFailure(Self.FName, E.ToString);
        on E: TObject do
          AResult.AddError(Self.FName, 'Unhandled exception');
      end;
    finally
      Self.TearDown;
    end;
  finally
    AResult.EndTest(Self);
  end;
end;

{ -----------------------------------------------------------------------
  TTestResult
  ----------------------------------------------------------------------- }

constructor TTestResult.Create;
begin
  inherited Create;
  Self.FNumberOfTests    := 0;
  Self.FNumberOfFailures := 0;
  Self.FNumberOfErrors   := 0;
  Self.FFailureList      := TStringList.Create;
  Self.FErrorList        := TStringList.Create;
end;

destructor TTestResult.Destroy;
begin
  Self.FFailureList.Free;
  Self.FErrorList.Free;
  inherited Destroy;
end;

procedure TTestResult.StartTest(ATest: TObject);
begin
  Self.FNumberOfTests := Self.FNumberOfTests + 1;
end;

procedure TTestResult.EndTest(ATest: TObject);
begin
end;

procedure TTestResult.AddFailure(AName, AMessage: string);
begin
  Self.FNumberOfFailures := Self.FNumberOfFailures + 1;
  Self.FFailureList.Add(AName + ': ' + AMessage);
end;

procedure TTestResult.AddError(AName, AMessage: string);
begin
  Self.FNumberOfErrors := Self.FNumberOfErrors + 1;
  Self.FErrorList.Add(AName + ': ' + AMessage);
end;

function TTestResult.Summary: string;
begin
  if (Self.FNumberOfFailures = 0) and (Self.FNumberOfErrors = 0) then
    Result := 'OK ('   + IntToStr(Self.FNumberOfTests) + ' tests)'
  else
    Result := 'FAIL (' + IntToStr(Self.FNumberOfTests)    + ' tests, '
                       + IntToStr(Self.FNumberOfFailures) + ' failures, '
                       + IntToStr(Self.FNumberOfErrors)   + ' errors)';
end;

{ -----------------------------------------------------------------------
  EAssertionFailed
  ----------------------------------------------------------------------- }

constructor EAssertionFailed.Create(AMessage: string);
begin
  inherited Create;
  Self.FMessage := AMessage;
end;

function EAssertionFailed.ToString: string;
begin
  Result := Self.FMessage;
end;

{ -----------------------------------------------------------------------
  Global registry
  ----------------------------------------------------------------------- }

procedure RegisterTest(ATestClass: TTestCaseClass);
begin
  if GRegistry = nil then
    GRegistry := TStringList.Create;
  { Store the metaclass typeinfo pointer in Objects[]; the name slot
    is reserved for a descriptive label the runner can print. }
  GRegistry.AddObject('', Pointer(ATestClass));
end;

function GetRegisteredTestCount: Integer;
begin
  if GRegistry = nil then
    Result := 0
  else
    Result := GRegistry.Count;
end;

function GetRegisteredTest(AIndex: Integer): TTestCaseClass;
begin
  Result := TTestCaseClass(GRegistry.Objects[AIndex]);
end;

end.
