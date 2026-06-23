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
  blaise.testing — minimum xUnit runtime surface for Blaise.

  Step 11d.  Direct port of the runtime surface of fpcunit.pp, scoped to the
  slice the 54 cp.test.*.pas regression units actually use.  The runner
  (text reporter) lives in a separate unit and is the subject of Step 11e.

  Departures from fpcunit:

    * No GUID on ITestListener — Blaise interfaces are GUID-free.
    * EAssertionFailed descends from TObject (not Exception) so that
      assertion failures are never accidentally caught by a user-level
      'on E: Exception do' handler inside a test method.
    * AssertException / ExpectException are intentionally absent — no
      cp.test.*.pas unit currently relies on them.  Re-add when needed.
    * Test enumeration of a registered class via 'class of TTestCase' is
      deferred to Step 11e (the runner).  v0 only stores the registered
      classes for the runner to walk later.
}

unit blaise.testing;

interface

uses
  Classes, Generics.Collections, SysUtils;

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
    FNumberOfIgnored:  Integer;
    FFailureList:      TList<String>;
    FErrorList:        TList<String>;
    FVerbose:          Boolean;
    FCurrentClassName: string;
    FCurrentTestName:  string;
  public
    constructor Create;

    procedure StartTest (AClassName, ATestName: string);
    procedure EndTest   (AOutcome: string);
    procedure AddFailure(AName, AMessage: string);
    procedure AddError  (AName, AMessage: string);
    procedure AddIgnored(AName, AMessage: string);
    procedure MergeFrom(ASource: TTestResult);

    function  Summary: string;

    property  NumberOfTests:    Integer read FNumberOfTests;
    property  NumberOfFailures: Integer read FNumberOfFailures;
    property  NumberOfErrors:   Integer read FNumberOfErrors;
    property  NumberOfIgnored:  Integer read FNumberOfIgnored;
    property  Failures:         TList<String> read FFailureList;
    property  Errors:           TList<String> read FErrorList;
    property  Verbose:          Boolean read FVerbose write FVerbose;
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
    procedure AssertTrue (AMsg: string; ACondition: Boolean); overload;
    procedure AssertTrue (ACondition: Boolean); overload;
    procedure AssertFalse(AMsg: string; ACondition: Boolean); overload;
    procedure AssertFalse(ACondition: Boolean); overload;

    procedure AssertEquals(AMsg: string; AExpected, AActual: Integer); overload;
    procedure AssertEquals(AExpected, AActual: Integer); overload;
    procedure AssertEquals(AMsg: string; AExpected, AActual: Int64); overload;
    procedure AssertEquals(AExpected, AActual: Int64); overload;
    procedure AssertEquals(AMsg: string; AExpected, AActual: string); overload;
    procedure AssertEquals(AExpected, AActual: string); overload;
    procedure AssertEquals(AMsg: string; AExpected, AActual: Pointer); overload;
    procedure AssertEquals(AExpected, AActual: Pointer); overload;
    procedure AssertEquals(AMsg: string; AExpected, AActual: Boolean); overload;
    procedure AssertEquals(AExpected, AActual: Boolean); overload;

    procedure AssertNotEquals(AMsg: string; AExpected, AActual: Integer); overload;
    procedure AssertNotEquals(AExpected, AActual: Integer); overload;
    procedure AssertNotEquals(AMsg: string; AExpected, AActual: Int64); overload;
    procedure AssertNotEquals(AExpected, AActual: Int64); overload;
    procedure AssertNotEquals(AMsg: string; AExpected, AActual: string); overload;
    procedure AssertNotEquals(AExpected, AActual: string); overload;
    procedure AssertNotEquals(AMsg: string; AExpected, AActual: Boolean); overload;
    procedure AssertNotEquals(AExpected, AActual: Boolean); overload;
    procedure AssertNotEquals(AMsg: string; AExpected, AActual: Pointer); overload;
    procedure AssertNotEquals(AExpected, AActual: Pointer); overload;

    procedure AssertNotNull(AMsg: string; AObject: TObject); overload;
    procedure AssertNotNull(AObject: TObject); overload;
    procedure AssertNull   (AMsg: string; AObject: TObject); overload;
    procedure AssertNull   (AObject: TObject); overload;
    { AssertNotNil — verifies that a Pointer value is not nil.
      Use for type descriptors, raw pointers, and other non-TObject values. }
    procedure AssertNotNil(AMsg: string; APtr: Pointer); overload;
    procedure AssertNotNil(APtr: Pointer); overload;
    procedure AssertSame   (AMsg: string; AExpected, AActual: TObject); overload;
    procedure AssertSame   (AExpected, AActual: TObject); overload;

    { AssertContains — verifies that AHaystack contains ASubstring.
      Failure message quotes both the needle and haystack, which is far
      more useful than 'AssertTrue failed' when a Pos() check fails. }
    procedure AssertContains(AMsg: string; const ASubstring, AHaystack: string); overload;
    procedure AssertContains(const ASubstring, AHaystack: string); overload;

    procedure Fail(AMsg: string);
    procedure Ignore(AMsg: string);
  end;

  { TTestCase — base class for fixtures.  Each fixture class declares its
    test methods inside a 'published' visibility section; the hot path
    in RunTest looks them up via MethodAddress and dispatches via a
    procedure-of-object cast. }
  TTestCase = class(TAssert)
  private
    FName:      string;
    FClassName: string;
  protected
    procedure SetUp;    virtual;
    procedure TearDown; virtual;
  public
    constructor Create(AName: string);
    procedure   SetClassName(AClassName: string);
    procedure   RunTest;            virtual;
    procedure   Run(AResult: TTestResult); override;
    function    CountTestCases: Integer; override;
    property    TestName:  string read FName;
    property    ClassName: string read FClassName;
  end;

  { TTestCaseClass — class-of reference used by RegisterTest. }
  TTestCaseClass = class of TTestCase;

  { ThreadedAttribute — apply [Threaded] to a TTestCase subclass to signal
    the test runner to execute that suite in a dedicated subprocess, enabling
    parallel execution of independent test suites. }
  ThreadedAttribute = class(TCustomAttribute)
  end;

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

  { EIgnoredTest — raised by Ignore() to signal the runner to skip the
    test and record it as ignored rather than failed or errored. }
  EIgnoredTest = class(TObject)
  private
    FMessage: string;
  public
    constructor Create(AMessage: string);
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

procedure TAssert.AssertTrue(AMsg: string; ACondition: Boolean);
begin
  if not ACondition then
    Self.Fail(AMsg);
end;

procedure TAssert.AssertTrue(ACondition: Boolean);
begin
  if not ACondition then
    Self.Fail('AssertTrue failed');
end;

procedure TAssert.AssertFalse(AMsg: string; ACondition: Boolean);
begin
  if ACondition then
    Self.Fail(AMsg);
end;

procedure TAssert.AssertFalse(ACondition: Boolean);
begin
  if ACondition then
    Self.Fail('AssertFalse failed');
end;

procedure TAssert.AssertEquals(AMsg: string; AExpected, AActual: Integer);
begin
  if AExpected <> AActual then
    Self.Fail(AMsg + ' Expected: ' + IntToStr(AExpected)
                   + '  Actual: '  + IntToStr(AActual));
end;

procedure TAssert.AssertEquals(AExpected, AActual: Integer);
begin
  if AExpected <> AActual then
    Self.Fail('Expected: ' + IntToStr(AExpected)
              + '  Actual: '  + IntToStr(AActual));
end;

procedure TAssert.AssertEquals(AMsg: string; AExpected, AActual: Int64);
begin
  if AExpected <> AActual then
    Self.Fail(AMsg + ' Expected: ' + Int64ToStr(AExpected)
                   + '  Actual: '  + Int64ToStr(AActual));
end;

procedure TAssert.AssertEquals(AExpected, AActual: Int64);
begin
  if AExpected <> AActual then
    Self.Fail('Expected: ' + Int64ToStr(AExpected)
              + '  Actual: '  + Int64ToStr(AActual));
end;

procedure TAssert.AssertEquals(AMsg: string; AExpected, AActual: string);
begin
  if AExpected <> AActual then
    Self.Fail(AMsg + ' Expected: "' + AExpected + '"  Actual: "' + AActual + '"');
end;

procedure TAssert.AssertEquals(AExpected, AActual: string);
begin
  if AExpected <> AActual then
    Self.Fail('Expected: "' + AExpected + '"  Actual: "' + AActual + '"');
end;

procedure TAssert.AssertEquals(AMsg: string; AExpected, AActual: Pointer);
begin
  if AExpected <> AActual then
    Self.Fail(AMsg + ' Expected and actual pointers differ');
end;

procedure TAssert.AssertEquals(AExpected, AActual: Pointer);
begin
  if AExpected <> AActual then
    Self.Fail('Expected and actual pointers differ');
end;

procedure TAssert.AssertEquals(AMsg: string; AExpected, AActual: Boolean);
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

procedure TAssert.AssertEquals(AExpected, AActual: Boolean);
var
  ExpStr, ActStr: string;
begin
  if AExpected <> AActual then
  begin
    if AExpected then ExpStr := 'True' else ExpStr := 'False';
    if AActual   then ActStr := 'True' else ActStr := 'False';
    Self.Fail('Expected: ' + ExpStr + '  Actual: ' + ActStr);
  end;
end;

procedure TAssert.AssertNotEquals(AMsg: string; AExpected, AActual: Integer);
begin
  if AExpected = AActual then
    Self.Fail(AMsg + ' Expected values to differ, both are: ' + IntToStr(AActual));
end;

procedure TAssert.AssertNotEquals(AExpected, AActual: Integer);
begin
  if AExpected = AActual then
    Self.Fail('Expected values to differ, both are: ' + IntToStr(AActual));
end;

procedure TAssert.AssertNotEquals(AMsg: string; AExpected, AActual: Int64);
begin
  if AExpected = AActual then
    Self.Fail(AMsg + ' Expected values to differ, both are: ' + Int64ToStr(AActual));
end;

procedure TAssert.AssertNotEquals(AExpected, AActual: Int64);
begin
  if AExpected = AActual then
    Self.Fail('Expected values to differ, both are: ' + Int64ToStr(AActual));
end;

procedure TAssert.AssertNotEquals(AMsg: string; AExpected, AActual: string);
begin
  if AExpected = AActual then
    Self.Fail(AMsg + ' Expected values to differ, both are: "' + AActual + '"');
end;

procedure TAssert.AssertNotEquals(AExpected, AActual: string);
begin
  if AExpected = AActual then
    Self.Fail('Expected values to differ, both are: "' + AActual + '"');
end;

procedure TAssert.AssertNotEquals(AMsg: string; AExpected, AActual: Boolean);
var S: string;
begin
  if AExpected = AActual then
  begin
    if AActual then S := 'True' else S := 'False';
    Self.Fail(AMsg + ' Expected values to differ, both are: ' + S);
  end;
end;

procedure TAssert.AssertNotEquals(AExpected, AActual: Boolean);
var S: string;
begin
  if AExpected = AActual then
  begin
    if AActual then S := 'True' else S := 'False';
    Self.Fail('Expected values to differ, both are: ' + S);
  end;
end;

procedure TAssert.AssertNotEquals(AMsg: string; AExpected, AActual: Pointer);
begin
  if AExpected = AActual then
    Self.Fail(AMsg + ' Expected pointers to differ');
end;

procedure TAssert.AssertNotEquals(AExpected, AActual: Pointer);
begin
  if AExpected = AActual then
    Self.Fail('Expected pointers to differ');
end;

procedure TAssert.AssertContains(AMsg: string; const ASubstring, AHaystack: string);
begin
  if Pos(ASubstring, AHaystack) < 0 then
    Self.Fail(AMsg + ' Expected "' + ASubstring + '" to appear in: "' + AHaystack + '"');
end;

procedure TAssert.AssertContains(const ASubstring, AHaystack: string);
begin
  if Pos(ASubstring, AHaystack) < 0 then
    Self.Fail('Expected "' + ASubstring + '" to appear in: "' + AHaystack + '"');
end;

procedure TAssert.AssertNotNull(AMsg: string; AObject: TObject);
begin
  if AObject = nil then
    Self.Fail(AMsg + ' Expected non-nil object');
end;

procedure TAssert.AssertNotNull(AObject: TObject);
begin
  if AObject = nil then
    Self.Fail('Expected non-nil object');
end;

procedure TAssert.AssertNull(AMsg: string; AObject: TObject);
begin
  if AObject <> nil then
    Self.Fail(AMsg + ' Expected nil object');
end;

procedure TAssert.AssertNull(AObject: TObject);
begin
  if AObject <> nil then
    Self.Fail('Expected nil object');
end;

procedure TAssert.AssertNotNil(AMsg: string; APtr: Pointer);
begin
  if APtr = nil then
    Self.Fail(AMsg + ' Expected non-nil pointer');
end;

procedure TAssert.AssertNotNil(APtr: Pointer);
begin
  if APtr = nil then
    Self.Fail('Expected non-nil pointer');
end;

procedure TAssert.AssertSame(AMsg: string; AExpected, AActual: TObject);
begin
  if AExpected <> AActual then
    Self.Fail(AMsg + ' Expected the same object instance');
end;

procedure TAssert.AssertSame(AExpected, AActual: TObject);
begin
  if AExpected <> AActual then
    Self.Fail('Expected the same object instance');
end;

procedure TAssert.Fail(AMsg: string);
begin
  raise EAssertionFailed.Create(AMsg);
end;

procedure TAssert.Ignore(AMsg: string);
begin
  raise EIgnoredTest.Create(AMsg);
end;

{ -----------------------------------------------------------------------
  TTestCase
  ----------------------------------------------------------------------- }

constructor TTestCase.Create(AName: string);
begin
  inherited Create();
  Self.FName      := AName;
  Self.FClassName := '';
end;

procedure TTestCase.SetClassName(AClassName: string);
begin
  Self.FClassName := AClassName;
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
  Run();
end;

procedure TTestCase.Run(AResult: TTestResult);
var
  Outcome: string;
begin
  AResult.StartTest(Self.FClassName, Self.FName);
  Outcome := 'OK';
  try
    Self.SetUp();
    try
      try
        Self.RunTest();
      except
        on E: EAssertionFailed do
        begin
          Outcome := 'FAIL';
          AResult.AddFailure(Self.FName, E.ToString());
        end;
        on E: EIgnoredTest do
        begin
          Outcome := 'IGNORED';
          AResult.AddIgnored(Self.FName, E.FMessage);
        end;
        on E: Exception do
        begin
          Outcome := 'ERROR';
          AResult.AddError(Self.FName, E.ClassName + ': ' + E.Message);
        end;
        on E: TObject do
        begin
          Outcome := 'ERROR';
          AResult.AddError(Self.FName, 'Unhandled exception: ' + E.ClassName);
        end;
      end;
    finally
      Self.TearDown();
    end;
  finally
    AResult.EndTest(Outcome);
  end;
end;

{ -----------------------------------------------------------------------
  TTestResult
  ----------------------------------------------------------------------- }

constructor TTestResult.Create;
begin
  inherited Create();
  Self.FNumberOfTests    := 0;
  Self.FNumberOfFailures := 0;
  Self.FNumberOfErrors   := 0;
  Self.FNumberOfIgnored  := 0;
  Self.FFailureList      := TList<String>.Create();
  Self.FErrorList        := TList<String>.Create();
  Self.FVerbose          := False;
  Self.FCurrentClassName := '';
  Self.FCurrentTestName  := '';
end;

procedure TTestResult.StartTest(AClassName, ATestName: string);
begin
  Self.FNumberOfTests    := Self.FNumberOfTests + 1;
  Self.FCurrentClassName := AClassName;
  Self.FCurrentTestName  := ATestName;
  if Self.FVerbose then
    Write(AClassName + '.' + ATestName + ' ... ');
end;

procedure TTestResult.EndTest(AOutcome: string);
begin
  if Self.FVerbose then
    WriteLn(AOutcome);
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

procedure TTestResult.AddIgnored(AName, AMessage: string);
begin
  Self.FNumberOfIgnored := Self.FNumberOfIgnored + 1;
end;

procedure TTestResult.MergeFrom(ASource: TTestResult);
var I: Integer;
begin
  Self.FNumberOfTests    := Self.FNumberOfTests    + ASource.FNumberOfTests;
  Self.FNumberOfFailures := Self.FNumberOfFailures + ASource.FNumberOfFailures;
  Self.FNumberOfErrors   := Self.FNumberOfErrors   + ASource.FNumberOfErrors;
  Self.FNumberOfIgnored  := Self.FNumberOfIgnored  + ASource.FNumberOfIgnored;
  for I := 0 to ASource.FFailureList.Count - 1 do
    Self.FFailureList.Add(ASource.FFailureList.Get(I));
  for I := 0 to ASource.FErrorList.Count - 1 do
    Self.FErrorList.Add(ASource.FErrorList.Get(I));
end;

function TTestResult.Summary: string;
begin
  if (Self.FNumberOfFailures = 0) and (Self.FNumberOfErrors = 0) then
  begin
    Result := 'OK (' + IntToStr(Self.FNumberOfTests) + ' tests';
    if Self.FNumberOfIgnored > 0 then
      Result := Result + ', ' + IntToStr(Self.FNumberOfIgnored) + ' ignored';
    Result := Result + ')';
  end
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
  inherited Create();
  Self.FMessage := AMessage;
end;

function EAssertionFailed.ToString: string;
begin
  Result := Self.FMessage;
end;

constructor EIgnoredTest.Create(AMessage: string);
begin
  inherited Create();
  Self.FMessage := AMessage;
end;

{ -----------------------------------------------------------------------
  Global registry
  ----------------------------------------------------------------------- }

procedure RegisterTest(ATestClass: TTestCaseClass);
begin
  if GRegistry = nil then
    GRegistry := TStringList.Create();
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
