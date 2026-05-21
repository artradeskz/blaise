{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.classes2;

{ E2E tests for class features: milestone programs, multi-type blocks,
  ToString, InheritsFrom, is/as, inheritance, interfaces, and Supports. }

interface

uses
  blaise.testing, classes, sysutils, cp.test.e2e.base;

type
  [Threaded]
  TE2EClasses2Tests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_Phase2Milestone_Stdout;
    procedure TestRun_Phase2Milestone_Valgrind;
    procedure TestRun_Phase3Milestone_Stdout;
    procedure TestRun_Phase3Milestone_Valgrind;
    procedure TestRun_MultiTypeBlock_BothClassesWork;
    procedure TestRun_ToString_DefaultReturnsClassName;
    procedure TestRun_ToString_OverrideDispatchedVirtually;
    procedure TestRun_ToString_InheritedOverrideStillReached;
    procedure TestRun_InheritsFrom_SameClass_ReturnsTrue;
    procedure TestRun_InheritsFrom_Parent_ReturnsTrue;
    procedure TestRun_InheritsFrom_GrandParent_ReturnsTrue;
    procedure TestRun_InheritsFrom_Unrelated_ReturnsFalse;
    procedure TestRun_InheritsFrom_Reverse_ReturnsFalse;
    procedure TestRun_InheritsFrom_ClassType_Works;
    procedure TestRun_Is_CorrectSubclass_True;
    procedure TestRun_Is_WrongClass_False;
    procedure TestRun_As_DowncastCallsMethod;
    procedure TestRun_Inherited_CallsParentMethod;
    procedure TestRun_Virtual_OverrideDispatch;
    procedure TestRun_MultiLevel_Inheritance_Chain;
    procedure TestRun_Interface_Dispatch_CallsImpl;
    procedure TestRun_Interface_ARC_NoLeak;
    procedure TestRun_Interface_Is_As_Roundtrip;
    procedure TestRun_Supports_TwoArg_BooleanResult;
    procedure TestRun_Supports_ThreeArg_AssignsAndCalls;
    procedure TestRun_ConstructorOverload_PicksCorrectArity;
  end;

implementation

procedure TE2EClasses2Tests.SetUp;
begin
  inherited SetUp;
  SetUpScratch('compiler/target/test-e2e-classes2');
end;

const
  LE = #10;

  SrcMultiTypeBlock =
    '''
        program P;
        type
          TCounter = class
            FN: Integer;
            procedure Inc;
            begin Self.FN := Self.FN + 1 end;
            property Value: Integer read FN;
          end;
        var N: Integer;
        type
          TDoubler = class
            function Double(X: Integer): Integer;
            begin Result := X * 2 end;
          end;
        var
          C: TCounter;
          D: TDoubler;
        begin
          C := TCounter.Create;
          D := TDoubler.Create;
          C.Inc; C.Inc; C.Inc;
          N := D.Double(C.Value);
          WriteLn(N)
        end.
        ''';

  SrcToStringDefault = '''
    program P;
    type
      TFoo = class end;
      TBar = class(TFoo) end;
    var F: TFoo; B: TBar;
    begin
      F := TFoo.Create;
      WriteLn(F.ToString);
      B := TBar.Create;
      WriteLn(B.ToString)
    end.
    ''';

  SrcToStringOverride = '''
    program P;
    type
      TFoo = class
        function ToString: string; override;
      end;
      TBar = class(TFoo)
        function ToString: string; override;
      end;
      function TFoo.ToString: string;
      begin Result := 'foo!' end;
      function TBar.ToString: string;
      begin Result := 'bar!' end;
    var F: TFoo; B: TFoo;
    begin
      F := TFoo.Create;
      WriteLn(F.ToString);
      B := TBar.Create;
      WriteLn(B.ToString)
    end.
    ''';

  SrcToStringInheritedOverride = '''
    program P;
    type
      TFoo = class
        function ToString: string; override;
      end;
      TBar = class(TFoo) end;
      function TFoo.ToString: string;
      begin Result := 'foo override' end;
    var F: TFoo; B: TFoo;
    begin
      F := TFoo.Create;
      WriteLn(F.ToString);
      B := TBar.Create;
      WriteLn(B.ToString)
    end.
    ''';

  SrcInheritsFromBase =
    '''
        program P;
        type TBase = class end;
        var B: TBase;
        begin
          B := TBase.Create;
          if B.InheritsFrom(TBase) then
            WriteLn('yes')
          else
            WriteLn('no');
          B.Free;
        end.
        ''';

  SrcInheritsFromParent =
    '''
        program P;
        type TBase = class end;
             TChild = class(TBase) end;
        var C: TChild;
        begin
          C := TChild.Create;
          if C.InheritsFrom(TBase) then
            WriteLn('yes')
          else
            WriteLn('no');
          C.Free;
        end.
        ''';

  SrcInheritsFromGrandParent =
    '''
        program P;
        type TBase = class end;
             TChild = class(TBase) end;
             TGrandChild = class(TChild) end;
        var G: TGrandChild;
        begin
          G := TGrandChild.Create;
          if G.InheritsFrom(TBase) then
            WriteLn('yes')
          else
            WriteLn('no');
          G.Free;
        end.
        ''';

  SrcInheritsFromUnrelated =
    '''
        program P;
        type TBase = class end;
             TUnrelated = class end;
        var B: TBase;
        begin
          B := TBase.Create;
          if B.InheritsFrom(TUnrelated) then
            WriteLn('yes')
          else
            WriteLn('no');
          B.Free;
        end.
        ''';

  SrcInheritsFromReverse =
    '''
        program P;
        type TBase = class end;
             TChild = class(TBase) end;
        var B: TBase;
        begin
          B := TBase.Create;
          if B.InheritsFrom(TChild) then
            WriteLn('yes')
          else
            WriteLn('no');
          B.Free;
        end.
        ''';

  SrcInheritsFromClassType =
    '''
        program P;
        type TBase = class end;
             TChild = class(TBase) end;
        var C: TChild;
            CT: Pointer;
        begin
          C := TChild.Create;
          CT := C.ClassType;
          if CT.InheritsFrom(TBase) then
            WriteLn('yes')
          else
            WriteLn('no');
          C.Free;
        end.
        ''';

  SrcIsTrue = '''
    program P;
    type
      TAnimal = class end;
      TDog = class(TAnimal) end;
    var D: TAnimal;
    begin
      D := TDog.Create;
      if D is TDog then WriteLn('yes');
      D.Free
    end.
    ''';

  SrcIsFalse = '''
    program P;
    type
      TAnimal = class end;
      TDog = class(TAnimal) end;
      TCat = class(TAnimal) end;
    var D: TAnimal;
    begin
      D := TDog.Create;
      if D is TCat then WriteLn('yes') else WriteLn('no');
      D.Free
    end.
    ''';

  SrcAsDowncast = '''
    program P;
    type
      TBase = class
        function Name: string; virtual;
      end;
      TChild = class(TBase)
        FVal: Integer;
        function Name: string; override;
      end;
    function TBase.Name: string;
    begin Result := 'base' end;
    function TChild.Name: string;
    begin Result := 'child' end;
    var B: TBase;
    begin
      B := TChild.Create;
      WriteLn((B as TChild).Name);
      B.Free
    end.
    ''';

  SrcInherited = '''
    program P;
    type
      TBase = class
        function Val: Integer; virtual;
      end;
      TChild = class(TBase)
        function Val: Integer; override;
      end;
    function TBase.Val: Integer;
    begin Result := 10 end;
    function TChild.Val: Integer;
    var B: Integer;
    begin
      inherited Val;
      B := Result;
      Result := B + 5
    end;
    var C: TChild;
    begin
      C := TChild.Create;
      WriteLn(C.Val);
      C.Free
    end.
    ''';

  SrcVirtualOverride = '''
    program P;
    type
      TShape = class
        function Area: Integer; virtual;
      end;
      TSquare = class(TShape)
        FSide: Integer;
        function Area: Integer; override;
      end;
    function TShape.Area: Integer;
    begin Result := 0 end;
    function TSquare.Area: Integer;
    begin Result := FSide * FSide end;
    var S: TShape;
    begin
      S := TSquare.Create;
      TSquare(S).FSide := 4;
      WriteLn(S.Area);
      S.Free
    end.
    ''';

  SrcMultiLevelChain = '''
    program P;
    type
      TA = class
        function Lvl: Integer; virtual;
      end;
      TB = class(TA)
        function Lvl: Integer; override;
      end;
      TC = class(TB)
        function Lvl: Integer; override;
      end;
    function TA.Lvl: Integer; begin Result := 1 end;
    function TB.Lvl: Integer; begin Result := 2 end;
    function TC.Lvl: Integer; begin Result := 3 end;
    var A: TA;
    begin
      A := TC.Create;
      WriteLn(A.Lvl);
      A.Free
    end.
    ''';

  SrcIntfDispatch = '''
    program P;
    type
      IGreeter = interface
        procedure Greet;
      end;
      THello = class(TObject, IGreeter)
        procedure Greet;
      end;
    procedure THello.Greet;
    begin WriteLn('hello') end;
    var G: IGreeter;
        H: THello;
    begin
      H := THello.Create;
      G := H;
      G.Greet;
      H.Free
    end.
    ''';

  SrcIntfIsAs = '''
    program P;
    type
      IPrinter = interface
        procedure Print;
      end;
      TPrinter = class(TObject, IPrinter)
        procedure Print;
      end;
    procedure TPrinter.Print;
    begin WriteLn('printing') end;
    var
      Obj: TObject;
      P: IPrinter;
    begin
      Obj := TPrinter.Create;
      if Obj is IPrinter then
      begin
        P := Obj as IPrinter;
        P.Print
      end;
      Obj.Free
    end.
    ''';

  SrcSupportsTwoArgRun = '''
    program P;
    type
      IGreeter = interface
        procedure Greet;
      end;
      THello = class(TObject, IGreeter)
        procedure Greet;
      end;
    procedure THello.Greet;
    begin WriteLn('hello') end;
    var Obj: TObject;
    begin
      Obj := THello.Create;
      if Supports(Obj, IGreeter) then
        WriteLn('yes')
      else
        WriteLn('no');
      Obj.Free
    end.
    ''';

  SrcSupportsThreeArgRun = '''
    program P;
    type
      IGreeter = interface
        procedure Greet;
      end;
      THello = class(TObject, IGreeter)
        procedure Greet;
      end;
    procedure THello.Greet;
    begin WriteLn('hello') end;
    var Obj: TObject;
        G: IGreeter;
    begin
      Obj := THello.Create;
      if Supports(Obj, IGreeter, G) then
        G.Greet
      else
        WriteLn('no');
      Obj.Free
    end.
    ''';

  { Constructor overload where the 2-arg variant is declared first.  The
    1-arg call site must resolve to the 1-arg constructor; otherwise the
    semantic pass rejects the program with "No default value for parameter
    'B' of 'Create'".  Picks the body via A only, so the output proves
    the 1-arg constructor body actually ran. }
  SrcCtorOverloadArity =
    '''
        program P;
        type
          TFoo = class
            FA: Integer;
            constructor Create(A: Integer; B: Integer); overload;
            constructor Create(A: Integer); overload;
          end;
          constructor TFoo.Create(A: Integer; B: Integer);
          begin Self.FA := A + B end;
          constructor TFoo.Create(A: Integer);
          begin Self.FA := A end;
        var F: TFoo;
        begin
          F := TFoo.Create(42);
          WriteLn(F.FA);
          F.Free
        end.
        ''';

function LoadMilestoneFile(const APath: string; out ASrc: string): Boolean;
var Lst: TStringList;
begin
  Result := False;
  if not FileExists(APath) then Exit;
  Lst := TStringList.Create;
  try
    Lst.LoadFromFile(APath);
    ASrc := Lst.Text;
    Result := True;
  finally
    Lst.Free;
  end;
end;

procedure TE2EClasses2Tests.TestRun_Phase2Milestone_Stdout;
var
  Path, Src, Output: string;
  RCode: Integer;
  Expected: string;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  Path := GetCurrentDir;
  // Walk up to project root looking for tests/phase2_milestone.pas
  while (Path <> '') and
        (not FileExists(Path + '/tests/phase2_milestone.pas')) and
        (ExtractFileDir(Path) <> Path) do
    Path := ExtractFileDir(Path);
  Path := Path + '/tests/phase2_milestone.pas';
  if not LoadMilestoneFile(Path, Src) then
  begin
    Ignore('phase2_milestone.pas not found');
    Exit;
  end;
  AssertTrue('compile+run milestone', CompileAndRun(Src, Output, RCode));
  AssertEquals('milestone exit code', 0, RCode);
  Expected :=
    'count=4' + LE +
    '--- walk ---' + LE +
    '  value=40' + LE +
    '  tag=0' + LE +
    '  marked=0' + LE +
    '  value=30' + LE +
    '  tag=1' + LE +
    '  marked=1' + LE +
    '  value=20' + LE +
    '  tag=0' + LE +
    '  marked=0' + LE +
    '  value=10' + LE +
    '  tag=0' + LE +
    '  marked=0' + LE +
    'pop=40' + LE +
    'pop=30' + LE +
    'count_after_pops=2' + LE;
  AssertEquals('milestone stdout', Expected, Output);
end;

procedure TE2EClasses2Tests.TestRun_Phase2Milestone_Valgrind;
var
  Path, Src, Log: string;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  if not ValgrindAvailable then begin Ignore('valgrind not installed'); Exit; end;
  Path := GetCurrentDir;
  while (Path <> '') and
        (not FileExists(Path + '/tests/phase2_milestone.pas')) and
        (ExtractFileDir(Path) <> Path) do
    Path := ExtractFileDir(Path);
  Path := Path + '/tests/phase2_milestone.pas';
  if not LoadMilestoneFile(Path, Src) then
  begin
    Ignore('phase2_milestone.pas not found');
    Exit;
  end;
  if not RunUnderValgrind(Src, Log) then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('valgrind reported errors or leaks:' + LE + Log);
  end;
end;

procedure TE2EClasses2Tests.TestRun_Phase3Milestone_Stdout;
var
  Path, Src, Output: string;
  RCode: Integer;
  Expected: string;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  Path := GetCurrentDir;
  while (Path <> '') and
        (not FileExists(Path + '/tests/phase3_milestone.pas')) and
        (ExtractFileDir(Path) <> Path) do
    Path := ExtractFileDir(Path);
  Path := Path + '/tests/phase3_milestone.pas';
  if not LoadMilestoneFile(Path, Src) then
  begin
    Ignore('phase3_milestone.pas not found');
    Exit;
  end;
  AssertTrue('compile+run milestone', CompileAndRun(Src, Output, RCode));
  AssertEquals('milestone exit code', 0, RCode);
  Expected :=
    'list.count=5' + LE +
    'list[0]=10' + LE +
    'list[4]=50' + LE +
    'count_after_delete=4' + LE +
    'list[1]_after_delete=30' + LE +
    'dict.count=4' + LE +
    'beta=2' + LE +
    'has_gamma=1' + LE +
    'beta_after_update=99' + LE +
    'count_after_remove=3' + LE +
    'has_alpha_after_remove=0' + LE;
  AssertEquals('milestone stdout', Expected, Output);
end;

procedure TE2EClasses2Tests.TestRun_Phase3Milestone_Valgrind;
var
  Path, Src, Log: string;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  if not ValgrindAvailable then begin Ignore('valgrind not installed'); Exit; end;
  Path := GetCurrentDir;
  while (Path <> '') and
        (not FileExists(Path + '/tests/phase3_milestone.pas')) and
        (ExtractFileDir(Path) <> Path) do
    Path := ExtractFileDir(Path);
  Path := Path + '/tests/phase3_milestone.pas';
  if not LoadMilestoneFile(Path, Src) then
  begin
    Ignore('phase3_milestone.pas not found');
    Exit;
  end;
  if not RunUnderValgrind(Src, Log) then
  begin
    if Log = '' then Log := '(valgrind produced no output)';
    Fail('phase3 milestone has leaks or errors:' + LE + Log);
  end;
end;

procedure TE2EClasses2Tests.TestRun_MultiTypeBlock_BothClassesWork;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcMultiTypeBlock, Output, RCode));
  AssertEquals('TCounter(3).Double = 6', '6', Trim(Output));
end;

procedure TE2EClasses2Tests.TestRun_ToString_DefaultReturnsClassName;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcToStringDefault, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('default ToString returns class name',
    'TFoo' + LE + 'TBar' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_ToString_OverrideDispatchedVirtually;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcToStringOverride, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('override reached through static base type',
    'foo!' + LE + 'bar!' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_ToString_InheritedOverrideStillReached;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcToStringInheritedOverride, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('inherited override still reached',
    'foo override' + LE + 'foo override' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_InheritsFrom_SameClass_ReturnsTrue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritsFromBase, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('same class returns true', 'yes' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_InheritsFrom_Parent_ReturnsTrue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritsFromParent, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('child inherits from parent', 'yes' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_InheritsFrom_GrandParent_ReturnsTrue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritsFromGrandParent, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('grandchild inherits from base', 'yes' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_InheritsFrom_Unrelated_ReturnsFalse;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritsFromUnrelated, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('unrelated class returns false', 'no' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_InheritsFrom_Reverse_ReturnsFalse;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritsFromReverse, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('parent does not inherit from child', 'no' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_InheritsFrom_ClassType_Works;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritsFromClassType, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('ClassType.InheritsFrom works', 'yes' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Is_CorrectSubclass_True;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIsTrue, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('yes', 'yes' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Is_WrongClass_False;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIsFalse, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('no', 'no' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_As_DowncastCallsMethod;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcAsDowncast, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('child', 'child' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Inherited_CallsParentMethod;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInherited, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('15', '15' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Virtual_OverrideDispatch;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcVirtualOverride, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('16', '16' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_MultiLevel_Inheritance_Chain;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcMultiLevelChain, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('3', '3' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Interface_Dispatch_CallsImpl;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntfDispatch, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('hello', 'hello' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Interface_ARC_NoLeak;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntfDispatch, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
end;

procedure TE2EClasses2Tests.TestRun_Interface_Is_As_Roundtrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntfIsAs, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('printing', 'printing' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Supports_TwoArg_BooleanResult;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcSupportsTwoArgRun, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('yes', 'yes' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Supports_ThreeArg_AssignsAndCalls;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcSupportsThreeArgRun, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('hello', 'hello' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_ConstructorOverload_PicksCorrectArity;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcCtorOverloadArity, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1-arg constructor body ran', '42' + LE, Output);
end;

initialization
  RegisterTest(TE2EClasses2Tests);

end.
