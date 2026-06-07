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
    procedure TestRun_Inherited_VarParam_PassesByReference;
    procedure TestRun_Virtual_OverrideDispatch;
    procedure TestRun_MultiLevel_Inheritance_Chain;
    procedure TestRun_Interface_Dispatch_CallsImpl;
    procedure TestRun_Interface_ARC_NoLeak;
    procedure TestRun_Interface_GlobalNil_LinksAndRuns;
    procedure TestRun_Interface_Is_As_Roundtrip;
    procedure TestRun_Interface_MethodParam_ByValue_Dispatches;
    procedure TestRun_Supports_TwoArg_BooleanResult;
    procedure TestRun_Supports_ThreeArg_AssignsAndCalls;
    procedure TestRun_ConstructorOverload_PicksCorrectArity;
    procedure TestRun_MethodReadsProgramGlobal;
    procedure TestRun_VarParam_ClassFields_WritebackVisible;
    { Name-resolution priority for unqualified calls inside a class
      method.  Adjacent-level distinctions, top wins:
        1. local vars / parameters
        2. implicit Self.member (incl. inherited via class chain)
        3. program-level / uses-clause unit exports
      Sub-distinctions inside level 2 (own vs parent), and level 3
      (program vs uses-clause), depend on orthogonal mechanisms
      (virtual dispatch; Blaise's duplicate-identifier rule for
      program-level shadowing of unit exports).  They're worth
      pinning separately when their own bugs surface.

      Cross-unit visibility (private skipped, protected accessible to
      subclasses) is a follow-up commit. }
    procedure TestRun_LocalVar_ShadowsOwnMethod;
    procedure TestRun_ParentMethod_ShadowsProgramProc;
    { Explicit qualifiers are unambiguous paths — the priority order
      does not apply.  Self.X must hit a class member; inherited X
      must hit a parent method.  Neither falls through to unit-level. }
    procedure TestRun_ExplicitSelf_AlwaysClassMember;
    procedure TestRun_InheritedCall_AlwaysParent;
    { Regression (issue #64): interface-typed field with same name as a
      program-level global of a different type. }
    procedure TestRun_InterfaceField_ShadowsGlobal_Dispatches;
  end;

implementation

procedure TE2EClasses2Tests.SetUp;
begin
  inherited SetUp();
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
          C := TCounter.Create();
          D := TDoubler.Create();
          C.Inc(); C.Inc(); C.Inc();
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
      F := TFoo.Create();
      WriteLn(F.ToString());
      B := TBar.Create();
      WriteLn(B.ToString())
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
      F := TFoo.Create();
      WriteLn(F.ToString());
      B := TBar.Create();
      WriteLn(B.ToString())
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
      F := TFoo.Create();
      WriteLn(F.ToString());
      B := TBar.Create();
      WriteLn(B.ToString())
    end.
    ''';

  SrcInheritsFromBase =
    '''
        program P;
        type TBase = class end;
        var B: TBase;
        begin
          B := TBase.Create();
          if B.InheritsFrom(TBase) then
            WriteLn('yes')
          else
            WriteLn('no');
          B.Free();
        end.
        ''';

  SrcInheritsFromParent =
    '''
        program P;
        type TBase = class end;
             TChild = class(TBase) end;
        var C: TChild;
        begin
          C := TChild.Create();
          if C.InheritsFrom(TBase) then
            WriteLn('yes')
          else
            WriteLn('no');
          C.Free();
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
          G := TGrandChild.Create();
          if G.InheritsFrom(TBase) then
            WriteLn('yes')
          else
            WriteLn('no');
          G.Free();
        end.
        ''';

  SrcInheritsFromUnrelated =
    '''
        program P;
        type TBase = class end;
             TUnrelated = class end;
        var B: TBase;
        begin
          B := TBase.Create();
          if B.InheritsFrom(TUnrelated) then
            WriteLn('yes')
          else
            WriteLn('no');
          B.Free();
        end.
        ''';

  SrcInheritsFromReverse =
    '''
        program P;
        type TBase = class end;
             TChild = class(TBase) end;
        var B: TBase;
        begin
          B := TBase.Create();
          if B.InheritsFrom(TChild) then
            WriteLn('yes')
          else
            WriteLn('no');
          B.Free();
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
          C := TChild.Create();
          CT := C.ClassType;
          if CT.InheritsFrom(TBase) then
            WriteLn('yes')
          else
            WriteLn('no');
          C.Free();
        end.
        ''';

  SrcIsTrue = '''
    program P;
    type
      TAnimal = class end;
      TDog = class(TAnimal) end;
    var D: TAnimal;
    begin
      D := TDog.Create();
      if D is TDog then WriteLn('yes');
      D.Free()
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
      D := TDog.Create();
      if D is TCat then WriteLn('yes') else WriteLn('no');
      D.Free()
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
      B := TChild.Create();
      WriteLn((B as TChild).Name());
      B.Free()
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
      inherited Val();
      B := Result;
      Result := B + 5
    end;
    var C: TChild;
    begin
      C := TChild.Create();
      WriteLn(C.Val());
      C.Free()
    end.
    ''';

  { Regression: `inherited Foo(X)` where the parent method has a var/out param.
    The inherited-call arg loop had no var-param branch, so it passed the
    loaded VALUE (a `w`) where the callee expects an address (`l`) — the parent
    then dereferenced a small integer as a pointer and the program crashed. }
  SrcInheritedVarParam = '''
    program P;
    type
      TBase = class
        procedure Bump(var X: Integer); virtual;
      end;
      TDer = class(TBase)
        procedure Bump(var X: Integer); override;
      end;
    procedure TBase.Bump(var X: Integer);
    begin X := X + 10 end;
    procedure TDer.Bump(var X: Integer);
    begin
      inherited Bump(X);
      X := X + 1
    end;
    var
      D: TDer;
      N: Integer;
    begin
      D := TDer.Create();
      N := 5;
      D.Bump(N);
      WriteLn(N);
      D.Free()
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
      S := TSquare.Create();
      TSquare(S).FSide := 4;
      WriteLn(S.Area());
      S.Free()
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
      A := TC.Create();
      WriteLn(A.Lvl());
      A.Free()
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
      H := THello.Create();
      G := H;
      G.Greet();
      H.Free()
    end.
    ''';

  { Regression: assigning nil to an interface-typed GLOBAL variable.  An
    interface global is emitted as a fat-pointer pair ($G_obj / $G_itab); the
    `:= nil` path previously fell through to a scalar store against a bare $G
    symbol with no data definition, causing an undefined-reference link error.
    Must be an e2e test: the IR-only harness never links, so it cannot see it. }
  SrcIntfGlobalNil = '''
    program P;
    type
      ISpeaker = interface
        procedure Speak;
      end;
      TSpeaker = class(TObject, ISpeaker)
        procedure Speak;
      end;
    procedure TSpeaker.Speak;
    begin WriteLn('spoke') end;
    var G: ISpeaker;
    begin
      G := TSpeaker.Create();
      G.Speak();
      G := nil;
      WriteLn('after nil')
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
      Obj := TPrinter.Create();
      if Obj is IPrinter then
      begin
        P := Obj as IPrinter;
        P.Print()
      end;
      Obj.Free()
    end.
    ''';

  { Regression: a class METHOD taking a by-value interface parameter.  The
    method-codegen path emitted the param as a single `w` slot instead of the
    two-slot fat pointer the standalone-routine path uses, so QBE rejected the
    `storel %_par_X` ("invalid type for first operand") and the program failed
    to compile.  The method must receive obj+itab and dispatch through them. }
  SrcIntfMethodParam = '''
    program P;
    type
      IGreeter = interface
        function Greet: Integer;
      end;
      THello = class(TObject, IGreeter)
        function Greet: Integer;
      end;
      TUser = class
        function Use(G: IGreeter): Integer;
      end;
    function THello.Greet: Integer;
    begin Result := 42 end;
    function TUser.Use(G: IGreeter): Integer;
    begin Result := G.Greet() + 1 end;
    var
      H: THello;
      I: IGreeter;
      U: TUser;
    begin
      H := THello.Create();
      I := H;
      U := TUser.Create();
      WriteLn(U.Use(I))
    end.
    ''';

  { Regression (issue #64): class has an interface-typed field 'im' AND the
    program declares a same-named global variable 'im' of the class type.
    Inside the constructor and a method, bare 'im' must resolve to the field
    (Iprinter), not the global (Tmi).  Previously the semantic analyser found
    the global first and reported a type-mismatch. }
  SrcIntfFieldShadowsGlobal = '''
    program P;
    type
      Iprinter = interface
        procedure print;
      end;
      Toutput = class(TObject, Iprinter)
        procedure print;
      end;
      Tmi = class
        im: Iprinter;
        constructor create(am: Iprinter);
        procedure use;
      end;
    procedure Toutput.print;
    begin
      WriteLn('printed');
    end;
    constructor Tmi.Create(am: Iprinter);
    begin
      im := am;
    end;
    procedure Tmi.use;
    begin
      im.print();
    end;
    var
      im: Tmi;
    begin
      im := Tmi.Create(Toutput.Create());
      im.use();
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
      Obj := THello.Create();
      if Supports(Obj, IGreeter) then
        WriteLn('yes')
      else
        WriteLn('no');
      Obj.Free()
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
      Obj := THello.Create();
      if Supports(Obj, IGreeter, G) then
        G.Greet()
      else
        WriteLn('no');
      Obj.Free()
    end.
    ''';

  { Constructor overload where the 2-arg variant is declared first.  The
    1-arg call site must resolve to the 1-arg constructor; otherwise the
    semantic pass rejects the program with "No default value for parameter
    'B' of 'Create'".  Picks the body via A only, so the output proves
    the 1-arg constructor body actually ran. }
  { Regression for issue #43: a class method body must be able to read and
    write a program-level global variable declared above the class type. }
  SrcMethodReadsProgramGlobal =
    '''
        program GlobalAccessBug;
        var
          gValue: Integer;
        type
          TFoo = class
            function GetValue: Integer;
          end;
        function TFoo.GetValue: Integer;
        begin
          Result := gValue
        end;
        var
          Foo: TFoo;
        begin
          gValue := 42;
          Foo := TFoo.Create();
          WriteLn(Foo.GetValue());
          Foo.Free()
        end.
        ''';

  SrcVarParamClassFields =
    '''
        program VarParamClassFields;
        procedure Fill(var V: Int64; var F: Boolean);
        begin
          V := 4096;
          F := True
        end;
        type
          TNode = class
            Value: Int64;
            IsBig: Boolean;
          end;
        var N: TNode;
        begin
          N := TNode.Create();
          Fill(N.Value, N.IsBig);
          WriteLn(N.Value);
          WriteLn(N.IsBig);
          N.Free()
        end.
        ''';

  { ----- Name-resolution priority (Option A: single-program tests).
    Visibility (private / protected across units) is a follow-up. ----- }

  { Level 1 beats level 2: a local procedural-typed variable shadows a
    class method of the same name.  This is the use case in
    blaise.testing.TTestCase.RunTest (`var Run: TRunMethod`). }
  SrcResolve_LocalVar_OverOwnMethod =
    '''
        program ResLocalVar;
        function Helper: Integer;
        begin Result := 42 end;
        type
          TFn  = function: Integer;
          TFoo = class
            function Compute: Integer;
            function Run: Integer;
          end;
        function TFoo.Compute: Integer;
        begin Result := 100 end;
        function TFoo.Run: Integer;
        var Compute: TFn;
        begin
          Compute := @Helper;
          Result  := Compute()
        end;
        var F: TFoo;
        begin
          F := TFoo.Create();
          WriteLn(F.Run());
          F.Free()
        end.
        ''';

  { Level 2 beats level 3: a class method shadows a program-level
    proc.  A subclass with no own method X but with an inherited X
    (and a program-level proc X also in scope) — the unqualified call
    inside the subclass binds to the inherited method, not the
    program-level proc.  Pre-fix, the global lookup ran first and
    bound to the program-level Tag (output '1'); post-fix the
    implicit-Self check finds parent.Tag and wins (output '2'). }
  SrcResolve_ParentMethod_OverProgramProc =
    '''
        program ResParentOverProgram;
        function Tag: Integer;
        begin Result := 1 end;
        type
          TParent = class
            function Tag: Integer;
            function Echo: Integer;
          end;
          TChild = class(TParent)
          end;
        function TParent.Tag: Integer;
        begin Result := 2 end;
        function TParent.Echo: Integer;
        begin Result := Tag() end;
        var C: TChild;
        begin
          C := TChild.Create();
          WriteLn(C.Echo());
          C.Free()
        end.
        ''';

  { `inherited X;` is an explicit qualifier that calls the parent's X
    statically — does NOT go through subclass override, does NOT fall
    through to any program-level X.  Statement form is used because
    Blaise doesn't yet parse `inherited X` in expression context;
    parent's body sets Result, which Child.FromInh returns. }
  SrcResolve_InheritedAlwaysParent =
    '''
        program ResInherited;
        type
          TParent = class
            function Tag: Integer;
          end;
          TChild = class(TParent)
            function Tag: Integer;
            function FromInh: Integer;
          end;
        function TParent.Tag: Integer;
        begin Result := 1 end;
        function TChild.Tag: Integer;
        begin Result := 2 end;
        function TChild.FromInh: Integer;
        begin
          inherited Tag()
        end;
        var C: TChild;
        begin
          C := TChild.Create();
          WriteLn(C.FromInh());
          C.Free()
        end.
        ''';

  { Self.X is an explicit path: it MUST resolve to a member of Self's
    class hierarchy, regardless of any same-named local var that
    would otherwise win in the unqualified priority order. }
  SrcResolve_ExplicitSelf_AlwaysClassMember =
    '''
        program ResExplicitSelf;
        type
          TFoo = class
            function Compute: Integer;
            function Run: Integer;
          end;
        function TFoo.Compute: Integer;
        begin Result := 200 end;
        function TFoo.Run: Integer;
        var Compute: Integer;
        begin
          Compute := 7;
          Result  := Self.Compute()
        end;
        var F: TFoo;
        begin
          F := TFoo.Create();
          WriteLn(F.Run());
          F.Free()
        end.
        ''';


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
          F.Free()
        end.
        ''';

function LoadMilestoneFile(const APath: string; out ASrc: string): Boolean;
var Lst: TStringList;
begin
  Result := False;
  if not FileExists(APath) then Exit;
  Lst := TStringList.Create();
  try
    Lst.LoadFromFile(APath);
    ASrc := Lst.Text;
    Result := True;
  finally
    Lst.Free();
  end;
end;

procedure TE2EClasses2Tests.TestRun_Phase2Milestone_Stdout;
var
  Path, Src, Output: string;
  RCode: Integer;
  Expected: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Path := GetCurrentDir();
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
    '  marked=False' + LE +
    '  value=30' + LE +
    '  tag=1' + LE +
    '  marked=True' + LE +
    '  value=20' + LE +
    '  tag=0' + LE +
    '  marked=False' + LE +
    '  value=10' + LE +
    '  tag=0' + LE +
    '  marked=False' + LE +
    'pop=40' + LE +
    'pop=30' + LE +
    'count_after_pops=2' + LE;
  AssertEquals('milestone stdout', Expected, Output);
end;

procedure TE2EClasses2Tests.TestRun_Phase2Milestone_Valgrind;
var
  Path, Src, Log: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  if not ValgrindAvailable() then begin Ignore('valgrind not installed'); Exit; end;
  Path := GetCurrentDir();
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
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Path := GetCurrentDir();
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
    'has_gamma=True' + LE +
    'beta_after_update=99' + LE +
    'count_after_remove=3' + LE +
    'has_alpha_after_remove=False' + LE;
  AssertEquals('milestone stdout', Expected, Output);
end;

procedure TE2EClasses2Tests.TestRun_Phase3Milestone_Valgrind;
var
  Path, Src, Log: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  if not ValgrindAvailable() then begin Ignore('valgrind not installed'); Exit; end;
  Path := GetCurrentDir();
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
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcMultiTypeBlock, Output, RCode));
  AssertEquals('TCounter(3).Double = 6', '6', Trim(Output));
end;

procedure TE2EClasses2Tests.TestRun_ToString_DefaultReturnsClassName;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcToStringDefault, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('default ToString returns class name',
    'TFoo' + LE + 'TBar' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_ToString_OverrideDispatchedVirtually;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcToStringOverride, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('override reached through static base type',
    'foo!' + LE + 'bar!' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_ToString_InheritedOverrideStillReached;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcToStringInheritedOverride, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('inherited override still reached',
    'foo override' + LE + 'foo override' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_InheritsFrom_SameClass_ReturnsTrue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritsFromBase, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('same class returns true', 'yes' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_InheritsFrom_Parent_ReturnsTrue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritsFromParent, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('child inherits from parent', 'yes' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_InheritsFrom_GrandParent_ReturnsTrue;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritsFromGrandParent, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('grandchild inherits from base', 'yes' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_InheritsFrom_Unrelated_ReturnsFalse;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritsFromUnrelated, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('unrelated class returns false', 'no' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_InheritsFrom_Reverse_ReturnsFalse;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritsFromReverse, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('parent does not inherit from child', 'no' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_InheritsFrom_ClassType_Works;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritsFromClassType, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('ClassType.InheritsFrom works', 'yes' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Is_CorrectSubclass_True;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIsTrue, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('yes', 'yes' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Is_WrongClass_False;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIsFalse, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('no', 'no' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_As_DowncastCallsMethod;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcAsDowncast, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('child', 'child' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Inherited_CallsParentMethod;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInherited, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('15', '15' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Inherited_VarParam_PassesByReference;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcInheritedVarParam, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('5+10+1', '16' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Virtual_OverrideDispatch;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcVirtualOverride, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('16', '16' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_MultiLevel_Inheritance_Chain;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcMultiLevelChain, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('3', '3' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Interface_Dispatch_CallsImpl;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntfDispatch, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('hello', 'hello' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Interface_ARC_NoLeak;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntfDispatch, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
end;

procedure TE2EClasses2Tests.TestRun_Interface_GlobalNil_LinksAndRuns;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntfGlobalNil, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('spoke then after nil',
    'spoke' + LE + 'after nil' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Interface_Is_As_Roundtrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntfIsAs, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('printing', 'printing' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Interface_MethodParam_ByValue_Dispatches;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntfMethodParam, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('greet+1', '43' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Supports_TwoArg_BooleanResult;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcSupportsTwoArgRun, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('yes', 'yes' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_Supports_ThreeArg_AssignsAndCalls;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcSupportsThreeArgRun, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('hello', 'hello' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_ConstructorOverload_PicksCorrectArity;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcCtorOverloadArity, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('1-arg constructor body ran', '42' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_MethodReadsProgramGlobal;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcMethodReadsProgramGlobal, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('global read by method', '42' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_VarParam_ClassFields_WritebackVisible;
var Output: string; RCode: Integer;
begin
  { Regression for bugs.txt BUG-001 — Fill(N.Value, N.IsBig) where N is a
    class reference must address into the heap object, not into the storage
    slot of N itself.  Before the fix the writes landed in unrelated memory
    and the WriteLn calls printed 0 / False. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcVarParamClassFields, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('var-param writeback visible through class field', '4096' + LE + 'True' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_LocalVar_ShadowsOwnMethod;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcResolve_LocalVar_OverOwnMethod, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('local var wins over class method', '42' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_ParentMethod_ShadowsProgramProc;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcResolve_ParentMethod_OverProgramProc, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('inherited method wins over program-level proc', '2' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_ExplicitSelf_AlwaysClassMember;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcResolve_ExplicitSelf_AlwaysClassMember, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Self.X reaches class method despite local var X', '200' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_InheritedCall_AlwaysParent;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcResolve_InheritedAlwaysParent, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('inherited Tag reaches parent despite subclass override', '1' + LE, Output);
end;

procedure TE2EClasses2Tests.TestRun_InterfaceField_ShadowsGlobal_Dispatches;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcIntfFieldShadowsGlobal, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('interface dispatch through field shadowing global', 'printed' + LE, Output);
end;

initialization
  RegisterTest(TE2EClasses2Tests);

end.
