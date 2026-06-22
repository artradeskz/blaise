{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.sepcompile;

{ End-to-end separate-compilation gate.

  Drives the headline feature through the actual blaise binary rather
  than the in-process pipeline used by the other E2E suites:

    1. blaise --source Dep.pas --output Dep.o
         -> ELF .o with .blaise.iface embedded
    2. Dep.pas removed from disk
    3. blaise --source UseDep.pas --output use_dep --unit-path <dir-with-Dep.o>
         -> compiler picks up Dep.o via auto-discovery, reads the iface
            out of the embedded section, links the program
    4. ./use_dep
         -> prints the expected output

  Covers both free routines (where only the call site needs the iface)
  and generic classes (where the consumer instantiates the template
  using bodies carried in the .blaise.iface — no source TUnit
  required). }

interface

uses
  classes, sysutils, process, blaise.testing,
  cp.test.e2e.base;

type
  TSepCompileTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  private
    function  BlaisePath(): string;
    function  RunBlaise(const AArgs: array of string;
                        out AStdout: string): Integer;
    function  RunBinary(const AExe: string; out AStdout: string): Integer;
  published
    procedure TestFreeRoutine_RoundTrip_WithoutSource;
    procedure TestGenericClass_RoundTrip_WithoutSource;
    procedure TestUninstantiatedGenericFunc_InUnit_Compiles;
    procedure TestDuplicateExternalAcrossUnits_Compiles;
    procedure TestNativeIncremental_MultiUnitClass_Compiles;
    procedure TestNativeNoIncremental_MultiUnitClass_Compiles;
    { Regression: compiling a UNIT (unit-mode, top source is a `unit`) that
      USES another unit, with the default incremental path, segfaulted — the
      incremental worker setup read Prog.SymbolTable, but in unit-mode Prog is
      nil (the table comes from the semantic pass).  This is the exact path the
      runtime Makefile drives (every RTL unit is compiled `--source X.pas
      --output X.o`), so it broke `make` in runtime/. }
    procedure TestNativeIncremental_UnitUsesUnit_Compiles;
    { Regression: a Double field read via implicit Self (Result := FFloat
      inside a method) compiled in unit-mode (.o) emitted `movsd FFloat(%rip)`
      — a load from a global symbol named after the field instead of from
      Self+offset — producing an undefined `FFloat` symbol.  The store path was
      already correct; only the read was broken, and only in per-unit codegen
      (whole-program builds resolved it as a field offset). }
    procedure TestNativeIncremental_FloatFieldRead_InUnit;
    { Regression: a unit that USES another unit only in its IMPLEMENTATION
      section.  On a clean build all units are parsed, so the impl-only
      dependency's object is linked.  But on an incremental REBUILD, the
      consuming unit is loaded from its cached .o/.bif — and the .bif only
      recorded the INTERFACE uses, so the impl-only dependency was never
      loaded and its .o was dropped from the link → undefined symbol at
      run time.  This is exactly what broke a second `pasbuild test-compile`
      (the compiler rebuilt itself incrementally into a populated cache and
      lost ~880 KB of impl-only-dependency code). }
    procedure TestIncrementalRebuild_ImplOnlyUses_LinksDependency;
    { Regression: a non-virtual constructor named 'Create' receives an
      implicit vtable slot (metaclass dispatch through a class-of
      reference).  The source-side semantic pass added that slot, but the
      cached-.bif importer (uSemanticImport.RegisterClassMethod) only added
      slots for virtual/override methods — so a descendant class compiled
      against a CACHED base unit built a vtable that omitted the Create slot
      and shifted every later virtual method up.  A Cls.Create call then
      dispatched through the wrong vtable slot (it hit the method that fell
      into Create's old index), so the constructor body never ran and the
      object's fields stayed nil.  This crashed the stdlib JSON test suite
      when its TTestCase base came from target/units. }
    procedure TestIncrementalRebuild_VirtualCtorVtableSlot;
    procedure TestDebugOpdf_PerUnitSection_InDependencyObject;
  end;

implementation

procedure TSepCompileTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-sepcompile')
end;

function TSepCompileTests.BlaisePath(): string;
var
  ProjectRoot: string;
begin
  ProjectRoot := GetEnvironmentVariable('BLAISE_PROJECT_ROOT');
  if ProjectRoot <> '' then
    Result := IncludeTrailingPathDelimiter(ProjectRoot) + 'compiler/target/blaise'
  else
    Result := ExtractFilePath(ParamStr(0)) + 'blaise'
end;

function TSepCompileTests.RunBlaise(const AArgs: array of string;
                                    out AStdout: string): Integer;
var
  Proc:  TProcess;
  I:     Integer;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := BlaisePath();
    for I := 0 to High(AArgs) do
      Proc.Parameters.Add(AArgs[I]);
    Proc.Execute();
    AStdout := '';
    repeat
      Chunk := Proc.ReadOutput();
      AStdout := AStdout + Chunk
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode
  finally
    Proc.Free()
  end
end;

function TSepCompileTests.RunBinary(const AExe: string;
                                    out AStdout: string): Integer;
var
  Proc:  TProcess;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    Proc.Execute();
    AStdout := '';
    repeat
      Chunk := Proc.ReadOutput();
      AStdout := AStdout + Chunk
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode
  finally
    Proc.Free()
  end
end;

procedure TSepCompileTests.TestFreeRoutine_RoundTrip_WithoutSource;
const
  DepSrc =
    '''
    unit MyDep;
    interface
    function Triple(N: Integer): Integer;
    implementation
    function Triple(N: Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 1 to 3 do Result := Result + N
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseMyDep;
    uses MyDep;
    begin
      WriteLn('Triple(7) = ', Triple(7))
    end.
    ''';
var
  DepPas, DepObj, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  DepPas  := FScratch + '/MyDep.pas';
  DepObj  := FScratch + '/MyDep.o';
  ProgPas := FScratch + '/use_mydep.pas';
  ProgBin := FScratch + '/use_mydep';

  { Step 1: build the dep into an .o with embedded .blaise.iface. }
  WriteFile(DepPas, DepSrc);
  Rc := RunBlaise(['--source', DepPas, '--output', DepObj], Captured);
  AssertEquals('blaise(MyDep) exit code', 0, Rc);
  AssertTrue('MyDep.o exists', FileExists(DepObj));

  { Step 2: hide the source so the consumer cannot reach it. }
  DeleteFile(DepPas);
  AssertFalse('MyDep.pas hidden', FileExists(DepPas));

  { Step 3: compile the consumer.  The loader's auto-discovery walks
    the unit path looking for a sibling <unit>.o with an embedded
    iface; the call site for Triple is resolved from that iface and
    the .o is linked into the final binary. }
  WriteFile(ProgPas, ProgSrc);
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_mydep) exit code', 0, Rc);
  AssertTrue('use_mydep exists', FileExists(ProgBin));

  { Step 4: run the program. }
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_mydep exit code', 0, Rc);
  AssertEquals('use_mydep stdout', 'Triple(7) = 21' + #10, Captured)
end;

procedure TSepCompileTests.TestGenericClass_RoundTrip_WithoutSource;
const
  DepSrc =
    '''
    unit MyContainers;
    interface
    type
      TBox<T> = class
      private
        FValue: T;
      public
        constructor Create(AValue: T);
        function Get: T;
      end;
    implementation
    constructor TBox<T>.Create(AValue: T);
    begin
      FValue := AValue
    end;
    function TBox<T>.Get: T;
    begin
      Result := FValue
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseBox;
    uses MyContainers;
    var B: TBox<Integer>;
    begin
      B := TBox<Integer>.Create(42);
      WriteLn('Box = ', B.Get());
      B.Free()
    end.
    ''';
var
  DepPas, DepObj, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  DepPas  := FScratch + '/MyContainers.pas';
  DepObj  := FScratch + '/MyContainers.o';
  ProgPas := FScratch + '/use_box.pas';
  ProgBin := FScratch + '/use_box';

  { Step 1: compile the generic-bearing unit to an .o with embedded
    iface.  The .bif must carry enough of the generic template body
    (statements + types) for the consumer to instantiate TBox<Integer>
    without ever reading MyContainers.pas back. }
  WriteFile(DepPas, DepSrc);
  Rc := RunBlaise(['--source', DepPas, '--output', DepObj], Captured);
  AssertEquals('blaise(MyContainers) exit code 0' + #10 + Captured, 0, Rc);
  AssertTrue('MyContainers.o exists', FileExists(DepObj));

  { Step 2: hide the source. }
  DeleteFile(DepPas);
  AssertFalse('MyContainers.pas hidden', FileExists(DepPas));

  { Step 3: instantiate the generic in a consumer with only the .o
    visible.  Codegen has to clone the template body, substitute the
    Integer type argument, and emit a fresh TBox_Integer_* family —
    all sourced from the imported iface, not from the (absent) TUnit. }
  WriteFile(ProgPas, ProgSrc);
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_box) exit code 0' + #10 + Captured, 0, Rc);
  AssertTrue('use_box exists', FileExists(ProgBin));

  { Step 4: run the program. }
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_box exit code', 0, Rc);
  AssertEquals('use_box stdout', 'Box = 42' + #10, Captured)
end;

{ Regression for issue #107: a generic FUNCTION declared in a unit but never
  instantiated was code-generated as a template, whose `T`-typed locals have
  no resolved type — codegen raised "Variable 'MaxValue' has no resolved type
  — semantic pass required".  EmitStandaloneDefs skipped templates, but the
  unit-emission path (GenerateUnit/AppendUnit → EmitFuncDef) did not.  The
  unit must compile to an .o even when nothing uses the generic. }
procedure TSepCompileTests.TestUninstantiatedGenericFunc_InUnit_Compiles;
const
  DepSrc =
    '''
    unit MyMaxUnit;
    interface
    function Doubled(N: Integer): Integer;
    function FindMaxValue<T>(arr: array of T): T;
    implementation
    function Doubled(N: Integer): Integer;
    begin
      Result := N * 2
    end;
    function FindMaxValue<T>(arr: array of T): T;
    var
      MaxValue: T;
      x: UInt64;
    begin
      x := Low(arr);
      MaxValue := arr[0];
      while x <= High(arr) do
      begin
        if arr[x] > MaxValue then
          MaxValue := arr[x];
        Inc(x)
      end;
      Result := MaxValue
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseMyMax;
    uses MyMaxUnit;
    begin
      { Use only the non-generic routine — the generic stays uninstantiated. }
      WriteLn('Doubled(21) = ', Doubled(21))
    end.
    ''';
var
  DepPas, DepObj, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  DepPas  := FScratch + '/MyMaxUnit.pas';
  DepObj  := FScratch + '/MyMaxUnit.o';
  ProgPas := FScratch + '/use_mymax.pas';
  ProgBin := FScratch + '/use_mymax';

  { Step 1: compile the unit.  The uninstantiated generic template must be
    skipped by codegen — this is the step that previously crashed. }
  WriteFile(DepPas, DepSrc);
  Rc := RunBlaise(['--source', DepPas, '--output', DepObj], Captured);
  AssertEquals('blaise(MyMaxUnit) exit code 0' + #10 + Captured, 0, Rc);
  AssertTrue('MyMaxUnit.o exists', FileExists(DepObj));

  { Step 2: a consumer that never instantiates the generic links and runs. }
  WriteFile(ProgPas, ProgSrc);
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_mymax) exit code 0' + #10 + Captured, 0, Rc);
  AssertTrue('use_mymax exists', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_mymax exit code', 0, Rc);
  AssertEquals('use_mymax stdout', 'Doubled(21) = 42' + #10, Captured)
end;

{ Two units that each privately declare the SAME C function via
  `external name '...'` must both resolve calls to it.  Regression for a
  cross-unit clash in impl-only proc matching: the per-unit forward-decl
  fallback (FProcIndex.IndexOf) ignored unit ownership, so the second unit's
  external matched the FIRST unit's already-indexed decl and was never defined
  into its own scope -> "Undeclared function" at the call site. }
procedure TSepCompileTests.TestDuplicateExternalAcrossUnits_Compiles;
const
  UnitASrc =
    '''
    unit DupExtA;
    interface
    function LenA(const S: string): Integer;
    implementation
    function _strlenA(S: Pointer): Int64; external name 'strlen';
    function LenA(const S: string): Integer;
    begin
      Result := Integer(_strlenA(PChar(S)))
    end;
    end.
    ''';
  UnitBSrc =
    '''
    unit DupExtB;
    interface
    function LenB(const S: string): Integer;
    implementation
    function _strlenA(S: Pointer): Int64; external name 'strlen';
    function LenB(const S: string): Integer;
    begin
      Result := Integer(_strlenA(PChar(S)))
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseDupExt;
    uses DupExtA, DupExtB;
    begin
      WriteLn(LenA('abc') + LenB('defgh'))
    end.
    ''';
var
  APas, BPas, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  APas    := FScratch + '/DupExtA.pas';
  BPas    := FScratch + '/DupExtB.pas';
  ProgPas := FScratch + '/use_dupext.pas';
  ProgBin := FScratch + '/use_dupext';

  WriteFile(APas, UnitASrc);
  WriteFile(BPas, UnitBSrc);
  WriteFile(ProgPas, ProgSrc);

  { Single invocation: both units are picked up off the unit path and
    compiled alongside the program. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_dupext) exit code 0' + #10 + Captured, 0, Rc);
  AssertTrue('use_dupext exists', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_dupext exit code', 0, Rc);
  AssertEquals('use_dupext stdout', '8' + #10, Captured)
end;

procedure TSepCompileTests.TestNativeIncremental_MultiUnitClass_Compiles;
{ Incremental compilation (per-unit .o + embedded .bif) is the DEFAULT on the
  native backend (as it is on QBE).  Compile a program using a unit that
  declares a class (exercises the system-def suppression + global
  typeinfo_TObject and per-unit string literals in the unit object) WITHOUT any
  --incremental flag — the default path must produce a working binary and leave
  a per-unit .o behind. }
const
  UnitSrc =
    '''
    unit ShapesU;
    interface
    type
      TShape = class
        Name: string;
        function Describe: string;
      end;
    implementation
    function TShape.Describe: string;
    begin Result := 'shape:' + Name end;
    end.
    ''';
  ProgSrc =
    '''
    program UseShapes;
    uses ShapesU;
    var S: TShape;
    begin
      S := TShape.Create();
      S.Name := 'box';
      WriteLn(S.Describe());
      S.Free()
    end.
    ''';
var
  UnitPas, ProgPas, ProgBin, UnitObj: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  UnitPas := FScratch + '/ShapesU.pas';
  ProgPas := FScratch + '/use_shapes.pas';
  ProgBin := FScratch + '/use_shapes';
  { Incremental writes the per-unit .o next to the output with a lowercased
    unit name (see UnitOPath in Blaise.pas). }
  UnitObj := FScratch + '/shapesu.o';

  WriteFile(UnitPas, UnitSrc);
  WriteFile(ProgPas, ProgSrc);
  DeleteFile(UnitObj);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'native',
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_shapes) exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_shapes exists', FileExists(ProgBin));
  AssertTrue('per-unit ShapesU.o cached', FileExists(UnitObj));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_shapes exit code', 0, Rc);
  AssertEquals('use_shapes stdout', 'shape:box' + #10, Captured)
end;

procedure TSepCompileTests.TestNativeNoIncremental_MultiUnitClass_Compiles;
{ --no-incremental opts out of the default per-unit .o emission: the same
  multi-unit-class program must still compile and run as a single whole-program
  object, and NO per-unit .o is left behind. }
const
  UnitSrc =
    '''
    unit ShapesU;
    interface
    type
      TShape = class
        Name: string;
        function Describe: string;
      end;
    implementation
    function TShape.Describe: string;
    begin Result := 'shape:' + Name end;
    end.
    ''';
  ProgSrc =
    '''
    program UseShapes;
    uses ShapesU;
    var S: TShape;
    begin
      S := TShape.Create();
      S.Name := 'box';
      WriteLn(S.Describe());
      S.Free()
    end.
    ''';
var
  UnitPas, ProgPas, ProgBin, UnitObj: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  UnitPas := FScratch + '/ShapesU.pas';
  ProgPas := FScratch + '/use_shapes_ni.pas';
  ProgBin := FScratch + '/use_shapes_ni';
  UnitObj := FScratch + '/shapesu.o';

  WriteFile(UnitPas, UnitSrc);
  WriteFile(ProgPas, ProgSrc);
  DeleteFile(UnitObj);

  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'native', '--no-incremental',
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_shapes_ni) exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_shapes_ni exists', FileExists(ProgBin));
  AssertFalse('no per-unit ShapesU.o with --no-incremental', FileExists(UnitObj));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_shapes_ni exit code', 0, Rc);
  AssertEquals('use_shapes_ni stdout', 'shape:box' + #10, Captured)
end;

procedure TSepCompileTests.TestNativeIncremental_UnitUsesUnit_Compiles;
{ Compile a UNIT that uses another unit, in unit-mode (--source <unit>.pas
  --output <unit>.o), via the default incremental path.  This is the runtime
  Makefile's exact invocation and used to segfault (nil Prog.SymbolTable in the
  incremental worker setup).  A program that uses the compiled unit must then
  build and run, proving the per-unit object is correct. }
const
  BaseSrc =
    '''
    unit BaseU;
    interface
    type TFoo = record A: Integer; end;
    function MakeFoo(N: Integer): TFoo;
    implementation
    function MakeFoo(N: Integer): TFoo;
    begin Result.A := N end;
    end.
    ''';
  DerivedSrc =
    '''
    unit DerivedU;
    interface
    uses BaseU;
    function Doubled(N: Integer): Integer;
    implementation
    function Doubled(N: Integer): Integer;
    var F: TFoo;
    begin F := MakeFoo(N); Result := F.A * 2 end;
    end.
    ''';
  ProgSrc =
    '''
    program UseDerived;
    uses DerivedU;
    begin
      WriteLn(Doubled(21))
    end.
    ''';
var
  BasePas, DerivedPas, DerivedObj, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  BasePas    := FScratch + '/BaseU.pas';
  DerivedPas := FScratch + '/DerivedU.pas';
  DerivedObj := FScratch + '/derivedu.o';
  ProgPas    := FScratch + '/use_derived.pas';
  ProgBin    := FScratch + '/use_derived';

  WriteFile(BasePas, BaseSrc);
  WriteFile(DerivedPas, DerivedSrc);
  DeleteFile(DerivedObj);

  { Unit-mode incremental compile: this is the call that crashed. }
  Rc := RunBlaise(['--source', DerivedPas, '--output', DerivedObj,
                   '--backend', 'native',
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(DerivedU unit) exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('DerivedU.o exists', FileExists(DerivedObj));

  { The emitted unit object must be usable: build + run a program over it. }
  WriteFile(ProgPas, ProgSrc);
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'native',
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_derived) exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_derived exists', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_derived exit code', 0, Rc);
  AssertEquals('use_derived stdout', '42' + #10, Captured)
end;

procedure TSepCompileTests.TestNativeIncremental_FloatFieldRead_InUnit;
const
  UnitSrc =
    '''
    unit NumU;
    interface
    type
      TNum = class
        FFloat: Double;
        procedure SetF(v: Double);
        function GetF: Double;
      end;
    implementation
    procedure TNum.SetF(v: Double); begin FFloat := v; end;
    function TNum.GetF: Double; begin Result := FFloat; end;
    end.
    ''';
  ProgSrc =
    '''
    program UseNum;
    uses NumU;
    var N: TNum;
    begin
      N := TNum.Create();
      N.SetF(3.5);
      WriteLn(N.GetF());
      N.Free()
    end.
    ''';
var
  UnitPas, ProgPas, ProgBin: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  UnitPas := FScratch + '/NumU.pas';
  ProgPas := FScratch + '/use_num.pas';
  ProgBin := FScratch + '/use_num';

  WriteFile(UnitPas, UnitSrc);
  WriteFile(ProgPas, ProgSrc);

  { Incremental (per-unit .o) is the default; NumU is compiled to numu.o, whose
    GetF must read FFloat from Self+offset, not a global symbol. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'native',
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_num) exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_num exists', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_num exit code', 0, Rc);
  AssertEquals('use_num stdout', '3.5' + #10, Captured)
end;

procedure TSepCompileTests.TestIncrementalRebuild_ImplOnlyUses_LinksDependency;
const
  HelperSrc =
    '''
    unit HelperU;
    interface
    function HelperVal: Integer;
    implementation
    function HelperVal: Integer;
    begin Result := 42 end;
    end.
    ''';
  { MidU uses HelperU only in its IMPLEMENTATION section — HelperU does not
    appear in MidU's interface, so MidU's .bif must still record it as an
    implementation-section dependency. }
  MidSrc =
    '''
    unit MidU;
    interface
    function MidVal: Integer;
    implementation
    uses HelperU;
    function MidVal: Integer;
    begin Result := HelperVal() + 1 end;
    end.
    ''';
  ProgSrc =
    '''
    program UseMid;
    uses MidU;
    begin
      WriteLn(MidVal())
    end.
    ''';
var
  HelperPas, MidPas, ProgPas, ProgBin, CacheDir: string;
  Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  HelperPas := FScratch + '/HelperU.pas';
  MidPas    := FScratch + '/MidU.pas';
  ProgPas   := FScratch + '/use_mid.pas';
  ProgBin   := FScratch + '/use_mid';
  CacheDir  := FScratch + '/units-impl';

  WriteFile(HelperPas, HelperSrc);
  WriteFile(MidPas, MidSrc);
  WriteFile(ProgPas, ProgSrc);
  ForceDirectories(CacheDir);

  { Build 1 (clean cache): every unit is parsed from source, so HelperU's
    object is linked.  This populates the cache with .o/.bif for MidU and
    HelperU. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('build1 exit code (out: ' + Captured + ')', 0, Rc);
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('build1 run exit code', 0, Rc);
  AssertEquals('build1 stdout', '43' + #10, Captured);

  { Build 2 (populated cache): MidU is now loaded from its cached iface.
    The loader must still pull in HelperU (MidU's impl-only dependency) and
    link helperu.o — otherwise the link drops it and the program aborts at
    run time with an undefined symbol. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('build2 exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_mid exists after rebuild', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('build2 run exit code (impl-only dep must be linked)', 0, Rc);
  AssertEquals('build2 stdout', '43' + #10, Captured)
end;

{ Regression for the cached-unit virtual-constructor vtable-slot bug.

  BaseU declares a class with a non-virtual constructor Create (which still
  takes a vtable slot for class-of dispatch) FOLLOWED by a virtual method
  Tag.  A descendant TDerived overrides Tag, and the program creates the
  instance through a class-of reference (Cls.Create) so the constructor is
  reached via the vtable.  Create sets FValue := 7; if the cached import
  drops Create's vtable slot, Cls.Create dispatches into Tag's slot instead,
  FValue stays 0, and the program prints '0' rather than '7'. }
procedure TSepCompileTests.TestIncrementalRebuild_VirtualCtorVtableSlot;
const
  BaseSrc =
    '''
    unit BaseU;
    interface
    type
      TBase = class(TObject)
      private
        FValue: Integer;
      public
        constructor Create;
        function Tag: Integer; virtual;
        property Value: Integer read FValue;
      end;
      TBaseClass = class of TBase;
    implementation
    constructor TBase.Create;
    begin
      inherited Create();
      Self.FValue := 7
    end;
    function TBase.Tag: Integer;
    begin
      Result := 100
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseBase;
    uses BaseU;
    var
      Cls: TBaseClass;
      Obj: TBase;
    begin
      Cls := TBase;
      Obj := Cls.Create();
      WriteLn(Obj.Value)
    end.
    ''';
var
  BasePas, ProgPas, ProgBin, CacheDir, Captured: string;
  Rc: Integer;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  BasePas  := FScratch + '/BaseU.pas';
  ProgPas  := FScratch + '/use_base.pas';
  ProgBin  := FScratch + '/use_base';
  CacheDir := FScratch + '/units-vctor';

  WriteFile(BasePas, BaseSrc);
  WriteFile(ProgPas, ProgSrc);
  ForceDirectories(CacheDir);

  { Build 1 (clean cache): BaseU is parsed from source.  Populates the
    cache with BaseU's .o/.bif. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('build1 exit code (out: ' + Captured + ')', 0, Rc);
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('build1 run exit code', 0, Rc);
  AssertEquals('build1 stdout (ctor ran)', '7' + #10, Captured);

  { Build 2 (populated cache): BaseU is loaded from its cached .bif.  The
    importer must re-create the Create vtable slot so Cls.Create dispatches
    to the constructor and FValue is set to 7. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('build2 exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_base exists after rebuild', FileExists(ProgBin));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('build2 run exit code', 0, Rc);
  AssertEquals('build2 stdout (cached ctor slot)', '7' + #10, Captured)
end;

procedure TSepCompileTests.TestDebugOpdf_PerUnitSection_InDependencyObject;
const
  DepSrc =
    '''
    unit OpdfDep;
    interface
    procedure Greet(const AName: string);
    implementation
    procedure Greet(const AName: string);
    var
      Total: Integer;
      Msg: string;
    begin
      Total := 0;
      Msg := 'Hello, ';
      Msg := Msg + AName;
      Total := Total + 1;
      WriteLn(Msg);
      Total := Total + 1;
      WriteLn('Count is ', Total)
    end;
    end.
    ''';
  ProgSrc =
    '''
    program UseOpdfDep;
    uses OpdfDep;
    begin
      Greet('World')
    end.
    ''';
var
  DepPas, ProgPas, ProgBin, CacheDir, DepObj: string;
  Captured, ObjOut: string;
  Rc: Integer;
  Proc: TProcess;
  Chunk: string;
begin
  if not ToolchainAvailable() then
  begin
    Fail('toolchain missing — qbe or RTL not found');
    Exit
  end;
  if not FileExists(BlaisePath()) then
  begin
    Fail('blaise binary missing at ' + BlaisePath());
    Exit
  end;

  DepPas   := FScratch + '/OpdfDep.pas';
  ProgPas  := FScratch + '/use_opdfdep.pas';
  ProgBin  := FScratch + '/use_opdfdep';
  CacheDir := FScratch + '/units-opdf';
  DepObj   := CacheDir + '/opdfdep.o';

  WriteFile(DepPas, DepSrc);
  WriteFile(ProgPas, ProgSrc);
  ForceDirectories(CacheDir);

  { Default (incremental) native build with --debug-opdf: the dependency
    unit is compiled to its own .o in the cache dir.  With per-unit OPDF the
    worker embeds a self-contained .opdf section into that .o so pdr can break
    inside OpdfDep.Greet.  Before this feature only the program object carried
    OPDF, so the dependency .o had no .opdf section. }
  Rc := RunBlaise(['--source', ProgPas, '--output', ProgBin,
                   '--backend', 'native', '--debug-opdf',
                   '--unit-cache', CacheDir,
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(--debug-opdf) exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_opdfdep exists', FileExists(ProgBin));
  AssertTrue('dependency object exists at ' + DepObj, FileExists(DepObj));

  { The unit .o must carry an .opdf section (objdump -h shows it). }
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := 'objdump';
    Proc.Parameters.Add('-h');
    Proc.Parameters.Add(DepObj);
    Proc.Execute();
    ObjOut := '';
    repeat
      Chunk := Proc.ReadOutput();
      ObjOut := ObjOut + Chunk
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit()
  finally
    Proc.Free()
  end;
  AssertTrue('dependency .o has an .opdf section (objdump -h)',
    Pos('.opdf', ObjOut) >= 0);

  { The program still runs correctly. }
  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_opdfdep exit code', 0, Rc);
  AssertEquals('use_opdfdep stdout', 'Hello, World' + #10 + 'Count is 2' + #10,
    Captured)
end;

initialization
  RegisterTest(TSepCompileTests);

end.
