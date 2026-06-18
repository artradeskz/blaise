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
{ The native backend supports --incremental (per-unit .o + embedded .bif) the
  same as QBE.  Compile a program using a unit that declares a class (exercises
  the system-def suppression + global typeinfo_TObject and per-unit string
  literals in the unit object), then run it.  A unit .o must be left behind. }
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
                   '--backend', 'native', '--incremental',
                   '--unit-path', FScratch], Captured);
  AssertEquals('blaise(use_shapes) exit code (out: ' + Captured + ')', 0, Rc);
  AssertTrue('use_shapes exists', FileExists(ProgBin));
  AssertTrue('per-unit ShapesU.o cached', FileExists(UnitObj));

  Rc := RunBinary(ProgBin, Captured);
  AssertEquals('use_shapes exit code', 0, Rc);
  AssertEquals('use_shapes stdout', 'shape:box' + #10, Captured)
end;

initialization
  RegisterTest(TSepCompileTests);

end.
