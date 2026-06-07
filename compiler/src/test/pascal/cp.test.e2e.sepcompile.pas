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
  end;

implementation

procedure TSepCompileTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-sepcompile')
end;

function TSepCompileTests.BlaisePath(): string;
var
  Root: string;
begin
  Root := GetEnvironmentVariable('BLAISE_PROJECT_ROOT');
  if Root = '' then
    Root := GetCurrentDir();
  Result := IncludeTrailingPathDelimiter(Root) + 'compiler/target/blaise'
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

initialization
  RegisterTest(TSepCompileTests);

end.
