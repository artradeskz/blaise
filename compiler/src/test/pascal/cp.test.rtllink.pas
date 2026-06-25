{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.rtllink;

{ Shared RTL link helper for the standalone E2E test helpers (those that lower a
  program to assembly themselves and link it, rather than via cp.test.e2e.base).

  The RTL is built from source by scripts/build-rtl-objects.sh — there is no
  blaise_rtl.a archive (RTL-unification Stage 3).  A whole-program assembly dump
  inlines the RTL units the program uses, so --exclude-defined-by drops the RTL
  objects whose symbols the program already defines, avoiding double-definition. }

interface

{ Link AAsmFile (assembled program, .s) into ABinFile against the RTL.
  AProjectRoot must end with a path delimiter.  Returns the cc exit code; 0 on
  success.  Non-zero (and a negative value for a failed RTL build) on failure. }
function LinkProgramWithRTL(const AProjectRoot, AAsmFile,
                           ABinFile: string): Integer;

{ True when the toolchain needed by LinkProgramWithRTL is present: the QBE
  assembler, the compiler binary, and the RTL source. }
function RTLLinkToolchainAvailable(const AProjectRoot: string): Boolean;

implementation

uses
  classes, sysutils, process;

function RTLLinkToolchainAvailable(const AProjectRoot: string): Boolean;
begin
  Result := FileExists(AProjectRoot + 'vendor/qbe/qbe')
        and FileExists(AProjectRoot + 'compiler/target/blaise')
        and FileExists(AProjectRoot + 'compiler/src/main/pascal/runtime.arc.pas');
end;

function RunCapture(const AExe: string; const AArgs: array of string;
                   out AOut: string): Integer;
var
  Proc:  TProcess;
  I:     Integer;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    for I := 0 to High(AArgs) do
      Proc.Parameters.Add(AArgs[I]);
    Proc.Execute();
    AOut := '';
    repeat
      Chunk := Proc.ReadOutput();
      AOut := AOut + Chunk
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode
  finally
    Proc.Free()
  end
end;

function LinkProgramWithRTL(const AProjectRoot, AAsmFile,
                           ABinFile: string): Integer;
var
  ProgObj, ObjDir, Compiler, ScriptOut: string;
  Objs: TStringList;
  Proc: TProcess;
  I: Integer;
begin
  { Assemble the program so the RTL build can see which RTL symbols it inlined. }
  ProgObj := AAsmFile + '.o';
  Result := RunCapture('cc', ['-c', '-o', ProgObj, AAsmFile], ScriptOut);
  if Result <> 0 then Exit;

  Compiler := AProjectRoot + 'compiler/target/blaise';
  ObjDir   := ExtractFilePath(AAsmFile) + 'rtlobj';
  Result := RunCapture(AProjectRoot + 'scripts/build-rtl-objects.sh',
                       [Compiler, ObjDir, '--exclude-defined-by', ProgObj],
                       ScriptOut);
  if Result <> 0 then
  begin
    Result := -1;
    Exit;
  end;

  Objs := TStringList.Create();
  Proc := TProcess.Create(nil);
  try
    Objs.Text := ScriptOut;
    Proc.Executable := 'cc';
    Proc.Parameters.Add('-o');
    Proc.Parameters.Add(ABinFile);
    Proc.Parameters.Add(ProgObj);
    for I := 0 to Objs.Count - 1 do
      if Trim(Objs.Strings[I]) <> '' then
        Proc.Parameters.Add(Trim(Objs.Strings[I]));
    Proc.Parameters.Add('-lm');
    Proc.Parameters.Add('-lpthread');
    Proc.Execute();
    repeat
      ScriptOut := Proc.ReadOutput();
    until (ScriptOut = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode;
  finally
    Proc.Free();
    Objs.Free();
  end;
end;

end.
