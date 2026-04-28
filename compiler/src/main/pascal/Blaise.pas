{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

program Blaise;

{$mode objfpc}{$H+}

{ Blaise Compiler — main entry point.

  Usage:
    blaise --source Hello.pas --output hello
    blaise --source Hello.pas --emit-ir
    blaise --source Hello.pas --output hello --target linux-x86_64

  Generates QBE IR, then shells out to qbe + cc to produce the final
  binary. With --emit-ir, the IR is written to stdout and no binary
  is produced.
}

uses
  SysUtils, Classes, Process, contnrs,
  uLexer, uParser, uAST, uSemantic, uCodeGenQBE, uUnitLoader;

const
  Version = '0.3.0-dev';
  CompilerName = 'Blaise';

procedure PrintUsage;
begin
  WriteLn('Blaise Compiler v', Version);
  WriteLn('Copyright (c) 2026 Graeme Geldenhuys');
  WriteLn('');
  WriteLn('Usage:');
  WriteLn('  blaise --source <file.pas> --output <binary>');
  WriteLn('  blaise --source <file.pas> --emit-ir');
  WriteLn('');
  WriteLn('Flags:');
  WriteLn('  --source <path>     Pascal source file');
  WriteLn('  --output <path>     Output binary path');
  WriteLn('  --unit-path <dir>   Add directory to unit search path (repeatable)');
  WriteLn('  --target <id>       linux-x86_64 (default), macos-arm64');
  WriteLn('  --emit-ir           Print QBE IR to stdout and exit');
end;

{ Handle FPC -i query flags: -iV (version), -iTP (target processor), -iTO (target OS).
  PasBuild probes the compiler with these before invoking a full compile. }
procedure HandleFPCInfoQuery(const AArg: string);
var
  Query: string;
begin
  Query := Copy(AArg, 3, MaxInt);  { strip leading '-i' }
  if Query = 'V' then
  begin
    WriteLn('3.2.2');
    Halt(0);
  end
  else if Query = 'TP' then
  begin
    WriteLn('x86_64');
    Halt(0);
  end
  else if Query = 'TO' then
  begin
    WriteLn('linux');
    Halt(0);
  end;
  { Unknown -i query — ignore silently }
end;

{ Parse FPC-style arguments emitted by PasBuild when --fpc /path/to/blaise is used.
  Handles: -iV/-iTP/-iTO, -FE<dir>, -Fu<path>, -FU<path>, -o<name>,
           -Mobjfpc, -O<n>, -g, -gl, -CX, -d<define>, and the positional source file. }
function ParseFPCArgs(
  out SourceFile:  string;
  out OutputFile:  string;
  out SearchPaths: TStringList): Boolean;
var
  I:       Integer;
  Arg:     string;
  OutDir:  string;
  OutName: string;
begin
  Result      := False;
  SourceFile  := '';
  OutputFile  := '';
  OutDir      := '';
  OutName     := '';
  SearchPaths := TStringList.Create;

  I := 1;
  while I <= ParamCount do
  begin
    Arg := ParamStr(I);

    if Copy(Arg, 1, 2) = '-i' then
      HandleFPCInfoQuery(Arg)
    else if Copy(Arg, 1, 3) = '-FE' then
      OutDir := Copy(Arg, 4, MaxInt)
    else if Copy(Arg, 1, 3) = '-FU' then
      { unit cache directory — ignored in Phase 1 }
    else if Copy(Arg, 1, 3) = '-Fu' then
      SearchPaths.Add(Copy(Arg, 4, MaxInt))
    else if Copy(Arg, 1, 2) = '-o' then
      OutName := Copy(Arg, 3, MaxInt)
    else if Copy(Arg, 1, 2) = '-M' then
      { mode switch (e.g. -Mobjfpc) — ignored }
    else if Copy(Arg, 1, 2) = '-O' then
      { optimisation level — ignored }
    else if Copy(Arg, 1, 2) = '-d' then
      { conditional define — ignored in Phase 1 }
    else if (Arg = '-g') or (Arg = '-gl') or (Arg = '-CX') or
            (Arg = '-XX') or (Arg = '-Xs') then
      { debug / linking flags — ignored }
    else if (Arg = '--help') or (Arg = '-h') then
    begin
      PrintUsage;
      Halt(0);
    end
    else if (Length(Arg) > 0) and (Arg[1] <> '-') then
    begin
      { Positional argument — the source file }
      if SourceFile = '' then
        SourceFile := Arg;
    end;
    { Any other unrecognised -X flag is silently ignored for forward-compat }

    Inc(I);
  end;

  if SourceFile = '' then
  begin
    WriteLn(StdErr, 'Error: no source file specified');
    SearchPaths.Free;
    Exit;
  end;

  { Build output path from -FE and -o, mirroring FPC behaviour }
  if OutName = '' then
    OutName := ChangeFileExt(ExtractFileName(SourceFile), '');
  if OutDir <> '' then
    OutputFile := IncludeTrailingPathDelimiter(OutDir) + OutName
  else
    OutputFile := OutName;

  Result := True;
end;

{ Returns True when the argument list looks like FPC-style flags (single-dash,
  single-letter prefix) rather than Blaise native (double-dash) flags. }
function IsFPCStyleInvocation: Boolean;
var
  I: Integer;
  Arg: string;
begin
  Result := False;
  for I := 1 to ParamCount do
  begin
    Arg := ParamStr(I);
    if (Length(Arg) >= 2) and (Arg[1] = '-') and (Arg[2] <> '-') then
    begin
      Result := True;
      Exit;
    end;
  end;
end;

function ParseArgs(
  out SourceFile:  string;
  out OutputFile:  string;
  out EmitIR:      Boolean;
  out SearchPaths: TStringList): Boolean;
var
  I: Integer;
  Arg: string;
begin
  Result      := False;
  SourceFile  := '';
  OutputFile  := '';
  EmitIR      := False;
  SearchPaths := TStringList.Create;

  I := 1;
  while I <= ParamCount do
  begin
    Arg := ParamStr(I);
    if (Arg = '--source') and (I < ParamCount) then
    begin
      Inc(I);
      SourceFile := ParamStr(I);
    end
    else if (Arg = '--output') and (I < ParamCount) then
    begin
      Inc(I);
      OutputFile := ParamStr(I);
    end
    else if (Arg = '--unit-path') and (I < ParamCount) then
    begin
      Inc(I);
      SearchPaths.Add(ParamStr(I));
    end
    else if Arg = '--emit-ir' then
      EmitIR := True
    else if Arg = '--target' then
      Inc(I)  { consume next arg — target is not used in Phase 1 }
    else if (Arg = '--help') or (Arg = '-h') then
    begin
      PrintUsage;
      Halt(0);
    end
    else
    begin
      WriteLn(StdErr, 'Unknown flag: ', Arg);
      SearchPaths.Free;
      Exit;
    end;
    Inc(I);
  end;

  if SourceFile = '' then
  begin
    WriteLn(StdErr, 'Error: --source is required');
    SearchPaths.Free;
    Exit;
  end;
  if (not EmitIR) and (OutputFile = '') then
  begin
    WriteLn(StdErr, 'Error: --output is required (or use --emit-ir)');
    SearchPaths.Free;
    Exit;
  end;

  Result := True;
end;

function RunProcess(const AExe: string; const AArgs: array of string;
  out AOutput: string): Integer;
const
  BufSize = 4096;
var
  Proc: TProcess;
  Buf:  array[0..BufSize-1] of Byte;
  N:    Integer;
  I:    Integer;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    for I := Low(AArgs) to High(AArgs) do
      Proc.Parameters.Add(AArgs[I]);
    { Do NOT use poWaitOnExit with poUsePipes — if the child fills the pipe
      buffer before we read, both sides deadlock.  Drain stderr in a loop. }
    Proc.Options := [poUsePipes, poStderrToOutPut];
    Proc.Execute;
    AOutput := '';
    repeat
      N := Proc.Output.Read(Buf, BufSize);
      if N > 0 then
        AOutput := AOutput + Copy(string(PChar(@Buf[0])), 1, N);
    until (N = 0) and not Proc.Running;
    Proc.WaitOnExit;
    Result := Proc.ExitCode;
  finally
    Proc.Free;
  end;
end;

{ Locate the Blaise RTL static library.
  Search order:
    1. BLAISE_RTL environment variable (explicit override)
    2. Same directory as this compiler binary (installed layout) }
function FindRTL: string;
var
  BinDir: string;
begin
  Result := GetEnvironmentVariable('BLAISE_RTL');
  if (Result <> '') and FileExists(Result) then
    Exit;
  BinDir := ExtractFilePath(ParamStr(0));
  Result  := IncludeTrailingPathDelimiter(BinDir) + 'blaise_rtl.a';
  if FileExists(Result) then
    Exit;
  Result := '';
end;

procedure CompileToNative(const AIRFile, AOutputFile: string);
var
  AsmFile, RTLPath: string;
  Msg:              string;
  ExitCode:         Integer;
begin
  AsmFile := ChangeFileExt(AIRFile, '.s');
  RTLPath := FindRTL;

  ExitCode := RunProcess('qbe', ['-o', AsmFile, AIRFile], Msg);
  if ExitCode <> 0 then
  begin
    WriteLn(StdErr, 'qbe error (exit ', ExitCode, '):');
    Write(StdErr, Msg);
    Halt(1);
  end;

  if RTLPath <> '' then
    ExitCode := RunProcess('cc', ['-o', AOutputFile, AsmFile, RTLPath], Msg)
  else
    ExitCode := RunProcess('cc', ['-o', AOutputFile, AsmFile], Msg);

  if ExitCode <> 0 then
  begin
    WriteLn(StdErr, 'cc error (exit ', ExitCode, '):');
    Write(StdErr, Msg);
    Halt(1);
  end;

  DeleteFile(AsmFile);
end;

var
  SourceFile, OutputFile: string;
  SearchPaths: TStringList;
  EmitIR:   Boolean;
  Source:   TStringList;
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  CG:       TCodeGenQBE;
  Loader:   TUnitLoader;
  Units:    TObjectList;
  I:        Integer;
  IR:       string;
  IRFile:   string;

begin
  SearchPaths := nil;
  if IsFPCStyleInvocation then
  begin
    if not ParseFPCArgs(SourceFile, OutputFile, SearchPaths) then
    begin
      PrintUsage;
      Halt(1);
    end;
    EmitIR := False;
  end
  else
  begin
    if not ParseArgs(SourceFile, OutputFile, EmitIR, SearchPaths) then
    begin
      PrintUsage;
      Halt(1);
    end;
  end;

  if not FileExists(SourceFile) then
  begin
    WriteLn(StdErr, 'Error: source file not found: ', SourceFile);
    Halt(1);
  end;

  Source := TStringList.Create;
  try
    Source.LoadFromFile(SourceFile);
  except
    on E: Exception do
    begin
      WriteLn(StdErr, 'Error reading source: ', E.Message);
      Halt(1);
    end;
  end;

  Lexer    := nil;
  Parser   := nil;
  Prog     := nil;
  Semantic := nil;
  CG       := nil;
  Loader   := nil;
  Units    := nil;
  try
    try
      Lexer  := TLexer.Create(Source.Text);
      Parser := TParser.Create(Lexer);
      Prog   := Parser.Parse;
    except
      on E: Exception do
      begin
        WriteLn(StdErr, 'Parse error: ', E.Message);
        Halt(1);
      end;
    end;

    try
      Semantic := TSemanticAnalyser.Create;
      if (SearchPaths <> nil) and (SearchPaths.Count > 0) and
         (Prog.UsedUnits.Count > 0) then
      begin
        Loader := TUnitLoader.Create(SearchPaths);
        Units  := Loader.LoadAll(Prog.UsedUnits);
        for I := 0 to Units.Count - 1 do
          Semantic.AnalyseUnitForExport(TUnit(Units[I]));
      end;
      Semantic.Analyse(Prog);
    except
      on E: ESemanticError do
      begin
        WriteLn(StdErr, 'Semantic error: ', E.Message);
        Halt(1);
      end;
      on E: EUnitNotFound do
      begin
        WriteLn(StdErr, 'Unit not found: ', E.Message);
        Halt(1);
      end;
      on E: ECircularDependency do
      begin
        WriteLn(StdErr, 'Circular dependency: ', E.Message);
        Halt(1);
      end;
    end;

    try
      CG := TCodeGenQBE.Create;
      if (Units <> nil) and (Units.Count > 0) then
      begin
        for I := 0 to Units.Count - 1 do
          CG.AppendUnit(TUnit(Units[I]));
        CG.AppendProgram(Prog);
      end
      else
        CG.Generate(Prog);
      IR := CG.GetOutput;
    except
      on E: Exception do
      begin
        WriteLn(StdErr, 'Code generation error: ', E.Message);
        Halt(1);
      end;
    end;
  finally
    Units.Free;
    Loader.Free;
    SearchPaths.Free;
    CG.Free;
    Semantic.Free;
    Prog.Free;
    Parser.Free;
    Lexer.Free;
    Source.Free;
  end;

  if EmitIR then
  begin
    Write(IR);
    Halt(0);
  end;

  IRFile := ChangeFileExt(OutputFile, '.ssa');
  try
    Source := TStringList.Create;
    try
      Source.Text := IR;
      Source.SaveToFile(IRFile);
    finally
      Source.Free;
    end;
  except
    on E: Exception do
    begin
      WriteLn(StdErr, 'Error writing IR: ', E.Message);
      Halt(1);
    end;
  end;

  CompileToNative(IRFile, OutputFile);
  DeleteFile(IRFile);
end.
