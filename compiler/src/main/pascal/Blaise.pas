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
  SysUtils, Classes, Process,
  uLexer, uParser, uAST, uCodeGenQBE;

const
  Version = '0.1.0-alpha';
  CompilerName = 'Blaise';

procedure PrintUsage;
begin
  WriteLn('Blaise Compiler v', Version);
  WriteLn('');
  WriteLn('Usage:');
  WriteLn('  blaise --source <file.pas> --output <binary>');
  WriteLn('  blaise --source <file.pas> --emit-ir');
  WriteLn('');
  WriteLn('Flags:');
  WriteLn('  --source <path>     Pascal source file');
  WriteLn('  --output <path>     Output binary path');
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
  out SourceFile: string;
  out OutputFile: string): Boolean;
var
  I:       Integer;
  Arg:     string;
  OutDir:  string;
  OutName: string;
begin
  Result     := False;
  SourceFile := '';
  OutputFile := '';
  OutDir     := '';
  OutName    := '';

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
      { unit search path — ignored in Phase 1 }
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
  out SourceFile: string;
  out OutputFile: string;
  out EmitIR:     Boolean): Boolean;
var
  I: Integer;
  Arg: string;
begin
  Result     := False;
  SourceFile := '';
  OutputFile := '';
  EmitIR     := False;

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
      Exit;
    end;
    Inc(I);
  end;

  if SourceFile = '' then
  begin
    WriteLn(StdErr, 'Error: --source is required');
    Exit;
  end;
  if (not EmitIR) and (OutputFile = '') then
  begin
    WriteLn(StdErr, 'Error: --output is required (or use --emit-ir)');
    Exit;
  end;

  Result := True;
end;

function RunProcess(const AExe: string; const AArgs: array of string;
  out AOutput: string): Integer;
var
  Proc:  TProcess;
  Lines: TStringList;
  I:     Integer;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    for I := Low(AArgs) to High(AArgs) do
      Proc.Parameters.Add(AArgs[I]);
    Proc.Options := [poWaitOnExit, poUsePipes];
    Proc.Execute;
    Lines := TStringList.Create;
    try
      Lines.LoadFromStream(Proc.Stderr);
      AOutput := Lines.Text;
    finally
      Lines.Free;
    end;
    Result := Proc.ExitCode;
  finally
    Proc.Free;
  end;
end;

procedure CompileToNative(const AIRFile, AOutputFile: string);
var
  AsmFile:    string;
  Msg:        string;
  ExitCode:   Integer;
begin
  AsmFile := ChangeFileExt(AIRFile, '.s');

  ExitCode := RunProcess('qbe', ['-o', AsmFile, AIRFile], Msg);
  if ExitCode <> 0 then
  begin
    WriteLn(StdErr, 'qbe error (exit ', ExitCode, '):');
    Write(StdErr, Msg);
    Halt(1);
  end;

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
  EmitIR: Boolean;
  Source: TStringList;
  Lexer:  TLexer;
  Parser: TParser;
  Prog:   TProgram;
  CG:     TCodeGenQBE;
  IR:     string;
  IRFile: string;

begin
  if IsFPCStyleInvocation then
  begin
    if not ParseFPCArgs(SourceFile, OutputFile) then
    begin
      PrintUsage;
      Halt(1);
    end;
    EmitIR := False;
  end
  else
  begin
    if not ParseArgs(SourceFile, OutputFile, EmitIR) then
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

  Lexer  := nil;
  Parser := nil;
  Prog   := nil;
  CG     := nil;
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
      CG := TCodeGenQBE.Create;
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
    CG.Free;
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
