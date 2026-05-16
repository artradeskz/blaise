{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
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
  uLexer, uParser, uAST, uSemantic, uCodeGenQBE, uUnitLoader, uDebugOPDF,
  uStrCompat;

const
  Version = '0.9.0-dev';
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
  WriteLn('  --debug-opdf        Emit OPDF debug info (.opdf.s companion file)');
  WriteLn('  --cache-dir <dir>   Directory for per-unit IR cache (speeds up incremental builds)');
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
  out SourceFile:   string;
  out OutputFile:   string;
  out SearchPaths:  TStringList;
  out OPDFEnabled:  Boolean): Boolean;
var
  I:       Integer;
  Arg:     string;
  OutDir:  string;
  OutName: string;
begin
  Result      := False;
  SourceFile  := '';
  OutputFile  := '';
  OPDFEnabled := False;
  OutDir      := '';
  OutName     := '';
  SearchPaths := TStringList.Create;

  I := 1;
  while I <= ParamCount do
  begin
    Arg := ParamStr(I);

    if StrHead(Arg, 2) = '-i' then
      HandleFPCInfoQuery(Arg)
    else if StrHead(Arg, 3) = '-FE' then
      OutDir := StrCopyTail(Arg, 3)
    else if StrHead(Arg, 3) = '-FU' then
      { unit cache directory — ignored in Phase 1 }
    else if StrHead(Arg, 3) = '-Fu' then
      SearchPaths.Add(StrCopyTail(Arg, 3))
    else if StrHead(Arg, 2) = '-o' then
      OutName := StrCopyTail(Arg, 2)
    else if StrHead(Arg, 2) = '-M' then
      { mode switch (e.g. -Mobjfpc) — ignored }
    else if StrHead(Arg, 2) = '-O' then
      { optimisation level — ignored }
    else if StrHead(Arg, 2) = '-d' then
      { conditional define — ignored in Phase 1 }
    else if (Arg = '-g') or (Arg = '-gl') then
      OPDFEnabled := True
    else if (Arg = '-CX') or (Arg = '-XX') or (Arg = '-Xs') then
      { other linking flags — ignored }
    else if (Arg = '--help') or (Arg = '-h') then
    begin
      PrintUsage;
      Halt(0);
    end
    else if (Length(Arg) > 0) and (StrAt(Arg, 0) <> Ord('-')) then
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
    if (Length(Arg) >= 2) and (StrAt(Arg, 0) = Ord('-')) and (StrAt(Arg, 1) <> Ord('-')) then
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
  out OPDFEnabled: Boolean;
  out SearchPaths: TStringList;
  out CacheDir:    string): Boolean;
var
  I: Integer;
  Arg: string;
begin
  Result      := False;
  SourceFile  := '';
  OutputFile  := '';
  EmitIR      := False;
  OPDFEnabled := False;
  CacheDir    := '';
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
    else if (Arg = '--cache-dir') and (I < ParamCount) then
    begin
      Inc(I);
      CacheDir := ParamStr(I);
    end
    else if Arg = '--emit-ir' then
      EmitIR := True
    else if Arg = '--debug-opdf' then
      OPDFEnabled := True
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

{$IFDEF FPC}
{ Returns a cache key string for the given source file: "<mtime>:<size>".
  Returns '' if the file cannot be stat'd. }
function CacheKeyForFile(const APath: string): string;
var
  SR: TSearchRec;
begin
  Result := '';
  if FindFirst(APath, faAnyFile, SR) = 0 then
  begin
    Result := IntToStr(SR.Time) + ':' + IntToStr(SR.Size);
    FindClose(SR);
  end;
end;

{ Try to load cached IR for a unit.  Returns '' on cache miss. }
function LoadCachedIR(const ACacheDir, AUnitName, ASourcePath: string): string;
var
  IRFile, KeyFile: string;
  StoredKey, CurrentKey: string;
  SL: TStringList;
begin
  Result := '';
  if ACacheDir = '' then Exit;
  IRFile  := IncludeTrailingPathDelimiter(ACacheDir) + AUnitName + '.ssa';
  KeyFile := IRFile + '.key';
  if not FileExists(IRFile) or not FileExists(KeyFile) then Exit;
  CurrentKey := CacheKeyForFile(ASourcePath);
  if CurrentKey = '' then Exit;
  SL := TStringList.Create;
  try
    SL.LoadFromFile(KeyFile);
    StoredKey := Trim(SL.Text);
  finally
    SL.Free;
  end;
  if StoredKey <> CurrentKey then Exit;
  SL := TStringList.Create;
  try
    SL.LoadFromFile(IRFile);
    Result := SL.Text;
  finally
    SL.Free;
  end;
end;

{ Write IR and its cache key to the cache directory. }
procedure StoreCachedIR(const ACacheDir, AUnitName, ASourcePath, AIR: string);
var
  IRFile, KeyFile: string;
  Key: string;
  SL: TStringList;
begin
  if ACacheDir = '' then Exit;
  if not ForceDirectories(ACacheDir) then Exit;
  Key     := CacheKeyForFile(ASourcePath);
  if Key = '' then Exit;
  IRFile  := IncludeTrailingPathDelimiter(ACacheDir) + AUnitName + '.ssa';
  KeyFile := IRFile + '.key';
  SL := TStringList.Create;
  try
    SL.Text := AIR;
    SL.SaveToFile(IRFile);
  finally
    SL.Free;
  end;
  SL := TStringList.Create;
  try
    SL.Text := Key;
    SL.SaveToFile(KeyFile);
  finally
    SL.Free;
  end;
end;
{$ENDIF}

function ReadProcessChunk(AProc: TProcess): string;
{$IFDEF FPC}
const
  BufSize = 4096;
var
  Buf: array[0..4095] of Byte;
  N:   Integer;
begin
  N := AProc.Output.Read(Buf, BufSize);
  Result := '';
  if N > 0 then
    Result := StrHead(string(PChar(@Buf[0])), N);
end;
{$ELSE}
begin
  Result := AProc.ReadOutput
end;
{$ENDIF}

function RunProcess(const AExe: string; AArgs: TStringList;
  out AOutput: string): Integer;
var
  Proc:  TProcess;
  Chunk: string;
  I:     Integer;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
{$IFDEF FPC}
    Proc.Options := [poUsePipes, poStderrToOutPut];
{$ENDIF}
    for I := 0 to AArgs.Count - 1 do
      Proc.Parameters.Add(AArgs.Strings[I]);
    Proc.Execute;
    AOutput := '';
    repeat
      Chunk := ReadProcessChunk(Proc);
      AOutput := AOutput + Chunk;
    until (Chunk = '') and not Proc.Running;
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

procedure CompileToNative(const AIRFile, AOutputFile, AOPDFAsmFile: string);
var
  AsmFile, RTLPath: string;
  Msg:              string;
  ExitCode:         Integer;
  Args:             TStringList;
begin
  AsmFile := ChangeFileExt(AIRFile, '.s');
  RTLPath := FindRTL;

  Args := TStringList.Create;
  try
    Args.Add('-o');
    Args.Add(AsmFile);
    Args.Add(AIRFile);
    ExitCode := RunProcess('qbe', Args, Msg);
  finally
    Args.Free;
  end;
  if ExitCode <> 0 then
  begin
    WriteLn(StdErr, 'qbe error (exit ', ExitCode, '):');
    Write(StdErr, Msg);
    Halt(1);
  end;

  Args := TStringList.Create;
  try
    Args.Add('-o');
    Args.Add(AOutputFile);
    if AOPDFAsmFile <> '' then
      Args.Add('-no-pie');  { OPDF addresses are absolute; PIE relocation breaks them }
    Args.Add(AsmFile);
    if (AOPDFAsmFile <> '') and FileExists(AOPDFAsmFile) then
      Args.Add(AOPDFAsmFile);
    if RTLPath <> '' then
      Args.Add(RTLPath);
    Args.Add('-lm');  { math functions (sqrt, sin, cos, etc.) }
    ExitCode := RunProcess('cc', Args, Msg);
  finally
    Args.Free;
  end;

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
  EmitIR:      Boolean;
  OPDFEnabled: Boolean;
  OPDFAsmFile: string;
  CacheDir:    string;
  Source:   TStringList;
  Lexer:    TLexer;
  Parser:   TParser;
  Prog:     TProgram;
  Semantic: TSemanticAnalyser;
  CG:       TCodeGenQBE;
  OE:       TOPDFEmitter;
  Loader:   TUnitLoader;
  Units:    TObjectList;
  I:        Integer;
  IR:       string;
  UnitIR:   string;
  IRFile:   string;
  UnitName: string;
  UnitPath: string;

begin
  SearchPaths := nil;
  OPDFEnabled := False;
  OPDFAsmFile := '';
  CacheDir    := '';
  if IsFPCStyleInvocation then
  begin
    if not ParseFPCArgs(SourceFile, OutputFile, SearchPaths, OPDFEnabled) then
    begin
      PrintUsage;
      Halt(1);
    end;
    EmitIR := False;
  end
  else
  begin
    if not ParseArgs(SourceFile, OutputFile, EmitIR, OPDFEnabled, SearchPaths, CacheDir) then
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
      WriteLn(StdErr, 'Error reading source: ', Exception(E).Message);
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
      Lexer  := TLexer.Create(Source.Text, SourceFile);
      Parser := TParser.Create(Lexer);
      Prog   := Parser.Parse;
    except
      on E: Exception do
      begin
        WriteLn(StdErr, 'Parse error: ', Exception(E).Message);
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
          Semantic.AnalyseUnitForExport(TUnit(Units.Items[I]));
      end;
      Semantic.Analyse(Prog);
    except
      on E: ESemanticError do
      begin
        WriteLn(StdErr, 'Semantic error: ', Exception(E).Message);
        Halt(1);
      end;
      on E: EUnitNotFound do
      begin
        WriteLn(StdErr, 'Unit not found: ', Exception(E).Message);
        Halt(1);
      end;
      on E: ECircularDependency do
      begin
        WriteLn(StdErr, 'Circular dependency: ', Exception(E).Message);
        Halt(1);
      end;
      on E: Exception do
      begin
        WriteLn(StdErr, 'Compiler error: ', Exception(E).Message);
        Halt(1);
      end;
    end;

    try
      {$IFDEF FPC}
      { IR caching — FPC-only; uses TSearchRec etc. not available under Blaise }
      if CacheDir <> '' then
      begin
        UnitIR := CacheKeyForFile(SourceFile);
        if Units <> nil then
          for I := 0 to Units.Count - 1 do
          begin
            UnitName := TUnit(Units.Items[I]).Name;
            UnitPath := TUnit(Units.Items[I]).SourceFile;
            UnitIR := UnitIR + '|' + UnitName + ':' + CacheKeyForFile(UnitPath);
          end;

        IRFile := IncludeTrailingPathDelimiter(CacheDir) + '__full__.ssa';
        Source := TStringList.Create;
        try
          if FileExists(IRFile) and FileExists(IRFile + '.key') then
          begin
            Source.LoadFromFile(IRFile + '.key');
            if Trim(Source.Text) = UnitIR then
            begin
              Source.LoadFromFile(IRFile);
              IR := Source.Text;
            end;
          end;
        finally
          Source.Free;
          Source := nil;
        end;
      end;
      {$ENDIF}

      { Full codegen (or fallback if caching was skipped/missed) }
      if IR = '' then
      begin
        CG := TCodeGenQBE.Create;
        try
          if (Units <> nil) and (Units.Count > 0) then
          begin
            CG.SetSymbolTable(Prog.SymbolTable);
            for I := 0 to Units.Count - 1 do
              CG.AppendUnit(TUnit(Units.Items[I]));
            CG.AppendProgram(Prog);
          end
          else
            CG.Generate(Prog);
          IR := CG.GetOutput;
        finally
          CG.Free;
          CG := nil;
        end;

        {$IFDEF FPC}
        if CacheDir <> '' then
        begin
          if ForceDirectories(CacheDir) then
          begin
            IRFile := IncludeTrailingPathDelimiter(CacheDir) + '__full__.ssa';
            Source := TStringList.Create;
            try
              Source.Text := IR;
              Source.SaveToFile(IRFile);
            finally
              Source.Free;
              Source := nil;
            end;
            Source := TStringList.Create;
            try
              Source.Text := UnitIR;
              Source.SaveToFile(IRFile + '.key');
            finally
              Source.Free;
              Source := nil;
            end;
          end;
        end;
        {$ENDIF}
      end;

      if OPDFEnabled then
      begin
        OPDFAsmFile := ChangeFileExt(OutputFile, '.opdf.s');
        OE := TOPDFEmitter.Create(Prog, SourceFile);
        try
          OE.EmitToFile(OPDFAsmFile);
        finally
          OE.Free;
        end;
      end;
    except
      on E: Exception do
      begin
        WriteLn(StdErr, 'Code generation error: ', Exception(E).Message);
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
      WriteLn(StdErr, 'Error writing IR: ', Exception(E).Message);
      Halt(1);
    end;
  end;

  CompileToNative(IRFile, OutputFile, OPDFAsmFile);
  DeleteFile(IRFile);
  if OPDFAsmFile <> '' then
    DeleteFile(OPDFAsmFile);
end.
