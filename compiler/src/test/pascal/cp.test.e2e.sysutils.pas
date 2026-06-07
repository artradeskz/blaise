{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.sysutils;

{ E2E tests for file I/O, CLI arguments, OS utility functions, and process
  management built-ins. }

interface

uses
  blaise.testing, classes, sysutils, cp.test.e2e.base;

type
  [Threaded]
  TE2ESysUtilsTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_ParamStr_PrintsArg;
    procedure TestRun_ParamCount_WithArgs;
    procedure TestRun_ReadWriteFile_RoundTrip;
    procedure TestRun_FileExists_TrueAndFalse;
    procedure TestRun_GetEnvVar_Path;
    procedure TestRun_Halt_ExitCode;
    procedure TestRun_ChangeFileExt_ChangesExtension;
    procedure TestRun_ExtractFileName_ReturnsName;
    procedure TestRun_ExtractFilePath_ReturnsDir;
    procedure TestRun_IncludeTrailingPathDelimiter_AppendsSlash;
    procedure TestRun_GetProcessID_ReturnsNonZero;
    procedure TestRun_DirectoryExists_TrueAndFalse;
    procedure TestRun_GetTempDir_ReturnsPath;
    procedure TestRun_ForceDirectories_CreatesTree;
    procedure TestRun_Sleep_DoesNotCrash;
    procedure TestRun_ProcessBuiltins_CapturesOutput;
    procedure TestRun_ProcessBuiltins_ExitCode;
    { New tests for Step 5 builtins }
    procedure TestRun_RenameFile_Works;
    procedure TestRun_RenameFile_MissingSource_ReturnsFalse;
    procedure TestRun_SetCurrentDir_ChangesDir;
    procedure TestRun_ExtractFileExt_ReturnsExt;
    procedure TestRun_BoolToStr_TrueAndFalse;
    procedure TestRun_PlatformConstants;
    procedure TestRun_GetCurrentDir_ReturnsNonEmpty;
    procedure TestRun_FileAge_ReturnsTimestamp;
  end;

implementation

procedure TE2ESysUtilsTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-sysutils');
end;

const
  SrcParamStrPrint =
    '''
        program P;
        begin
          WriteLn(ParamStr(1))
        end.
        ''';

  SrcParamCountPrint =
    '''
        program P;
        begin
          WriteLn(ParamCount())
        end.
        ''';

  SrcReadWriteFile =
    '''
        program P;
        var S: string;
        begin
          WriteFile(ParamStr(1), 'hello file');
          S := ReadFile(ParamStr(1));
          WriteLn(S)
        end.
        ''';

  SrcFileExistsTest =
    '''
        program P;
        begin
          WriteLn(FileExists(ParamStr(1)));
          WriteLn(FileExists('__no_such_file_xyz__'))
        end.
        ''';

  SrcGetEnvVarTest =
    '''
        program P;
        var S: string;
        begin
          S := GetEnvVar('BLAISE_TEST_VAR');
          WriteLn(S)
        end.
        ''';

  SrcHaltTest =
    '''
        program P;
        begin
          WriteLn(42);
          Halt(7)
        end.
        ''';

  SrcChangeFileExtTest =
    '''
        program P;
        begin
          WriteLn(ChangeFileExt('test.pas', '.bak'));
          WriteLn(ChangeFileExt('noext', '.o'));
          WriteLn(ChangeFileExt('a.b.c', ''))
        end.
        ''';

  SrcExtractFileNameTest =
    '''
        program P;
        begin
          WriteLn(ExtractFileName('/usr/bin/ls'));
          WriteLn(ExtractFileName('ls'))
        end.
        ''';

  SrcExtractFilePathTest =
    '''
        program P;
        begin
          WriteLn(ExtractFilePath('/usr/bin/ls'));
          WriteLn('[' + ExtractFilePath('ls') + ']')
        end.
        ''';

  SrcIncludeTrailingPathDelimiterTest =
    '''
        program P;
        begin
          WriteLn(IncludeTrailingPathDelimiter('/usr/bin'));
          WriteLn(IncludeTrailingPathDelimiter('/usr/bin/'))
        end.
        ''';

  SrcGetProcessID =
    '''
        program P;
        begin
          WriteLn(GetProcessID())
        end.
        ''';

  SrcDirectoryExists =
    '''
        program P;
        begin
          WriteLn(DirectoryExists('/tmp'));
          WriteLn(DirectoryExists('/__no_such_dir__'))
        end.
        ''';

  SrcGetTempDir =
    '''
        program P;
        begin
          WriteLn(GetTempDir())
        end.
        ''';

  SrcForceDirectories =
    '''
        program P;
        var Dir: string;
        begin
          Dir := ParamStr(1);
          WriteLn(ForceDirectories(Dir));
          WriteLn(DirectoryExists(Dir))
        end.
        ''';

  SrcSleepTest =
    '''
        program P;
        begin
          Sleep(1);
          WriteLn('ok')
        end.
        ''';

  SrcProcessBuiltinsCapture =
    '''
        program P;
        var
          H:     Pointer;
          Output: string;
          Chunk:  string;
        begin
          H := ProcessCreate();
          ProcessSetExe(H, 'echo');
          ProcessAddArg(H, 'hello from process');
          ProcessExecute(H);
          Output := '';
          Chunk := ProcessReadOutput(H);
          while Chunk <> '' do
          begin
            Output := Output + Chunk;
            Chunk := ProcessReadOutput(H)
          end;
          ProcessWaitOnExit(H);
          ProcessFree(H);
          Write(Output)
        end.
        ''';

  SrcProcessBuiltinsExitCode =
    '''
        program P;
        var
          H:    Pointer;
          Code: Integer;
          Chunk: string;
        begin
          H := ProcessCreate();
          ProcessSetExe(H, 'true');
          ProcessExecute(H);
          Chunk := ProcessReadOutput(H);
          while Chunk <> '' do
            Chunk := ProcessReadOutput(H);
          ProcessWaitOnExit(H);
          Code := ProcessExitCode(H);
          ProcessFree(H);
          WriteLn(IntToStr(Code))
        end.
        ''';

procedure TE2ESysUtilsTests.TestRun_ParamStr_PrintsArg;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcParamStrPrint, Output, RCode, ['hello']));
  AssertEquals('ParamStr(1) = hello', 'hello', Trim(Output));
end;

procedure TE2ESysUtilsTests.TestRun_ParamCount_WithArgs;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcParamCountPrint, Output, RCode, ['a', 'b', 'c']));
  AssertEquals('ParamCount = 3', '3', Trim(Output));
end;

procedure TE2ESysUtilsTests.TestRun_ReadWriteFile_RoundTrip;
var Output: string; RCode: Integer; TmpFile: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  TmpFile := GetTempFileName('', 'blaise_rwtest');
  try
    AssertTrue('compile+run',
      CompileAndRun(SrcReadWriteFile, Output, RCode, [TmpFile]));
    AssertEquals('ReadFile content', 'hello file', Trim(Output));
  finally
    if FileExists(TmpFile) then DeleteFile(TmpFile);
  end;
end;

procedure TE2ESysUtilsTests.TestRun_FileExists_TrueAndFalse;
var
  Output: string;
  RCode: Integer;
  TmpFile: string;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  TmpFile := GetTempFileName('', 'blaise_fe_test');
  Lines := TStringList.Create();
  Lines.Add('x');
  Lines.SaveToFile(TmpFile);
  Lines.Free();
  try
    AssertTrue('compile+run',
      CompileAndRun(SrcFileExistsTest, Output, RCode, [TmpFile]));
    Lines := TStringList.Create();
    try
      Lines.Text := Trim(Output);
      AssertEquals('existing file = True', 'True', Lines.Strings[0]);
      AssertEquals('missing file = False', 'False', Lines.Strings[1]);
    finally
      Lines.Free();
    end;
  finally
    if FileExists(TmpFile) then DeleteFile(TmpFile);
  end;
end;

procedure TE2ESysUtilsTests.TestRun_GetEnvVar_Path;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcGetEnvVarTest, Output, RCode));
  AssertTrue('GetEnvVar(BLAISE_TEST_VAR) returns empty when unset',
    Trim(Output) = '');
end;

procedure TE2ESysUtilsTests.TestRun_Halt_ExitCode;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  CompileAndRun(SrcHaltTest, Output, RCode);
  AssertEquals('WriteLn before Halt', '42', Trim(Output));
  AssertEquals('Halt(7) sets exit code', 7, RCode);
end;

procedure TE2ESysUtilsTests.TestRun_ChangeFileExt_ChangesExtension;
var Output: string; RCode: Integer; Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcChangeFileExtTest, Output, RCode));
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('test.pas->bak', 'test.bak', Lines.Strings[0]);
    AssertEquals('noext->o',      'noext.o',  Lines.Strings[1]);
    AssertEquals('a.b.c->empty',  'a.b',      Lines.Strings[2]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ESysUtilsTests.TestRun_ExtractFileName_ReturnsName;
var Output: string; RCode: Integer; Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcExtractFileNameTest, Output, RCode));
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('/usr/bin/ls -> ls', 'ls', Lines.Strings[0]);
    AssertEquals('ls -> ls',          'ls', Lines.Strings[1]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ESysUtilsTests.TestRun_ExtractFilePath_ReturnsDir;
var Output: string; RCode: Integer; Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcExtractFilePathTest, Output, RCode));
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('/usr/bin/ls -> /usr/bin/', '/usr/bin/', Lines.Strings[0]);
    AssertEquals('ls -> empty',              '[]',        Lines.Strings[1]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ESysUtilsTests.TestRun_IncludeTrailingPathDelimiter_AppendsSlash;
var Output: string; RCode: Integer; Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run',
    CompileAndRun(SrcIncludeTrailingPathDelimiterTest, Output, RCode));
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('/usr/bin -> /usr/bin/', '/usr/bin/', Lines.Strings[0]);
    AssertEquals('/usr/bin/ unchanged',   '/usr/bin/', Lines.Strings[1]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ESysUtilsTests.TestRun_GetProcessID_ReturnsNonZero;
var Output: string; RCode: Integer; PID: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcGetProcessID, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  PID := StrToInt(Trim(Output));
  AssertTrue('PID > 0', PID > 0);
end;

procedure TE2ESysUtilsTests.TestRun_DirectoryExists_TrueAndFalse;
var Output: string; RCode: Integer; Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcDirectoryExists, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('/tmp exists = True',  'True',  Lines.Strings[0]);
    AssertEquals('missing dir = False', 'False', Lines.Strings[1]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ESysUtilsTests.TestRun_GetTempDir_ReturnsPath;
var Output: string; RCode: Integer; Dir: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcGetTempDir, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  Dir := Trim(Output);
  AssertTrue('dir is non-empty', Length(Dir) > 0);
  AssertTrue('dir ends with /', Dir[Length(Dir) - 1] = '/');
end;

procedure TE2ESysUtilsTests.TestRun_ForceDirectories_CreatesTree;
var
  Output: string;
  RCode: Integer;
  Lines: TStringList;
  Dir: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Dir := IncludeTrailingPathDelimiter(GetTempDir()) +
         'blaise_test_' + IntToStr(GetProcessID()) + '/a/b/c';
  try
    AssertTrue('compile+run',
      CompileAndRun(SrcForceDirectories, Output, RCode, [Dir]));
    AssertEquals('exit code 0', 0, RCode);
    Lines := TStringList.Create();
    try
      Lines.Text := Trim(Output);
      AssertEquals('ForceDirectories returned True', 'True', Lines.Strings[0]);
      AssertEquals('DirectoryExists returned True',  'True', Lines.Strings[1]);
    finally
      Lines.Free();
    end;
  finally
    RemoveDir(Dir);
    RemoveDir(ExtractFilePath(ExcludeTrailingPathDelimiter(Dir)));
    RemoveDir(ExtractFilePath(ExcludeTrailingPathDelimiter(
      ExtractFilePath(ExcludeTrailingPathDelimiter(Dir)))));
    RemoveDir(ExtractFilePath(ExcludeTrailingPathDelimiter(
      ExtractFilePath(ExcludeTrailingPathDelimiter(
        ExtractFilePath(ExcludeTrailingPathDelimiter(Dir)))))));
  end;
end;

procedure TE2ESysUtilsTests.TestRun_Sleep_DoesNotCrash;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcSleepTest, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output is ok', 'ok', Trim(Output));
end;

procedure TE2ESysUtilsTests.TestRun_ProcessBuiltins_CapturesOutput;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcProcessBuiltinsCapture, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('captured echo output', 'hello from process', Trim(Output));
end;

procedure TE2ESysUtilsTests.TestRun_ProcessBuiltins_ExitCode;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcProcessBuiltinsExitCode, Output, RCode));
  AssertEquals('program exit code 0', 0, RCode);
  AssertEquals('true exits with 0', '0', Trim(Output));
end;

const
  SrcRenameFileWorks =
    '''
        program P;
        var OldName, NewName: string;
        begin
          OldName := ParamStr(1);
          NewName := ParamStr(2);
          WriteFile(OldName, 'rename-me');
          WriteLn(RenameFile(OldName, NewName));
          WriteLn(FileExists(OldName));
          WriteLn(FileExists(NewName))
        end.
        ''';

  SrcRenameFileMissing =
    '''
        program P;
        begin
          WriteLn(RenameFile('__no_such_source_xyz__', '__no_such_dest_xyz__'))
        end.
        ''';

  SrcSetCurrentDir =
    '''
        program P;
        var D: string;
        begin
          WriteLn(SetCurrentDir('/tmp'));
          D := GetCurrentDir();
          WriteLn(Length(D) > 0)
        end.
        ''';

  SrcExtractFileExt =
    '''
        program P;
        begin
          WriteLn(ExtractFileExt('/foo/bar.txt'));
          WriteLn(ExtractFileExt('noext'));
          WriteLn(ExtractFileExt('/usr/bin/ls.sh'))
        end.
        ''';

  SrcBoolToStr =
    '''
        program P;
        uses SysUtils;
        begin
          WriteLn(BoolToStr(True));
          WriteLn(BoolToStr(False))
        end.
        ''';

  SrcPlatformConstants =
    '''
        program P;
        begin
          WriteLn(LineEnding = #10);
          WriteLn(DirectorySeparator = '/');
          WriteLn(PathSeparator = ':')
        end.
        ''';

  SrcGetCurrentDir =
    '''
        program P;
        begin
          WriteLn(Length(GetCurrentDir()) > 0)
        end.
        ''';

  SrcFileAge =
    '''
        program P;
        var Age: Int64;
        begin
          Age := FileAge(ParamStr(1));
          WriteLn(Age > 0);
          WriteLn(FileAge('__no_such_file_xyz__'))
        end.
        ''';

procedure TE2ESysUtilsTests.TestRun_RenameFile_Works;
var
  Output: string;
  RCode: Integer;
  OldFile, NewFile: string;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  OldFile := GetTempFileName('', 'blaise_rename_old');
  NewFile := OldFile + '.renamed';
  try
    AssertTrue('compile+run',
      CompileAndRun(SrcRenameFileWorks, Output, RCode, [OldFile, NewFile]));
    AssertEquals('exit code 0', 0, RCode);
    Lines := TStringList.Create();
    try
      Lines.Text := Trim(Output);
      AssertEquals('RenameFile returns True',  'True',  Lines.Strings[0]);
      AssertEquals('old name gone (False)',    'False', Lines.Strings[1]);
      AssertEquals('new name exists (True)',   'True',  Lines.Strings[2]);
    finally
      Lines.Free();
    end;
  finally
    if FileExists(OldFile) then DeleteFile(OldFile);
    if FileExists(NewFile) then DeleteFile(NewFile);
  end;
end;

procedure TE2ESysUtilsTests.TestRun_RenameFile_MissingSource_ReturnsFalse;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcRenameFileMissing, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('RenameFile missing = False', 'False', Trim(Output));
end;

procedure TE2ESysUtilsTests.TestRun_SetCurrentDir_ChangesDir;
var
  Output: string;
  RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcSetCurrentDir, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('SetCurrentDir /tmp returns True', 'True', Lines.Strings[0]);
    AssertEquals('GetCurrentDir non-empty',         'True', Lines.Strings[1]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ESysUtilsTests.TestRun_ExtractFileExt_ReturnsExt;
var
  Output: string;
  RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcExtractFileExt, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('/foo/bar.txt -> .txt', '.txt', Lines.Strings[0]);
    AssertEquals('noext -> empty',       '',     Lines.Strings[1]);
    AssertEquals('/usr/bin/ls.sh -> .sh', '.sh', Lines.Strings[2]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ESysUtilsTests.TestRun_BoolToStr_TrueAndFalse;
var
  Output: string;
  RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcBoolToStr, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('BoolToStr(True)',  'True',  Lines.Strings[0]);
    AssertEquals('BoolToStr(False)', 'False', Lines.Strings[1]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ESysUtilsTests.TestRun_PlatformConstants;
var
  Output: string;
  RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcPlatformConstants, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('LineEnding = #10', 'True', Lines.Strings[0]);
    AssertEquals('DirectorySeparator = /', 'True', Lines.Strings[1]);
    AssertEquals('PathSeparator = :', 'True', Lines.Strings[2]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ESysUtilsTests.TestRun_GetCurrentDir_ReturnsNonEmpty;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcGetCurrentDir, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('GetCurrentDir non-empty', 'True', Trim(Output));
end;

procedure TE2ESysUtilsTests.TestRun_FileAge_ReturnsTimestamp;
var
  Output: string;
  RCode: Integer;
  TmpFile: string;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  TmpFile := GetTempFileName('', 'blaise_fileage_test');
  Lines := TStringList.Create();
  Lines.Add('x');
  Lines.SaveToFile(TmpFile);
  Lines.Free();
  try
    AssertTrue('compile+run',
      CompileAndRun(SrcFileAge, Output, RCode, [TmpFile]));
    Lines := TStringList.Create();
    try
      Lines.Text := Trim(Output);
      AssertEquals('existing file age > 0', 'True', Lines.Strings[0]);
      AssertEquals('missing file age = -1', '-1', Lines.Strings[1]);
    finally
      Lines.Free();
    end;
  finally
    if FileExists(TmpFile) then DeleteFile(TmpFile);
  end;
end;

initialization
  RegisterTest(TE2ESysUtilsTests);

end.
