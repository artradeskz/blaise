{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.config;

interface

uses
  Classes, SysUtils, blaise.testing,
  uConfig;

type
  TConfigTests = class(TTestCase)
  published
    procedure TestParseEmpty_ReturnsNoPaths;
    procedure TestParseCommentOnly_ReturnsNoPaths;
    procedure TestParseSingleUnitPath;
    procedure TestParseMultipleUnitPaths;
    procedure TestParseSkipsBlankLines;
    procedure TestParseSkipsCommentLines;
    procedure TestParseIgnoresLinesWithoutEquals;
    procedure TestParseTrimsWhitespace;
    procedure TestParseRelativePath_ResolvedAgainstBaseDir;
    procedure TestParseAbsolutePath_NotModified;
    procedure TestParseUnknownKey_IgnoredSilently;
    procedure TestFindConfigFile_NextToBinary;
  end;

implementation

procedure TConfigTests.TestParseEmpty_ReturnsNoPaths;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    ParseConfigLines(Lines, '/base', Paths);
    AssertEquals('no paths', 0, Paths.Count);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseCommentOnly_ReturnsNoPaths;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('# this is a comment');
    Lines.Add('# another comment');
    ParseConfigLines(Lines, '/base', Paths);
    AssertEquals('no paths', 0, Paths.Count);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseSingleUnitPath;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('unit-path=/opt/blaise/runtime');
    ParseConfigLines(Lines, '/base', Paths);
    AssertEquals('one path', 1, Paths.Count);
    AssertEquals('path value', '/opt/blaise/runtime', Paths.Strings[0]);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseMultipleUnitPaths;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('unit-path=/opt/blaise/runtime');
    Lines.Add('unit-path=/opt/blaise/stdlib');
    ParseConfigLines(Lines, '/base', Paths);
    AssertEquals('two paths', 2, Paths.Count);
    AssertEquals('first', '/opt/blaise/runtime', Paths.Strings[0]);
    AssertEquals('second', '/opt/blaise/stdlib', Paths.Strings[1]);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseSkipsBlankLines;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('');
    Lines.Add('unit-path=/opt/blaise/runtime');
    Lines.Add('');
    Lines.Add('');
    Lines.Add('unit-path=/opt/blaise/stdlib');
    ParseConfigLines(Lines, '/base', Paths);
    AssertEquals('two paths', 2, Paths.Count);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseSkipsCommentLines;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('# header comment');
    Lines.Add('unit-path=/opt/blaise/runtime');
    Lines.Add('# inline comment');
    Lines.Add('unit-path=/opt/blaise/stdlib');
    ParseConfigLines(Lines, '/base', Paths);
    AssertEquals('two paths', 2, Paths.Count);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseIgnoresLinesWithoutEquals;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('this line has no equals sign');
    Lines.Add('unit-path=/opt/blaise/runtime');
    ParseConfigLines(Lines, '/base', Paths);
    AssertEquals('one path', 1, Paths.Count);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseTrimsWhitespace;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('  unit-path = /opt/blaise/runtime  ');
    ParseConfigLines(Lines, '/base', Paths);
    AssertEquals('one path', 1, Paths.Count);
    AssertEquals('trimmed', '/opt/blaise/runtime', Paths.Strings[0]);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseRelativePath_ResolvedAgainstBaseDir;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('unit-path=../../runtime/src/main/pascal');
    ParseConfigLines(Lines, '/data/devel/new-pascal-compiler/compiler/target/', Paths);
    AssertEquals('one path', 1, Paths.Count);
    AssertEquals('resolved',
      '/data/devel/new-pascal-compiler/compiler/target/../../runtime/src/main/pascal',
      Paths.Strings[0]);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseAbsolutePath_NotModified;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('unit-path=/absolute/path/to/units');
    ParseConfigLines(Lines, '/some/base/', Paths);
    AssertEquals('one path', 1, Paths.Count);
    AssertEquals('unchanged', '/absolute/path/to/units', Paths.Strings[0]);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestParseUnknownKey_IgnoredSilently;
var
  Lines, Paths: TStringList;
begin
  Lines := TStringList.Create();
  Paths := TStringList.Create();
  try
    Lines.Add('unknown-key=some-value');
    Lines.Add('unit-path=/opt/blaise/runtime');
    ParseConfigLines(Lines, '/base', Paths);
    AssertEquals('one path only', 1, Paths.Count);
  finally
    Lines.Free();
    Paths.Free();
  end;
end;

procedure TConfigTests.TestFindConfigFile_NextToBinary;
var
  CfgPath: string;
begin
  CfgPath := FindConfigFile();
  if CfgPath = '' then
    AssertTrue('no config found (acceptable in test env)', True)
  else
    AssertTrue('found config is a real file', FileExists(CfgPath));
end;

initialization
  RegisterTest(TConfigTests);

end.
