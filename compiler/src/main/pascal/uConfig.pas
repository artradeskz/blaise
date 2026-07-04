{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uConfig;

interface

uses
  Classes, SysUtils;

function FindConfigFile: string;

procedure ParseConfigLines(ALines: TStringList; const ABaseDir: string;
  APaths: TStringList);

procedure LoadConfigPaths(APaths: TStringList);

implementation

function FindConfigFile: string;
var
  BinDir: string;
  Home:   string;
begin
  BinDir := IncludeTrailingPathDelimiter(ExtractFilePath(ParamStr(0)));
  Result := BinDir + 'blaise.cfg';
  if FileExists(Result) then
    Exit;
  Home := GetEnvironmentVariable('HOME');
  if Home <> '' then
  begin
    Result := IncludeTrailingPathDelimiter(Home) + '.blaise.cfg';
    if FileExists(Result) then
      Exit;
  end;
  Result := '';
end;

procedure ParseConfigLines(ALines: TStringList; const ABaseDir: string;
  APaths: TStringList);
var
  I:     Integer;
  Line:  string;
  EqPos: Integer;
  Key:   string;
  Value: string;
begin
  for I := 0 to ALines.Count - 1 do
  begin
    Line := Trim(ALines.Strings[I]);
    if Length(Line) = 0 then
      Continue;
    if Copy(Line, 0, 1) = '#' then
      Continue;
    EqPos := Pos('=', Line);
    if EqPos < 0 then
      Continue;
    Key   := Trim(Copy(Line, 0, EqPos));
    Value := Trim(Copy(Line, EqPos + 1, Length(Line)));
    if SameText(Key, 'unit-path') then
    begin
      if (Length(Value) > 0) and (Copy(Value, 0, 1) <> '/') then
        Value := IncludeTrailingPathDelimiter(ABaseDir) + Value;
      APaths.Add(Value);
    end
    else
      ; { silently skip unrecognised keys }
  end;
end;

procedure LoadConfigPaths(APaths: TStringList);
var
  CfgFile: string;
  Lines:   TStringList;
  BaseDir: string;
begin
  CfgFile := FindConfigFile();
  if CfgFile = '' then
    Exit;
  Lines := TStringList.Create();
  try
    Lines.LoadFromFile(CfgFile);
    BaseDir := ExtractFilePath(CfgFile);
    ParseConfigLines(Lines, BaseDir, APaths);
  finally
    Lines.Free();
  end;
end;

end.
