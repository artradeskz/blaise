{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uUnitLoader;

{ Resolves unit names to source files, parses them, and returns a
  dependency-ordered list (leaves first).  Cycle detection raises
  ECircularDependency; missing units raise EUnitNotFound.

  Built-in FPC RTL unit names (SysUtils, Classes, etc.) are silently
  skipped — their symbols are already registered by TSymbolTable.RegisterBuiltins.
  User-defined units in the search paths are loaded and parsed normally. }

interface

uses
  SysUtils, Classes, contnrs,
  uLexer, uParser, uAST;

type
  EUnitNotFound       = class(Exception);
  ECircularDependency = class(Exception);

  TUnitLoader = class
  public
    constructor Create(const ASearchPaths: TStringList);
    destructor Destroy; override;
    { Returns an owned TObjectList of TUnit in dependency order (leaves
      first).  The caller is responsible for freeing the list. }
    function LoadAll(const AUnitNames: TStringList): TObjectList;
  private
    FSearchPaths: TStringList;  { not owned }
    FLoading:     TStringList;  { units currently on the load stack — cycle detection }
    FLoadedNames: TStringList;  { units already fully loaded }
    FResult:      TObjectList;  { the in-progress output list (not owned here) }
    function IsBuiltin(const AName: string): Boolean;
    function Locate(const AName: string): string;
    function LoadOne(const APath: string): TUnit;
    procedure LoadTransitive(const AName: string);
  end;

implementation

function TUnitLoader.IsBuiltin(const AName: string): Boolean;
begin
  Result :=
    SameText(AName, 'System')   or SameText(AName, 'Windows')   or
    SameText(AName, 'Unix')     or SameText(AName, 'BaseUnix')  or
    SameText(AName, 'CThreads') or SameText(AName, 'FGL')       or
    SameText(AName, 'Types');
end;

function TUnitLoader.Locate(const AName: string): string;
var
  I:    Integer;
  Base: string;
  Path: string;
begin
  for I := 0 to FSearchPaths.Count - 1 do
  begin
    Base := IncludeTrailingPathDelimiter(FSearchPaths.Strings[I]);
    { Try lowercase first — Blaise convention for unit file names }
    Path := Base + LowerCase(AName) + '.pas';
    if FileExists(Path) then
    begin
      Exit(Path);
    end;
    { Fallback: exact case as written in the uses clause }
    Path := Base + AName + '.pas';
    if FileExists(Path) then
    begin
      Exit(Path);
    end;
  end;
  Result := '';
end;

function TUnitLoader.LoadOne(const APath: string): TUnit;
var
  SL: TStringList;
  L:  TLexer;
  P:  TParser;
begin
  SL := TStringList.Create;
  try
    SL.LoadFromFile(APath);
    L := TLexer.Create(SL.Text, APath);
    try
      P := TParser.Create(L);
      try
        Result := P.ParseUnit;
        Result.SourceFile := APath;
      finally
        P.Free;
      end;
    finally
      L.Free;
    end;
  finally
    SL.Free;
  end;
end;

procedure TUnitLoader.LoadTransitive(const AName: string);
var
  Path: string;
  U:    TUnit;
  I:    Integer;
begin
  if IsBuiltin(AName) then Exit;
  if FLoadedNames.IndexOf(AName) >= 0 then Exit;  { already in result list }

  if FLoading.IndexOf(AName) >= 0 then
    raise ECircularDependency.Create(Format(
      'Circular unit dependency: ''%s''', [AName]));

  Path := Locate(AName);
  if Path = '' then
    raise EUnitNotFound.Create(Format(
      'Unit ''%s'' not found in search paths', [AName]));

  FLoading.Add(AName);
  U := nil;
  try
    U := LoadOne(Path);
    { Post-order DFS: process dependencies before this unit }
    for I := 0 to U.UsedUnits.Count - 1 do
      LoadTransitive(U.UsedUnits.Strings[I]);
    { Append this unit after all its dependencies }
    FResult.Add(U);
    FLoadedNames.Add(AName);
    U := nil;  { ownership transferred to FResult }
  finally
    U.Free;  { no-op if U = nil (success path) or on error }
    FLoading.Delete(FLoading.IndexOf(AName));
  end;
end;

constructor TUnitLoader.Create(const ASearchPaths: TStringList);
begin
  inherited Create;
  FSearchPaths := ASearchPaths;
  FLoading     := TStringList.Create;
  FLoading.CaseSensitive := False;
  FLoadedNames := TStringList.Create;
  FLoadedNames.CaseSensitive := False;
end;

destructor TUnitLoader.Destroy;
begin
  FLoadedNames.Free;
  FLoading.Free;
  inherited Destroy;
end;

function TUnitLoader.LoadAll(const AUnitNames: TStringList): TObjectList;
var
  I: Integer;
begin
  Result  := TObjectList.Create(True);  { owns TUnit items }
  FResult := Result;
  try
    for I := 0 to AUnitNames.Count - 1 do
      LoadTransitive(AUnitNames.Strings[I]);
  except
    FResult := nil;
    Result.Free;
    raise;
  end;
  FResult := nil;
end;

end.
