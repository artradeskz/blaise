{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit kanban.data;

interface

uses Classes, Contnrs, StrUtils, DateUtils;

type
  TTaskStatus = (tsTodo, tsInProgress, tsDone);

  TTask = class
    FId: Integer;
    FTitle: string;
    FStatus: TTaskStatus;
    FCreated: string;
    FPriority: string;
    property Id: Integer read FId;
    property Title: string read FTitle write FTitle;
    property Status: TTaskStatus read FStatus write FStatus;
    property Created: string read FCreated;
    property Priority: string read FPriority write FPriority;
  end;

  TBoard = class
    FTasks: TObjectList;
    FNextId: Integer;
    FFilePath: string;
    function GetCount: Integer;
    procedure ParseLine(const Line: string; CurrentStatus: TTaskStatus);
    function FormatTask(Task: TTask): string;
  public
    constructor Create(const AFilePath: string);
    destructor Destroy; override;
    procedure Load;
    procedure Save;
    function AddTask(const ATitle: string; AStatus: TTaskStatus): TTask;
    procedure DeleteTask(AId: Integer);
    procedure MoveTask(AId: Integer; NewStatus: TTaskStatus);
    function FindById(AId: Integer): TTask;
    function CountByStatus(AStatus: TTaskStatus): Integer;
    function GetByStatusAt(AStatus: TTaskStatus; Index: Integer): TTask;
    function GetDetailPath(AId: Integer): string;
    function HasDetail(AId: Integer): Boolean;
    function LoadDetail(AId: Integer): string;
    procedure SaveDetail(AId: Integer; const AContent: string);
    property Count: Integer read GetCount;
    property FilePath: string read FFilePath;
  end;

function CreatedToLocalDate(const AUtcStr: string): string;

implementation

constructor TBoard.Create(const AFilePath: string);
begin
  inherited Create;
  FFilePath := AFilePath;
  FTasks := TObjectList.Create(True);
  FNextId := 1
end;

destructor TBoard.Destroy;
begin
  FTasks.Free;
  inherited Destroy
end;

function TBoard.GetCount: Integer;
begin
  Result := FTasks.Count
end;

procedure TBoard.ParseLine(const Line: string; CurrentStatus: TTaskStatus);
var
  S, Part, Key, Val: string;
  Task: TTask;
  PipePos, EqPos, TaskId: Integer;
begin
  S := Trim(Line);
  if Length(S) < 4 then Exit;
  if (S[0] <> '-') or (S[1] <> ' ') then Exit;

  S := Trim(Copy(S, 2, Length(S) - 2));

  PipePos := Pos('|', S);
  if PipePos < 0 then
  begin
    TaskId := StrToInt(Trim(S));
    Task := TTask.Create;
    Task.FId := TaskId;
    Task.FTitle := '(untitled)';
    Task.FStatus := CurrentStatus;
    Task.FCreated := '';
    Task.FPriority := '';
    FTasks.Add(Task);
    if TaskId >= FNextId then
      FNextId := TaskId + 1;
    Exit
  end;

  TaskId := StrToInt(Trim(Copy(S, 0, PipePos)));
  S := Trim(Copy(S, PipePos + 1, Length(S) - PipePos - 1));

  PipePos := Pos('|', S);
  if PipePos < 0 then
  begin
    Task := TTask.Create;
    Task.FId := TaskId;
    Task.FTitle := Trim(S);
    Task.FStatus := CurrentStatus;
    Task.FCreated := '';
    Task.FPriority := '';
    FTasks.Add(Task);
    if TaskId >= FNextId then
      FNextId := TaskId + 1;
    Exit
  end;

  Task := TTask.Create;
  Task.FId := TaskId;
  Task.FTitle := Trim(Copy(S, 0, PipePos));
  Task.FStatus := CurrentStatus;
  Task.FCreated := '';
  Task.FPriority := '';

  S := Trim(Copy(S, PipePos + 1, Length(S) - PipePos - 1));
  while Length(S) > 0 do
  begin
    PipePos := Pos('|', S);
    if PipePos < 0 then
    begin
      Part := Trim(S);
      S := ''
    end
    else
    begin
      Part := Trim(Copy(S, 0, PipePos));
      S := Trim(Copy(S, PipePos + 1, Length(S) - PipePos - 1))
    end;

    EqPos := Pos(':', Part);
    if EqPos >= 0 then
    begin
      Key := Trim(Copy(Part, 0, EqPos));
      Val := Trim(Copy(Part, EqPos + 1, Length(Part) - EqPos - 1));
      if Key = 'priority' then
        Task.FPriority := Val
      else if Key = 'created' then
        Task.FCreated := Val
    end
  end;

  FTasks.Add(Task);
  if Task.FId >= FNextId then
    FNextId := Task.FId + 1
end;

function TBoard.FormatTask(Task: TTask): string;
var
  S: string;
begin
  S := '- ' + IntToStr(Task.FId) + ' | ' + Task.FTitle;
  if Length(Task.FPriority) > 0 then
    S := S + ' | priority:' + Task.FPriority;
  if Length(Task.FCreated) > 0 then
    S := S + ' | created:' + Task.FCreated;
  Result := S
end;

procedure TBoard.Load;
var
  Lines: TStringList;
  I: Integer;
  Line: string;
  CurrentStatus: TTaskStatus;
  IdLine: string;
begin
  if not FileExists(FFilePath) then Exit;

  Lines := TStringList.Create;
  try
    Lines.LoadFromFile(FFilePath);
    CurrentStatus := tsTodo;
    I := 0;
    while I < Lines.Count do
    begin
      Line := Lines.Get(I);
      if StartsStr('## Todo', Line) then
        CurrentStatus := tsTodo
      else if StartsStr('## In Progress', Line) then
        CurrentStatus := tsInProgress
      else if StartsStr('## Done', Line) then
        CurrentStatus := tsDone
      else if StartsStr('#next-id:', Line) then
      begin
        IdLine := Trim(Copy(Line, 9, Length(Line) - 9));
        FNextId := StrToInt(IdLine)
      end
      else if StartsStr('- ', Line) then
        Self.ParseLine(Line, CurrentStatus);
      I := I + 1
    end
  finally
    Lines.Free
  end
end;

procedure TBoard.Save;
var
  Lines: TStringList;
  I: Integer;
  Task: TTask;
begin
  Lines := TStringList.Create;
  try
    Lines.Add('#next-id: ' + IntToStr(FNextId));
    Lines.Add('');
    Lines.Add('## Todo');
    I := 0;
    while I < FTasks.Count do
    begin
      Task := TTask(FTasks.Get(I));
      if Task.FStatus = tsTodo then
        Lines.Add(Self.FormatTask(Task));
      I := I + 1
    end;

    Lines.Add('');
    Lines.Add('## In Progress');
    I := 0;
    while I < FTasks.Count do
    begin
      Task := TTask(FTasks.Get(I));
      if Task.FStatus = tsInProgress then
        Lines.Add(Self.FormatTask(Task));
      I := I + 1
    end;

    Lines.Add('');
    Lines.Add('## Done');
    I := 0;
    while I < FTasks.Count do
    begin
      Task := TTask(FTasks.Get(I));
      if Task.FStatus = tsDone then
        Lines.Add(Self.FormatTask(Task));
      I := I + 1
    end;

    Lines.SaveToFile(FFilePath)
  finally
    Lines.Free
  end
end;

function TBoard.AddTask(const ATitle: string; AStatus: TTaskStatus): TTask;
var
  Now: TInstant;
  UtcDT: TDateTime;
begin
  Now := InstantNow;
  UtcDT := Now.ToUtcDateTime;
  Result := TTask.Create;
  Result.FId := FNextId;
  Result.FTitle := ATitle;
  Result.FStatus := AStatus;
  Result.FCreated := UtcDT.ToString;
  Result.FPriority := '';
  FNextId := FNextId + 1;
  FTasks.Add(Result)
end;

procedure TBoard.DeleteTask(AId: Integer);
var
  I: Integer;
  Task: TTask;
  DetailPath: string;
begin
  I := 0;
  while I < FTasks.Count do
  begin
    Task := TTask(FTasks.Get(I));
    if Task.FId = AId then
    begin
      DetailPath := Self.GetDetailPath(AId);
      if FileExists(DetailPath) then
        DeleteFile(DetailPath);
      FTasks.Delete(I);
      Exit
    end;
    I := I + 1
  end
end;

procedure TBoard.MoveTask(AId: Integer; NewStatus: TTaskStatus);
var
  Task: TTask;
begin
  Task := Self.FindById(AId);
  if Task <> nil then
    Task.FStatus := NewStatus
end;

function TBoard.FindById(AId: Integer): TTask;
var
  I: Integer;
  Task: TTask;
begin
  I := 0;
  while I < FTasks.Count do
  begin
    Task := TTask(FTasks.Get(I));
    if Task.FId = AId then
      Exit(Task);
    I := I + 1
  end;
  Result := nil
end;

function TBoard.CountByStatus(AStatus: TTaskStatus): Integer;
var
  I: Integer;
  Task: TTask;
begin
  Result := 0;
  I := 0;
  while I < FTasks.Count do
  begin
    Task := TTask(FTasks.Get(I));
    if Task.FStatus = AStatus then
      Result := Result + 1;
    I := I + 1
  end
end;

function TBoard.GetByStatusAt(AStatus: TTaskStatus; Index: Integer): TTask;
var
  I, Cnt: Integer;
  Task: TTask;
begin
  Cnt := 0;
  I := 0;
  while I < FTasks.Count do
  begin
    Task := TTask(FTasks.Get(I));
    if Task.FStatus = AStatus then
    begin
      if Cnt = Index then
        Exit(Task);
      Cnt := Cnt + 1
    end;
    I := I + 1
  end;
  Result := nil
end;

function TBoard.GetDetailPath(AId: Integer): string;
var
  DirPath: string;
begin
  DirPath := FFilePath + '.d';
  Result := DirPath + '/' + IntToStr(AId) + '.txt'
end;

function TBoard.HasDetail(AId: Integer): Boolean;
begin
  Result := FileExists(Self.GetDetailPath(AId))
end;

function TBoard.LoadDetail(AId: Integer): string;
var
  Path: string;
begin
  Path := Self.GetDetailPath(AId);
  if FileExists(Path) then
    Result := ReadFile(Path)
  else
    Result := ''
end;

procedure TBoard.SaveDetail(AId: Integer; const AContent: string);
var
  DirPath: string;
begin
  DirPath := FFilePath + '.d';
  if not DirectoryExists(DirPath) then
    ForceDirectories(DirPath);
  WriteFile(Self.GetDetailPath(AId), AContent)
end;

function CreatedToLocalDate(const AUtcStr: string): string;
var
  UtcDT: TDateTime;
  Inst: TInstant;
  LocalDT: TDateTime;
begin
  if Length(AUtcStr) = 0 then
    Exit('');
  UtcDT := ParseDateTime(AUtcStr);
  Inst := MakeInstantUtc(UtcDT.Date, UtcDT.Time);
  LocalDT := Inst.ToLocalDateTime(SystemOffset);
  Result := LocalDT.Date.ToString
end;

end.
