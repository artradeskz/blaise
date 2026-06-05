{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

program KanbanApp;

{ TUI Kanban board — a three-column task tracker.
  Data is stored in a .kanban file with optional per-task detail files
  in a .kanban.d/ subdirectory.

  Usage:  kanban [path/to/board.kanban]
  Default: ./board.kanban }

uses
  kanban.terminal, kanban.data, kanban.ui;

var
  FilePath: string;
  Term: TTerminal;
  Board: TBoard;
  UI: TKanbanUI;

begin
  if ParamCount >= 1 then
    FilePath := ParamStr(1)
  else
    FilePath := 'board.kanban';

  Term := TTerminal.Create;
  Board := TBoard.Create(FilePath);
  UI := TKanbanUI.Create(Term, Board);
  try
    Board.Load;
    UI.Run
  finally
    UI.Free;
    Board.Free;
    Term.Free
  end
end.
