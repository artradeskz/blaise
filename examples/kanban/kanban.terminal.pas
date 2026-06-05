{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit kanban.terminal;

interface

const
  KEY_NONE      = -1;
  KEY_ENTER     = 13;
  KEY_ESCAPE    = 27;
  KEY_BACKSPACE = 127;
  KEY_UP        = 1000;
  KEY_DOWN      = 1001;
  KEY_LEFT      = 1002;
  KEY_RIGHT     = 1003;
  KEY_HOME      = 1004;
  KEY_END       = 1005;
  KEY_TAB       = 9;

  COLOR_RESET   = 0;
  COLOR_RED     = 31;
  COLOR_GREEN   = 32;
  COLOR_YELLOW  = 33;
  COLOR_BLUE    = 34;
  COLOR_MAGENTA = 35;
  COLOR_CYAN    = 36;
  COLOR_WHITE   = 37;
  COLOR_GREY    = 90;

  STDIN_FD  = 0;
  STDOUT_FD = 1;

  TCSAFLUSH = 2;

  ICANON = 2;
  ECHO_  = 8;
  ISIG   = 1;
  IEXTEN = 32768;

  ICRNL = 256;
  IXON  = 1024;

  IFLAG_MASK = ICRNL or IXON;
  LFLAG_MASK = ECHO_ or ICANON or ISIG or IEXTEN;

  VMIN_IDX  = 6;
  VTIME_IDX = 5;

  TIOCGWINSZ = 21523;

type
  TTermios = record
    IFlag:  Integer;
    OFlag:  Integer;
    CFlag:  Integer;
    LFlag:  Integer;
    Line:   Byte;
    CC:     array[0..31] of Byte;
    ISpeed: Integer;
    OSpeed: Integer;
  end;
  PTermios = ^TTermios;

  TWinSize = record
    Row:    Word;
    Col:    Word;
    XPixel: Word;
    YPixel: Word;
  end;
  PWinSize = ^TWinSize;

function tcgetattr(Fd: Integer; T: PTermios): Integer;
  external name 'tcgetattr';
function tcsetattr(Fd: Integer; Action: Integer; T: PTermios): Integer;
  external name 'tcsetattr';
function ioctl(Fd: Integer; Request: Integer; Arg: Pointer): Integer;
  external name 'ioctl';
function libc_read(Fd: Integer; Buf: Pointer; Count: Int64): Int64;
  external name 'read';

type
  TTerminal = class
    FRows: Integer;
    FCols: Integer;
    FBuf: string;
    FSaved: Boolean;
    procedure EnableRawMode;
    procedure DisableRawMode;
    procedure QuerySize;
    function ReadByte: Integer;
    function ReadKey: Integer;
    procedure BufClear;
    procedure BufWrite(const S: string);
    procedure BufFlush;
    procedure HideCursor;
    procedure ShowCursor;
    procedure MoveTo(Row, Col: Integer);
    procedure ClearScreen;
    procedure SetFg(Color: Integer);
    procedure SetBg(Color: Integer);
    procedure SetBold;
    procedure ResetAttr;
    procedure DrawBox(Row, Col, Width, Height: Integer; const Title: string);
    procedure DrawHLine(Row, Col, Width: Integer);
    property Rows: Integer read FRows;
    property Cols: Integer read FCols;
  end;

implementation

uses StrUtils;

var
  GOrigTermios: TTermios;

procedure TTerminal.EnableRawMode;
var
  Raw: TTermios;
  P: PChar;
begin
  if not FSaved then
  begin
    tcgetattr(STDIN_FD, @GOrigTermios);
    FSaved := True
  end;
  Raw := GOrigTermios;
  Raw.IFlag := Raw.IFlag and (IFLAG_MASK xor -1);
  Raw.LFlag := Raw.LFlag and (LFLAG_MASK xor -1);
  P := PChar(@Raw.CC);
  P[VMIN_IDX] := #0;
  P[VTIME_IDX] := #1;
  tcsetattr(STDIN_FD, TCSAFLUSH, @Raw)
end;

procedure TTerminal.DisableRawMode;
begin
  if FSaved then
    tcsetattr(STDIN_FD, TCSAFLUSH, @GOrigTermios)
end;

procedure TTerminal.QuerySize;
var
  WS: TWinSize;
begin
  if ioctl(STDOUT_FD, TIOCGWINSZ, @WS) = 0 then
  begin
    FRows := WS.Row;
    FCols := WS.Col
  end
  else
  begin
    FRows := 24;
    FCols := 80
  end
end;

function TTerminal.ReadByte: Integer;
var
  Ch: Byte;
  N: Int64;
begin
  N := libc_read(STDIN_FD, @Ch, 1);
  if N <= 0 then
    Result := -1
  else
    Result := Ch
end;

function TTerminal.ReadKey: Integer;
var
  B1, B2, B3: Integer;
begin
  B1 := Self.ReadByte;
  if B1 = KEY_NONE then Exit(KEY_NONE);

  if B1 <> 27 then Exit(B1);

  B2 := Self.ReadByte;
  if B2 = KEY_NONE then Exit(KEY_ESCAPE);

  if B2 = 91 then
  begin
    B3 := Self.ReadByte;
    if B3 = 65 then Exit(KEY_UP);
    if B3 = 66 then Exit(KEY_DOWN);
    if B3 = 67 then Exit(KEY_RIGHT);
    if B3 = 68 then Exit(KEY_LEFT);
    if B3 = 72 then Exit(KEY_HOME);
    if B3 = 70 then Exit(KEY_END)
  end;

  Result := KEY_ESCAPE
end;

procedure TTerminal.BufClear;
begin
  FBuf := ''
end;

procedure TTerminal.BufWrite(const S: string);
begin
  FBuf := FBuf + S
end;

procedure TTerminal.BufFlush;
begin
  if Length(FBuf) > 0 then
    Write(FBuf);
  FBuf := ''
end;

procedure TTerminal.HideCursor;
begin
  Self.BufWrite(Chr(27) + '[?25l')
end;

procedure TTerminal.ShowCursor;
begin
  Self.BufWrite(Chr(27) + '[?25h')
end;

procedure TTerminal.MoveTo(Row, Col: Integer);
begin
  Self.BufWrite(Chr(27) + '[' + IntToStr(Row) + ';' + IntToStr(Col) + 'H')
end;

procedure TTerminal.ClearScreen;
begin
  Self.BufWrite(Chr(27) + '[2J');
  Self.BufWrite(Chr(27) + '[H')
end;

procedure TTerminal.SetFg(Color: Integer);
begin
  Self.BufWrite(Chr(27) + '[' + IntToStr(Color) + 'm')
end;

procedure TTerminal.SetBg(Color: Integer);
begin
  Self.BufWrite(Chr(27) + '[' + IntToStr(Color + 10) + 'm')
end;

procedure TTerminal.SetBold;
begin
  Self.BufWrite(Chr(27) + '[1m')
end;

procedure TTerminal.ResetAttr;
begin
  Self.BufWrite(Chr(27) + '[0m')
end;

procedure TTerminal.DrawBox(Row, Col, Width, Height: Integer; const Title: string);
var
  I: Integer;
  TitleStr: string;
begin
  Self.MoveTo(Row, Col);
  Self.BufWrite(Chr(226) + Chr(148) + Chr(140));
  I := 0;
  while I < Width - 2 do
  begin
    Self.BufWrite(Chr(226) + Chr(148) + Chr(128));
    I := I + 1
  end;
  Self.BufWrite(Chr(226) + Chr(148) + Chr(144));

  if Length(Title) > 0 then
  begin
    TitleStr := ' ' + Title + ' ';
    Self.MoveTo(Row, Col + 2);
    Self.SetBold;
    Self.BufWrite(TitleStr);
    Self.ResetAttr
  end;

  I := 1;
  while I < Height - 1 do
  begin
    Self.MoveTo(Row + I, Col);
    Self.BufWrite(Chr(226) + Chr(148) + Chr(130));
    Self.MoveTo(Row + I, Col + Width - 1);
    Self.BufWrite(Chr(226) + Chr(148) + Chr(130));
    I := I + 1
  end;

  Self.MoveTo(Row + Height - 1, Col);
  Self.BufWrite(Chr(226) + Chr(148) + Chr(148));
  I := 0;
  while I < Width - 2 do
  begin
    Self.BufWrite(Chr(226) + Chr(148) + Chr(128));
    I := I + 1
  end;
  Self.BufWrite(Chr(226) + Chr(148) + Chr(152))
end;

procedure TTerminal.DrawHLine(Row, Col, Width: Integer);
var
  I: Integer;
begin
  Self.MoveTo(Row, Col);
  I := 0;
  while I < Width do
  begin
    Self.BufWrite(Chr(226) + Chr(148) + Chr(128));
    I := I + 1
  end
end;

end.
