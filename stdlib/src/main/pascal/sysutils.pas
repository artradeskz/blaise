{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit SysUtils;

// Blaise RTL — SysUtils unit.
//
// Provides the Exception base class and the BoolToStr helper.
//
// Platform constants (LineEnding, DirectorySeparator, PathSeparator) are
// defined in system.pas — they are platform fundamentals, not SysUtils
// concerns.  Blaise does not carry the Delphi/FPC legacy aliases
// (sLineBreak, PathDelim).
//
// Functions that are already compiler built-ins (FileExists, DeleteFile,
// RenameFile, SetCurrentDir, ExtractFileExt, IntToStr, StrToInt, Format,
// UpperCase, LowerCase, Trim, CompareStr, CompareText, SameText, etc.) are
// deliberately absent from this interface.  Re-declaring them here would
// shadow the built-ins and produce a duplicate-identifier error at compile time.

interface

type
  Exception = class
    FMessage: string;
    constructor Create(AMessage: string);
    property Message: string read FMessage;
  end;

  EInOutError = class(Exception)
  end;

  EConvertError = class(Exception)
  end;

  { Raised by integer `div`/`mod` when the divisor is zero.  The compiler
    emits a divisor==0 guard before each integer division that calls
    _RaiseDivByZero (below) when SysUtils is in scope; without SysUtils the
    division traps in hardware (SIGFPE) as before.  Matches Delphi, where
    EDivByZero lives in System.SysUtils. }
  EDivByZero = class(Exception)
  end;

{ _RaiseDivByZero — raises EDivByZero('Division by zero').  Called by the
  compiler-emitted div/mod guard; not intended for direct use.  Declared in
  the interface so the code generator can reference the $SysUtils_RaiseDivByZero
  symbol. }
procedure _RaiseDivByZero;

{ BoolToStr — not a compiler built-in; pure Pascal implementation }
function BoolToStr(B: Boolean; AUseBoolStrs: Boolean = False): string;

{ ExpandFileName — resolve a relative path to an absolute path.
  If APath is already absolute (starts with '/') it is returned unchanged
  after normalising redundant separators and '.' components.
  Otherwise it is resolved relative to GetCurrentDir().
  Note: '..' segments are removed by simple text processing; symlinks are
  not resolved (unlike POSIX realpath).  This matches Delphi/FPC behaviour
  on paths that do not traverse symlinks. }
function ExpandFileName(const APath: string): string;

implementation

constructor Exception.Create(AMessage: string);
begin
  Self.FMessage := AMessage
end;

procedure _RaiseDivByZero;
begin
  raise EDivByZero.Create('Division by zero')
end;

function BoolToStr(B: Boolean; AUseBoolStrs: Boolean): string;
begin
  if B then
    Result := 'True'
  else
    Result := 'False'
end;

{ ExpandFileName — pure Pascal path normaliser.
  Resolves '..' and '.' components without a local string array.
  The algorithm builds the result as a string, treating it as a stack:
  appending '/' + segment to push, trimming the last segment to pop. }
function ExpandFileName(const APath: string): string;
var
  Base: string;
  Len, I, SegStart, LastSlash: Integer;
  SP: PChar;
  Seg: string;
begin
  if APath = '' then
  begin
    Exit(GetCurrentDir());
  end;

  { Determine base: absolute or relative }
  if APath[0] = 47 then  { '/' }
    Base := APath
  else
    Base := GetCurrentDir() + '/' + APath;

  Len    := Length(Base);
  SP     := PChar(Base);
  Result := '';
  I      := 0;

  { Skip leading slash }
  if (Len > 0) and (SP[0] = 47) then
    I := 1;

  while I <= Len do
  begin
    SegStart := I;
    while (I < Len) and (SP[I] <> 47) do
      I := I + 1;
    if I > SegStart then
      Seg := Copy(Base, SegStart, I - SegStart)
    else
      Seg := '';
    if (Seg <> '') and (Seg <> '.') then
    begin
      if Seg = '..' then
      begin
        { Pop the last segment from Result: find the last '/' and truncate }
        LastSlash := Length(Result) - 1;
        while (LastSlash > 0) and (Result[LastSlash] <> 47) do
          LastSlash := LastSlash - 1;
        if LastSlash >= 0 then
          Result := Copy(Result, 0, LastSlash);
      end
      else
        Result := Result + '/' + Seg;
    end;
    I := I + 1;  { skip '/' }
  end;

  if Result = '' then
    Result := '/';
end;

end.
