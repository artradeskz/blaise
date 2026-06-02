{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit StrUtils;

// Blaise RTL — StrUtils unit.
//
// String indexing in Blaise is 0-based throughout:
//   - PosEx/Pos return -1 when not found, 0 for the first position.
//   - LeftStr/RightStr/MidStr are thin wrappers over the built-in Copy.
//   - IndexStr/IndexText return -1 when not found, 0 for the first element.
//
// Str vs Text naming convention (identical to Delphi/FPC):
//   xxxStr  — case-sensitive
//   xxxText — case-insensitive (ASCII fold only; no locale)
//
// All higher-level functions are implemented in pure Blaise Pascal using
// only the small set of primitives exposed by blaise_str.pas.

interface


{ ------------------------------------------------------------------ }
{ Containment                                                          }
{ ------------------------------------------------------------------ }

{ Returns True if Sub appears anywhere in S (case-sensitive). }
function ContainsStr(const S, Sub: string): Boolean;

{ Returns True if Sub appears anywhere in S (case-insensitive). }
function ContainsText(const S, Sub: string): Boolean;

{ ------------------------------------------------------------------ }
{ Prefix / suffix                                                      }
{ ------------------------------------------------------------------ }

{ Returns True if S begins with Prefix (case-sensitive). }
function StartsStr(const Prefix, S: string): Boolean;

{ Returns True if S begins with Prefix (case-insensitive). }
function StartsText(const Prefix, S: string): Boolean;

{ Returns True if S ends with Suffix (case-sensitive). }
function EndsStr(const Suffix, S: string): Boolean;

{ Returns True if S ends with Suffix (case-insensitive). }
function EndsText(const Suffix, S: string): Boolean;

{ ------------------------------------------------------------------ }
{ Extraction — thin wrappers over the built-in Copy                    }
{ ------------------------------------------------------------------ }

{ Returns the first Count bytes of S. }
function LeftStr(const S: string; Count: Integer): string;

{ Returns the last Count bytes of S. }
function RightStr(const S: string; Count: Integer): string;

{ Returns Count bytes of S starting at 0-based position Start. }
function MidStr(const S: string; Start, Count: Integer): string;

{ ------------------------------------------------------------------ }
{ Search                                                               }
{ ------------------------------------------------------------------ }

{ Note: PosEx(Sub, S, StartPos) is a compiler built-in — not declared here. }

{ Returns the 0-based index of Str in Arr (case-sensitive), or -1. }
function IndexStr(const Str: string; const Arr: array of string): Integer;

{ Returns the 0-based index of Str in Arr (case-insensitive), or -1. }
function IndexText(const Str: string; const Arr: array of string): Integer;

{ ------------------------------------------------------------------ }
{ Replacement                                                          }
{ ------------------------------------------------------------------ }

{ Replaces all occurrences of OldPattern with NewPattern (case-sensitive). }
function ReplaceStr(const S, OldPattern, NewPattern: string): string;

{ Replaces all occurrences of OldPattern with NewPattern (case-insensitive). }
function ReplaceText(const S, OldPattern, NewPattern: string): string;

{ ------------------------------------------------------------------ }
{ Manipulation                                                         }
{ ------------------------------------------------------------------ }

{ Returns S repeated Count times. }
function DupeString(const S: string; Count: Integer): string;

{ Returns S with its bytes in reverse order. }
function ReverseString(const S: string): string;

{ Deletes Len bytes at 0-based position Start and inserts Replacement. }
function StuffString(const S: string; Start, Len: Integer;
                     const Replacement: string): string;

{ Returns S with leading whitespace (bytes <= 32) removed. }
function TrimLeft(const S: string): string;

{ Returns S with trailing whitespace (bytes <= 32) removed. }
function TrimRight(const S: string): string;

{ Returns S left-padded with PadByte to at least Width bytes. }
function PadLeft(const S: string; Width: Integer; PadByte: Byte = 32): string;

{ Returns S right-padded with PadByte to at least Width bytes. }
function PadRight(const S: string; Width: Integer; PadByte: Byte = 32): string;

{ Returns the number of non-overlapping occurrences of Sub in S. }
function CountOccurrences(const Sub, S: string): Integer;

{ Returns S with a leading Prefix removed (if present). }
function RemovePrefix(const S, Prefix: string): string;

{ Returns S with a trailing Suffix removed (if present). }
function RemoveSuffix(const S, Suffix: string): string;

{ Returns True when S contains only whitespace (or is empty). }
function IsEmptyOrWhitespace(const S: string): Boolean;

{ Joins Parts with Sep between each element. }
function JoinStr(const Sep: string; const Parts: array of string): string;

{ ------------------------------------------------------------------ }
{ TStringBuilder — efficient incremental string construction           }
{ ------------------------------------------------------------------ }

{ TStringBuilder avoids the O(N²) cost of repeated string concatenation
  by maintaining a raw byte buffer that grows geometrically.  Append
  operations write directly into the buffer without allocating intermediate
  ARC strings.  Call ToString to obtain a single managed string at the end.

  This mirrors the compiler's internal TIRBuffer that produced the 460×
  speedup in QBE IR generation.  The same technique is now available to
  Blaise user code. }
type
  TStringBuilder = class
  private
    FData: PChar;
    FLen:  Integer;
    FCap:  Integer;
    procedure Grow(ANeed: Integer);
  public
    constructor Create;
    destructor  Destroy; override;
    { Append a string value. }
    procedure Append(const S: string); overload;
    { Append a single byte as a character. }
    procedure AppendByte(B: Byte); overload;
    { Append a newline (#10). }
    procedure AppendLine; overload;
    { Append a string followed by a newline. }
    procedure AppendLine(const S: string); overload;
    { Remove all content without releasing the buffer. }
    procedure Clear;
    { Return the accumulated content as a managed string. }
    function  ToString: string;
    { Current byte length. }
    property  Length: Integer read FLen;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Internal helpers                                                     }
{ ------------------------------------------------------------------ }

{ ASCII case-fold: returns lowercase byte value. }
function FoldLower(C: Integer): Integer;
begin
  if (C >= 65) and (C <= 90) then
    Result := C + 32
  else
    Result := C;
end;

{ ------------------------------------------------------------------ }
{ Containment                                                          }
{ ------------------------------------------------------------------ }

function ContainsStr(const S, Sub: string): Boolean;
begin
  Result := Pos(Sub, S) >= 0;
end;

function ContainsText(const S, Sub: string): Boolean;
var
  SL, SubL: string;
begin
  SL   := LowerCase(S);
  SubL := LowerCase(Sub);
  Result := Pos(SubL, SL) >= 0;
end;

{ ------------------------------------------------------------------ }
{ Prefix / suffix                                                      }
{ ------------------------------------------------------------------ }

function StartsStr(const Prefix, S: string): Boolean;
var
  PLen, SLen: Integer;
  SP, PP: PChar;
  I: Integer;
begin
  PLen := Length(Prefix);
  SLen := Length(S);
  if PLen = 0 then begin Result := True; Exit; end;
  if PLen > SLen then begin Result := False; Exit; end;
  SP := PChar(S);
  PP := PChar(Prefix);
  for I := 0 to PLen - 1 do
    if SP[I] <> PP[I] then begin Result := False; Exit; end;
  Result := True;
end;

function StartsText(const Prefix, S: string): Boolean;
var
  PLen, SLen: Integer;
  SP, PP: PChar;
  I: Integer;
begin
  PLen := Length(Prefix);
  SLen := Length(S);
  if PLen = 0 then begin Result := True; Exit; end;
  if PLen > SLen then begin Result := False; Exit; end;
  SP := PChar(S);
  PP := PChar(Prefix);
  for I := 0 to PLen - 1 do
    if FoldLower(SP[I]) <> FoldLower(PP[I]) then begin Result := False; Exit; end;
  Result := True;
end;

function EndsStr(const Suffix, S: string): Boolean;
var
  SufLen, SLen: Integer;
  SP, SufP: PChar;
  Offset, I: Integer;
begin
  SufLen := Length(Suffix);
  SLen   := Length(S);
  if SufLen = 0 then begin Result := True; Exit; end;
  if SufLen > SLen then begin Result := False; Exit; end;
  SP     := PChar(S);
  SufP   := PChar(Suffix);
  Offset := SLen - SufLen;
  for I := 0 to SufLen - 1 do
    if SP[Offset + I] <> SufP[I] then begin Result := False; Exit; end;
  Result := True;
end;

function EndsText(const Suffix, S: string): Boolean;
var
  SufLen, SLen: Integer;
  SP, SufP: PChar;
  Offset, I: Integer;
begin
  SufLen := Length(Suffix);
  SLen   := Length(S);
  if SufLen = 0 then begin Result := True; Exit; end;
  if SufLen > SLen then begin Result := False; Exit; end;
  SP     := PChar(S);
  SufP   := PChar(Suffix);
  Offset := SLen - SufLen;
  for I := 0 to SufLen - 1 do
    if FoldLower(SP[Offset + I]) <> FoldLower(SufP[I]) then begin Result := False; Exit; end;
  Result := True;
end;

{ ------------------------------------------------------------------ }
{ Extraction                                                           }
{ ------------------------------------------------------------------ }

function LeftStr(const S: string; Count: Integer): string;
begin
  Result := Copy(S, 0, Count);
end;

function RightStr(const S: string; Count: Integer): string;
var
  Len: Integer;
begin
  Len := Length(S);
  if Count >= Len then
    Result := S
  else
    Result := Copy(S, Len - Count, Count);
end;

function MidStr(const S: string; Start, Count: Integer): string;
begin
  Result := Copy(S, Start, Count);
end;

{ ------------------------------------------------------------------ }
{ Search                                                               }
{ ------------------------------------------------------------------ }

{ PosEx is a compiler built-in — implementation omitted. }

function IndexStr(const Str: string; const Arr: array of string): Integer;
var
  I: Integer;
begin
  for I := 0 to High(Arr) do
    if Arr[I] = Str then
    begin
      Exit(I);
    end;
  Result := -1;
end;

function IndexText(const Str: string; const Arr: array of string): Integer;
var
  I:   Integer;
  SL:  string;
  EL:  string;
begin
  SL := LowerCase(Str);
  for I := 0 to High(Arr) do
  begin
    EL := LowerCase(Arr[I]);
    if EL = SL then
    begin
      Exit(I);
    end;
  end;
  Result := -1;
end;

{ ------------------------------------------------------------------ }
{ Replacement                                                          }
{ ------------------------------------------------------------------ }

{ Internal: replace all occurrences of OldP with NewP; Fold=True for case-insensitive. }
function ReplaceAll(const S, OldP, NewP: string; Fold: Boolean): string;
var
  SLen, OldLen, NewLen: Integer;
  SB: TStringBuilder;
  I, J: Integer;
  Match: Boolean;
  SP, OP: PChar;
  C1, C2: Integer;
begin
  SLen   := Length(S);
  OldLen := Length(OldP);
  NewLen := Length(NewP);
  if (SLen = 0) or (OldLen = 0) then
  begin
    Exit(S);
  end;
  SP := PChar(S);
  OP := PChar(OldP);
  SB := TStringBuilder.Create;
  I  := 0;
  while I <= SLen - OldLen do
  begin
    Match := True;
    for J := 0 to OldLen - 1 do
    begin
      if Fold then
      begin
        C1 := FoldLower(SP[I + J]);
        C2 := FoldLower(OP[J]);
      end
      else
      begin
        C1 := SP[I + J];
        C2 := OP[J];
      end;
      if C1 <> C2 then begin Match := False; Break; end;
    end;
    if Match then
    begin
      if NewLen > 0 then
        SB.Append(NewP);
      I := I + OldLen;
    end
    else
    begin
      SB.AppendByte(SP[I]);
      I := I + 1;
    end;
  end;
  { copy any remaining tail }
  while I < SLen do
  begin
    SB.AppendByte(SP[I]);
    I := I + 1;
  end;
  Result := SB.ToString;
  SB.Free;
end;

function ReplaceStr(const S, OldPattern, NewPattern: string): string;
begin
  Result := ReplaceAll(S, OldPattern, NewPattern, False);
end;

function ReplaceText(const S, OldPattern, NewPattern: string): string;
begin
  Result := ReplaceAll(S, OldPattern, NewPattern, True);
end;

{ ------------------------------------------------------------------ }
{ Manipulation                                                         }
{ ------------------------------------------------------------------ }

function DupeString(const S: string; Count: Integer): string;
var
  SB: TStringBuilder;
  I: Integer;
begin
  if (Count <= 0) or (Length(S) = 0) then
  begin
    Exit('');
  end;
  SB := TStringBuilder.Create;
  for I := 1 to Count do
    SB.Append(S);
  Result := SB.ToString;
  SB.Free;
end;

function ReverseString(const S: string): string;
var
  Len, I: Integer;
  SP, RP: PChar;
begin
  Len := Length(S);
  SetLength(Result, Len);
  if Len = 0 then Exit;
  SP := PChar(S);
  RP := PChar(Result);
  for I := 0 to Len - 1 do
    RP[I] := SP[Len - 1 - I];
end;

function StuffString(const S: string; Start, Len: Integer;
                     const Replacement: string): string;
var
  SLen, RepLen, ActualLen: Integer;
begin
  SLen   := Length(S);
  RepLen := Length(Replacement);
  if Start < 0 then Start := 0;
  if Start > SLen then Start := SLen;
  ActualLen := Len;
  if ActualLen < 0 then ActualLen := 0;
  if Start + ActualLen > SLen then ActualLen := SLen - Start;
  { Build: head + replacement + tail }
  Result := Copy(S, 0, Start) + Replacement + Copy(S, Start + ActualLen, SLen - Start - ActualLen);
end;

function TrimLeft(const S: string): string;
var
  Len, Lo: Integer;
  SP: PChar;
begin
  Len := Length(S);
  SP  := PChar(S);
  Lo  := 0;
  while Lo < Len do
  begin
    if SP[Lo] > 32 then Break;
    Lo := Lo + 1;
  end;
  Result := Copy(S, Lo, Len - Lo);
end;

function TrimRight(const S: string): string;
var
  Len, Hi: Integer;
  SP: PChar;
begin
  Len := Length(S);
  SP  := PChar(S);
  Hi  := Len - 1;
  while Hi >= 0 do
  begin
    if SP[Hi] > 32 then Break;
    Hi := Hi - 1;
  end;
  Result := Copy(S, 0, Hi + 1);
end;

function PadLeft(const S: string; Width: Integer; PadByte: Byte): string;
var
  Len, PadCount, I: Integer;
  SB: TStringBuilder;
begin
  Len := Length(S);
  if Len >= Width then
  begin
    Exit(S);
  end;
  PadCount := Width - Len;
  SB := TStringBuilder.Create;
  for I := 1 to PadCount do
    SB.AppendByte(PadByte);
  SB.Append(S);
  Result := SB.ToString;
  SB.Free;
end;

function PadRight(const S: string; Width: Integer; PadByte: Byte): string;
var
  Len, PadCount, I: Integer;
  SB: TStringBuilder;
begin
  Len := Length(S);
  if Len >= Width then
  begin
    Exit(S);
  end;
  PadCount := Width - Len;
  SB := TStringBuilder.Create;
  SB.Append(S);
  for I := 1 to PadCount do
    SB.AppendByte(PadByte);
  Result := SB.ToString;
  SB.Free;
end;

function CountOccurrences(const Sub, S: string): Integer;
var
  SLen, SubLen: Integer;
  SP, SubP: PChar;
  I, J: Integer;
  Match: Boolean;
begin
  Result := 0;
  SLen   := Length(S);
  SubLen := Length(Sub);
  if (SubLen = 0) or (SubLen > SLen) then Exit;
  SP   := PChar(S);
  SubP := PChar(Sub);
  I    := 0;
  while I <= SLen - SubLen do
  begin
    Match := True;
    for J := 0 to SubLen - 1 do
      if SP[I + J] <> SubP[J] then begin Match := False; Break; end;
    if Match then
    begin
      Result := Result + 1;
      I := I + SubLen;
    end
    else
      I := I + 1;
  end;
end;

function RemovePrefix(const S, Prefix: string): string;
var
  PLen: Integer;
begin
  if StartsStr(Prefix, S) then
  begin
    PLen   := Length(Prefix);
    Result := Copy(S, PLen, Length(S) - PLen);
  end
  else
    Result := S;
end;

function RemoveSuffix(const S, Suffix: string): string;
var
  SLen, SufLen: Integer;
begin
  if EndsStr(Suffix, S) then
  begin
    SLen   := Length(S);
    SufLen := Length(Suffix);
    Result := Copy(S, 0, SLen - SufLen);
  end
  else
    Result := S;
end;

function IsEmptyOrWhitespace(const S: string): Boolean;
var
  Trimmed: string;
begin
  Trimmed := TrimLeft(S);
  Result  := Length(Trimmed) = 0;
end;

function JoinStr(const Sep: string; const Parts: array of string): string;
var
  SB: TStringBuilder;
  I:  Integer;
begin
  if High(Parts) < 0 then
  begin
    Exit('');
  end;
  SB := TStringBuilder.Create;
  for I := 0 to High(Parts) do
  begin
    SB.Append(Parts[I]);
    if I < High(Parts) then
      SB.Append(Sep);
  end;
  Result := SB.ToString;
  SB.Free;
end;

{ ------------------------------------------------------------------ }
{ TStringBuilder                                                       }
{ ------------------------------------------------------------------ }

constructor TStringBuilder.Create;
begin
  inherited Create;
  Self.FCap  := 256;
  Self.FLen  := 0;
  Self.FData := GetMem(Self.FCap);
end;

destructor TStringBuilder.Destroy;
begin
  FreeMem(Self.FData);
  inherited Destroy;
end;

procedure TStringBuilder.Grow(ANeed: Integer);
var
  NewCap:  Integer;
  NewData: PChar;
  OldData: PChar;
  I:       Integer;
begin
  NewCap  := Self.FCap;
  while NewCap < Self.FLen + ANeed do
    NewCap := NewCap * 2;
  NewData := GetMem(NewCap);
  OldData := Self.FData;
  for I := 0 to Self.FLen - 1 do
    NewData[I] := OldData[I];
  FreeMem(OldData);
  Self.FData := NewData;
  Self.FCap  := NewCap;
end;

procedure TStringBuilder.Append(const S: string);
var
  SLen:   Integer;
  SP:     PChar;
  DP:     PChar;
  Offset: Integer;
  I:      Integer;
begin
  SLen := Length(S);
  if SLen = 0 then Exit;
  if Self.FLen + SLen > Self.FCap then Self.Grow(SLen);
  SP     := PChar(S);
  DP     := Self.FData;
  Offset := Self.FLen;
  for I := 0 to SLen - 1 do
    DP[Offset + I] := SP[I];
  Self.FLen := Self.FLen + SLen;
end;

procedure TStringBuilder.AppendByte(B: Byte);
var
  DP:  PChar;
  Pos: Integer;
begin
  if Self.FLen + 1 > Self.FCap then Self.Grow(1);
  DP  := Self.FData;
  Pos := Self.FLen;
  DP[Pos] := B;
  Self.FLen := Self.FLen + 1;
end;

procedure TStringBuilder.AppendLine;
begin
  Self.AppendByte(10);
end;

procedure TStringBuilder.AppendLine(const S: string);
begin
  Self.Append(S);
  Self.AppendByte(10);
end;

procedure TStringBuilder.Clear;
begin
  Self.FLen := 0;
end;

function TStringBuilder.ToString: string;
var
  I:  Integer;
  RP: PChar;
  SP: PChar;
begin
  SetLength(Result, Self.FLen);
  if Self.FLen > 0 then
  begin
    RP := PChar(Result);
    SP := Self.FData;
    for I := 0 to Self.FLen - 1 do
      RP[I] := SP[I];
  end;
end;

end.
