{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  uIfaceObject.pas author: Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ uIfaceObject — embed / extract TUnitInterface (.bif) blobs inside
  object files.

  Why: keep .bif and .o in lock-step.  When the iface lives as its
  own file next to the .o, a build-system glitch or stale copy can
  produce a mismatch where the compiler trusts an interface for
  symbols that the object file no longer exports.  Embedding the
  bytes inside the .o makes the artefacts inseparable — copying
  the .o brings the iface along, and a regenerated .o can't carry
  an older iface by accident.

  Implementation: direct ELF section read/append via uElfObject —
  no objcopy / binutils dependency.  The section is marked
  SHF_EXCLUDE so GNU ld drops it from the final executable but
  preserves it through `ar` archives and `ld -r` partial links.

  Format abstraction:
    * ELF (Linux): section '.blaise.iface'.
    * PE/COFF (Windows): section name is shortened to '.bliface'
      (8 chars).  Not implemented yet but the section-name
      constant + format-dispatch shape leaves room. }

unit uIfaceObject;

interface

uses
  Classes, SysUtils, streams, uElfObject;

type
  TObjectFormat = (ofELF);

const
  IFACE_SECTION_ELF    = '.blaise.iface';
  IFACE_SECTION_PECOFF = '.bliface';

{ Embed ABifFile bytes into AObjectFile under a non-loaded
  metadata section.  Returns True on success. }
function EmbedBifInObject(const AObjectFile, ABifFile: string;
                          AFormat: TObjectFormat): Boolean;

{ Extract the embedded iface bytes into a fresh path and return
  it.  Returns '' on absence or any failure.  Caller deletes. }
function ExtractBifFromObject(const AObjectFile: string;
                              AFormat: TObjectFormat): string;

{ Convenience: extract and load as a string.  Empty on absence. }
function LoadEmbeddedBifString(const AObjectFile: string;
                               AFormat: TObjectFormat): string;

implementation

function SectionName(AFormat: TObjectFormat): string;
begin
  if AFormat = ofELF then
    Result := IFACE_SECTION_ELF
  else
    Result := IFACE_SECTION_PECOFF;
end;

function ReadFileAsString(const APath: string): string;
var
  FIn: TFileInputStream;
begin
  Result := '';
  FIn := TFileInputStream.Create(APath);
  try
    SetLength(Result, Integer(FIn.Size));
    if Length(Result) > 0 then
      FIn.Read(PChar(Result), Length(Result));
  finally
    FIn.Free;
  end;
end;

function EmbedBifInObject(const AObjectFile, ABifFile: string;
                          AFormat: TObjectFormat): Boolean;
var
  Bytes: string;
begin
  Result := False;
  try
    Bytes := ReadFileAsString(ABifFile);
    AppendSection(AObjectFile, SectionName(AFormat), Bytes);
    Result := True;
  except
    on E: EElfObject do
      WriteLn(StdErr, 'embed iface failed: ', Exception(E).Message);
    on E: Exception do
      WriteLn(StdErr, 'embed iface failed: ', Exception(E).Message);
  end;
end;

function ExtractBifFromObject(const AObjectFile: string;
                              AFormat: TObjectFormat): string;
var
  Data:    string;
  TmpPath: string;
  FOut:    TFileOutputStream;
begin
  Result := '';
  try
    if not ReadSection(AObjectFile, SectionName(AFormat), Data) then
      Exit;
    if Data = '' then
      Exit;
  except
    on E: EElfObject do
    begin
      Exit;
    end;
  end;
  TmpPath := AObjectFile + '.bifx.tmp';
  try
    FOut := TFileOutputStream.Create(TmpPath);
    try
      if Length(Data) > 0 then
        FOut.Write(PChar(Data), Length(Data));
    finally
      FOut.Close;
      FOut.Free;
    end;
    Result := TmpPath;
  except
    on E: Exception do
    begin
      if FileExists(TmpPath) then DeleteFile(TmpPath);
    end;
  end;
end;

function LoadEmbeddedBifString(const AObjectFile: string;
                               AFormat: TObjectFormat): string;
begin
  Result := '';
  try
    ReadSection(AObjectFile, SectionName(AFormat), Result);
  except
    on E: EElfObject do
      Result := '';
  end;
end;

end.
