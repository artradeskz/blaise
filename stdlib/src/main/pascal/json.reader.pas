{
  Blaise stdlib - JSON reader
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - JSON reader facade.

  GetJSON parses a JSON document string into the Json.Types tree by driving the
  Json.Parser engine.  The caller owns the returned root (parent-owns-child);
  releasing it frees the whole tree.  EJSONParseError is raised on malformed
  input.
}

unit Json.Reader;

interface

uses
  Json.Types, Json.Parser;

{ Parse AText into a JSON tree.  Raises EJSONParseError on malformed input. }
function GetJSON(const AText: string): TJSONData;

implementation

function GetJSON(const AText: string): TJSONData;
var
  P: TJSONParser;
begin
  P := TJSONParser.Create(AText);
  Result := P.Parse();
  P.Free();
end;

end.
