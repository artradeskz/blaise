{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.textblock;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer;

type
  TTextBlockTests = class(TTestCase)
  private
    FLexer: TLexer;
    procedure SetLexer(const ASource: string);
  protected
    procedure TearDown; override;
  published
    procedure TestTextBlock_Basic;
    procedure TestTextBlock_MarginStrip;
    procedure TestTextBlock_EmbeddedSingleQuote;
    procedure TestTextBlock_EmptyBlock;
    procedure TestTextBlock_SingleContentLine;
    procedure TestTextBlock_NoMarginStrip_CloserAtCol1;
    procedure TestTextBlock_PreservesRelativeIndent;
    procedure TestTextBlock_Disambiguation_FourQuotes;
    procedure TestTextBlock_TrailingContentAfterCloser;
    procedure TestTextBlock_TabsInContent;
    procedure TestTextBlock_BlankLinesPreserved;
  end;

implementation

const
  TQ = #39#39#39;

procedure TTextBlockTests.SetLexer(const ASource: string);
begin
  FreeAndNil(FLexer);
  FLexer := TLexer.Create(ASource);
end;

procedure TTextBlockTests.TearDown;
begin
  FreeAndNil(FLexer);
end;

procedure TTextBlockTests.TestTextBlock_Basic;
var
  tok: TToken;
begin
  SetLexer(TQ + LineEnding +
           'hello' + LineEnding +
           TQ);
  tok := FLexer.Next;
  AssertEquals('Kind', Ord(tkStringLit), Ord(tok.Kind));
  AssertEquals('Value', 'hello' + #10, tok.Value);
end;

procedure TTextBlockTests.TestTextBlock_MarginStrip;
var
  tok: TToken;
begin
  SetLexer(TQ + LineEnding +
           '  line one' + LineEnding +
           '  line two' + LineEnding +
           '  ' + TQ);
  tok := FLexer.Next;
  AssertEquals('Kind', Ord(tkStringLit), Ord(tok.Kind));
  AssertEquals('Value', 'line one' + #10 + 'line two' + #10, tok.Value);
end;

procedure TTextBlockTests.TestTextBlock_EmbeddedSingleQuote;
var
  tok: TToken;
begin
  SetLexer(TQ + LineEnding +
           'it' + #39 + 's here' + LineEnding +
           TQ);
  tok := FLexer.Next;
  AssertEquals('Kind', Ord(tkStringLit), Ord(tok.Kind));
  AssertEquals('Value', 'it' + #39 + 's here' + #10, tok.Value);
end;

procedure TTextBlockTests.TestTextBlock_EmptyBlock;
var
  tok: TToken;
begin
  SetLexer(TQ + LineEnding +
           TQ);
  tok := FLexer.Next;
  AssertEquals('Kind', Ord(tkStringLit), Ord(tok.Kind));
  AssertEquals('Value', '', tok.Value);
end;

procedure TTextBlockTests.TestTextBlock_SingleContentLine;
var
  tok: TToken;
begin
  SetLexer(TQ + LineEnding +
           'only line' + LineEnding +
           TQ);
  tok := FLexer.Next;
  AssertEquals('Kind', Ord(tkStringLit), Ord(tok.Kind));
  AssertEquals('Value', 'only line' + #10, tok.Value);
end;

procedure TTextBlockTests.TestTextBlock_NoMarginStrip_CloserAtCol1;
var
  tok: TToken;
begin
  SetLexer(TQ + LineEnding +
           '  indented' + LineEnding +
           TQ);
  tok := FLexer.Next;
  AssertEquals('Kind', Ord(tkStringLit), Ord(tok.Kind));
  AssertEquals('Value', '  indented' + #10, tok.Value);
end;

procedure TTextBlockTests.TestTextBlock_PreservesRelativeIndent;
var
  tok: TToken;
begin
  SetLexer(TQ + LineEnding +
           '    begin' + LineEnding +
           '      X := 1;' + LineEnding +
           '    end.' + LineEnding +
           '    ' + TQ);
  tok := FLexer.Next;
  AssertEquals('Kind', Ord(tkStringLit), Ord(tok.Kind));
  AssertEquals('Value', 'begin' + #10 + '  X := 1;' + #10 + 'end.' + #10, tok.Value);
end;

procedure TTextBlockTests.TestTextBlock_Disambiguation_FourQuotes;
var
  tok: TToken;
begin
  { '''' (four quotes) is a classic Pascal string containing one single
    quote character.  The tokeniser must NOT treat the leading ''' as a
    text block opener when the fourth character is also a quote. }
  SetLexer(#39#39#39#39);
  tok := FLexer.Next;
  AssertEquals('Kind', Ord(tkStringLit), Ord(tok.Kind));
  AssertEquals('Value', #39, tok.Value);
end;

procedure TTextBlockTests.TestTextBlock_TrailingContentAfterCloser;
var
  tok, tok2: TToken;
begin
  SetLexer(TQ + LineEnding +
           'content' + LineEnding +
           TQ + ';');
  tok := FLexer.Next;
  AssertEquals('Kind', Ord(tkStringLit), Ord(tok.Kind));
  AssertEquals('Value', 'content' + #10, tok.Value);
  tok2 := FLexer.Next;
  AssertEquals('Semi', Ord(tkSemicolon), Ord(tok2.Kind));
end;

procedure TTextBlockTests.TestTextBlock_TabsInContent;
var
  tok: TToken;
begin
  SetLexer(TQ + LineEnding +
           #9 + 'tabbed' + LineEnding +
           TQ);
  tok := FLexer.Next;
  AssertEquals('Kind', Ord(tkStringLit), Ord(tok.Kind));
  AssertEquals('Value', #9 + 'tabbed' + #10, tok.Value);
end;

procedure TTextBlockTests.TestTextBlock_BlankLinesPreserved;
var
  tok: TToken;
begin
  SetLexer(TQ + LineEnding +
           'line one' + LineEnding +
           '' + LineEnding +
           'line three' + LineEnding +
           TQ);
  tok := FLexer.Next;
  AssertEquals('Kind', Ord(tkStringLit), Ord(tok.Kind));
  AssertEquals('Value', 'line one' + #10 + #10 + 'line three' + #10, tok.Value);
end;

initialization
  RegisterTest(TTextBlockTests);

end.
