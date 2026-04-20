unit cp.test.forloop;

{$mode objfpc}{$H+}

{ Tests for for-loop: to and downto forms. }

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TForTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Lexer                                                                }
    { ------------------------------------------------------------------ }
    procedure TestLexer_For_Keyword;
    procedure TestLexer_To_Keyword;
    procedure TestLexer_Downto_Keyword;

    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_For_IsTForStmt;
    procedure TestParse_For_VarName;
    procedure TestParse_For_IsUpward;
    procedure TestParse_Downto_IsDownward;
    procedure TestParse_For_StartIsIntLiteral;
    procedure TestParse_For_EndIsIntLiteral;
    procedure TestParse_For_BodyIsAssignment;
    procedure TestParse_For_CompoundBody;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_For_Upward_OK;
    procedure TestSemantic_For_Downto_OK;
    procedure TestSemantic_For_NonOrdinalVar_RaisesError;
    procedure TestSemantic_For_StartTypeMismatch_RaisesError;
    procedure TestSemantic_For_EndTypeMismatch_RaisesError;

    { ------------------------------------------------------------------ }
    { Codegen                                                              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_For_InitStoresStart;
    procedure TestCodegen_For_CondUsesSlew;
    procedure TestCodegen_Downto_CondUsesSgew;
    procedure TestCodegen_For_BodyIncrementsVar;
    procedure TestCodegen_Downto_BodyDecrementsVar;
    procedure TestCodegen_For_HasForCondLabel;
    procedure TestCodegen_For_HasForBodyLabel;
    procedure TestCodegen_For_HasForEndLabel;
    procedure TestCodegen_For_JumpsBackToCond;
    procedure TestCodegen_For_Compound_OK;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TForTests.ParseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse;
  finally
    P.Free; L.Free;
  end;
end;

function TForTests.AnalyseSrc(const ASrc: string): TProgram;
var A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create;
  try
    A.Analyse(Result);
  finally
    A.Free;
  end;
end;

function TForTests.GenIR(const ASrc: string): string;
var Prog: TProgram; CG: TCodeGenQBE;
begin
  Prog := AnalyseSrc(ASrc);
  try
    CG := TCodeGenQBE.Create;
    try
      CG.Generate(Prog);
      Result := CG.GetOutput;
    finally
      CG.Free;
    end;
  finally
    Prog.Free;
  end;
end;

procedure TForTests.AnalyseExpectError(const ASrc: string);
var Prog: TProgram;
begin
  try
    Prog := AnalyseSrc(ASrc);
    Prog.Free;
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ;
  end;
end;

{ ------------------------------------------------------------------ }
{ Shared source snippets                                               }
{ ------------------------------------------------------------------ }

const
  SrcForUpward =
    'program P;'             + LineEnding +
    'var I: Integer;'        + LineEnding +
    'var S: Integer;'        + LineEnding +
    'begin'                  + LineEnding +
    '  S := 0;'              + LineEnding +
    '  for I := 1 to 5 do'  + LineEnding +
    '    S := S + I'         + LineEnding +
    'end.';

  SrcForDownto =
    'program P;'                  + LineEnding +
    'var I: Integer;'             + LineEnding +
    'var S: Integer;'             + LineEnding +
    'begin'                       + LineEnding +
    '  S := 0;'                   + LineEnding +
    '  for I := 5 downto 1 do'   + LineEnding +
    '    S := S + I'              + LineEnding +
    'end.';

  SrcForCompound =
    'program P;'             + LineEnding +
    'var I: Integer;'        + LineEnding +
    'var S: Integer;'        + LineEnding +
    'begin'                  + LineEnding +
    '  S := 0;'              + LineEnding +
    '  for I := 1 to 3 do'  + LineEnding +
    '  begin'                + LineEnding +
    '    S := S + I;'        + LineEnding +
    '    S := S + 1'         + LineEnding +
    '  end'                  + LineEnding +
    'end.';

{ ------------------------------------------------------------------ }
{ Lexer tests                                                          }
{ ------------------------------------------------------------------ }

procedure TForTests.TestLexer_For_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('for');
  try
    T := L.Next;
    AssertEquals('for token', Ord(tkFor), Ord(T.Kind));
  finally L.Free; end;
end;

procedure TForTests.TestLexer_To_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('to');
  try
    T := L.Next;
    AssertEquals('to token', Ord(tkTo), Ord(T.Kind));
  finally L.Free; end;
end;

procedure TForTests.TestLexer_Downto_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('downto');
  try
    T := L.Next;
    AssertEquals('downto token', Ord(tkDownto), Ord(T.Kind));
  finally L.Free; end;
end;

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TForTests.TestParse_For_IsTForStmt;
var Prog: TProgram;
begin
  Prog := ParseSrc(SrcForUpward);
  try
    { second stmt (index 1): for I := 1 to 5 do ... }
    AssertTrue('stmt is TForStmt', Prog.Block.Stmts[1] is TForStmt);
  finally Prog.Free; end;
end;

procedure TForTests.TestParse_For_VarName;
var Prog: TProgram; FS: TForStmt;
begin
  Prog := ParseSrc(SrcForUpward);
  try
    FS := TForStmt(Prog.Block.Stmts[1]);
    AssertEquals('loop var is I', 'I', FS.VarName);
  finally Prog.Free; end;
end;

procedure TForTests.TestParse_For_IsUpward;
var Prog: TProgram; FS: TForStmt;
begin
  Prog := ParseSrc(SrcForUpward);
  try
    FS := TForStmt(Prog.Block.Stmts[1]);
    AssertFalse('to loop: IsDownTo is False', FS.IsDownTo);
  finally Prog.Free; end;
end;

procedure TForTests.TestParse_Downto_IsDownward;
var Prog: TProgram; FS: TForStmt;
begin
  Prog := ParseSrc(SrcForDownto);
  try
    FS := TForStmt(Prog.Block.Stmts[1]);
    AssertTrue('downto loop: IsDownTo is True', FS.IsDownTo);
  finally Prog.Free; end;
end;

procedure TForTests.TestParse_For_StartIsIntLiteral;
var Prog: TProgram; FS: TForStmt;
begin
  Prog := ParseSrc(SrcForUpward);
  try
    FS := TForStmt(Prog.Block.Stmts[1]);
    AssertTrue('start is TIntLiteral', FS.StartExpr is TIntLiteral);
    AssertEquals('start value = 1', 1, TIntLiteral(FS.StartExpr).Value);
  finally Prog.Free; end;
end;

procedure TForTests.TestParse_For_EndIsIntLiteral;
var Prog: TProgram; FS: TForStmt;
begin
  Prog := ParseSrc(SrcForUpward);
  try
    FS := TForStmt(Prog.Block.Stmts[1]);
    AssertTrue('end is TIntLiteral', FS.EndExpr is TIntLiteral);
    AssertEquals('end value = 5', 5, TIntLiteral(FS.EndExpr).Value);
  finally Prog.Free; end;
end;

procedure TForTests.TestParse_For_BodyIsAssignment;
var Prog: TProgram; FS: TForStmt;
begin
  Prog := ParseSrc(SrcForUpward);
  try
    FS := TForStmt(Prog.Block.Stmts[1]);
    AssertTrue('body is TAssignment', FS.Body is TAssignment);
  finally Prog.Free; end;
end;

procedure TForTests.TestParse_For_CompoundBody;
var Prog: TProgram; FS: TForStmt;
begin
  Prog := ParseSrc(SrcForCompound);
  try
    FS := TForStmt(Prog.Block.Stmts[1]);
    AssertTrue('body is TCompoundStmt', FS.Body is TCompoundStmt);
    AssertEquals('compound body has 2 stmts', 2,
      TCompoundStmt(FS.Body).Stmts.Count);
  finally Prog.Free; end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TForTests.TestSemantic_For_Upward_OK;
begin
  AnalyseSrc(SrcForUpward).Free;
end;

procedure TForTests.TestSemantic_For_Downto_OK;
begin
  AnalyseSrc(SrcForDownto).Free;
end;

procedure TForTests.TestSemantic_For_NonOrdinalVar_RaisesError;
begin
  AnalyseExpectError(
    'program P;'              + LineEnding +
    'var S: string;'          + LineEnding +
    'begin'                   + LineEnding +
    '  for S := 1 to 5 do'   + LineEnding +
    '    S := S'              + LineEnding +
    'end.');
end;

procedure TForTests.TestSemantic_For_StartTypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    'program P;'                + LineEnding +
    'var I: Integer;'           + LineEnding +
    'var S: string;'            + LineEnding +
    'begin'                     + LineEnding +
    '  for I := S to 5 do'     + LineEnding +
    '    I := I'                + LineEnding +
    'end.');
end;

procedure TForTests.TestSemantic_For_EndTypeMismatch_RaisesError;
begin
  AnalyseExpectError(
    'program P;'                + LineEnding +
    'var I: Integer;'           + LineEnding +
    'var S: string;'            + LineEnding +
    'begin'                     + LineEnding +
    '  for I := 1 to S do'     + LineEnding +
    '    I := I'                + LineEnding +
    'end.');
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                        }
{ ------------------------------------------------------------------ }

procedure TForTests.TestCodegen_For_InitStoresStart;
var IR: string;
begin
  IR := GenIR(SrcForUpward);
  { Start value 1 is stored into the loop var slot }
  AssertTrue('storew for loop init', Pos('storew', IR) > 0);
end;

procedure TForTests.TestCodegen_For_CondUsesSlew;
var IR: string;
begin
  IR := GenIR(SrcForUpward);
  { "to" loop: I <= End uses cslew }
  AssertTrue('cslew for upward condition', Pos('cslew', IR) > 0);
end;

procedure TForTests.TestCodegen_Downto_CondUsesSgew;
var IR: string;
begin
  IR := GenIR(SrcForDownto);
  { "downto" loop: I >= End uses csgew }
  AssertTrue('csgew for downto condition', Pos('csgew', IR) > 0);
end;

procedure TForTests.TestCodegen_For_BodyIncrementsVar;
var IR: string;
begin
  IR := GenIR(SrcForUpward);
  { Loop var is incremented by 1 after each iteration }
  AssertTrue('add 1 for increment', Pos(', 1', IR) > 0);
end;

procedure TForTests.TestCodegen_Downto_BodyDecrementsVar;
var IR: string;
begin
  IR := GenIR(SrcForDownto);
  { Loop var is decremented by 1 after each iteration }
  AssertTrue('sub for decrement', Pos('sub', IR) > 0);
end;

procedure TForTests.TestCodegen_For_HasForCondLabel;
var IR: string;
begin
  IR := GenIR(SrcForUpward);
  AssertTrue('for_cond label present', Pos('for_cond', IR) > 0);
end;

procedure TForTests.TestCodegen_For_HasForBodyLabel;
var IR: string;
begin
  IR := GenIR(SrcForUpward);
  AssertTrue('for_body label present', Pos('for_body', IR) > 0);
end;

procedure TForTests.TestCodegen_For_HasForEndLabel;
var IR: string;
begin
  IR := GenIR(SrcForUpward);
  AssertTrue('for_end label present', Pos('for_end', IR) > 0);
end;

procedure TForTests.TestCodegen_For_JumpsBackToCond;
var IR: string;
begin
  IR := GenIR(SrcForUpward);
  { After body, must jump back to condition block }
  AssertTrue('jmp @for_cond in IR', Pos('jmp @for_cond', IR) > 0);
end;

procedure TForTests.TestCodegen_For_Compound_OK;
var IR: string;
begin
  IR := GenIR(SrcForCompound);
  { Just verify it compiles without error and produces a for_cond label }
  AssertTrue('compound body for loop generates IR', Pos('for_cond', IR) > 0);
end;

initialization
  RegisterTest(TForTests);

end.
