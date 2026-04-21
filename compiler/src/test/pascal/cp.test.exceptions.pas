unit cp.test.exceptions;

{$mode objfpc}{$H+}

{ Tests for try/finally, try/except, and raise statements. }

interface

uses
  Classes, SysUtils, StrUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TExceptionTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Lexer                                                                }
    { ------------------------------------------------------------------ }
    procedure TestLexer_Try_Keyword;
    procedure TestLexer_Finally_Keyword;
    procedure TestLexer_Except_Keyword;
    procedure TestLexer_Raise_Keyword;

    { ------------------------------------------------------------------ }
    { Parser — try/finally                                                 }
    { ------------------------------------------------------------------ }
    procedure TestParse_TryFinally_IsTTryFinallyStmt;
    procedure TestParse_TryFinally_TryBodyStmtCount;
    procedure TestParse_TryFinally_FinallyBodyStmtCount;
    procedure TestParse_TryFinally_MultipleStmtsInTryBody;
    procedure TestParse_TryFinally_MultipleStmtsInFinallyBody;

    { ------------------------------------------------------------------ }
    { Parser — try/except                                                  }
    { ------------------------------------------------------------------ }
    procedure TestParse_TryExcept_IsTTryExceptStmt;
    procedure TestParse_TryExcept_TryBodyStmtCount;
    procedure TestParse_TryExcept_ExceptBodyStmtCount;

    { ------------------------------------------------------------------ }
    { Parser — raise                                                       }
    { ------------------------------------------------------------------ }
    procedure TestParse_Raise_IsTRaiseStmt;
    procedure TestParse_Raise_HasExpr;
    procedure TestParse_Raise_Bare_HasNilExpr;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_TryFinally_OK;
    procedure TestSemantic_TryExcept_OK;
    procedure TestSemantic_Raise_ClassExpr_OK;
    procedure TestSemantic_Raise_NonClass_RaisesError;
    procedure TestSemantic_Raise_Bare_OK;

    { ------------------------------------------------------------------ }
    { Codegen — try/finally                                                }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_TryFinally_TryBodyInIR;
    procedure TestCodegen_TryFinally_FinallyBodyInIR;
    procedure TestCodegen_TryFinally_FinallyAfterTry;

    { ------------------------------------------------------------------ }
    { Codegen — try/except                                                 }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_TryExcept_TryBodyInIR;
    procedure TestCodegen_TryExcept_ExceptLabelPresent;

    { ------------------------------------------------------------------ }
    { Codegen — raise                                                      }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_Raise_CallsRTL;

    { ------------------------------------------------------------------ }
    { Codegen — setjmp-based real dispatch                                 }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_TryExcept_PushesExcFrame;
    procedure TestCodegen_TryExcept_CallsSetjmp;
    procedure TestCodegen_TryExcept_PopsFrame;
    procedure TestCodegen_TryFinally_PushesExcFrame;
    procedure TestCodegen_TryFinally_CallsReraise;
    procedure TestCodegen_TryFinally_FinallyOnBothPaths;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TExceptionTests.ParseSrc(const ASrc: string): TProgram;
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

function TExceptionTests.AnalyseSrc(const ASrc: string): TProgram;
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

function TExceptionTests.GenIR(const ASrc: string): string;
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

procedure TExceptionTests.AnalyseExpectError(const ASrc: string);
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
  SrcTryFinally =
    'program P;'                + LineEnding +
    'var X: Integer;'           + LineEnding +
    'begin'                     + LineEnding +
    '  X := 0;'                 + LineEnding +
    '  try'                     + LineEnding +
    '    X := 1'                + LineEnding +
    '  finally'                 + LineEnding +
    '    X := 2'                + LineEnding +
    '  end'                     + LineEnding +
    'end.';

  SrcTryFinallyMulti =
    'program P;'                + LineEnding +
    'var X: Integer;'           + LineEnding +
    'var Y: Integer;'           + LineEnding +
    'begin'                     + LineEnding +
    '  try'                     + LineEnding +
    '    X := 1;'               + LineEnding +
    '    Y := 2'                + LineEnding +
    '  finally'                 + LineEnding +
    '    X := 0;'               + LineEnding +
    '    Y := 0'                + LineEnding +
    '  end'                     + LineEnding +
    'end.';

  SrcTryExcept =
    'program P;'                + LineEnding +
    'var X: Integer;'           + LineEnding +
    'begin'                     + LineEnding +
    '  X := 0;'                 + LineEnding +
    '  try'                     + LineEnding +
    '    X := 1'                + LineEnding +
    '  except'                  + LineEnding +
    '    X := 99'               + LineEnding +
    '  end'                     + LineEnding +
    'end.';

  SrcRaise =
    'program P;'                + LineEnding +
    'type'                      + LineEnding +
    '  TError = class'          + LineEnding +
    '    Code: Integer;'        + LineEnding +
    '  end;'                    + LineEnding +
    'var E: TError;'            + LineEnding +
    'begin'                     + LineEnding +
    '  E := TError.Create;'     + LineEnding +
    '  raise E'                 + LineEnding +
    'end.';

  SrcBareRaise =
    'program P;'                + LineEnding +
    'var X: Integer;'           + LineEnding +
    'begin'                     + LineEnding +
    '  try'                     + LineEnding +
    '    X := 1'                + LineEnding +
    '  except'                  + LineEnding +
    '    raise'                 + LineEnding +
    '  end'                     + LineEnding +
    'end.';

{ ------------------------------------------------------------------ }
{ Lexer tests                                                          }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestLexer_Try_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('try');
  try
    T := L.Next;
    AssertEquals('try token', Ord(tkTry), Ord(T.Kind));
  finally L.Free; end;
end;

procedure TExceptionTests.TestLexer_Finally_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('finally');
  try
    T := L.Next;
    AssertEquals('finally token', Ord(tkFinally), Ord(T.Kind));
  finally L.Free; end;
end;

procedure TExceptionTests.TestLexer_Except_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('except');
  try
    T := L.Next;
    AssertEquals('except token', Ord(tkExcept), Ord(T.Kind));
  finally L.Free; end;
end;

procedure TExceptionTests.TestLexer_Raise_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('raise');
  try
    T := L.Next;
    AssertEquals('raise token', Ord(tkRaise), Ord(T.Kind));
  finally L.Free; end;
end;

{ ------------------------------------------------------------------ }
{ Parser — try/finally                                                 }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestParse_TryFinally_IsTTryFinallyStmt;
var Prog: TProgram;
begin
  Prog := ParseSrc(SrcTryFinally);
  try
    AssertTrue('stmt is TTryFinallyStmt',
      Prog.Block.Stmts[1] is TTryFinallyStmt);
  finally Prog.Free; end;
end;

procedure TExceptionTests.TestParse_TryFinally_TryBodyStmtCount;
var Prog: TProgram; TS: TTryFinallyStmt;
begin
  Prog := ParseSrc(SrcTryFinally);
  try
    TS := TTryFinallyStmt(Prog.Block.Stmts[1]);
    AssertEquals('try body has 1 stmt', 1, TS.TryBody.Stmts.Count);
  finally Prog.Free; end;
end;

procedure TExceptionTests.TestParse_TryFinally_FinallyBodyStmtCount;
var Prog: TProgram; TS: TTryFinallyStmt;
begin
  Prog := ParseSrc(SrcTryFinally);
  try
    TS := TTryFinallyStmt(Prog.Block.Stmts[1]);
    AssertEquals('finally body has 1 stmt', 1, TS.FinallyBody.Stmts.Count);
  finally Prog.Free; end;
end;

procedure TExceptionTests.TestParse_TryFinally_MultipleStmtsInTryBody;
var Prog: TProgram; TS: TTryFinallyStmt;
begin
  Prog := ParseSrc(SrcTryFinallyMulti);
  try
    TS := TTryFinallyStmt(Prog.Block.Stmts[0]);
    AssertEquals('multi try body has 2 stmts', 2, TS.TryBody.Stmts.Count);
  finally Prog.Free; end;
end;

procedure TExceptionTests.TestParse_TryFinally_MultipleStmtsInFinallyBody;
var Prog: TProgram; TS: TTryFinallyStmt;
begin
  Prog := ParseSrc(SrcTryFinallyMulti);
  try
    TS := TTryFinallyStmt(Prog.Block.Stmts[0]);
    AssertEquals('multi finally body has 2 stmts', 2, TS.FinallyBody.Stmts.Count);
  finally Prog.Free; end;
end;

{ ------------------------------------------------------------------ }
{ Parser — try/except                                                  }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestParse_TryExcept_IsTTryExceptStmt;
var Prog: TProgram;
begin
  Prog := ParseSrc(SrcTryExcept);
  try
    AssertTrue('stmt is TTryExceptStmt',
      Prog.Block.Stmts[1] is TTryExceptStmt);
  finally Prog.Free; end;
end;

procedure TExceptionTests.TestParse_TryExcept_TryBodyStmtCount;
var Prog: TProgram; TS: TTryExceptStmt;
begin
  Prog := ParseSrc(SrcTryExcept);
  try
    TS := TTryExceptStmt(Prog.Block.Stmts[1]);
    AssertEquals('try body has 1 stmt', 1, TS.TryBody.Stmts.Count);
  finally Prog.Free; end;
end;

procedure TExceptionTests.TestParse_TryExcept_ExceptBodyStmtCount;
var Prog: TProgram; TS: TTryExceptStmt;
begin
  Prog := ParseSrc(SrcTryExcept);
  try
    TS := TTryExceptStmt(Prog.Block.Stmts[1]);
    AssertEquals('except body has 1 stmt', 1, TS.ExceptBody.Stmts.Count);
  finally Prog.Free; end;
end;

{ ------------------------------------------------------------------ }
{ Parser — raise                                                       }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestParse_Raise_IsTRaiseStmt;
var Prog: TProgram;
begin
  Prog := ParseSrc(SrcRaise);
  try
    AssertTrue('stmt is TRaiseStmt', Prog.Block.Stmts[1] is TRaiseStmt);
  finally Prog.Free; end;
end;

procedure TExceptionTests.TestParse_Raise_HasExpr;
var Prog: TProgram; RS: TRaiseStmt;
begin
  Prog := ParseSrc(SrcRaise);
  try
    RS := TRaiseStmt(Prog.Block.Stmts[1]);
    AssertNotNull('raise has non-nil expression', RS.Expr);
  finally Prog.Free; end;
end;

procedure TExceptionTests.TestParse_Raise_Bare_HasNilExpr;
var Prog: TProgram; TS: TTryExceptStmt; RS: TRaiseStmt;
begin
  Prog := ParseSrc(SrcBareRaise);
  try
    TS := TTryExceptStmt(Prog.Block.Stmts[0]);
    AssertTrue('except body stmt is TRaiseStmt',
      TS.ExceptBody.Stmts[0] is TRaiseStmt);
    RS := TRaiseStmt(TS.ExceptBody.Stmts[0]);
    AssertNull('bare raise has nil expression', RS.Expr);
  finally Prog.Free; end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestSemantic_TryFinally_OK;
begin
  AnalyseSrc(SrcTryFinally).Free;
end;

procedure TExceptionTests.TestSemantic_TryExcept_OK;
begin
  AnalyseSrc(SrcTryExcept).Free;
end;

procedure TExceptionTests.TestSemantic_Raise_ClassExpr_OK;
begin
  AnalyseSrc(SrcRaise).Free;
end;

procedure TExceptionTests.TestSemantic_Raise_NonClass_RaisesError;
begin
  AnalyseExpectError(
    'program P;'          + LineEnding +
    'var X: Integer;'     + LineEnding +
    'begin'               + LineEnding +
    '  X := 1;'           + LineEnding +
    '  raise X'           + LineEnding +
    'end.');
end;

procedure TExceptionTests.TestSemantic_Raise_Bare_OK;
begin
  AnalyseSrc(SrcBareRaise).Free;
end;

{ ------------------------------------------------------------------ }
{ Codegen — try/finally                                                }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestCodegen_TryFinally_TryBodyInIR;
var IR: string;
begin
  IR := GenIR(SrcTryFinally);
  { X := 1 inside try block }
  AssertTrue('try body copy 1 in IR', Pos('copy 1', IR) > 0);
end;

procedure TExceptionTests.TestCodegen_TryFinally_FinallyBodyInIR;
var IR: string;
begin
  IR := GenIR(SrcTryFinally);
  { X := 2 inside finally block }
  AssertTrue('finally body copy 2 in IR', Pos('copy 2', IR) > 0);
end;

procedure TExceptionTests.TestCodegen_TryFinally_FinallyAfterTry;
var IR: string; PosTry, PosFinally: Integer;
begin
  IR := GenIR(SrcTryFinally);
  { finally code (copy 2) must appear after try code (copy 1) }
  PosTry     := Pos('copy 1', IR);
  PosFinally := Pos('copy 2', IR);
  AssertTrue('try body present', PosTry > 0);
  AssertTrue('finally body present', PosFinally > 0);
  AssertTrue('finally appears after try in IR', PosFinally > PosTry);
end;

{ ------------------------------------------------------------------ }
{ Codegen — try/except                                                 }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestCodegen_TryExcept_TryBodyInIR;
var IR: string;
begin
  IR := GenIR(SrcTryExcept);
  { X := 1 inside try block }
  AssertTrue('try body in IR', Pos('copy 1', IR) > 0);
end;

procedure TExceptionTests.TestCodegen_TryExcept_ExceptLabelPresent;
var IR: string;
begin
  IR := GenIR(SrcTryExcept);
  { Except handler block has a label }
  AssertTrue('except handler label in IR', Pos('except_handler', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Codegen — raise                                                      }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestCodegen_Raise_CallsRTL;
var IR: string;
begin
  IR := GenIR(SrcRaise);
  { raise emits a call to the RTL raise function }
  AssertTrue('call $_Raise in IR', Pos('call $_Raise', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Codegen — setjmp-based real dispatch                                 }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestCodegen_TryExcept_PushesExcFrame;
var IR: string;
begin
  IR := GenIR(SrcTryExcept);
  AssertTrue('try/except pushes exc frame', Pos('call $_PushExcFrame', IR) > 0);
end;

procedure TExceptionTests.TestCodegen_TryExcept_CallsSetjmp;
var IR: string;
begin
  IR := GenIR(SrcTryExcept);
  AssertTrue('try/except calls setjmp', Pos('call $setjmp', IR) > 0);
end;

procedure TExceptionTests.TestCodegen_TryExcept_PopsFrame;
var IR: string;
begin
  IR := GenIR(SrcTryExcept);
  AssertTrue('try/except pops exc frame', Pos('call $_PopExcFrame', IR) > 0);
end;

procedure TExceptionTests.TestCodegen_TryFinally_PushesExcFrame;
var IR: string;
begin
  IR := GenIR(SrcTryFinally);
  AssertTrue('try/finally pushes exc frame', Pos('call $_PushExcFrame', IR) > 0);
end;

procedure TExceptionTests.TestCodegen_TryFinally_CallsReraise;
var IR: string;
begin
  IR := GenIR(SrcTryFinally);
  AssertTrue('try/finally re-raises on exception path', Pos('call $_Reraise', IR) > 0);
end;

procedure TExceptionTests.TestCodegen_TryFinally_FinallyOnBothPaths;
var
  IR:   string;
  N:    Integer;
  Idx:  Integer;
begin
  { finally body (copy 2) must appear on both the normal and exception paths }
  IR  := GenIR(SrcTryFinally);
  N   := 0;
  Idx := 1;
  while True do
  begin
    Idx := PosEx('copy 2', IR, Idx);
    if Idx = 0 then Break;
    Inc(N);
    Inc(Idx);
  end;
  AssertTrue('finally body appears on both paths (>= 2 occurrences)', N >= 2);
end;

initialization
  RegisterTest(TExceptionTests);

end.
