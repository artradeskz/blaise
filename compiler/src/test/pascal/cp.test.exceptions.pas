{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.exceptions;

{ Tests for try/finally, try/except, and raise statements. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

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
    procedure TestSemantic_ExceptionSubclass_CreateAndMessage_OK;

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
    procedure TestCodegen_TryExcept_FrameAllocSize;
    procedure TestCodegen_TryFinally_FrameAllocSize;
    { Exit inside try/finally must emit the finally body on the exit path,
      not just pop the frame. }
    procedure TestCodegen_ExitInTryFinally_RunsFinally;
    { Exit inside the SECOND try block of a function must still pop its
      frame: the emitter's FExcDepth bookkeeping is per-path, and the
      exception path must rebalance it (regression: a double decrement left
      later try blocks at depth 0, so their Exit paths skipped the pop and
      left a stale g_exc_top -> crash on a later raise/pop). }
    procedure TestCodegen_ExitInSecondTryExcept_PopsFrame;

    { ------------------------------------------------------------------ }
    { Codegen — ARC cleanup on exception paths                            }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_TryFinally_NoArcCleanup_BeforeReraise;
    procedure TestCodegen_TryFinally_NoArcZero_BeforeReraise;
    procedure TestCodegen_ExceptionSubclass_CtorCallWithMessage;

    { ------------------------------------------------------------------ }
    { Parser — typed except handlers (on E: TClass do)                   }
    { ------------------------------------------------------------------ }
    procedure TestParse_TypedExcept_HasOneHandler;
    procedure TestParse_TypedExcept_HandlerTypeName;
    procedure TestParse_TypedExcept_HandlerVarName;
    procedure TestParse_TypedExcept_HandlerBodyStmtCount;
    procedure TestParse_TypedExcept_TwoHandlers;
    procedure TestParse_TypedExcept_WithElseBody;
    procedure TestParse_TypedExcept_NoVarBinding;

    { ------------------------------------------------------------------ }
    { Semantic — typed except handlers                                    }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_TypedExcept_SingleHandler_OK;
    procedure TestSemantic_TypedExcept_TwoHandlers_OK;
    procedure TestSemantic_TypedExcept_NonClassType_RaisesError;
    procedure TestSemantic_TypedExcept_WithElse_OK;
    procedure TestSemantic_TypedExcept_HandlerVarUsableInBody;

    { ------------------------------------------------------------------ }
    { Codegen — typed except handlers                                     }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_TypedExcept_CallsIsInstance;
    procedure TestCodegen_TypedExcept_TwoHandlers_TwoIsInstanceCalls;
    procedure TestCodegen_TypedExcept_ElseBodyPresent;
    procedure TestCodegen_TypedExcept_UsesCurrentException;

    { ------------------------------------------------------------------ }
    { Codegen — bare raise in except handler                              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_BareRaise_InTypedHandler_CallsReraise;
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
    Result := P.Parse();
  finally
    P.Free(); L.Free();
  end;
end;

function TExceptionTests.AnalyseSrc(const ASrc: string): TProgram;
var A: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  A := TSemanticAnalyser.Create();
  try
    A.Analyse(Result);
  finally
    A.Free();
  end;
end;

function TExceptionTests.GenIR(const ASrc: string): string;
var Prog: TProgram; CG: TCodeGenQBE;
begin
  Prog := AnalyseSrc(ASrc);
  try
    CG := TCodeGenQBE.Create();
    try
      CG.Generate(Prog);
      Result := CG.GetOutput();
    finally
      CG.Free();
    end;
  finally
    Prog.Free();
  end;
end;

procedure TExceptionTests.AnalyseExpectError(const ASrc: string);
var Prog: TProgram;
begin
  try
    Prog := AnalyseSrc(ASrc);
    Prog.Free();
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
    '''
        program P;
        var X: Integer;
        begin
          X := 0;
          try
            X := 1
          finally
            X := 2
          end
        end.
        ''';

  SrcTryFinallyMulti =
    '''
        program P;
        var X: Integer;
        var Y: Integer;
        begin
          try
            X := 1;
            Y := 2
          finally
            X := 0;
            Y := 0
          end
        end.
        ''';

  { Exit inside the try body: the finally (X := 7) must be emitted on the
    exit path too, so 'copy 7' appears three times — normal, exception, exit. }
  SrcExitInTryFinally =
    '''
        program P;
        var X: Integer;
        procedure Run;
        begin
          try
            Exit
          finally
            X := 7
          end
        end;
        begin
          Run
        end.
        ''';

  SrcTryExcept =
    '''
        program P;
        var X: Integer;
        begin
          X := 0;
          try
            X := 1
          except
            X := 99
          end
        end.
        ''';

  SrcRaise =
    '''
        program P;
        type
          TError = class
            Code: Integer;
          end;
        var E: TError;
        begin
          E := TError.Create();
          raise E
        end.
        ''';

  SrcBareRaise =
    '''
        program P;
        var X: Integer;
        begin
          try
            X := 1
          except
            raise
          end
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Lexer tests                                                          }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestLexer_Try_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('try');
  try
    T := L.Next();
    AssertEquals('try token', Ord(tkTry), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TExceptionTests.TestLexer_Finally_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('finally');
  try
    T := L.Next();
    AssertEquals('finally token', Ord(tkFinally), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TExceptionTests.TestLexer_Except_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('except');
  try
    T := L.Next();
    AssertEquals('except token', Ord(tkExcept), Ord(T.Kind));
  finally L.Free(); end;
end;

procedure TExceptionTests.TestLexer_Raise_Keyword;
var L: TLexer; T: TToken;
begin
  L := TLexer.Create('raise');
  try
    T := L.Next();
    AssertEquals('raise token', Ord(tkRaise), Ord(T.Kind));
  finally L.Free(); end;
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
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TryFinally_TryBodyStmtCount;
var Prog: TProgram; TS: TTryFinallyStmt;
begin
  Prog := ParseSrc(SrcTryFinally);
  try
    TS := TTryFinallyStmt(Prog.Block.Stmts[1]);
    AssertEquals('try body has 1 stmt', 1, TS.TryBody.Stmts.Count);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TryFinally_FinallyBodyStmtCount;
var Prog: TProgram; TS: TTryFinallyStmt;
begin
  Prog := ParseSrc(SrcTryFinally);
  try
    TS := TTryFinallyStmt(Prog.Block.Stmts[1]);
    AssertEquals('finally body has 1 stmt', 1, TS.FinallyBody.Stmts.Count);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TryFinally_MultipleStmtsInTryBody;
var Prog: TProgram; TS: TTryFinallyStmt;
begin
  Prog := ParseSrc(SrcTryFinallyMulti);
  try
    TS := TTryFinallyStmt(Prog.Block.Stmts[0]);
    AssertEquals('multi try body has 2 stmts', 2, TS.TryBody.Stmts.Count);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TryFinally_MultipleStmtsInFinallyBody;
var Prog: TProgram; TS: TTryFinallyStmt;
begin
  Prog := ParseSrc(SrcTryFinallyMulti);
  try
    TS := TTryFinallyStmt(Prog.Block.Stmts[0]);
    AssertEquals('multi finally body has 2 stmts', 2, TS.FinallyBody.Stmts.Count);
  finally Prog.Free(); end;
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
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TryExcept_TryBodyStmtCount;
var Prog: TProgram; TS: TTryExceptStmt;
begin
  Prog := ParseSrc(SrcTryExcept);
  try
    TS := TTryExceptStmt(Prog.Block.Stmts[1]);
    AssertEquals('try body has 1 stmt', 1, TS.TryBody.Stmts.Count);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TryExcept_ExceptBodyStmtCount;
var Prog: TProgram; TS: TTryExceptStmt;
begin
  Prog := ParseSrc(SrcTryExcept);
  try
    TS := TTryExceptStmt(Prog.Block.Stmts[1]);
    AssertEquals('except body has 1 stmt', 1, TS.ExceptBody.Stmts.Count);
  finally Prog.Free(); end;
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
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_Raise_HasExpr;
var Prog: TProgram; RS: TRaiseStmt;
begin
  Prog := ParseSrc(SrcRaise);
  try
    RS := TRaiseStmt(Prog.Block.Stmts[1]);
    AssertNotNull('raise has non-nil expression', RS.Expr);
  finally Prog.Free(); end;
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
  finally Prog.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestSemantic_TryFinally_OK;
begin
  AnalyseSrc(SrcTryFinally).Free();
end;

procedure TExceptionTests.TestSemantic_TryExcept_OK;
begin
  AnalyseSrc(SrcTryExcept).Free();
end;

procedure TExceptionTests.TestSemantic_Raise_ClassExpr_OK;
begin
  AnalyseSrc(SrcRaise).Free();
end;

procedure TExceptionTests.TestSemantic_Raise_NonClass_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var X: Integer;
        begin
          X := 1;
          raise X
        end.
        ''');
end;

procedure TExceptionTests.TestSemantic_Raise_Bare_OK;
begin
  AnalyseSrc(SrcBareRaise).Free();
end;

procedure TExceptionTests.TestSemantic_ExceptionSubclass_CreateAndMessage_OK;
begin
  { Verify that an Exception base class with a string property and a subclass
    that inherits it can be declared, instantiated, and raised without semantic
    errors.  This mirrors the API exposed by stdlib/src/main/pascal/sysutils.pas. }
  AnalyseSrc(
    '''
        program P;
        type
          Exception = class
            FMessage: string;
            constructor Create(AMessage: string);
            property Message: string read FMessage;
          end;
          ECompileError = class(Exception)
          end;
        var E: ECompileError;
        begin
          E := ECompileError.Create('compile error');
          raise E
        end.
        ''').Free();
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
  AssertTrue('try/except calls _blaise_setjmp', Pos('call $_blaise_setjmp', IR) > 0);
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
  Idx := 0;    { 0-based start }
  while True do
  begin
    Idx := PosEx('copy 2', IR, Idx);
    if Idx < 0 then Break;   { Blaise PosEx returns -1 when not found }
    Inc(N);
    Inc(Idx);
  end;
  AssertTrue('finally body appears on both paths (>= 2 occurrences)', N >= 2);
end;

procedure TExceptionTests.TestCodegen_ExitInTryFinally_RunsFinally;
var
  IR:  string;
  N:   Integer;
  Idx: Integer;
begin
  { With Exit inside the try body the finally (X := 7 → 'copy 7') must be
    emitted on three paths: normal fall-through, exception, and the Exit
    unwind.  Before the fix the Exit path only popped the frame and jumped
    straight to the function exit, skipping the finally entirely. }
  IR  := GenIR(SrcExitInTryFinally);
  N   := 0;
  Idx := 0;
  while True do
  begin
    Idx := PosEx('copy 7', IR, Idx);
    if Idx < 0 then Break;
    Inc(N);
    Inc(Idx);
  end;
  AssertTrue('finally body emitted on exit path too (>= 3 occurrences)', N >= 3);
end;

{ Exception frame must be >= sizeof(BlaiseExcFrame) on every supported target.
  The RTL (blaise_exc.c) fixes the contract at 512 bytes — jmp_buf alone is
  200 B on Linux x86_64 / ~312 B on macOS ARM64, plus two pointer fields.
  Undersizing silently corrupts the caller's stack when setjmp writes jbuf. }
procedure TExceptionTests.TestCodegen_ExitInSecondTryExcept_PopsFrame;
var
  IR:  string;
  N:   Integer;
  Idx: Integer;
begin
  IR := GenIR('''
      program P;
      function F(n: Integer): Integer;
      begin
        Result := 0;
        try
          if n = 0 then
          begin
            Exit(100);
          end;
        except
        end;
        try
          repeat
            if n > 2 then
            begin
              Exit(n * 10);
            end;
            n := n + 1;
          until False;
        except
        end;
      end;
      begin
      end.
      ''');
  { Each try/except emits three pops: the Exit path inside the try body,
    the normal fall-through path, and the handler path.  Two try blocks
    with one Exit each = 6 pops.  The double-decrement bug dropped the
    Exit-path pop of the second block (5 pops). }
  N := 0;
  Idx := 0;
  while True do
  begin
    Idx := PosEx('call $_PopExcFrame()', IR, Idx);
    if Idx < 0 then Break;
    Inc(N);
    Inc(Idx);
  end;
  AssertEquals('balanced frame pops across both try blocks', 6, N);
end;

procedure TExceptionTests.TestCodegen_TryExcept_FrameAllocSize;
var IR: string;
begin
  IR := GenIR(SrcTryExcept);
  AssertTrue('try/except allocates 512-byte exc frame', Pos('alloc16 512', IR) > 0);
end;

procedure TExceptionTests.TestCodegen_TryFinally_FrameAllocSize;
var IR: string;
begin
  IR := GenIR(SrcTryFinally);
  AssertTrue('try/finally allocates 512-byte exc frame', Pos('alloc16 512', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Codegen — ARC cleanup on exception paths                            }
{ ------------------------------------------------------------------ }

const
  { String assignment is ONLY inside the try body — no pre-try assignment.
    This ensures there is no assignment-site _StringRelease before @fin_exc
    that could produce a false positive in the position tests below. }
  SrcTryFinallyWithStr =
    '''
        program P;
        var S: string;
        begin
          try
            S := 'world'
          finally
          end
        end.
        ''';

procedure TExceptionTests.TestCodegen_TryFinally_NoArcCleanup_BeforeReraise;
var
  IR:         string;
  PosFinExc:  Integer;
  PosRelease: Integer;
  PosReraise: Integer;
begin
  IR := GenIR(SrcTryFinallyWithStr);
  PosFinExc  := Pos(#10 + '@fin_exc', IR);
  PosReraise := Pos('call $_Reraise', IR);
  AssertTrue('@fin_exc label present', PosFinExc > 0);
  AssertTrue('_Reraise present', PosReraise > 0);
  { ARC cleanup must NOT appear in the finally-exception path — variables
    must survive the re-raise so the outer handler can read them.  The
    function-exit block handles final release. }
  PosRelease := PosEx('call $_StringRelease', IR, PosFinExc);
  if PosRelease > 0 then
    AssertTrue('no _StringRelease before _Reraise', PosRelease > PosReraise);
end;

procedure TExceptionTests.TestCodegen_TryFinally_NoArcZero_BeforeReraise;
var
  IR:         string;
  PosFinExc:  Integer;
  PosReraise: Integer;
  PosZero:    Integer;
begin
  IR := GenIR(SrcTryFinallyWithStr);
  PosFinExc  := Pos(#10 + '@fin_exc', IR);
  PosReraise := Pos('call $_Reraise', IR);
  AssertTrue('@fin_exc label present', PosFinExc > 0);
  AssertTrue('_Reraise present', PosReraise > 0);
  { No storel 0 (variable zeroing) between @fin_exc and _Reraise — the
    outer handler or function exit is responsible for cleanup. }
  PosZero := PosEx('storel 0,', IR, PosFinExc);
  if PosZero > 0 then
    AssertTrue('no storel 0 before _Reraise', PosZero > PosReraise);
end;

procedure TExceptionTests.TestCodegen_ExceptionSubclass_CtorCallWithMessage;
var IR: string;
begin
  { Verify that constructing an Exception subclass with a message argument
    emits a constructor call that passes the string argument in the IR. }
  IR := GenIR(
    '''
        program P;
        type
          Exception = class
            FMessage: string;
            constructor Create(AMessage: string);
            property Message: string read FMessage;
          end;
          ECompileError = class(Exception)
          end;
        var E: ECompileError;
        begin
          E := ECompileError.Create('oops');
          raise E
        end.
        ''');
  AssertTrue('ctor call present',  Pos('$Exception_Create', IR) > 0);
  AssertTrue('string arg present', Pos('oops', IR) > 0);
  AssertTrue('raise RTL call',     Pos('$_Raise', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Shared source — typed except handlers                              }
{ ------------------------------------------------------------------ }

const
  SrcExcBase =
    '''
        program P;
        type
          Exception = class
            FMessage: string;
            constructor Create(AMessage: string);
            property Message: string read FMessage;
          end;
          EFoo = class(Exception) end;
          EBar = class(Exception) end;
        ''';

  SrcTypedExceptSingle =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          try
            X := 1
          except
            on E: EFoo do
              X := 42
          end
        end.
        ''';

  SrcTypedExceptTwo =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          try
            X := 1
          except
            on E: EFoo do
              X := 42;
            on E: EBar do
              X := 99
          end
        end.
        ''';

  SrcTypedExceptWithElse =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          try
            X := 1
          except
            on E: EFoo do
              X := 42
            else
              X := 0
          end
        end.
        ''';

  SrcTypedExceptNoVar =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          try
            X := 1
          except
            on EFoo do
              X := 42
          end
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Parser — typed except handlers                                     }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestParse_TypedExcept_HasOneHandler;
var Prog: TProgram; TES: TTryExceptStmt;
begin
  Prog := ParseSrc(SrcTypedExceptSingle);
  try
    TES := TTryExceptStmt(Prog.Block.Stmts[0]);
    AssertEquals('one handler', 1, TES.Handlers.Count);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TypedExcept_HandlerTypeName;
var Prog: TProgram; TES: TTryExceptStmt; H: TExceptHandlerClause;
begin
  Prog := ParseSrc(SrcTypedExceptSingle);
  try
    TES := TTryExceptStmt(Prog.Block.Stmts[0]);
    H := TExceptHandlerClause(TES.Handlers[0]);
    AssertEquals('handler type EFoo', 'EFoo', H.TypeName);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TypedExcept_HandlerVarName;
var Prog: TProgram; TES: TTryExceptStmt; H: TExceptHandlerClause;
begin
  Prog := ParseSrc(SrcTypedExceptSingle);
  try
    TES := TTryExceptStmt(Prog.Block.Stmts[0]);
    H := TExceptHandlerClause(TES.Handlers[0]);
    AssertEquals('handler var E', 'E', H.VarName);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TypedExcept_HandlerBodyStmtCount;
var Prog: TProgram; TES: TTryExceptStmt; H: TExceptHandlerClause;
begin
  Prog := ParseSrc(SrcTypedExceptSingle);
  try
    TES := TTryExceptStmt(Prog.Block.Stmts[0]);
    H := TExceptHandlerClause(TES.Handlers[0]);
    AssertEquals('handler body 1 stmt', 1, H.Body.Stmts.Count);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TypedExcept_TwoHandlers;
var Prog: TProgram; TES: TTryExceptStmt;
begin
  Prog := ParseSrc(SrcTypedExceptTwo);
  try
    TES := TTryExceptStmt(Prog.Block.Stmts[0]);
    AssertEquals('two handlers', 2, TES.Handlers.Count);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TypedExcept_WithElseBody;
var Prog: TProgram; TES: TTryExceptStmt;
begin
  Prog := ParseSrc(SrcTypedExceptWithElse);
  try
    TES := TTryExceptStmt(Prog.Block.Stmts[0]);
    AssertNotNull('else body present', TES.ElseBody);
    AssertEquals('else body 1 stmt', 1, TES.ElseBody.Stmts.Count);
  finally Prog.Free(); end;
end;

procedure TExceptionTests.TestParse_TypedExcept_NoVarBinding;
var Prog: TProgram; TES: TTryExceptStmt; H: TExceptHandlerClause;
begin
  Prog := ParseSrc(SrcTypedExceptNoVar);
  try
    TES := TTryExceptStmt(Prog.Block.Stmts[0]);
    H := TExceptHandlerClause(TES.Handlers[0]);
    AssertEquals('no-var handler: empty VarName', '', H.VarName);
    AssertEquals('no-var handler: TypeName is EFoo', 'EFoo', H.TypeName);
  finally Prog.Free(); end;
end;

{ ------------------------------------------------------------------ }
{ Semantic — typed except handlers                                   }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestSemantic_TypedExcept_SingleHandler_OK;
begin
  AnalyseSrc(SrcTypedExceptSingle).Free();
end;

procedure TExceptionTests.TestSemantic_TypedExcept_TwoHandlers_OK;
begin
  AnalyseSrc(SrcTypedExceptTwo).Free();
end;

procedure TExceptionTests.TestSemantic_TypedExcept_NonClassType_RaisesError;
begin
  AnalyseExpectError(
    '''
        program P;
        var X: Integer;
        begin
          try
            X := 1
          except
            on E: Integer do
              X := 0
          end
        end.
        ''');
end;

procedure TExceptionTests.TestSemantic_TypedExcept_WithElse_OK;
begin
  AnalyseSrc(SrcTypedExceptWithElse).Free();
end;

procedure TExceptionTests.TestSemantic_TypedExcept_HandlerVarUsableInBody;
begin
  { Handler variable E should be in scope and usable inside the handler body. }
  AnalyseSrc(
    SrcExcBase +
    '''
        var X: Integer;
        begin
          try
            X := 1
          except
            on E: EFoo do
              X := 0
          end
        end.
        ''').Free();
end;

{ ------------------------------------------------------------------ }
{ Codegen — typed except handlers                                    }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestCodegen_TypedExcept_CallsIsInstance;
var IR: string;
begin
  IR := GenIR(SrcTypedExceptSingle);
  AssertTrue('_IsInstance call for EFoo', Pos('$_IsInstance', IR) > 0);
  AssertTrue('typeinfo_EFoo referenced', Pos('typeinfo_EFoo', IR) > 0);
end;

procedure TExceptionTests.TestCodegen_TypedExcept_TwoHandlers_TwoIsInstanceCalls;
var IR: string; N: Integer; Idx: Integer;
begin
  IR := GenIR(SrcTypedExceptTwo);
  N := 0; Idx := 0;    { 0-based start }
  while True do
  begin
    Idx := PosEx('$_IsInstance', IR, Idx);
    if Idx < 0 then Break;   { Blaise PosEx returns -1 when not found }
    Inc(N); Inc(Idx);
  end;
  AssertTrue('two _IsInstance calls for two handlers', N >= 2);
end;

procedure TExceptionTests.TestCodegen_TypedExcept_ElseBodyPresent;
var IR: string;
begin
  IR := GenIR(SrcTypedExceptWithElse);
  { The else body assigns 0 to X }
  AssertTrue('else body (copy 0) in IR', Pos('copy 0', IR) > 0);
end;

procedure TExceptionTests.TestCodegen_TypedExcept_UsesCurrentException;
var IR: string;
begin
  IR := GenIR(SrcTypedExceptSingle);
  { Handler must call _CurrentException to get the live exception object }
  AssertTrue('_CurrentException called', Pos('$_CurrentException', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Codegen — bare raise in except handler                             }
{ ------------------------------------------------------------------ }

procedure TExceptionTests.TestCodegen_BareRaise_InTypedHandler_CallsReraise;
var IR: string;
begin
  IR := GenIR(
    SrcExcBase +
    '''
        var X: Integer;
        begin
          try
            X := 1
          except
            on E: EFoo do
              raise
          end
        end.
        ''');
  AssertTrue('bare raise calls _Reraise', Pos('call $_Reraise', IR) > 0);
end;

initialization
  RegisterTest(TExceptionTests);

end.
