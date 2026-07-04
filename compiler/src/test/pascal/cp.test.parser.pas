{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.parser;

interface

uses
  blaise.testing,
  uLexer, uParser, uAST;

type
  TParserTests = class(TTestCase)
  private
    function ParseSource(const ASrc: string): TProgram;
  published
    { Program structure }
    procedure TestMinimalProgram;
    procedure TestProgramName;
    procedure TestProgramWithUses;
    procedure TestProgramWithMultipleUses;
    procedure TestProgramWithDottedUnitName;

    { Var block }
    procedure TestSingleVarDecl;
    procedure TestMultipleVarDecls;
    procedure TestMultiNameVarDecl;
    { Qualified type name 'UnitName.TypeName' is captured whole. }
    procedure TestQualifiedTypeName;
    procedure TestQualifiedTypeName_DottedUnit;

    { Statements }
    procedure TestEmptyBeginEnd;
    procedure TestAssignment_IntLit;
    procedure TestAssignment_StringLit;
    procedure TestProcCall_NoArgs;
    procedure TestProcCall_NoParens;
    procedure TestProcCall_OneStringArg;
    procedure TestProcCall_OneIntArg;

    { Expressions }
    procedure TestExpr_Addition;
    procedure TestExpr_Subtraction;
    procedure TestExpr_Multiplication;
    procedure TestExpr_Precedence_MulBeforeAdd;
    procedure TestExpr_Parenthesised;
    procedure TestExpr_IdentInExpr;

    { Chained postfix access }
    procedure TestChain_MethodThenField;
    procedure TestChain_SubscriptThenField;
    procedure TestChain_MethodThenMethodThenField;
    procedure TestChain_FuncCallThenSubscript;

    { Named integer subrange types (issue #130 bug1) }
    procedure TestSubrange_NamedType_Parses;
    procedure TestSubrange_NegativeBounds_Parses;
    procedure TestSubrange_Descending_Error;

    { forward; in a program declaration section (issue #130 bug2) }
    procedure TestForward_InProgram_Parses;

    { Error cases }
    procedure TestError_MissingProgramKeyword;
    procedure TestError_MissingDot;
  end;

implementation

function TParserTests.ParseSource(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
end;

{ Program structure }

procedure TParserTests.TestMinimalProgram;
var
  Prog: TProgram;
begin
  Prog := ParseSource('program Empty; begin end.');
  try
    AssertNotNull('TProgram', Prog);
    AssertNotNull('Block', Prog.Block);
    AssertEquals('No decls', 0, Prog.Block.Decls.Count);
    AssertEquals('No stmts', 0, Prog.Block.Stmts.Count);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestProgramName;
var
  Prog: TProgram;
begin
  Prog := ParseSource('program MyApp; begin end.');
  try
    AssertEquals('Name', 'MyApp', Prog.Name);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestProgramWithUses;
var
  Prog: TProgram;
begin
  Prog := ParseSource('program P; uses System; begin end.');
  try
    AssertEquals('Uses count', 1, Prog.UsedUnits.Count);
    AssertEquals('Unit name', 'System', Prog.UsedUnits.Strings[0]);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestProgramWithMultipleUses;
var
  Prog: TProgram;
begin
  Prog := ParseSource('program P; uses System, SysUtils; begin end.');
  try
    AssertEquals('Uses count', 2, Prog.UsedUnits.Count);
    AssertEquals('First', 'System', Prog.UsedUnits.Strings[0]);
    AssertEquals('Second', 'SysUtils', Prog.UsedUnits.Strings[1]);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestProgramWithDottedUnitName;
var
  Prog: TProgram;
begin
  Prog := ParseSource('program P; uses Generics.Collections, SysUtils; begin end.');
  try
    AssertEquals('Uses count', 2, Prog.UsedUnits.Count);
    AssertEquals('Dotted unit name', 'Generics.Collections', Prog.UsedUnits.Strings[0]);
    AssertEquals('Plain unit name', 'SysUtils', Prog.UsedUnits.Strings[1]);
  finally
    Prog.Free();
  end;
end;

{ Var block }

procedure TParserTests.TestSingleVarDecl;
var
  Prog: TProgram;
  Decl: TVarDecl;
begin
  Prog := ParseSource('program P; var x: Integer; begin end.');
  try
    AssertEquals('1 decl', 1, Prog.Block.Decls.Count);
    Decl := TVarDecl(Prog.Block.Decls.Items[0]);
    AssertEquals('1 name', 1, Decl.Names.Count);
    AssertEquals('Name', 'x', Decl.Names.Strings[0]);
    AssertEquals('Type', 'Integer', Decl.TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestQualifiedTypeName;
var
  Prog: TProgram;
begin
  Prog := ParseSource('program P; var x: System.Integer; begin end.');
  try
    AssertEquals('qualified type captured whole', 'System.Integer',
      TVarDecl(Prog.Block.Decls.Items[0]).TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestQualifiedTypeName_DottedUnit;
var
  Prog: TProgram;
begin
  { The unit qualifier may itself be dotted; the whole dotted path is
    carried through to the type name. }
  Prog := ParseSource('program P; var x: System.SysUtils.TFoo; begin end.');
  try
    AssertEquals('dotted-unit qualified type captured whole',
      'System.SysUtils.TFoo',
      TVarDecl(Prog.Block.Decls.Items[0]).TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestMultipleVarDecls;
var
  Prog: TProgram;
begin
  Prog := ParseSource(
    'program P; var x: Integer; s: string; begin end.');
  try
    AssertEquals('2 decls', 2, Prog.Block.Decls.Count);
    AssertEquals('First type', 'Integer',
      TVarDecl(Prog.Block.Decls.Items[0]).TypeName);
    AssertEquals('Second type', 'string',
      TVarDecl(Prog.Block.Decls.Items[1]).TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestMultiNameVarDecl;
var
  Prog: TProgram;
  Decl: TVarDecl;
begin
  Prog := ParseSource('program P; var x, y: Integer; begin end.');
  try
    AssertEquals('1 decl group', 1, Prog.Block.Decls.Count);
    Decl := TVarDecl(Prog.Block.Decls.Items[0]);
    AssertEquals('2 names', 2, Decl.Names.Count);
    AssertEquals('First', 'x', Decl.Names.Strings[0]);
    AssertEquals('Second', 'y', Decl.Names.Strings[1]);
  finally
    Prog.Free();
  end;
end;

{ Statements }

procedure TParserTests.TestEmptyBeginEnd;
var
  Prog: TProgram;
begin
  Prog := ParseSource('program P; begin end.');
  try
    AssertEquals('No stmts', 0, Prog.Block.Stmts.Count);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestAssignment_IntLit;
var
  Prog:   TProgram;
  Assign: TAssignment;
  Lit:    TIntLiteral;
begin
  Prog := ParseSource('program P; var n: Integer; begin n := 42 end.');
  try
    AssertEquals('1 stmt', 1, Prog.Block.Stmts.Count);
    AssertTrue('Is TAssignment',
      Prog.Block.Stmts.Items[0] is TAssignment);
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertEquals('Name', 'n', Assign.Name);
    AssertTrue('Expr is TIntLiteral', Assign.Expr is TIntLiteral);
    Lit := TIntLiteral(Assign.Expr);
    AssertEquals('Value', 42, Lit.Value);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestAssignment_StringLit;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Prog := ParseSource(
    'program P; var s: string; begin s := ''hello'' end.');
  try
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertTrue('Expr is TStringLiteral', Assign.Expr is TStringLiteral);
    AssertEquals('Value', 'hello',
      TStringLiteral(Assign.Expr).Value);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestProcCall_NoArgs;
var
  Prog: TProgram;
  Call: TProcCall;
begin
  Prog := ParseSource('program P; begin WriteLn() end.');
  try
    AssertTrue('Is TProcCall',
      Prog.Block.Stmts.Items[0] is TProcCall);
    Call := TProcCall(Prog.Block.Stmts.Items[0]);
    AssertEquals('Name', 'WriteLn', Call.Name);
    AssertEquals('0 args', 0, Call.Args.Count);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestProcCall_NoParens;
var
  Prog: TProgram;
  Call: TProcCall;
begin
  Prog := ParseSource('program P; begin WriteLn end.');
  try
    Call := TProcCall(Prog.Block.Stmts.Items[0]);
    AssertEquals('Name', 'WriteLn', Call.Name);
    AssertEquals('0 args', 0, Call.Args.Count);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestProcCall_OneStringArg;
var
  Prog: TProgram;
  Call: TProcCall;
begin
  Prog := ParseSource('program P; begin WriteLn(''Hello'') end.');
  try
    Call := TProcCall(Prog.Block.Stmts.Items[0]);
    AssertEquals('1 arg', 1, Call.Args.Count);
    AssertTrue('Arg is TStringLiteral',
      Call.Args.Items[0] is TStringLiteral);
    AssertEquals('Value', 'Hello',
      TStringLiteral(Call.Args.Items[0]).Value);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestProcCall_OneIntArg;
var
  Prog: TProgram;
  Call: TProcCall;
begin
  Prog := ParseSource('program P; begin WriteLn(99) end.');
  try
    Call := TProcCall(Prog.Block.Stmts.Items[0]);
    AssertEquals('1 arg', 1, Call.Args.Count);
    AssertTrue('Arg is TIntLiteral', Call.Args.Items[0] is TIntLiteral);
    AssertEquals('Value', 99, TIntLiteral(Call.Args.Items[0]).Value);
  finally
    Prog.Free();
  end;
end;

{ Expressions }

procedure TParserTests.TestExpr_Addition;
var
  Prog:  TProgram;
  Bin:   TBinaryExpr;
begin
  Prog := ParseSource(
    'program P; var n: Integer; begin n := 1 + 2 end.');
  try
    Bin := TBinaryExpr(TAssignment(Prog.Block.Stmts.Items[0]).Expr);
    AssertEquals('Op', Ord(boAdd), Ord(Bin.Op));
    AssertEquals('Left', 1, TIntLiteral(Bin.Left).Value);
    AssertEquals('Right', 2, TIntLiteral(Bin.Right).Value);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestExpr_Subtraction;
var
  Prog: TProgram;
  Bin:  TBinaryExpr;
begin
  Prog := ParseSource(
    'program P; var n: Integer; begin n := 10 - 3 end.');
  try
    Bin := TBinaryExpr(TAssignment(Prog.Block.Stmts.Items[0]).Expr);
    AssertEquals('Op', Ord(boSub), Ord(Bin.Op));
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestExpr_Multiplication;
var
  Prog: TProgram;
  Bin:  TBinaryExpr;
begin
  Prog := ParseSource(
    'program P; var n: Integer; begin n := 3 * 4 end.');
  try
    Bin := TBinaryExpr(TAssignment(Prog.Block.Stmts.Items[0]).Expr);
    AssertEquals('Op', Ord(boMul), Ord(Bin.Op));
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestExpr_Precedence_MulBeforeAdd;
var
  Prog:  TProgram;
  Outer: TBinaryExpr;
  Inner: TBinaryExpr;
begin
  { 1 + 2 * 3 should parse as 1 + (2 * 3) }
  Prog := ParseSource(
    'program P; var n: Integer; begin n := 1 + 2 * 3 end.');
  try
    Outer := TBinaryExpr(TAssignment(Prog.Block.Stmts.Items[0]).Expr);
    AssertEquals('Outer op is Add', Ord(boAdd), Ord(Outer.Op));
    AssertTrue('Right is TBinaryExpr', Outer.Right is TBinaryExpr);
    Inner := TBinaryExpr(Outer.Right);
    AssertEquals('Inner op is Mul', Ord(boMul), Ord(Inner.Op));
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestExpr_Parenthesised;
var
  Prog:  TProgram;
  Outer: TBinaryExpr;
  Inner: TBinaryExpr;
begin
  { (1 + 2) * 3 — outer should be Mul, left child is Add }
  Prog := ParseSource(
    'program P; var n: Integer; begin n := (1 + 2) * 3 end.');
  try
    Outer := TBinaryExpr(TAssignment(Prog.Block.Stmts.Items[0]).Expr);
    AssertEquals('Outer op is Mul', Ord(boMul), Ord(Outer.Op));
    AssertTrue('Left is TBinaryExpr', Outer.Left is TBinaryExpr);
    Inner := TBinaryExpr(Outer.Left);
    AssertEquals('Inner op is Add', Ord(boAdd), Ord(Inner.Op));
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestExpr_IdentInExpr;
var
  Prog:   TProgram;
  Assign: TAssignment;
  Bin:    TBinaryExpr;
begin
  Prog := ParseSource(
    'program P; var x, y: Integer; begin y := x + 1 end.');
  try
    Assign := TAssignment(Prog.Block.Stmts.Items[0]);
    Bin := TBinaryExpr(Assign.Expr);
    AssertTrue('Left is TIdentExpr', Bin.Left is TIdentExpr);
    AssertEquals('Ident name', 'x', TIdentExpr(Bin.Left).Name);
  finally
    Prog.Free();
  end;
end;

{ Error cases }

{ Chained postfix access }

procedure TParserTests.TestChain_MethodThenField;
var
  Prog: TProgram;
  Stmt: TAssignment;
  Fld:  TFieldAccessExpr;
begin
  Prog := ParseSource(
    'program P; var N: Integer; begin N := Obj.GetRec().X end.');
  try
    Stmt := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertTrue('RHS is field access', Stmt.Expr is TFieldAccessExpr);
    Fld := TFieldAccessExpr(Stmt.Expr);
    AssertEquals('field name', 'X', Fld.FieldName);
    AssertTrue('base is method call', Fld.Base is TMethodCallExpr);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestChain_SubscriptThenField;
var
  Prog: TProgram;
  Stmt: TAssignment;
  Fld:  TFieldAccessExpr;
begin
  Prog := ParseSource(
    'program P; var N: Integer; begin N := Tokens[0].Kind end.');
  try
    Stmt := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertTrue('RHS is field access', Stmt.Expr is TFieldAccessExpr);
    Fld := TFieldAccessExpr(Stmt.Expr);
    AssertEquals('field name', 'Kind', Fld.FieldName);
    AssertTrue('base is subscript', Fld.Base is TStringSubscriptExpr);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestChain_MethodThenMethodThenField;
var
  Prog: TProgram;
  Stmt: TAssignment;
  Fld:  TFieldAccessExpr;
  MC:   TMethodCallExpr;
begin
  Prog := ParseSource(
    'program P; var N: Integer; begin N := A.GetB().GetC().Val end.');
  try
    Stmt := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertTrue('RHS is field access', Stmt.Expr is TFieldAccessExpr);
    Fld := TFieldAccessExpr(Stmt.Expr);
    AssertEquals('outer field', 'Val', Fld.FieldName);
    AssertTrue('base is method call', Fld.Base is TMethodCallExpr);
    MC := TMethodCallExpr(Fld.Base);
    AssertEquals('middle method', 'GetC', MC.Name);
    AssertTrue('middle base is method call', MC.ObjExpr is TMethodCallExpr);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestChain_FuncCallThenSubscript;
var
  Prog: TProgram;
  Stmt: TAssignment;
  Sub:  TStringSubscriptExpr;
begin
  Prog := ParseSource(
    'program P; var N: Integer; begin N := GetList()[0] end.');
  try
    Stmt := TAssignment(Prog.Block.Stmts.Items[0]);
    AssertTrue('RHS is subscript', Stmt.Expr is TStringSubscriptExpr);
    Sub := TStringSubscriptExpr(Stmt.Expr);
    AssertTrue('base is func call', Sub.StrExpr is TFuncCallExpr);
  finally
    Prog.Free();
  end;
end;

procedure TParserTests.TestError_MissingProgramKeyword;
begin
  try
    ParseSource('begin end.').Free();
    Fail('Expected EParseError');
  except
    on E: EParseError do ; { expected }
  end;
end;

procedure TParserTests.TestError_MissingDot;
begin
  try
    ParseSource('program P; begin end').Free();
    Fail('Expected EParseError');
  except
    on E: EParseError do ; { expected }
  end;
end;

procedure TParserTests.TestSubrange_NamedType_Parses;
begin
  { type TByte = 0..255; must parse (issue #130 bug1). }
  ParseSource('program P; type TByte = 0..255; var b: TByte; ' +
    'begin b := 5 end.').Free();
end;

procedure TParserTests.TestSubrange_NegativeBounds_Parses;
begin
  ParseSource('program P; type TIdx = -10..10; var i: TIdx; ' +
    'begin i := -3 end.').Free();
end;

procedure TParserTests.TestSubrange_Descending_Error;
begin
  try
    ParseSource('program P; type TBad = 10..0; begin end.').Free();
    Fail('Expected EParseError for descending subrange');
  except
    on E: EParseError do ; { expected }
  end;
end;

procedure TParserTests.TestForward_InProgram_Parses;
var
  Prog: TProgram;
begin
  { A forward; routine in a program's decl section, then its separate
    implementation, must parse — the forward decl must NOT swallow the
    implementation as a nested-proc body (issue #130 bug2). }
  Prog := ParseSource(
    'program P; ' +
    'function F(n: Integer): Boolean; forward; ' +
    'function F(n: Integer): Boolean; begin Result := n > 0 end; ' +
    'begin WriteLn(F(5)) end.');
  try
    { Two ProcDecls: the forward (no body) and the implementation (with body). }
    AssertEquals('two proc decls', 2, Prog.Block.ProcDecls.Count);
    AssertTrue('forward decl has no body',
      TMethodDecl(Prog.Block.ProcDecls.Items[0]).Body = nil);
    AssertTrue('impl decl has a body',
      TMethodDecl(Prog.Block.ProcDecls.Items[1]).Body <> nil);
  finally
    Prog.Free();
  end;
end;

initialization
  RegisterTest(TParserTests);

end.
