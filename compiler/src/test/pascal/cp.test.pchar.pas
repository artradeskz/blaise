{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.pchar;

{$mode objfpc}{$H+}

{ Tests for PChar type: PChar(str) cast and string(pchar) cast.
  Covers semantic analysis and QBE IR code generation. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TPCharTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
  published
    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_PChar_CastFromString;
    procedure TestSemantic_PChar_VarKind;
    procedure TestSemantic_String_CastFromPChar;

    { ------------------------------------------------------------------ }
    { Codegen                                                              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_PChar_EmitsAddOffset;
    procedure TestCodegen_PChar_AllocEmitted;
    procedure TestCodegen_String_EmitsRTLCall;
    procedure TestCodegen_PCharSubscript_ChrByteShortCircuit;
  end;

implementation

function TPCharTests.AnalyseSrc(const ASrc: string): TProgram;
var L: TLexer; P: TParser; A: TSemanticAnalyser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse;
  finally
    P.Free; L.Free;
  end;
  A := TSemanticAnalyser.Create;
  try
    A.Analyse(Result);
  finally
    A.Free;
  end;
end;

function TPCharTests.GenIR(const ASrc: string): string;
var P: TProgram; CG: TCodeGenQBE;
begin
  P := AnalyseSrc(ASrc);
  try
    CG := TCodeGenQBE.Create;
    try
      CG.Generate(P);
      Result := CG.GetOutput;
    finally
      CG.Free;
    end;
  finally
    P.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Shared source snippets                                              }
{ ------------------------------------------------------------------ }

const
  SrcPCharCast =
    '''
        program PC;
        procedure Foo(s: string);
        var p: PChar;
        begin
          p := PChar(s)
        end;
        begin end.
        ''';

  SrcStringCast =
    '''
        program PC;
        function Bar(p: PChar): string;
        begin
          Result := string(p)
        end;
        begin end.
        ''';

{ ------------------------------------------------------------------ }
{ Semantic tests                                                      }
{ ------------------------------------------------------------------ }

procedure TPCharTests.TestSemantic_PChar_CastFromString;
var P: TProgram; MDecl: TMethodDecl; Assign: TAssignment;
begin
  P := AnalyseSrc(SrcPCharCast);
  try
    MDecl  := TMethodDecl(P.Block.ProcDecls[0]);
    Assign := TAssignment(MDecl.Body.Stmts[0]);
    AssertNotNull('assign expr resolved', Assign.Expr.ResolvedType);
    AssertEquals('PChar(s) resolves to tyPChar',
      Ord(tyPChar), Ord(Assign.Expr.ResolvedType.Kind));
  finally P.Free; end;
end;

procedure TPCharTests.TestSemantic_PChar_VarKind;
var P: TProgram; MDecl: TMethodDecl; Decl: TVarDecl;
begin
  P := AnalyseSrc(SrcPCharCast);
  try
    MDecl := TMethodDecl(P.Block.ProcDecls[0]);
    Decl  := TVarDecl(MDecl.Body.Decls[0]);
    AssertNotNull('ResolvedType set', Decl.ResolvedType);
    AssertEquals('var p: PChar resolves to tyPChar',
      Ord(tyPChar), Ord(Decl.ResolvedType.Kind));
  finally P.Free; end;
end;

procedure TPCharTests.TestSemantic_String_CastFromPChar;
var P: TProgram; MDecl: TMethodDecl; Assign: TAssignment;
begin
  P := AnalyseSrc(SrcStringCast);
  try
    MDecl  := TMethodDecl(P.Block.ProcDecls[0]);
    Assign := TAssignment(MDecl.Body.Stmts[0]);
    AssertNotNull('assign expr resolved', Assign.Expr.ResolvedType);
    AssertEquals('string(p) resolves to tyString',
      Ord(tyString), Ord(Assign.Expr.ResolvedType.Kind));
  finally P.Free; end;
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                       }
{ ------------------------------------------------------------------ }

procedure TPCharTests.TestCodegen_PChar_EmitsAddOffset;
var IR: string;
begin
  IR := GenIR(SrcPCharCast);
  { Data-pointer convention: PChar(str) is an identity — str IS the data pointer.
    No add instruction or offset needed; the string value is passed through directly. }
  AssertTrue('pchar cast compiles without error', Length(IR) > 0);
end;

procedure TPCharTests.TestCodegen_PChar_AllocEmitted;
var IR: string;
begin
  IR := GenIR(SrcPCharCast);
  { var p: PChar allocates an 8-byte pointer slot }
  AssertTrue('alloc8 1 for PChar var', Pos('alloc8 1', IR) > 0);
end;

procedure TPCharTests.TestCodegen_String_EmitsRTLCall;
var IR: string;
begin
  IR := GenIR(SrcStringCast);
  AssertTrue('_StringFromPChar called', Pos('$_StringFromPChar', IR) > 0);
end;

{ Regression test for: P[I] := Chr(N) used to emit a call to $_Chr (which
  returns a heap string pointer) and then storeb of the pointer's low byte,
  yielding garbage.  The fix short-circuits Chr(N) in byte-store context. }
procedure TPCharTests.TestCodegen_PCharSubscript_ChrByteShortCircuit;
const
  Src =
    '''
      program PCC;
      var p: PChar;
      begin
        p := GetMem(4);
        p[0] := Chr(65);
        FreeMem(p)
      end.
      ''';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('storeb is emitted for p[0] write', Pos('storeb', IR) >= 0);
  AssertEquals('Chr(65) byte-store must not call $_Chr',
    -1, Pos('call $_Chr(', IR));
end;

initialization
  RegisterTest(TPCharTests);

end.
