{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.publishedrtti;

{$mode objfpc}{$H+}

{ Tests for Step 11b — published-method RTTI.  Exercises:

    * The parser tagging methods declared inside a 'published' visibility
      section with TMethodDecl.IsPublished.
    * Codegen emitting a $methods_<TName> table and pointing at it from
      the typeinfo's 4th slot.
    * The MethodAddress(Obj, Name) builtin emitting a call to the
      _MethodAddress runtime helper. }

interface

uses
  Classes, SysUtils, Process, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TPublishedRTTITests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    function CompileAndRun(const ASrc: string): string;
  published
    { Parser }
    procedure TestParse_Published_Sets_IsPublished;
    procedure TestParse_Public_Does_Not_Set_IsPublished;
    procedure TestParse_PublishedThenPublic_Boundary;

    { Codegen }
    procedure TestCodegen_TypeInfo_HasFourSlots;
    procedure TestCodegen_NoPublishedMethods_MethodsSlotZero;
    procedure TestCodegen_PublishedMethods_TableEmitted;
    procedure TestCodegen_PublishedMethods_TableCount;
    procedure TestCodegen_PublishedMethods_NameAndAddrPairs;
    procedure TestCodegen_MethodAddress_BuiltinCall;

    { End-to-end: compile + link + run }
    procedure TestE2E_MethodAddress_Found;
    procedure TestE2E_MethodAddress_NotFound;
    procedure TestE2E_MethodAddress_WalksParent;
    procedure TestE2E_MethodAddress_DistinctMethodsHaveDistinctAddresses;
  end;

implementation

function TPublishedRTTITests.ParseSrc(const ASrc: string): TProgram;
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

function TPublishedRTTITests.AnalyseSrc(const ASrc: string): TProgram;
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

function TPublishedRTTITests.GenIR(const ASrc: string): string;
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

{ Compile, assemble with QBE, link with the RTL static library, run, and
  capture stdout.  Used by the end-to-end tests below to confirm that the
  published-method table laid out by codegen is read correctly by
  _MethodAddress at runtime. }
function TPublishedRTTITests.CompileAndRun(const ASrc: string): string;

  function ProjectRoot: string;
  var
    Dir, Parent: string;
    Steps:       Integer;
  begin
    Result := GetEnvironmentVariable('BLAISE_PROJECT_ROOT');
    if Result <> '' then
    begin
      Result := IncludeTrailingPathDelimiter(Result);
      Exit;
    end;
    Dir := GetCurrentDir;
    for Steps := 0 to 5 do
    begin
      if DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'vendor/qbe') and
         DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'rtl') then
      begin
        Result := IncludeTrailingPathDelimiter(Dir);
        Exit;
      end;
      Parent := ExtractFileDir(Dir);
      if (Parent = '') or (Parent = Dir) then Break;
      Dir := Parent;
    end;
    Result := IncludeTrailingPathDelimiter(GetCurrentDir);
  end;

var
  IR:                       string;
  Root:                     string;
  QBE, RTL, Scratch:        string;
  IRFile, AsmFile, BinFile: string;
  Lst:                      TStringList;
  Proc:                     TProcess;
  OutLst:                   TStringList;
begin
  Result := '';
  Root   := ProjectRoot;
  QBE    := Root + 'vendor/qbe/qbe';
  RTL    := Root + 'compiler/target/blaise_rtl.a';
  if not (FileExists(QBE) and FileExists(RTL)) then
  begin
    Result := '<toolchain-missing>';
    Exit;
  end;
  Scratch := Root + 'compiler/target/test-publishedrtti';
  ForceDirectories(Scratch);
  IRFile  := IncludeTrailingPathDelimiter(Scratch) + 'case.ssa';
  AsmFile := IncludeTrailingPathDelimiter(Scratch) + 'case.s';
  BinFile := IncludeTrailingPathDelimiter(Scratch) + 'case.bin';

  IR := GenIR(ASrc);
  Lst := TStringList.Create;
  try
    Lst.Text := IR;
    Lst.SaveToFile(IRFile);
  finally
    Lst.Free;
  end;

  { qbe }
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := QBE;
    Proc.Parameters.Add('-o');
    Proc.Parameters.Add(AsmFile);
    Proc.Parameters.Add(IRFile);
    Proc.Options := [poWaitOnExit];
    Proc.Execute;
    if Proc.ExitStatus <> 0 then
    begin
      Result := '<qbe-failed>';
      Exit;
    end;
  finally
    Proc.Free;
  end;

  { link }
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := 'cc';
    Proc.Parameters.Add('-o');
    Proc.Parameters.Add(BinFile);
    Proc.Parameters.Add(AsmFile);
    Proc.Parameters.Add(RTL);
    Proc.Options := [poWaitOnExit];
    Proc.Execute;
    if Proc.ExitStatus <> 0 then
    begin
      Result := '<link-failed>';
      Exit;
    end;
  finally
    Proc.Free;
  end;

  { run + capture stdout }
  Proc := TProcess.Create(nil);
  OutLst := TStringList.Create;
  try
    Proc.Executable := BinFile;
    Proc.Options := [poWaitOnExit, poUsePipes];
    Proc.Execute;
    OutLst.LoadFromStream(Proc.Output);
    Result := TrimRight(OutLst.Text);
  finally
    OutLst.Free;
    Proc.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{  Parser                                                              }
{ ------------------------------------------------------------------ }

procedure TPublishedRTTITests.TestParse_Published_Sets_IsPublished;
const
  Src =
    'program P;'                                         + LineEnding +
    'type'                                               + LineEnding +
    '  TFoo = class(TObject)'                            + LineEnding +
    '  published'                                        + LineEnding +
    '    procedure Bar;'                                 + LineEnding +
    '    procedure Baz;'                                 + LineEnding +
    '  end;'                                             + LineEnding +
    'procedure TFoo.Bar; begin end;'                     + LineEnding +
    'procedure TFoo.Baz; begin end;'                     + LineEnding +
    'begin end.';
var
  Prog: TProgram;
  TD:   TTypeDecl;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    TD := TTypeDecl(Prog.Block.TypeDecls.Items[0]);
    CD := TClassTypeDef(TD.Def);
    AssertEquals('two methods', 2, CD.Methods.Count);
    AssertTrue('Bar is published', TMethodDecl(CD.Methods.Items[0]).IsPublished);
    AssertTrue('Baz is published', TMethodDecl(CD.Methods.Items[1]).IsPublished);
  finally
    Prog.Free;
  end;
end;

procedure TPublishedRTTITests.TestParse_Public_Does_Not_Set_IsPublished;
const
  Src =
    'program P;'                                         + LineEnding +
    'type'                                               + LineEnding +
    '  TFoo = class(TObject)'                            + LineEnding +
    '  public'                                           + LineEnding +
    '    procedure Bar;'                                 + LineEnding +
    '  end;'                                             + LineEnding +
    'procedure TFoo.Bar; begin end;'                     + LineEnding +
    'begin end.';
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertFalse('Bar is not published',
      TMethodDecl(CD.Methods.Items[0]).IsPublished);
  finally
    Prog.Free;
  end;
end;

procedure TPublishedRTTITests.TestParse_PublishedThenPublic_Boundary;
const
  Src =
    'program P;'                                         + LineEnding +
    'type'                                               + LineEnding +
    '  TFoo = class(TObject)'                            + LineEnding +
    '  published'                                        + LineEnding +
    '    procedure InPub;'                               + LineEnding +
    '  public'                                           + LineEnding +
    '    procedure InPlain;'                             + LineEnding +
    '  end;'                                             + LineEnding +
    'procedure TFoo.InPub;   begin end;'                 + LineEnding +
    'procedure TFoo.InPlain; begin end;'                 + LineEnding +
    'begin end.';
var
  Prog: TProgram;
  CD:   TClassTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    CD := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls.Items[0]).Def);
    AssertTrue('InPub published',  TMethodDecl(CD.Methods.Items[0]).IsPublished);
    AssertFalse('InPlain not published',
      TMethodDecl(CD.Methods.Items[1]).IsPublished);
  finally
    Prog.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{  Codegen — typeinfo and methods table layout                         }
{ ------------------------------------------------------------------ }

procedure TPublishedRTTITests.TestCodegen_TypeInfo_HasFourSlots;
const
  Src =
    'program P;'                                         + LineEnding +
    'type TFoo = class(TObject) end;'                    + LineEnding +
    'begin end.';
var IR: string;
begin
  { Layout: parent, impllist, name, methods, totalsize, fieldcleanup, vtable.
    The first four slots remain unchanged from Step 11b; the trailing
    three were added in Step 11e to support runtime ClassCreate. }
  IR := GenIR(Src);
  AssertTrue('typeinfo emits seven l-slots, first four unchanged',
    Pos('$typeinfo_TFoo = { l $typeinfo_TObject, l 0, l $__cn_TFoo + 12, l 0' +
        ', l 8, l $_FieldCleanup_TFoo, l $vtable_TFoo }', IR) > 0);
end;

procedure TPublishedRTTITests.TestCodegen_NoPublishedMethods_MethodsSlotZero;
const
  Src =
    'program P;'                                         + LineEnding +
    'type'                                               + LineEnding +
    '  TFoo = class(TObject)'                            + LineEnding +
    '  public'                                           + LineEnding +
    '    procedure Bar;'                                 + LineEnding +
    '  end;'                                             + LineEnding +
    'procedure TFoo.Bar; begin end;'                     + LineEnding +
    'begin end.';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('typeinfo methods slot is 0 when no published methods',
    Pos('$typeinfo_TFoo = { l $typeinfo_TObject, l 0, l $__cn_TFoo + 12, l 0,', IR) > 0);
  AssertEquals('no methods table emitted', 0, Pos('$methods_TFoo', IR));
end;

procedure TPublishedRTTITests.TestCodegen_PublishedMethods_TableEmitted;
const
  Src =
    'program P;'                                         + LineEnding +
    'type'                                               + LineEnding +
    '  TFoo = class(TObject)'                            + LineEnding +
    '  published'                                        + LineEnding +
    '    procedure Bar;'                                 + LineEnding +
    '  end;'                                             + LineEnding +
    'procedure TFoo.Bar; begin end;'                     + LineEnding +
    'begin end.';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('methods table emitted', Pos('$methods_TFoo', IR) > 0);
  AssertTrue('typeinfo points at methods table',
    Pos(', l $methods_TFoo,', IR) > 0);
end;

procedure TPublishedRTTITests.TestCodegen_PublishedMethods_TableCount;
const
  Src =
    'program P;'                                         + LineEnding +
    'type'                                               + LineEnding +
    '  TFoo = class(TObject)'                            + LineEnding +
    '  published'                                        + LineEnding +
    '    procedure Bar;'                                 + LineEnding +
    '    procedure Baz;'                                 + LineEnding +
    '    procedure Qux;'                                 + LineEnding +
    '  end;'                                             + LineEnding +
    'procedure TFoo.Bar; begin end;'                     + LineEnding +
    'procedure TFoo.Baz; begin end;'                     + LineEnding +
    'procedure TFoo.Qux; begin end;'                     + LineEnding +
    'begin end.';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('methods table starts with count = 3',
    Pos('$methods_TFoo = { l 3,', IR) > 0);
end;

procedure TPublishedRTTITests.TestCodegen_PublishedMethods_NameAndAddrPairs;
const
  Src =
    'program P;'                                         + LineEnding +
    'type'                                               + LineEnding +
    '  TFoo = class(TObject)'                            + LineEnding +
    '  published'                                        + LineEnding +
    '    procedure Bar;'                                 + LineEnding +
    '  end;'                                             + LineEnding +
    'procedure TFoo.Bar; begin end;'                     + LineEnding +
    'begin end.';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('table includes name pointer for Bar',
    Pos('$__cn_Bar + 12, l $TFoo_Bar', IR) > 0);
end;

procedure TPublishedRTTITests.TestCodegen_MethodAddress_BuiltinCall;
const
  Src =
    'program P;'                                         + LineEnding +
    'type'                                               + LineEnding +
    '  TFoo = class(TObject)'                            + LineEnding +
    '  published'                                        + LineEnding +
    '    procedure Bar;'                                 + LineEnding +
    '  end;'                                             + LineEnding +
    'procedure TFoo.Bar; begin end;'                     + LineEnding +
    'var F: TFoo; P: Pointer;'                           + LineEnding +
    'begin'                                              + LineEnding +
    '  F := TFoo.Create;'                                + LineEnding +
    '  P := MethodAddress(F, ''Bar'');'                  + LineEnding +
    '  F.Free'                                           + LineEnding +
    'end.';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('emits call to $_MethodAddress',
    Pos('call $_MethodAddress(', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{  End-to-end                                                          }
{ ------------------------------------------------------------------ }

procedure TPublishedRTTITests.TestE2E_MethodAddress_Found;
const
  Src =
    'program P;'                                         + LineEnding +
    'type'                                               + LineEnding +
    '  TFoo = class(TObject)'                            + LineEnding +
    '  published'                                        + LineEnding +
    '    procedure Bar;'                                 + LineEnding +
    '  end;'                                             + LineEnding +
    'procedure TFoo.Bar; begin end;'                     + LineEnding +
    'var F: TFoo;'                                       + LineEnding +
    'begin'                                              + LineEnding +
    '  F := TFoo.Create;'                                + LineEnding +
    '  if MethodAddress(F, ''Bar'') = nil then'          + LineEnding +
    '    WriteLn(''nil'')'                               + LineEnding +
    '  else'                                             + LineEnding +
    '    WriteLn(''found'');'                            + LineEnding +
    '  F.Free'                                           + LineEnding +
    'end.';
begin
  AssertEquals('Bar is found in the published-method table',
    'found', CompileAndRun(Src));
end;

procedure TPublishedRTTITests.TestE2E_MethodAddress_NotFound;
const
  Src =
    'program P;'                                         + LineEnding +
    'type'                                               + LineEnding +
    '  TFoo = class(TObject)'                            + LineEnding +
    '  published'                                        + LineEnding +
    '    procedure Bar;'                                 + LineEnding +
    '  end;'                                             + LineEnding +
    'procedure TFoo.Bar; begin end;'                     + LineEnding +
    'var F: TFoo;'                                       + LineEnding +
    'begin'                                              + LineEnding +
    '  F := TFoo.Create;'                                + LineEnding +
    '  if MethodAddress(F, ''NoSuch'') = nil then'       + LineEnding +
    '    WriteLn(''nil'')'                               + LineEnding +
    '  else'                                             + LineEnding +
    '    WriteLn(''found'');'                            + LineEnding +
    '  F.Free'                                           + LineEnding +
    'end.';
begin
  AssertEquals('Unknown method name returns nil',
    'nil', CompileAndRun(Src));
end;

procedure TPublishedRTTITests.TestE2E_MethodAddress_WalksParent;
const
  Src =
    'program P;'                                         + LineEnding +
    'type'                                               + LineEnding +
    '  TBase = class(TObject)'                           + LineEnding +
    '  published'                                        + LineEnding +
    '    procedure FromBase;'                            + LineEnding +
    '  end;'                                             + LineEnding +
    '  TDerived = class(TBase)'                          + LineEnding +
    '  published'                                        + LineEnding +
    '    procedure FromDerived;'                         + LineEnding +
    '  end;'                                             + LineEnding +
    'procedure TBase.FromBase;       begin end;'         + LineEnding +
    'procedure TDerived.FromDerived; begin end;'         + LineEnding +
    'var D: TDerived;'                                   + LineEnding +
    'begin'                                              + LineEnding +
    '  D := TDerived.Create;'                            + LineEnding +
    '  if MethodAddress(D, ''FromBase'') = nil then'     + LineEnding +
    '    WriteLn(''base nil'')'                          + LineEnding +
    '  else'                                             + LineEnding +
    '    WriteLn(''base found'');'                       + LineEnding +
    '  if MethodAddress(D, ''FromDerived'') = nil then'  + LineEnding +
    '    WriteLn(''derived nil'')'                       + LineEnding +
    '  else'                                             + LineEnding +
    '    WriteLn(''derived found'');'                    + LineEnding +
    '  D.Free'                                           + LineEnding +
    'end.';
begin
  AssertEquals('inherited and own published methods both reachable',
    'base found' + LineEnding + 'derived found', CompileAndRun(Src));
end;

procedure TPublishedRTTITests.TestE2E_MethodAddress_DistinctMethodsHaveDistinctAddresses;
const
  Src =
    'program P;'                                         + LineEnding +
    'type'                                               + LineEnding +
    '  TFoo = class(TObject)'                            + LineEnding +
    '  published'                                        + LineEnding +
    '    procedure Bar;'                                 + LineEnding +
    '    procedure Baz;'                                 + LineEnding +
    '  end;'                                             + LineEnding +
    'procedure TFoo.Bar; begin end;'                     + LineEnding +
    'procedure TFoo.Baz; begin end;'                     + LineEnding +
    'var F: TFoo;'                                       + LineEnding +
    'begin'                                              + LineEnding +
    '  F := TFoo.Create;'                                + LineEnding +
    '  if MethodAddress(F, ''Bar'') = MethodAddress(F, ''Baz'') then' + LineEnding +
    '    WriteLn(''same'')'                              + LineEnding +
    '  else'                                             + LineEnding +
    '    WriteLn(''different'');'                        + LineEnding +
    '  F.Free'                                           + LineEnding +
    'end.';
begin
  AssertEquals('two distinct methods have distinct code pointers',
    'different', CompileAndRun(Src));
end;

initialization
  RegisterTest(TPublishedRTTITests);
end.
