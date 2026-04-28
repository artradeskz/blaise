{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

unit cp.test.selfhosting;

{$mode objfpc}{$H+}

{ Tests for the two remaining self-hosting gaps:
    1. Multiple type/var sections in a single block
    2. File I/O and CLI builtins: ParamStr, ParamCount, ReadFile, WriteFile,
       FileExists, GetEnvVar, Exec, Halt }

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TSelfHostingTests = class(TTestCase)
  private
    function GenIR(const ASrc: string): string;
    procedure SemanticOK(const ASrc: string);
    procedure ParseOK(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Multi-section type/var block (Gap 1)                                }
    { ------------------------------------------------------------------ }
    procedure TestParse_MultiTypeSection_TwoTypeBlocks;
    procedure TestParse_MultiTypeSection_TypeVarTypeVar;
    procedure TestParse_MultiTypeSection_VarThenType;
    procedure TestSemantic_MultiTypeSection_TwoClasses_OK;
    procedure TestCodegen_MultiTypeSection_BothClassesEmitted;

    { ------------------------------------------------------------------ }
    { ParamCount / ParamStr (Gap 2 — CLI args)                           }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ParamCount_ReturnsInteger;
    procedure TestSemantic_ParamStr_ReturnsString;
    procedure TestCodegen_ParamCount_CallsRTL;
    procedure TestCodegen_ParamStr_CallsRTL;

    { ------------------------------------------------------------------ }
    { ReadFile / WriteFile / FileExists (Gap 2 — file I/O)               }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ReadFile_ReturnsString;
    procedure TestSemantic_WriteFile_OK;
    procedure TestSemantic_FileExists_ReturnsBoolean;
    procedure TestCodegen_ReadFile_CallsRTL;
    procedure TestCodegen_WriteFile_CallsRTL;
    procedure TestCodegen_FileExists_CallsRTL;

    { ------------------------------------------------------------------ }
    { GetEnvVar / Exec / Halt (Gap 2 — environment and process)          }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_GetEnvVar_ReturnsString;
    procedure TestSemantic_Exec_ReturnsInteger;
    procedure TestSemantic_Halt_OK;
    procedure TestCodegen_GetEnvVar_CallsRTL;
    procedure TestSemantic_GetEnvironmentVariable_ReturnsString;
    procedure TestCodegen_GetEnvironmentVariable_CallsRTL;
    procedure TestCodegen_Exec_CallsRTL;
    procedure TestCodegen_Halt_CallsRTL;

    { ------------------------------------------------------------------ }
    { Main emits argc/argv (required for ParamStr to work at runtime)    }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_Main_HasArgcArgv;
    procedure TestCodegen_Main_CallsSetArgs;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Source constants                                                     }
{ ------------------------------------------------------------------ }

const
  { Gap 1: multiple type sections }
  SrcTwoTypeBlocks =
    'program P;'                          + LineEnding +
    'type'                                + LineEnding +
    '  TA = class'                        + LineEnding +
    '    FX: Integer;'                    + LineEnding +
    '  end;'                              + LineEnding +
    'type'                                + LineEnding +
    '  TB = class'                        + LineEnding +
    '    FY: Integer;'                    + LineEnding +
    '  end;'                              + LineEnding +
    'begin'                               + LineEnding +
    'end.';

  SrcTypeVarTypeVar =
    'program P;'                          + LineEnding +
    'type'                                + LineEnding +
    '  TA = class'                        + LineEnding +
    '    FX: Integer;'                    + LineEnding +
    '  end;'                              + LineEnding +
    'var'                                 + LineEnding +
    '  A: TA;'                            + LineEnding +
    'type'                                + LineEnding +
    '  TB = class'                        + LineEnding +
    '    FY: Integer;'                    + LineEnding +
    '  end;'                              + LineEnding +
    'var'                                 + LineEnding +
    '  B: TB;'                            + LineEnding +
    'begin'                               + LineEnding +
    'end.';

  SrcVarThenType =
    'program P;'                          + LineEnding +
    'var'                                 + LineEnding +
    '  N: Integer;'                       + LineEnding +
    'type'                                + LineEnding +
    '  TA = class'                        + LineEnding +
    '    FX: Integer;'                    + LineEnding +
    '  end;'                              + LineEnding +
    'begin'                               + LineEnding +
    'end.';

  SrcTwoClassesBothUsed =
    'program P;'                          + LineEnding +
    'type'                                + LineEnding +
    '  TA = class'                        + LineEnding +
    '    FX: Integer;'                    + LineEnding +
    '  end;'                              + LineEnding +
    'type'                                + LineEnding +
    '  TB = class'                        + LineEnding +
    '    FY: Integer;'                    + LineEnding +
    '  end;'                              + LineEnding +
    'var'                                 + LineEnding +
    '  A: TA;'                            + LineEnding +
    '  B: TB;'                            + LineEnding +
    'begin'                               + LineEnding +
    '  A := TA.Create;'                   + LineEnding +
    '  B := TB.Create'                    + LineEnding +
    'end.';

  { Gap 2: CLI args }
  SrcParamCount =
    'program P;'                          + LineEnding +
    'var N: Integer;'                     + LineEnding +
    'begin'                               + LineEnding +
    '  N := ParamCount'                   + LineEnding +
    'end.';

  SrcParamStr =
    'program P;'                          + LineEnding +
    'var S: string;'                      + LineEnding +
    'begin'                               + LineEnding +
    '  S := ParamStr(0)'                  + LineEnding +
    'end.';

  { Gap 2: file I/O }
  SrcReadFile =
    'program P;'                          + LineEnding +
    'var S: string;'                      + LineEnding +
    'begin'                               + LineEnding +
    '  S := ReadFile(''test.txt'')'       + LineEnding +
    'end.';

  SrcWriteFile =
    'program P;'                          + LineEnding +
    'begin'                               + LineEnding +
    '  WriteFile(''out.txt'', ''hello'')' + LineEnding +
    'end.';

  SrcFileExists =
    'program P;'                          + LineEnding +
    'var B: Boolean;'                     + LineEnding +
    'begin'                               + LineEnding +
    '  B := FileExists(''test.txt'')'     + LineEnding +
    'end.';

  { Gap 2: environment and process }
  SrcGetEnvVar =
    'program P;'                          + LineEnding +
    'var S: string;'                      + LineEnding +
    'begin'                               + LineEnding +
    '  S := GetEnvVar(''PATH'')'          + LineEnding +
    'end.';

  SrcGetEnvironmentVariable =
    'program P;'                          + LineEnding +
    'var S: string;'                      + LineEnding +
    'begin'                               + LineEnding +
    '  S := GetEnvironmentVariable(''PATH'')' + LineEnding +
    'end.';

  SrcExec =
    'program P;'                          + LineEnding +
    'var N: Integer;'                     + LineEnding +
    'begin'                               + LineEnding +
    '  N := Exec(''echo hello'')'         + LineEnding +
    'end.';

  SrcHalt =
    'program P;'                          + LineEnding +
    'begin'                               + LineEnding +
    '  Halt(0)'                           + LineEnding +
    'end.';

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

function TSelfHostingTests.GenIR(const ASrc: string): string;
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  CG:   TCodeGenQBE;
  Prog: TProgram;
begin
  Lex  := TLexer.Create(ASrc);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse;
  Par.Free;
  Lex.Free;
  SA   := TSemanticAnalyser.Create;
  SA.Analyse(Prog);
  SA.Free;
  CG   := TCodeGenQBE.Create;
  CG.Generate(Prog);
  Result := CG.GetOutput;
  CG.Free;
  Prog.Free;
end;

procedure TSelfHostingTests.SemanticOK(const ASrc: string);
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  Prog: TProgram;
begin
  Lex  := TLexer.Create(ASrc);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse;
  Par.Free;
  Lex.Free;
  SA   := TSemanticAnalyser.Create;
  try
    SA.Analyse(Prog);
  finally
    SA.Free;
    Prog.Free;
  end;
end;

procedure TSelfHostingTests.ParseOK(const ASrc: string);
var
  Lex:  TLexer;
  Par:  TParser;
  Prog: TProgram;
begin
  Lex  := TLexer.Create(ASrc);
  Par  := TParser.Create(Lex);
  try
    Prog := Par.Parse;
    Prog.Free;
  finally
    Par.Free;
    Lex.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Gap 1: multiple type/var sections                                    }
{ ------------------------------------------------------------------ }

procedure TSelfHostingTests.TestParse_MultiTypeSection_TwoTypeBlocks;
begin
  ParseOK(SrcTwoTypeBlocks);
end;

procedure TSelfHostingTests.TestParse_MultiTypeSection_TypeVarTypeVar;
begin
  ParseOK(SrcTypeVarTypeVar);
end;

procedure TSelfHostingTests.TestParse_MultiTypeSection_VarThenType;
begin
  ParseOK(SrcVarThenType);
end;

procedure TSelfHostingTests.TestSemantic_MultiTypeSection_TwoClasses_OK;
begin
  SemanticOK(SrcTwoClassesBothUsed);
end;

procedure TSelfHostingTests.TestCodegen_MultiTypeSection_BothClassesEmitted;
var
  IR: string;
begin
  IR := GenIR(SrcTwoClassesBothUsed);
  { Both class type descriptors / cleanup stubs must be emitted }
  AssertTrue('TA typeinfo emitted', Pos('typeinfo_TA', IR) > 0);
  AssertTrue('TB typeinfo emitted', Pos('typeinfo_TB', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Gap 2: CLI args                                                      }
{ ------------------------------------------------------------------ }

procedure TSelfHostingTests.TestSemantic_ParamCount_ReturnsInteger;
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  Prog: TProgram;
  Ass:  TAssignment;
begin
  Lex  := TLexer.Create(SrcParamCount);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse;
  Par.Free;
  Lex.Free;
  SA   := TSemanticAnalyser.Create;
  SA.Analyse(Prog);
  SA.Free;
  Ass := TAssignment(Prog.Block.Stmts[0]);
  AssertEquals('ParamCount returns Integer',
    Ord(tyInteger), Ord(Ass.Expr.ResolvedType.Kind));
  Prog.Free;
end;

procedure TSelfHostingTests.TestSemantic_ParamStr_ReturnsString;
begin
  SemanticOK(SrcParamStr);
end;

procedure TSelfHostingTests.TestCodegen_ParamCount_CallsRTL;
var
  IR: string;
begin
  IR := GenIR(SrcParamCount);
  AssertTrue('ParamCount calls _ParamCount',
    Pos('_ParamCount', IR) > 0);
end;

procedure TSelfHostingTests.TestCodegen_ParamStr_CallsRTL;
var
  IR: string;
begin
  IR := GenIR(SrcParamStr);
  AssertTrue('ParamStr calls _ParamStr',
    Pos('_ParamStr', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Gap 2: file I/O                                                      }
{ ------------------------------------------------------------------ }

procedure TSelfHostingTests.TestSemantic_ReadFile_ReturnsString;
begin
  SemanticOK(SrcReadFile);
end;

procedure TSelfHostingTests.TestSemantic_WriteFile_OK;
begin
  SemanticOK(SrcWriteFile);
end;

procedure TSelfHostingTests.TestSemantic_FileExists_ReturnsBoolean;
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  Prog: TProgram;
  Ass:  TAssignment;
begin
  Lex  := TLexer.Create(SrcFileExists);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse;
  Par.Free;
  Lex.Free;
  SA   := TSemanticAnalyser.Create;
  SA.Analyse(Prog);
  SA.Free;
  Ass := TAssignment(Prog.Block.Stmts[0]);
  AssertEquals('FileExists returns Boolean',
    Ord(tyBoolean), Ord(Ass.Expr.ResolvedType.Kind));
  Prog.Free;
end;

procedure TSelfHostingTests.TestCodegen_ReadFile_CallsRTL;
var
  IR: string;
begin
  IR := GenIR(SrcReadFile);
  AssertTrue('ReadFile calls _ReadFile', Pos('_ReadFile', IR) > 0);
end;

procedure TSelfHostingTests.TestCodegen_WriteFile_CallsRTL;
var
  IR: string;
begin
  IR := GenIR(SrcWriteFile);
  AssertTrue('WriteFile calls _WriteFile', Pos('_WriteFile', IR) > 0);
end;

procedure TSelfHostingTests.TestCodegen_FileExists_CallsRTL;
var
  IR: string;
begin
  IR := GenIR(SrcFileExists);
  AssertTrue('FileExists calls _FileExists', Pos('_FileExists', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Gap 2: environment and process                                        }
{ ------------------------------------------------------------------ }

procedure TSelfHostingTests.TestSemantic_GetEnvVar_ReturnsString;
begin
  SemanticOK(SrcGetEnvVar);
end;

procedure TSelfHostingTests.TestSemantic_Exec_ReturnsInteger;
begin
  SemanticOK(SrcExec);
end;

procedure TSelfHostingTests.TestSemantic_Halt_OK;
begin
  SemanticOK(SrcHalt);
end;

procedure TSelfHostingTests.TestCodegen_GetEnvVar_CallsRTL;
var
  IR: string;
begin
  IR := GenIR(SrcGetEnvVar);
  AssertTrue('GetEnvVar calls _GetEnvVar', Pos('_GetEnvVar', IR) > 0);
end;

procedure TSelfHostingTests.TestSemantic_GetEnvironmentVariable_ReturnsString;
begin
  SemanticOK(SrcGetEnvironmentVariable);
end;

procedure TSelfHostingTests.TestCodegen_GetEnvironmentVariable_CallsRTL;
var
  IR: string;
begin
  IR := GenIR(SrcGetEnvironmentVariable);
  AssertTrue('GetEnvironmentVariable calls _GetEnvVar', Pos('_GetEnvVar', IR) > 0);
end;

procedure TSelfHostingTests.TestCodegen_Exec_CallsRTL;
var
  IR: string;
begin
  IR := GenIR(SrcExec);
  AssertTrue('Exec calls _Exec', Pos('_Exec', IR) > 0);
end;

procedure TSelfHostingTests.TestCodegen_Halt_CallsRTL;
var
  IR: string;
begin
  IR := GenIR(SrcHalt);
  AssertTrue('Halt calls $exit or _Halt', Pos('exit', IR) > 0);
end;

procedure TSelfHostingTests.TestCodegen_Main_HasArgcArgv;
var
  IR: string;
begin
  IR := GenIR(SrcHalt);
  AssertTrue('$main declares argc param', Pos('%argc', IR) > 0);
  AssertTrue('$main declares argv param', Pos('%argv', IR) > 0);
end;

procedure TSelfHostingTests.TestCodegen_Main_CallsSetArgs;
var
  IR: string;
begin
  IR := GenIR(SrcHalt);
  AssertTrue('$main calls _SetArgs at startup', Pos('_SetArgs', IR) > 0);
end;

initialization
  RegisterTest(TSelfHostingTests);

end.
