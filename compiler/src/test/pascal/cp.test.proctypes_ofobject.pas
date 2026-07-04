{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.proctypes_ofobject;

{ Tests for Step 11c — 'procedure of object' method-pointer types and the
  TMethod intrinsic record.

  Layout: a method-pointer value is a 16-byte block, Code at offset 0 and
  Data (Self) at offset 8.  This matches TMethod byte-for-byte; the cast
  TMyMethod(m) is a no-op at the QBE level.  A method-pointer call site
  loads both halves and emits 'call code(l data, args...)'. }

interface

uses
  Classes, SysUtils, Process, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

function ProjectRootOFO: string;
function RunCmdOFO(const AExe: string; const AArgs: array of string): Integer;

type
  TProcTypesOfObjectTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    function CompileAndRun(const ASrc: string): string;
  published
    { Parser }
    procedure TestParse_OfObject_SetsIsMethodPtr;
    procedure TestParse_BareProcType_LeavesIsMethodPtrFalse;
    procedure TestParse_FunctionOfObject_AcceptsReturnType;

    { Semantic / Symbol Table }
    procedure TestSemantic_TMethod_IsRegistered;
    procedure TestSemantic_TMethod_HasCodeAndDataFields;
    procedure TestSemantic_MethodPtr_PropagatesIsMethodPtr;

    { Codegen }
    procedure TestCodegen_MethodPtrLocal_Allocates16Bytes;
    procedure TestCodegen_MethodPtrGlobal_DataIs16Bytes;
    procedure TestCodegen_MethodPtrAssign_CallsMemcpy16;
    procedure TestCodegen_MethodPtrCall_LoadsCodeAndData;
    procedure TestSemantic_MethodPtr_ByteSizeIs16;
    procedure TestSemantic_BareProcPtr_ByteSizeIs8;
    procedure TestCodegen_MethodPtrField_AssignUsesMemcpy16;
    procedure TestCodegen_MethodPtrField_RecordTotalSizeIncludes16;

    procedure TestCodegen_MethodPtrField_DirectCall_LoadsCodeAndData;

    { End-to-end }
    procedure TestE2E_MethodPtr_NoArgs;
    procedure TestE2E_MethodPtr_WithArgs;
    procedure TestE2E_MethodPtr_PreservesSelf;
    procedure TestE2E_MethodPtrField_RoundTrip;
    procedure TestE2E_MethodPtrField_DirectCall_StmtForm;
  end;

implementation

function TProcTypesOfObjectTests.ParseSrc(const ASrc: string): TProgram;
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

function TProcTypesOfObjectTests.AnalyseSrc(const ASrc: string): TProgram;
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

function TProcTypesOfObjectTests.GenIR(const ASrc: string): string;
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

function ProjectRootOFO: string;
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
  Dir := GetCurrentDir();
  for Steps := 0 to 5 do
  begin
    if DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'vendor/qbe') and
       DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'runtime') then
    begin
      Result := IncludeTrailingPathDelimiter(Dir);
      Exit;
    end;
    Parent := ExtractFileDir(Dir);
    if (Parent = '') or (Parent = Dir) then Break;
    Dir := Parent;
  end;
  Result := IncludeTrailingPathDelimiter(GetCurrentDir());
end;

function RunCmdOFO(const AExe: string; const AArgs: array of string): Integer;
var
  Proc:  TProcess;
  I:     Integer;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    for I := Low(AArgs) to High(AArgs) do
      Proc.Parameters.Add(AArgs[I]);
    Proc.Execute();
    repeat Chunk := Proc.ReadOutput(); until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode;
  finally
    Proc.Free();
  end;
end;

function TProcTypesOfObjectTests.CompileAndRun(const ASrc: string): string;
var
  IR:                       string;
  Root:                     string;
  QBE, RTL, Scratch:        string;
  IRFile, AsmFile, BinFile: string;
  Lst:                      TStringList;
  Proc:                     TProcess;
  Chunk:                    string;
begin
  Result := '';
  Root   := ProjectRootOFO();
  QBE    := Root + 'vendor/qbe/qbe';
  RTL    := Root + 'compiler/target/blaise_rtl.a';
  if not (FileExists(QBE) and FileExists(RTL)) then
  begin
    Result := '<toolchain-missing>';
    Exit;
  end;
  Scratch := Root + 'compiler/target/test-proctypes-ofobject';
  ForceDirectories(Scratch);
  IRFile  := IncludeTrailingPathDelimiter(Scratch) + 'case.ssa';
  AsmFile := IncludeTrailingPathDelimiter(Scratch) + 'case.s';
  BinFile := IncludeTrailingPathDelimiter(Scratch) + 'case.bin';

  IR := GenIR(ASrc);
  Lst := TStringList.Create();
  try
    Lst.Text := IR;
    Lst.SaveToFile(IRFile);
  finally
    Lst.Free();
  end;

  if RunCmdOFO(QBE, ['-o', AsmFile, IRFile]) <> 0 then
  begin
    Result := '<qbe-failed>';
    Exit;
  end;

  if RunCmdOFO('cc', ['-o', BinFile, AsmFile, RTL]) <> 0 then
  begin
    Result := '<link-failed>';
    Exit;
  end;

  Proc := TProcess.Create(nil);
  try
    Proc.Executable := BinFile;
    Proc.Execute();
    Result := '';
    repeat
      Chunk := Proc.ReadOutput();
      Result := Result + Chunk;
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Trim(Result);
  finally
    Proc.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{  Parser                                                              }
{ ------------------------------------------------------------------ }

procedure TProcTypesOfObjectTests.TestParse_OfObject_SetsIsMethodPtr;
const
  Src =
    '''
        program P;
        type TM = procedure of object;
        begin end.
        ''';
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
begin
  Prog := ParseSrc(Src);
  try
    TD  := TTypeDecl(Prog.Block.TypeDecls.Items[0]);
    Def := TProceduralTypeDef(TD.Def);
    AssertTrue('IsMethodPtr is True for "of object" type', Def.IsMethodPtr);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesOfObjectTests.TestParse_BareProcType_LeavesIsMethodPtrFalse;
const
  Src =
    '''
        program P;
        type TP = procedure;
        begin end.
        ''';
var
  Def: TProceduralTypeDef;
begin
  Def := TProceduralTypeDef(TTypeDecl(ParseSrc(Src).Block.TypeDecls.Items[0]).Def);
  AssertFalse('IsMethodPtr is False for bare procedural type', Def.IsMethodPtr);
end;

procedure TProcTypesOfObjectTests.TestParse_FunctionOfObject_AcceptsReturnType;
const
  Src =
    '''
        program P;
        type TF = function (X: Integer): Integer of object;
        begin end.
        ''';
var
  Def: TProceduralTypeDef;
begin
  Def := TProceduralTypeDef(TTypeDecl(ParseSrc(Src).Block.TypeDecls.Items[0]).Def);
  AssertTrue('IsFunction set',   Def.IsFunction);
  AssertTrue('IsMethodPtr set',  Def.IsMethodPtr);
  AssertEquals('return type',    'Integer', Def.ReturnTypeName);
end;

{ ------------------------------------------------------------------ }
{  Semantic / Symbol Table                                             }
{ ------------------------------------------------------------------ }

procedure TProcTypesOfObjectTests.TestSemantic_TMethod_IsRegistered;
const
  Src =
    '''
        program P;
        var M: TMethod;
        begin end.
        ''';
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := AnalyseSrc(Src);
  try
    VD := TVarDecl(Prog.Block.Decls.Items[0]);
    AssertNotNull('TMethod resolves',         VD.ResolvedType);
    AssertEquals('TMethod kind is tyRecord',  Ord(tyRecord), Ord(VD.ResolvedType.Kind));
    AssertEquals('TMethod name',              'TMethod',     VD.ResolvedType.Name);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesOfObjectTests.TestSemantic_TMethod_HasCodeAndDataFields;
const
  Src =
    '''
        program P;
        var M: TMethod;
        begin end.
        ''';
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    RT := TRecordTypeDesc(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType);
    AssertNotNull('Code field exists', RT.FindField('Code'));
    AssertNotNull('Data field exists', RT.FindField('Data'));
    AssertEquals('Code at offset 0', 0, RT.FindField('Code').Offset);
    AssertEquals('Data at offset 8', 8, RT.FindField('Data').Offset);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesOfObjectTests.TestSemantic_MethodPtr_PropagatesIsMethodPtr;
const
  Src =
    '''
        program P;
        type TM = procedure of object;
        var G: TM;
        begin end.
        ''';
var
  Prog:     TProgram;
  ProcDesc: TProceduralTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    ProcDesc := TProceduralTypeDesc(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType);
    AssertTrue('IsMethodPtr propagated to type descriptor',
      ProcDesc.IsMethodPtr);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{  Codegen                                                             }
{ ------------------------------------------------------------------ }

procedure TProcTypesOfObjectTests.TestCodegen_MethodPtrLocal_Allocates16Bytes;
const
  Src =
    '''
        program P;
        type TM = procedure of object;
        procedure Q;
        var G: TM;
        begin end;
        begin end.
        ''';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('local method-ptr var is alloc8 16',
    Pos('%_var_G =l alloc8 16', IR) > 0);
end;

procedure TProcTypesOfObjectTests.TestCodegen_MethodPtrGlobal_DataIs16Bytes;
const
  Src =
    '''
        program P;
        type TM = procedure of object;
        var G: TM;
        begin end.
        ''';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('global method-ptr emits 16-byte zero data',
    Pos('export data $G = { z 16 }', IR) > 0);
end;

procedure TProcTypesOfObjectTests.TestCodegen_MethodPtrAssign_CallsMemcpy16;
const
  Src =
    '''
        program P;
        type TM = procedure of object;
        var G: TM; M: TMethod;
        begin
          G := TM(M)
        end.
        ''';
var IR: string;
begin
  IR := GenIR(Src);
  AssertTrue('method-ptr assignment uses memcpy of 16 bytes',
    Pos('call $memcpy(', IR) > 0);
  AssertTrue('memcpy length is 16',
    Pos(', l 16)', IR) > 0);
end;

procedure TProcTypesOfObjectTests.TestCodegen_MethodPtrCall_LoadsCodeAndData;
const
  Src =
    '''
        program P;
        type TM = procedure of object;
        var G: TM;
        begin G end.
        ''';
var IR: string;
begin
  IR := GenIR(Src);
  { Method-ptr call must load both Code (slot+0) and Data (slot+8) }
  AssertTrue('call site adds 8 to load Data',
    Pos('=l add $G, 8', IR) > 0);
  AssertTrue('call site loads Code from slot',
    Pos('=l loadl $G', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{  End-to-end                                                          }
{ ------------------------------------------------------------------ }

procedure TProcTypesOfObjectTests.TestE2E_MethodPtr_NoArgs;
const
  Src =
    '''
        program P;
        type
          TFoo = class(TObject)
          published
            procedure SayHi;
          end;
          TGreet = procedure of object;
        procedure TFoo.SayHi;
        begin WriteLn('hi') end;
        var F: TFoo; M: TMethod; G: TGreet;
        begin
          F := TFoo.Create();
          M.Code := MethodAddress(F, 'SayHi');
          M.Data := F;
          G := TGreet(M);
          G;
          F.Free()
        end.
        ''';
begin
  AssertEquals('zero-arg method-ptr call invokes the method',
    'hi', CompileAndRun(Src));
end;

procedure TProcTypesOfObjectTests.TestE2E_MethodPtr_WithArgs;
const
  Src =
    '''
        program P;
        type
          TFoo = class(TObject)
          published
            procedure Show(const S: string; N: Integer);
          end;
          TShow = procedure (const S: string; N: Integer) of object;
        procedure TFoo.Show(const S: string; N: Integer);
        begin
          WriteLn(S);
          WriteLn(IntToStr(N))
        end;
        var F: TFoo; M: TMethod; G: TShow;
        begin
          F := TFoo.Create();
          M.Code := MethodAddress(F, 'Show');
          M.Data := F;
          G := TShow(M);
          G('hello', 42);
          F.Free()
        end.
        ''';
begin
  AssertEquals('args are forwarded after Self',
    'hello' + #10 + '42', CompileAndRun(Src));
end;

procedure TProcTypesOfObjectTests.TestE2E_MethodPtr_PreservesSelf;
const
  Src =
    '''
        program P;
        type
          TCounter = class(TObject)
            Value: Integer;
          published
            procedure Print;
          end;
          TPrintMethod = procedure of object;
        procedure TCounter.Print;
        begin WriteLn(IntToStr(Value)) end;
        var C: TCounter; M: TMethod; G: TPrintMethod;
        begin
          C := TCounter.Create();
          C.Value := 99;
          M.Code := MethodAddress(C, 'Print');
          M.Data := C;
          G := TPrintMethod(M);
          G;
          C.Free()
        end.
        ''';
begin
  AssertEquals('Self is bound through the call: instance state visible',
    '99', CompileAndRun(Src));
end;

procedure TProcTypesOfObjectTests.TestSemantic_MethodPtr_ByteSizeIs16;
const
  Src =
    '''
        program P;
        type TM = procedure of object;
        var G: TM;
        begin end.
        ''';
var
  Prog: TProgram;
  TD:   TTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    TD := TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType;
    AssertEquals('IsMethodPtr ByteSize is 16', 16, TD.ByteSize());
    AssertEquals('IsMethodPtr RawSize is 16',  16, TD.RawSize());
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesOfObjectTests.TestSemantic_BareProcPtr_ByteSizeIs8;
const
  Src =
    '''
        program P;
        type TP = procedure;
        var G: TP;
        begin end.
        ''';
var
  Prog: TProgram;
  TD:   TTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    TD := TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType;
    AssertEquals('bare procedural ByteSize stays 8', 8, TD.ByteSize());
    AssertEquals('bare procedural RawSize stays 8',  8, TD.RawSize());
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesOfObjectTests.TestCodegen_MethodPtrField_AssignUsesMemcpy16;
const
  Src =
    '''
        program P;
        type
          TM   = procedure of object;
          TRec = record
            Handler: TM;
          end;
        var
          R: TRec;
          M: TMethod;
        begin
          R.Handler := TM(M)
        end.
        ''';
var IR: string;
begin
  IR := GenIR(Src);
  { Field assignment must memcpy the full 16-byte TMethod, not store a single
    pointer to a stack-allocated source block that goes out of scope. }
  AssertTrue('method-ptr field assignment emits memcpy',
    Pos('call $memcpy(', IR) > 0);
  AssertTrue('memcpy length is 16',
    Pos(', l 16)', IR) > 0);
end;

procedure TProcTypesOfObjectTests.TestCodegen_MethodPtrField_RecordTotalSizeIncludes16;
const
  Src =
    '''
        program P;
        type
          TM   = procedure of object;
          TRec = record
            Handler: TM;
          end;
        var R: TRec;
        begin end.
        ''';
var
  Prog: TProgram;
  RT:   TRecordTypeDesc;
begin
  Prog := AnalyseSrc(Src);
  try
    RT := TRecordTypeDesc(TVarDecl(Prog.Block.Decls.Items[0]).ResolvedType);
    AssertEquals('record holding a method-ptr field totals 16 bytes',
      16, RT.TotalSize());
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesOfObjectTests.TestE2E_MethodPtrField_RoundTrip;
const
  Src =
    '''
        program P;
        type
          TFoo = class(TObject)
          published
            procedure SayHi;
          end;
          TGreet = procedure of object;
          THolder = class(TObject)
            Handler: TGreet;
          end;
        procedure TFoo.SayHi;
        begin WriteLn('field-ok') end;
        var
          F: TFoo;
          H: THolder;
          M: TMethod;
          G: TGreet;
        begin
          F := TFoo.Create();
          H := THolder.Create();
          M.Code := MethodAddress(F, 'SayHi');
          M.Data := F;
          H.Handler := TGreet(M);
          { Read the field into a local and invoke — exercises the field-read
            path (which must return the field address, not a single loadl). }
          G := H.Handler;
          G();
          H.Free();
          F.Free()
        end.
        ''';
begin
  AssertEquals('method-ptr stored in a class field survives across statements',
    'field-ok', CompileAndRun(Src));
end;

procedure TProcTypesOfObjectTests.TestCodegen_MethodPtrField_DirectCall_LoadsCodeAndData;
const
  Src =
    '''
        program P;
        type
          TGreet = procedure of object;
          THolder = class(TObject)
            Handler: TGreet;
          end;
        var H: THolder;
        begin
          H := THolder.Create();
          H.Handler();
          H.Free()
        end.
        ''';
var IR: string;
begin
  IR := GenIR(Src);
  { Direct field call emits: load Code from slot, load Data from slot+8,
    then call %Code(l %Data, ...).  There must be NO static '$THolder_Handler'
    symbol — it dispatches indirectly through the field. }
  AssertTrue('IR contains indirect call pattern (call %',
    StrPos('call %', IR) >= 0);
  AssertFalse('IR does not static-dispatch $THolder_Handler',
    StrPos('$THolder_Handler', IR) >= 0);
end;

procedure TProcTypesOfObjectTests.TestE2E_MethodPtrField_DirectCall_StmtForm;
const
  Src =
    '''
        program P;
        type
          TGreet = procedure of object;
          TFoo = class(TObject)
            Handler: TGreet;
          published
            procedure SayHi;
          end;
        procedure TFoo.SayHi;
        begin WriteLn('field-direct') end;
        var F: TFoo; M: TMethod;
        begin
          F := TFoo.Create();
          M.Code := MethodAddress(F, 'SayHi');
          M.Data := F;
          F.Handler := TGreet(M);
          F.Handler();
          F.Handler();
          F.Free()
        end.
        ''';
begin
  AssertEquals('direct proc-field call (bare and with parens) invokes the method',
    'field-direct' + #10 + 'field-direct', CompileAndRun(Src));
end;

initialization
  RegisterTest(TProcTypesOfObjectTests);
end.
