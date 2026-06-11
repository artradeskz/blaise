{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.tlist;

{ Tests for TList<T> generic dynamic list: type substitution with ^T fields,
  SizeOf built-in, nil/Pointer compatibility with typed pointers, and
  end-to-end Add/Get/Count codegen. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

type
  TTListTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
  published
    { ------------------------------------------------------------------ }
    { Parser — ^T field, SizeOf                                           }
    { ------------------------------------------------------------------ }
    procedure TestParse_CaretT_FieldType;
    procedure TestParse_SizeOf_ParsedAsFuncCall;

    { ------------------------------------------------------------------ }
    { Semantic — SizeOf, nil/Pointer compat, ^T substitution             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_SizeOf_Integer;
    procedure TestSemantic_SizeOf_Pointer;
    procedure TestSemantic_NilAssign_ToTypedPointer;
    procedure TestSemantic_Pointer_AssignToTypedPointer;
    procedure TestSemantic_TList_Instantiation;

    { ------------------------------------------------------------------ }
    { Codegen — SizeOf literal, full TList<Integer> add/get              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_SizeOf_Integer_EmitsFour;
    procedure TestCodegen_SizeOf_Int64_EmitsEight;
    procedure TestCodegen_TList_Compiles;
    procedure TestCodegen_TList_AddGet_IR;
    procedure TestCodegen_TList_Grow_EmitsRealloc;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Blaise source constants                                              }
{ ------------------------------------------------------------------ }

const
  SrcSizeOfInteger =
    '''
        program Prg;
        var N: Integer;
        begin
          N := SizeOf(Integer)
        end.
        ''';

  SrcSizeOfInt64 =
    '''
        program Prg;
        var N: Integer;
        begin
          N := SizeOf(Int64)
        end.
        ''';

  SrcNilToTypedPtr =
    '''
        program Prg;
        var P: ^Integer;
        begin
          P := nil
        end.
        ''';

  SrcPointerToTypedPtr =
    '''
        program Prg;
        var
          P: ^Integer;
          Q: Pointer;
        begin
          Q := GetMem(4);
          P := Q
        end.
        ''';

  SrcTListType =
    '''
        program Prg;
        type
          TList<T> = class
            FData: ^T;
            FCount: Integer;
            FCapacity: Integer;
            procedure Add(Value: T);
            var
              Dest: ^T;
            begin
              Dest := Self.FData + Self.FCount * SizeOf(T);
              Dest^ := Value;
              Self.FCount := Self.FCount + 1
            end;
            function Get(AIndex: Integer): T;
            var
              Src: ^T;
            begin
              Src := Self.FData + AIndex * SizeOf(T);
              Result := Src^
            end;
            property Count: Integer read FCount;
          end;
        var
          L: TList<Integer>;
        begin
          L := TList<Integer>.Create();
          L.Add(10);
          L.Add(20)
        end.
        ''';

  SrcTListGetResult =
    '''
        program Prg;
        type
          TList<T> = class
            FData: ^T;
            FCount: Integer;
            FCapacity: Integer;
            procedure Add(Value: T);
            var
              Dest: ^T;
            begin
              Dest := Self.FData + Self.FCount * SizeOf(T);
              Dest^ := Value;
              Self.FCount := Self.FCount + 1
            end;
            function Get(AIndex: Integer): T;
            var
              Src: ^T;
            begin
              Src := Self.FData + AIndex * SizeOf(T);
              Result := Src^
            end;
            property Count: Integer read FCount;
          end;
        var
          L: TList<Integer>;
          V: Integer;
        begin
          L := TList<Integer>.Create();
          L.Add(42);
          V := L.Get(0)
        end.
        ''';

  SrcTListFull =
    '''
        program Prg;
        type
          TList<T> = class
            FData: ^T;
            FCount: Integer;
            FCapacity: Integer;
            procedure Grow;
            var
              NewCap: Integer;
            begin
              if Self.FCapacity = 0 then
                NewCap := 4
              else
                NewCap := Self.FCapacity * 2;
              Self.FData := ReallocMem(Self.FData,
                NewCap * SizeOf(T));
              Self.FCapacity := NewCap
            end;
            procedure Add(Value: T);
            var
              Dest: ^T;
            begin
              if Self.FCount = Self.FCapacity then
                Self.Grow();
              Dest := Self.FData + Self.FCount * SizeOf(T);
              Dest^ := Value;
              Self.FCount := Self.FCount + 1
            end;
            function Get(AIndex: Integer): T;
            var
              Src: ^T;
            begin
              Src := Self.FData + AIndex * SizeOf(T);
              Result := Src^
            end;
            property Count: Integer read FCount;
          end;
        var
          L: TList<Integer>;
          V: Integer;
        begin
          L := TList<Integer>.Create();
          L.Add(10);
          L.Add(20);
          V := L.Get(0)
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

function TTListTests.ParseSrc(const ASrc: string): TProgram;
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

function TTListTests.AnalyseSrc(const ASrc: string): TProgram;
var
  SA: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  SA     := TSemanticAnalyser.Create();
  try
    SA.Analyse(Result);
  finally
    SA.Free();
  end;
end;

function TTListTests.GenIR(const ASrc: string): string;
var
  CG:   TCodeGenQBE;
  Prog: TProgram;
begin
  Prog := AnalyseSrc(ASrc);
  CG   := TCodeGenQBE.Create();
  try
    CG.Generate(Prog);
    Result := CG.GetOutput();
  finally
    CG.Free();
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TTListTests.TestParse_CaretT_FieldType;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  CD:   TClassTypeDef;
  FD:   TFieldDecl;
begin
  Prog := ParseSrc(SrcTListType);
  try
    AssertTrue('At least one type decl', Prog.Block.TypeDecls.Count > 0);
    TD := TTypeDecl(Prog.Block.TypeDecls[0]);
    AssertTrue('Is generic', TD.Def is TGenericTypeDef);
    CD := TGenericTypeDef(TD.Def).ClassDef;
    FD := TFieldDecl(CD.Fields[0]);
    AssertEquals('FData field name', 'FData', FD.Names[0]);
    AssertEquals('FData type is ^T', '^T', FD.TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TTListTests.TestParse_SizeOf_ParsedAsFuncCall;
var
  Prog:   TProgram;
  Assign: TAssignment;
  Call:   TFuncCallExpr;
begin
  Prog := ParseSrc(SrcSizeOfInteger);
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertTrue('RHS is TFuncCallExpr', Assign.Expr is TFuncCallExpr);
    Call := TFuncCallExpr(Assign.Expr);
    AssertEquals('Name is SizeOf', 'SizeOf', Call.Name);
    AssertEquals('One argument', 1, Call.Args.Count);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                        }
{ ------------------------------------------------------------------ }

procedure TTListTests.TestSemantic_SizeOf_Integer;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Prog := AnalyseSrc(SrcSizeOfInteger);
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertEquals('SizeOf(Integer) resolves to Integer type',
      Ord(tyInteger), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TTListTests.TestSemantic_SizeOf_Pointer;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Prog := AnalyseSrc(SrcSizeOfInt64);
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertEquals('SizeOf(Int64) resolves to Integer type',
      Ord(tyInteger), Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TTListTests.TestSemantic_NilAssign_ToTypedPointer;
var
  Prog: TProgram;
begin
  { Should not raise — nil is compatible with ^Integer }
  Prog := AnalyseSrc(SrcNilToTypedPtr);
  Prog.Free();
end;

procedure TTListTests.TestSemantic_Pointer_AssignToTypedPointer;
var
  Prog: TProgram;
begin
  { Should not raise — Pointer (untyped) is compatible with ^Integer }
  Prog := AnalyseSrc(SrcPointerToTypedPtr);
  Prog.Free();
end;

procedure TTListTests.TestSemantic_TList_Instantiation;
var
  Prog: TProgram;
begin
  { Full TList<T> source with ^T fields and SizeOf should analyse without errors }
  Prog := AnalyseSrc(SrcTListType);
  Prog.Free();
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                         }
{ ------------------------------------------------------------------ }

procedure TTListTests.TestCodegen_SizeOf_Integer_EmitsFour;
var
  IR: string;
begin
  IR := GenIR(SrcSizeOfInteger);
  AssertTrue('SizeOf(Integer) emits copy 4', Pos('copy 4', IR) > 0);
end;

procedure TTListTests.TestCodegen_SizeOf_Int64_EmitsEight;
var
  IR: string;
begin
  IR := GenIR(SrcSizeOfInt64);
  AssertTrue('SizeOf(Int64) emits copy 8', Pos('copy 8', IR) > 0);
end;

procedure TTListTests.TestCodegen_TList_Compiles;
var
  IR: string;
begin
  { Full TList<T> program should produce valid IR without raising }
  IR := GenIR(SrcTListType);
  AssertTrue('IR is non-empty', Length(IR) > 0);
end;

procedure TTListTests.TestCodegen_TList_AddGet_IR;
var
  IR: string;
begin
  IR := GenIR(SrcTListGetResult);
  { Add method stores through a typed pointer }
  AssertTrue('Add emits storew', Pos('storew', IR) > 0);
  { Get method loads through a typed pointer }
  AssertTrue('Get emits loadw', Pos('loadw', IR) > 0);
  { Memory allocation via _ClassAlloc (ARC-aware class allocator) }
  AssertTrue('Create emits _ClassAlloc', Pos('_ClassAlloc', IR) > 0);
end;

procedure TTListTests.TestCodegen_TList_Grow_EmitsRealloc;
var
  IR: string;
begin
  IR := GenIR(SrcTListFull);
  { Grow method calls _BlaiseReallocMem for dynamic resizing }
  AssertTrue('Grow emits _BlaiseReallocMem',
    Pos('call $_BlaiseReallocMem', IR) > 0);
  { Add method stores elements }
  AssertTrue('Add emits storew for Integer elements', Pos('storew', IR) > 0);
  { Get method loads elements }
  AssertTrue('Get emits loadw for Integer elements', Pos('loadw', IR) > 0);
end;

initialization
  RegisterTest(TTListTests);

end.
