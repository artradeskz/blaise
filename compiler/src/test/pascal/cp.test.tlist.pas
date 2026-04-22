unit cp.test.tlist;

{$mode objfpc}{$H+}

{ Tests for TList<T> generic dynamic list: type substitution with ^T fields,
  SizeOf built-in, nil/Pointer compatibility with typed pointers, and
  end-to-end Add/Get/Count codegen. }

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

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
  end;

implementation

{ ------------------------------------------------------------------ }
{ Blaise source constants                                              }
{ ------------------------------------------------------------------ }

const
  SrcSizeOfInteger =
    'program P;'                                             + LineEnding +
    'var N: Integer;'                                        + LineEnding +
    'begin'                                                  + LineEnding +
    '  N := SizeOf(Integer)'                                 + LineEnding +
    'end.';

  SrcSizeOfInt64 =
    'program P;'                                             + LineEnding +
    'var N: Integer;'                                        + LineEnding +
    'begin'                                                  + LineEnding +
    '  N := SizeOf(Int64)'                                   + LineEnding +
    'end.';

  SrcNilToTypedPtr =
    'program P;'                                             + LineEnding +
    'var P: ^Integer;'                                       + LineEnding +
    'begin'                                                  + LineEnding +
    '  P := nil'                                             + LineEnding +
    'end.';

  SrcPointerToTypedPtr =
    'program P;'                                             + LineEnding +
    'var'                                                    + LineEnding +
    '  P: ^Integer;'                                         + LineEnding +
    '  Q: Pointer;'                                          + LineEnding +
    'begin'                                                  + LineEnding +
    '  Q := GetMem(4);'                                      + LineEnding +
    '  P := Q'                                               + LineEnding +
    'end.';

  SrcTListType =
    'program P;'                                             + LineEnding +
    'type'                                                   + LineEnding +
    '  TList<T> = class'                                     + LineEnding +
    '    FData: ^T;'                                         + LineEnding +
    '    FCount: Integer;'                                   + LineEnding +
    '    FCapacity: Integer;'                                + LineEnding +
    '    procedure Add(Value: T);'                           + LineEnding +
    '    var'                                                + LineEnding +
    '      Dest: ^T;'                                        + LineEnding +
    '    begin'                                              + LineEnding +
    '      Dest := Self.FData + Self.FCount * SizeOf(T);'   + LineEnding +
    '      Dest^ := Value;'                                  + LineEnding +
    '      Self.FCount := Self.FCount + 1'                   + LineEnding +
    '    end;'                                               + LineEnding +
    '    function Get(AIndex: Integer): T;'                  + LineEnding +
    '    var'                                                + LineEnding +
    '      Src: ^T;'                                         + LineEnding +
    '    begin'                                              + LineEnding +
    '      Src := Self.FData + AIndex * SizeOf(T);'         + LineEnding +
    '      Result := Src^'                                   + LineEnding +
    '    end;'                                               + LineEnding +
    '    property Count: Integer read FCount;'               + LineEnding +
    '  end;'                                                 + LineEnding +
    'var'                                                    + LineEnding +
    '  L: TList<Integer>;'                                   + LineEnding +
    'begin'                                                  + LineEnding +
    '  L := TList<Integer>.Create;'                          + LineEnding +
    '  L.Add(10);'                                           + LineEnding +
    '  L.Add(20)'                                            + LineEnding +
    'end.';

  SrcTListGetResult =
    'program P;'                                             + LineEnding +
    'type'                                                   + LineEnding +
    '  TList<T> = class'                                     + LineEnding +
    '    FData: ^T;'                                         + LineEnding +
    '    FCount: Integer;'                                   + LineEnding +
    '    FCapacity: Integer;'                                + LineEnding +
    '    procedure Add(Value: T);'                           + LineEnding +
    '    var'                                                + LineEnding +
    '      Dest: ^T;'                                        + LineEnding +
    '    begin'                                              + LineEnding +
    '      Dest := Self.FData + Self.FCount * SizeOf(T);'   + LineEnding +
    '      Dest^ := Value;'                                  + LineEnding +
    '      Self.FCount := Self.FCount + 1'                   + LineEnding +
    '    end;'                                               + LineEnding +
    '    function Get(AIndex: Integer): T;'                  + LineEnding +
    '    var'                                                + LineEnding +
    '      Src: ^T;'                                         + LineEnding +
    '    begin'                                              + LineEnding +
    '      Src := Self.FData + AIndex * SizeOf(T);'         + LineEnding +
    '      Result := Src^'                                   + LineEnding +
    '    end;'                                               + LineEnding +
    '    property Count: Integer read FCount;'               + LineEnding +
    '  end;'                                                 + LineEnding +
    'var'                                                    + LineEnding +
    '  L: TList<Integer>;'                                   + LineEnding +
    '  V: Integer;'                                          + LineEnding +
    'begin'                                                  + LineEnding +
    '  L := TList<Integer>.Create;'                          + LineEnding +
    '  L.Add(42);'                                           + LineEnding +
    '  V := L.Get(0)'                                        + LineEnding +
    'end.';

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
    Result := P.Parse;
  finally
    P.Free;
    L.Free;
  end;
end;

function TTListTests.AnalyseSrc(const ASrc: string): TProgram;
var
  SA: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  SA     := TSemanticAnalyser.Create;
  try
    SA.Analyse(Result);
  finally
    SA.Free;
  end;
end;

function TTListTests.GenIR(const ASrc: string): string;
var
  CG:   TCodeGenQBE;
  Prog: TProgram;
begin
  Prog := AnalyseSrc(ASrc);
  CG   := TCodeGenQBE.Create;
  try
    CG.Generate(Prog);
    Result := CG.GetOutput;
  finally
    CG.Free;
    Prog.Free;
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
    Prog.Free;
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
    Prog.Free;
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
    Prog.Free;
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
    Prog.Free;
  end;
end;

procedure TTListTests.TestSemantic_NilAssign_ToTypedPointer;
var
  Prog: TProgram;
begin
  { Should not raise — nil is compatible with ^Integer }
  Prog := AnalyseSrc(SrcNilToTypedPtr);
  Prog.Free;
end;

procedure TTListTests.TestSemantic_Pointer_AssignToTypedPointer;
var
  Prog: TProgram;
begin
  { Should not raise — Pointer (untyped) is compatible with ^Integer }
  Prog := AnalyseSrc(SrcPointerToTypedPtr);
  Prog.Free;
end;

procedure TTListTests.TestSemantic_TList_Instantiation;
var
  Prog: TProgram;
begin
  { Full TList<T> source with ^T fields and SizeOf should analyse without errors }
  Prog := AnalyseSrc(SrcTListType);
  Prog.Free;
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
  { Memory allocation via calloc }
  AssertTrue('Create emits calloc', Pos('calloc', IR) > 0);
end;

initialization
  RegisterTest(TTListTests);

end.
