unit cp.test.pointers;

{$mode objfpc}{$H+}

{ Tests for pointer type infrastructure: ^T types, P^ dereference,
  P^ := V store, GetMem/FreeMem/ReallocMem built-ins, and pointer arithmetic. }

interface

uses
  Classes, SysUtils, StrUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TPointerTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
  published
    { ------------------------------------------------------------------ }
    { Parser — pointer type names and expressions                          }
    { ------------------------------------------------------------------ }
    procedure TestParse_PointerTypeName_Caret;
    procedure TestParse_DerefExpr_NodeType;
    procedure TestParse_PointerWriteStmt_NodeType;

    { ------------------------------------------------------------------ }
    { Semantic — tyPointer kind and typed pointer base type                }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_UntypedPointer_Kind;
    procedure TestSemantic_TypedPointer_Kind;
    procedure TestSemantic_TypedPointer_BaseType;
    procedure TestSemantic_GetMem_ReturnsPointer;
    procedure TestSemantic_FreeMem_IsCallable;
    procedure TestSemantic_Deref_ResolvedType;
    procedure TestSemantic_PointerWrite_AcceptsMatchingType;

    { ------------------------------------------------------------------ }
    { Codegen — emit malloc / free / load / store / pointer arithmetic     }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_GetMem_EmitsMalloc;
    procedure TestCodegen_FreeMem_EmitsFree;
    procedure TestCodegen_Deref_EmitsLoad;
    procedure TestCodegen_PointerWrite_EmitsStore;
    procedure TestCodegen_PointerArith_EmitsAdd;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Source constants                                                     }
{ ------------------------------------------------------------------ }

const
  { Untyped pointer variable declaration }
  SrcUntypedPtr =
    'program P;'                                             + LineEnding +
    'var P: Pointer;'                                        + LineEnding +
    'begin'                                                  + LineEnding +
    'end.';

  { Typed pointer variable declaration }
  SrcTypedPtrDecl =
    'program P;'                                             + LineEnding +
    'var P: ^Integer;'                                       + LineEnding +
    'begin'                                                  + LineEnding +
    'end.';

  { GetMem allocation }
  SrcGetMem =
    'program P;'                                             + LineEnding +
    'var P: Pointer;'                                        + LineEnding +
    'begin'                                                  + LineEnding +
    '  P := GetMem(8)'                                       + LineEnding +
    'end.';

  { FreeMem call }
  SrcFreeMem =
    'program P;'                                             + LineEnding +
    'var P: Pointer;'                                        + LineEnding +
    'begin'                                                  + LineEnding +
    '  P := GetMem(8);'                                      + LineEnding +
    '  FreeMem(P)'                                           + LineEnding +
    'end.';

  { Typed pointer: write and read through a typed pointer variable.
    No allocation needed — we test AST/IR shapes, not runtime correctness. }
  SrcTypedPtrRW =
    'program P;'                                             + LineEnding +
    'var'                                                    + LineEnding +
    '  Ptr: ^Integer;'                                       + LineEnding +
    '  V: Integer;'                                          + LineEnding +
    'begin'                                                  + LineEnding +
    '  Ptr^ := 42;'                                          + LineEnding +
    '  V := Ptr^'                                            + LineEnding +
    'end.';

  { Pointer arithmetic }
  SrcPtrArith =
    'program P;'                                             + LineEnding +
    'var'                                                    + LineEnding +
    '  P1: Pointer;'                                         + LineEnding +
    '  P2: Pointer;'                                         + LineEnding +
    'begin'                                                  + LineEnding +
    '  P1 := GetMem(16);'                                    + LineEnding +
    '  P2 := P1 + 4'                                         + LineEnding +
    'end.';

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TPointerTests.ParseSrc(const ASrc: string): TProgram;
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

function TPointerTests.AnalyseSrc(const ASrc: string): TProgram;
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

function TPointerTests.GenIR(const ASrc: string): string;
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

procedure TPointerTests.TestParse_PointerTypeName_Caret;
var
  Prog: TProgram;
  Decl: TVarDecl;
begin
  Prog := ParseSrc(SrcTypedPtrDecl);
  try
    Decl := TVarDecl(Prog.Block.Decls[0]);
    AssertEquals('^Integer', Decl.TypeName);
  finally
    Prog.Free;
  end;
end;

procedure TPointerTests.TestParse_DerefExpr_NodeType;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  { V := Ptr^ — RHS should be TDerefExpr }
  Prog := ParseSrc(SrcTypedPtrRW);
  try
    { Second stmt: V := Ptr^ }
    Assign := TAssignment(Prog.Block.Stmts[1]);
    AssertTrue('Deref should be TDerefExpr', Assign.Expr is TDerefExpr);
  finally
    Prog.Free;
  end;
end;

procedure TPointerTests.TestParse_PointerWriteStmt_NodeType;
var
  Prog: TProgram;
begin
  { Ptr^ := 42 — should be TPointerWriteStmt }
  Prog := ParseSrc(SrcTypedPtrRW);
  try
    { First stmt: Ptr^ := 42 }
    AssertTrue('Ptr write should be TPointerWriteStmt',
      Prog.Block.Stmts[0] is TPointerWriteStmt);
  finally
    Prog.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TPointerTests.TestSemantic_UntypedPointer_Kind;
var
  Prog: TProgram;
  Decl: TVarDecl;
begin
  Prog := AnalyseSrc(SrcUntypedPtr);
  try
    Decl := TVarDecl(Prog.Block.Decls[0]);
    AssertEquals('Untyped pointer kind', Ord(tyPointer),
      Ord(Decl.ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TPointerTests.TestSemantic_TypedPointer_Kind;
var
  Prog: TProgram;
  Decl: TVarDecl;
begin
  Prog := AnalyseSrc(SrcTypedPtrDecl);
  try
    Decl := TVarDecl(Prog.Block.Decls[0]);
    AssertEquals('Typed pointer kind', Ord(tyPointer),
      Ord(Decl.ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TPointerTests.TestSemantic_TypedPointer_BaseType;
var
  Prog:    TProgram;
  Decl:    TVarDecl;
  PtrDesc: TPointerTypeDesc;
begin
  Prog := AnalyseSrc(SrcTypedPtrDecl);
  try
    Decl    := TVarDecl(Prog.Block.Decls[0]);
    PtrDesc := TPointerTypeDesc(Decl.ResolvedType);
    AssertNotNull('Typed pointer should have BaseType', PtrDesc.BaseType);
    AssertEquals('BaseType should be Integer', 'Integer', PtrDesc.BaseType.Name);
  finally
    Prog.Free;
  end;
end;

procedure TPointerTests.TestSemantic_GetMem_ReturnsPointer;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Prog := AnalyseSrc(SrcGetMem);
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertEquals('GetMem result type', Ord(tyPointer),
      Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TPointerTests.TestSemantic_FreeMem_IsCallable;
var
  Prog: TProgram;
begin
  { Should not raise }
  Prog := AnalyseSrc(SrcFreeMem);
  Prog.Free;
end;

procedure TPointerTests.TestSemantic_Deref_ResolvedType;
var
  Prog:        TProgram;
  Assign:      TAssignment;
  DerefExpr:   TDerefExpr;
begin
  Prog := AnalyseSrc(SrcTypedPtrRW);
  try
    Assign    := TAssignment(Prog.Block.Stmts[1]);
    DerefExpr := TDerefExpr(Assign.Expr);
    AssertEquals('Deref result type', Ord(tyInteger),
      Ord(DerefExpr.ResolvedType.Kind));
  finally
    Prog.Free;
  end;
end;

procedure TPointerTests.TestSemantic_PointerWrite_AcceptsMatchingType;
var
  Prog:     TProgram;
  PtrWrite: TPointerWriteStmt;
begin
  Prog := AnalyseSrc(SrcTypedPtrRW);
  try
    PtrWrite := TPointerWriteStmt(Prog.Block.Stmts[0]);
    AssertNotNull('PointerWrite BaseTy should be set', PtrWrite.BaseTy);
    AssertEquals('BaseTy should be Integer', 'Integer', PtrWrite.BaseTy.Name);
  finally
    Prog.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                        }
{ ------------------------------------------------------------------ }

procedure TPointerTests.TestCodegen_GetMem_EmitsMalloc;
var
  IR: string;
begin
  IR := GenIR(SrcGetMem);
  AssertTrue('GetMem should emit malloc', Pos('call $malloc', IR) > 0);
end;

procedure TPointerTests.TestCodegen_FreeMem_EmitsFree;
var
  IR: string;
begin
  IR := GenIR(SrcFreeMem);
  AssertTrue('FreeMem should emit free', Pos('call $free', IR) > 0);
end;

procedure TPointerTests.TestCodegen_Deref_EmitsLoad;
var
  IR: string;
begin
  IR := GenIR(SrcTypedPtrRW);
  AssertTrue('Deref should emit loadw', Pos('loadw', IR) > 0);
end;

procedure TPointerTests.TestCodegen_PointerWrite_EmitsStore;
var
  IR: string;
begin
  IR := GenIR(SrcTypedPtrRW);
  AssertTrue('Pointer write should emit storew', Pos('storew', IR) > 0);
end;

procedure TPointerTests.TestCodegen_PointerArith_EmitsAdd;
var
  IR: string;
begin
  IR := GenIR(SrcPtrArith);
  AssertTrue('Pointer arithmetic should emit add', Pos('add', IR) > 0);
end;

initialization
  RegisterTest(TPointerTests);

end.
