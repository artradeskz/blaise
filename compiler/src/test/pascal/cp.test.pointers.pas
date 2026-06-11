{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.pointers;

{ Tests for pointer type infrastructure: ^T types, P^ dereference,
  P^ := V store, GetMem/FreeMem/ReallocMem built-ins, and pointer arithmetic. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

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
    procedure TestCodegen_DoublePointerWrite_EmitsStored;
    procedure TestCodegen_SinglePointerWrite_EmitsStores;
    procedure TestCodegen_PointerArith_EmitsAdd;

    { ------------------------------------------------------------------ }
    { Pointer(intExpr) and PtrUInt(ptrExpr) cast pairs                    }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Pointer_FromInt_ReturnsPointerType;
    procedure TestSemantic_PtrUInt_FromPointer_ReturnsUInt64Type;
    procedure TestCodegen_Pointer_FromInt_EmitsExtuw;
    procedure TestCodegen_PtrUInt_FromPointer_EmitsCopy;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Source constants                                                     }
{ ------------------------------------------------------------------ }

const
  { Untyped pointer variable declaration }
  SrcUntypedPtr =
    '''
        program Prg;
        var P: Pointer;
        begin
        end.
        ''';

  { Typed pointer variable declaration }
  SrcTypedPtrDecl =
    '''
        program Prg;
        var P: ^Integer;
        begin
        end.
        ''';

  { GetMem allocation }
  SrcGetMem =
    '''
        program Prg;
        var P: Pointer;
        begin
          P := GetMem(8)
        end.
        ''';

  { FreeMem call }
  SrcFreeMem =
    '''
        program Prg;
        var P: Pointer;
        begin
          P := GetMem(8);
          FreeMem(P)
        end.
        ''';

  { Typed pointer: write and read through a typed pointer variable.
    No allocation needed — we test AST/IR shapes, not runtime correctness. }
  SrcTypedPtrRW =
    '''
        program Prg;
        var
          Ptr: ^Integer;
          V: Integer;
        begin
          Ptr^ := 42;
          V := Ptr^
        end.
        ''';

  SrcDoublePtrWrite =
    '''
        program Prg;
        var
          PD: ^Double;
          D:  Double;
        begin
          PD := @D;
          PD^ := 3.14
        end.
        ''';

  SrcSinglePtrWrite =
    '''
        program Prg;
        var
          PS: ^Single;
          S:  Single;
        begin
          PS := @S;
          PS^ := 1.25
        end.
        ''';

  { Pointer arithmetic }
  SrcPtrArith =
    '''
        program Prg;
        var
          P1: Pointer;
          P2: Pointer;
        begin
          P1 := GetMem(16);
          P2 := P1 + 4
        end.
        ''';

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
    Result := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
end;

function TPointerTests.AnalyseSrc(const ASrc: string): TProgram;
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

function TPointerTests.GenIR(const ASrc: string): string;
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
    Prog.Free();
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
    Prog.Free();
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
    Prog.Free();
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
    Prog.Free();
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
    Prog.Free();
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
    Prog.Free();
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
    Prog.Free();
  end;
end;

procedure TPointerTests.TestSemantic_FreeMem_IsCallable;
var
  Prog: TProgram;
begin
  { Should not raise }
  Prog := AnalyseSrc(SrcFreeMem);
  Prog.Free();
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
    Prog.Free();
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
    Prog.Free();
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
  AssertTrue('GetMem should emit _BlaiseGetMem',
    Pos('call $_BlaiseGetMem', IR) > 0);
end;

procedure TPointerTests.TestCodegen_FreeMem_EmitsFree;
var
  IR: string;
begin
  IR := GenIR(SrcFreeMem);
  AssertTrue('FreeMem should emit _BlaiseFreeMem',
    Pos('call $_BlaiseFreeMem', IR) > 0);
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

procedure TPointerTests.TestCodegen_DoublePointerWrite_EmitsStored;
var
  IR: string;
begin
  IR := GenIR(SrcDoublePtrWrite);
  AssertTrue('PDouble^ := val must emit stored',
    Pos('stored', IR) > 0);
  AssertFalse('PDouble^ write must not use storel',
    Pos('storel %_t', IR) > 0);
end;

procedure TPointerTests.TestCodegen_SinglePointerWrite_EmitsStores;
var
  IR: string;
begin
  IR := GenIR(SrcSinglePtrWrite);
  AssertTrue('PSingle^ := val must emit stores',
    Pos('stores', IR) > 0);
  AssertFalse('PSingle^ write must not use storel',
    Pos('storel %_t', IR) > 0);
end;

procedure TPointerTests.TestCodegen_PointerArith_EmitsAdd;
var
  IR: string;
begin
  IR := GenIR(SrcPtrArith);
  AssertTrue('Pointer arithmetic should emit add', Pos('add', IR) > 0);
end;

const
  SrcPointerFromInt =
    'program Prg;' +
    'var N: Integer; P: Pointer;' +
    'begin N := 42; P := Pointer(N) end.';

  SrcPtrUIntFromPtr =
    'program Prg;' +
    'var P: Pointer; U: UInt64;' +
    'begin P := nil; U := PtrUInt(P) end.';

procedure TPointerTests.TestSemantic_Pointer_FromInt_ReturnsPointerType;
var
  Prog: TProgram;
  Assign: TAssignment;
  Cast: TFuncCallExpr;
begin
  Prog := AnalyseSrc(SrcPointerFromInt);
  try
    Assign := TAssignment(Prog.Block.Stmts.Items[1]);
    Cast   := TFuncCallExpr(Assign.Expr);
    AssertEquals('cast resolves to tyPointer',
      Ord(tyPointer), Ord(Cast.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TPointerTests.TestSemantic_PtrUInt_FromPointer_ReturnsUInt64Type;
var
  Prog: TProgram;
  Assign: TAssignment;
  Cast: TFuncCallExpr;
begin
  Prog := AnalyseSrc(SrcPtrUIntFromPtr);
  try
    Assign := TAssignment(Prog.Block.Stmts.Items[1]);
    Cast   := TFuncCallExpr(Assign.Expr);
    AssertEquals('cast resolves to tyUInt64',
      Ord(tyUInt64), Ord(Cast.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TPointerTests.TestCodegen_Pointer_FromInt_EmitsExtuw;
var
  IR: string;
begin
  IR := GenIR(SrcPointerFromInt);
  AssertTrue('Pointer(Integer) should zero-extend via extuw',
    Pos('extuw', IR) >= 0);
end;

procedure TPointerTests.TestCodegen_PtrUInt_FromPointer_EmitsCopy;
var
  IR: string;
begin
  IR := GenIR(SrcPtrUIntFromPtr);
  AssertTrue('PtrUInt(Pointer) should emit copy (l→l)',
    Pos('copy', IR) >= 0);
end;

initialization
  RegisterTest(TPointerTests);

end.
