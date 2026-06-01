{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.tdictionary;

{ Tests for TDictionary<K,V> generic map: two-type-param generic,
  FindKey/Add/TryGetValue/ContainsKey/Remove operations, Count property.

  Key equality relies on the '=' operator on the monomorphized type;
  tests use Integer keys throughout.  String key support requires a
  content-aware RTL helper and is deferred. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TTDictionaryTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
  published
    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_TwoTypeParams_Parsed;
    procedure TestParse_Methods_InClassDecl;
    procedure TestParse_SeparateImpls_OwnerTypeName;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_IntInt_Instantiates;
    procedure TestSemantic_Add_ContainsKey_Compiles;
    procedure TestSemantic_TryGetValue_Compiles;
    procedure TestSemantic_Remove_Compiles;

    { ------------------------------------------------------------------ }
    { Codegen                                                              }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_TypeInfoEmitted;
    procedure TestCodegen_FindKeyEmitted;
    procedure TestCodegen_AddEmitted;
    procedure TestCodegen_TryGetValueEmitted;
    procedure TestCodegen_ContainsKeyEmitted;
    procedure TestCodegen_RemoveEmitted;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Shared source building blocks                                         }
{ ------------------------------------------------------------------ }

const
  { Forward-only class declaration (interface section style) }
  DictDecl =
    '''
        type
          TDictionary<K, V> = class
            FKeys:     ^K;
            FValues:   ^V;
            FCount:    Integer;
            FCapacity: Integer;
            procedure Grow;
            function  FindKey(Key: K): Integer;
            procedure Add(Key: K; Value: V);
            function  TryGetValue(Key: K; var Value: V): Boolean;
            function  ContainsKey(Key: K): Boolean;
            procedure Remove(Key: K);
            property Count: Integer read FCount;
          end;
        ''';

  { Separate method implementations }
  DictImpls =
    '''
        procedure TDictionary<K, V>.Grow;
        var
          NewCap: Integer;
        begin
          if Self.FCapacity = 0 then
            NewCap := 8
          else
            NewCap := Self.FCapacity * 2;
          Self.FKeys   := ReallocMem(Self.FKeys,   NewCap * SizeOf(K));
          Self.FValues := ReallocMem(Self.FValues, NewCap * SizeOf(V));
          Self.FCapacity := NewCap
        end;
        function TDictionary<K, V>.FindKey(Key: K): Integer;
        var
          I:   Integer;
          Ptr: ^K;
        begin
          Result := -1;
          I := 0;
          while I < Self.FCount do
          begin
            Ptr := Self.FKeys + I * SizeOf(K);
            if Ptr^ = Key then
            begin
              Result := I;
              I := Self.FCount
            end
            else
              I := I + 1
          end
        end;
        procedure TDictionary<K, V>.Add(Key: K; Value: V);
        var
          Idx:  Integer;
          KPtr: ^K;
          VPtr: ^V;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then
          begin
            VPtr  := Self.FValues + Idx * SizeOf(V);
            VPtr^ := Value
          end
          else
          begin
            if Self.FCount = Self.FCapacity then
              Self.Grow;
            KPtr  := Self.FKeys   + Self.FCount * SizeOf(K);
            VPtr  := Self.FValues + Self.FCount * SizeOf(V);
            KPtr^ := Key;
            VPtr^ := Value;
            Self.FCount := Self.FCount + 1
          end
        end;
        function TDictionary<K, V>.TryGetValue(Key: K; var Value: V): Boolean;
        var
          Idx:  Integer;
          VPtr: ^V;
        begin
          Idx    := Self.FindKey(Key);
          Result := Idx >= 0;
          if Idx >= 0 then
          begin
            VPtr  := Self.FValues + Idx * SizeOf(V);
            Value := VPtr^
          end
        end;
        function TDictionary<K, V>.ContainsKey(Key: K): Boolean;
        begin
          Result := Self.FindKey(Key) >= 0
        end;
        procedure TDictionary<K, V>.Remove(Key: K);
        var
          Idx:  Integer;
          I:    Integer;
          KDst: ^K;
          KSrc: ^K;
          VDst: ^V;
          VSrc: ^V;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then
          begin
            I := Idx;
            while I < Self.FCount - 1 do
            begin
              KDst  := Self.FKeys   + I * SizeOf(K);
              KSrc  := Self.FKeys   + (I + 1) * SizeOf(K);
              VDst  := Self.FValues + I * SizeOf(V);
              VSrc  := Self.FValues + (I + 1) * SizeOf(V);
              KDst^ := KSrc^;
              VDst^ := VSrc^;
              I     := I + 1
            end;
            Self.FCount := Self.FCount - 1
          end
        end;
        ''';

  { Complete programs using TDictionary<Integer,Integer> }

  SrcCreate =
    'program P;' + #10 +
    DictDecl +
    DictImpls +
    '''
        var D: TDictionary<Integer, Integer>;
        begin
          D := TDictionary<Integer, Integer>.Create
        end.
        ''';

  SrcAddGet =
    'program P;' + #10 +
    DictDecl +
    DictImpls +
    '''
        var
          D:  TDictionary<Integer, Integer>;
          OK: Boolean;
        begin
          D := TDictionary<Integer, Integer>.Create;
          D.Add(1, 100);
          D.Add(2, 200);
          OK := D.ContainsKey(1)
        end.
        ''';

  SrcTryGet =
    'program P;' + #10 +
    DictDecl +
    DictImpls +
    '''
        var
          D:  TDictionary<Integer, Integer>;
          V:  Integer;
          OK: Boolean;
        begin
          D := TDictionary<Integer, Integer>.Create;
          D.Add(42, 99);
          OK := D.TryGetValue(42, V)
        end.
        ''';

  SrcRemove =
    'program P;' + #10 +
    DictDecl +
    DictImpls +
    '''
        var
          D:  TDictionary<Integer, Integer>;
          OK: Boolean;
        begin
          D := TDictionary<Integer, Integer>.Create;
          D.Add(7, 70);
          D.Remove(7);
          OK := D.ContainsKey(7)
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

function TTDictionaryTests.ParseSrc(const ASrc: string): TProgram;
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

function TTDictionaryTests.AnalyseSrc(const ASrc: string): TProgram;
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

function TTDictionaryTests.GenIR(const ASrc: string): string;
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

procedure TTDictionaryTests.TestParse_TwoTypeParams_Parsed;
var
  Prog: TProgram;
  GD:   TGenericTypeDef;
begin
  Prog := ParseSrc(SrcCreate);
  try
    AssertEquals('One type decl', 1, Prog.Block.TypeDecls.Count);
    AssertTrue('Is generic type', TTypeDecl(Prog.Block.TypeDecls[0]).Def is TGenericTypeDef);
    GD := TGenericTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('Two type params', 2, GD.ParamNames.Count);
    AssertEquals('First param K', 'K', GD.ParamNames[0]);
    AssertEquals('Second param V', 'V', GD.ParamNames[1]);
  finally
    Prog.Free;
  end;
end;

procedure TTDictionaryTests.TestParse_Methods_InClassDecl;
var
  Prog: TProgram;
  GD:   TGenericTypeDef;
begin
  Prog := ParseSrc(SrcCreate);
  try
    GD := TGenericTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('Six methods in class', 6, GD.ClassDef.Methods.Count);
  finally
    Prog.Free;
  end;
end;

procedure TTDictionaryTests.TestParse_SeparateImpls_OwnerTypeName;
var
  Prog:  TProgram;
  MDecl: TMethodDecl;
begin
  Prog := ParseSrc(SrcCreate);
  try
    { ProcDecls[0] = Grow impl }
    AssertTrue('At least 6 proc decls', Prog.Block.ProcDecls.Count >= 6);
    MDecl := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('Grow OwnerTypeName', 'TDictionary', MDecl.OwnerTypeName);
    AssertTrue('Grow OwnerTypeParams set', MDecl.OwnerTypeParams <> nil);
    AssertEquals('Two owner type params', 2, MDecl.OwnerTypeParams.Count);
  finally
    Prog.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                        }
{ ------------------------------------------------------------------ }

procedure TTDictionaryTests.TestSemantic_IntInt_Instantiates;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcCreate);
  Prog.Free;
end;

procedure TTDictionaryTests.TestSemantic_Add_ContainsKey_Compiles;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcAddGet);
  Prog.Free;
end;

procedure TTDictionaryTests.TestSemantic_TryGetValue_Compiles;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcTryGet);
  Prog.Free;
end;

procedure TTDictionaryTests.TestSemantic_Remove_Compiles;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcRemove);
  Prog.Free;
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                         }
{ ------------------------------------------------------------------ }

procedure TTDictionaryTests.TestCodegen_TypeInfoEmitted;
var
  IR: string;
begin
  IR := GenIR(SrcCreate);
  AssertTrue('Typeinfo emitted',
    Pos('typeinfo_TDictionary_Integer_Integer', IR) > 0);
end;

procedure TTDictionaryTests.TestCodegen_FindKeyEmitted;
var
  IR: string;
begin
  IR := GenIR(SrcAddGet);
  AssertTrue('FindKey body emitted',
    Pos('$P_TDictionary_Integer_Integer_FindKey', IR) > 0);
end;

procedure TTDictionaryTests.TestCodegen_AddEmitted;
var
  IR: string;
begin
  IR := GenIR(SrcAddGet);
  AssertTrue('Add body emitted',
    Pos('$P_TDictionary_Integer_Integer_Add', IR) > 0);
end;

procedure TTDictionaryTests.TestCodegen_TryGetValueEmitted;
var
  IR: string;
begin
  IR := GenIR(SrcTryGet);
  AssertTrue('TryGetValue body emitted',
    Pos('$P_TDictionary_Integer_Integer_TryGetValue', IR) > 0);
end;

procedure TTDictionaryTests.TestCodegen_ContainsKeyEmitted;
var
  IR: string;
begin
  IR := GenIR(SrcAddGet);
  AssertTrue('ContainsKey body emitted',
    Pos('$P_TDictionary_Integer_Integer_ContainsKey', IR) > 0);
end;

procedure TTDictionaryTests.TestCodegen_RemoveEmitted;
var
  IR: string;
begin
  IR := GenIR(SrcRemove);
  AssertTrue('Remove body emitted',
    Pos('$P_TDictionary_Integer_Integer_Remove', IR) > 0);
end;

initialization
  RegisterTest(TTDictionaryTests);

end.
