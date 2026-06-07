{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.collections;

{ Tests for TObjectList and TStringList built in pure Blaise Pascal:
    - TObjectList: dynamic Pointer array, optional ownership
    - TStringList: dynamic string + Pointer parallel arrays with
      sorted binary search and case-insensitive lookup

  New builtins exercised:
    CompareStr(s1, s2) : Integer
    CompareText(s1, s2): Integer
    ZeroMem(ptr, count): procedure
    _ClassAddRef(ptr)  : procedure (raw ARC)
    _ClassRelease(ptr) : procedure (raw ARC)

  ARC correctness fix exercised:
    EmitPointerWrite emits retain/release when BaseTy is tyString. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TCollectionTests = class(TTestCase)
  private
    function GenIR(const ASrc: string): string;
    procedure SemanticOK(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { CompareStr / CompareText builtins                                    }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_CompareStr_OK;
    procedure TestSemantic_CompareText_OK;
    procedure TestSemantic_CompareStr_ReturnsInteger;
    procedure TestCodegen_CompareStr_CallsRTL;
    procedure TestCodegen_CompareText_CallsRTL;

    { ------------------------------------------------------------------ }
    { ZeroMem builtin                                                      }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_ZeroMem_OK;
    procedure TestCodegen_ZeroMem_CallsMemset;

    { ------------------------------------------------------------------ }
    { TObjectList — IR / semantic                                          }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_TObjectList_Compiles;
    procedure TestCodegen_TObjectList_AddEmitsStore;
    procedure TestCodegen_TObjectList_GetEmitsLoad;
    procedure TestCodegen_TObjectList_GrowEmitsRealloc;

    { ------------------------------------------------------------------ }
    { TStringList — IR / semantic                                          }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_TStringList_Compiles;
    procedure TestCodegen_TStringList_AddEmitsStringStore;
    procedure TestCodegen_TStringList_FindEmitsCompare;
    procedure TestCodegen_TStringList_ZeroMemInGrow;

    { ------------------------------------------------------------------ }
    { TStringList — Text property / LoadFromFile / SaveToFile              }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_TStringList_TextPropertyGet;
    procedure TestSemantic_TStringList_TextPropertySet;
    procedure TestSemantic_TStringList_LoadFromFile;
    procedure TestSemantic_TStringList_SaveToFile;
    procedure TestCodegen_TStringList_TextGetCallsGetText;
    procedure TestCodegen_TStringList_TextSetCallsSetText;
    procedure TestCodegen_TStringList_LoadFromFileCallsReadFile;
    procedure TestCodegen_TStringList_SaveToFileCallsWriteFile;

    { ------------------------------------------------------------------ }
    { TStringList — Strings[i] / Objects[i] indexed properties             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_TStringList_StringsIndexedRead;
    procedure TestSemantic_TStringList_StringsIndexedWrite;
    procedure TestSemantic_TStringList_ObjectsIndexedRead;
    procedure TestSemantic_TStringList_ObjectsIndexedWrite;
    procedure TestCodegen_TStringList_StringsReadCallsGet;
    procedure TestCodegen_TStringList_StringsWriteCallsPut;
    procedure TestCodegen_TStringList_ObjectsReadCallsGetObject;
    procedure TestCodegen_TStringList_ObjectsWriteCallsSetObject;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Blaise source constants                                              }
{ ------------------------------------------------------------------ }

const
  { Minimal TObjectList inline source }
  SrcTObjectListBase =
    '''
        program P;
        type
          TObjectList = class
            FData:     ^Pointer;
            FCount:    Integer;
            FCapacity: Integer;
            procedure Grow;
            var NewCap: Integer;
            begin
              if Self.FCapacity = 0 then NewCap := 4
              else NewCap := Self.FCapacity * 2;
              Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(Pointer));
              Self.FCapacity := NewCap
            end;
            function Add(AObject: Pointer): Integer;
            var Dest: ^Pointer;
            begin
              if Self.FCount = Self.FCapacity then Self.Grow();
              Dest        := Self.FData + Self.FCount * SizeOf(Pointer);
              Dest^       := AObject;
              Self.FCount := Self.FCount + 1;
              Result      := Self.FCount - 1
            end;
            function Get(AIndex: Integer): Pointer;
            var Src: ^Pointer;
            begin
              Src    := Self.FData + AIndex * SizeOf(Pointer);
              Result := Src^
            end;
            property Count: Integer read FCount;
          end;
        ''';

  SrcTObjectListUse =
    SrcTObjectListBase +
    '''
        var L: TObjectList;
        begin
          L := TObjectList.Create();
          L.Add(nil);
          L.Add(nil)
        end.
        ''';

  SrcTObjectListGet =
    SrcTObjectListBase +
    '''
        var
          L: TObjectList;
          P: Pointer;
        begin
          L := TObjectList.Create();
          L.Add(nil);
          P := L.Get(0)
        end.
        ''';

  { CompareStr/CompareText test }
  SrcCompareStr =
    '''
        program P;
        var N: Integer;
        begin
          N := CompareStr('abc', 'abd')
        end.
        ''';

  SrcCompareText =
    '''
        program P;
        var N: Integer;
        begin
          N := CompareText('ABC', 'abc')
        end.
        ''';

  { ZeroMem test }
  SrcZeroMem =
    '''
        program P;
        var P: Pointer;
        begin
          P := GetMem(16);
          ZeroMem(P, 16)
        end.
        ''';

  { Minimal TStringList inline source }
  SrcTStringListBase =
    '''
        program P;
        type
          TStringList = class
            FStrings:    ^string;
            FObjects:    ^Pointer;
            FCount:      Integer;
            FCapacity:   Integer;
            FSorted:     Boolean;
            procedure Grow;
            var OldCap, NewCap: Integer;
            begin
              OldCap := Self.FCapacity;
              if OldCap = 0 then NewCap := 4
              else NewCap := OldCap * 2;
              Self.FStrings  := ReallocMem(Self.FStrings, NewCap * SizeOf(string));
              Self.FObjects  := ReallocMem(Self.FObjects, NewCap * SizeOf(Pointer));
              ZeroMem(Self.FStrings + OldCap * SizeOf(string), (NewCap - OldCap) * SizeOf(string));
              Self.FCapacity := NewCap
            end;
            function Add(S: string): Integer;
            var
              StrP: ^string;
              ObjP: ^Pointer;
            begin
              if Self.FCount = Self.FCapacity then Self.Grow();
              StrP        := Self.FStrings + Self.FCount * SizeOf(string);
              ObjP        := Self.FObjects + Self.FCount * SizeOf(Pointer);
              StrP^       := S;
              ObjP^       := nil;
              Result      := Self.FCount;
              Self.FCount := Self.FCount + 1
            end;
            function Get(AIndex: Integer): string;
            var Ptr: ^string;
            begin
              Ptr    := Self.FStrings + AIndex * SizeOf(string);
              Result := Ptr^
            end;
            function Find(S: string; var Index: Integer): Boolean;
            var
              Lo, Hi, Mid, Cmp: Integer;
              Ptr: ^string;
              MStr: string;
            begin
              Lo := 0;
              Hi := Self.FCount - 1;
              while Lo <= Hi do
              begin
                Mid  := (Lo + Hi) div 2;
                Ptr  := Self.FStrings + Mid * SizeOf(string);
                MStr := Ptr^;
                Cmp  := CompareText(S, MStr);
                if Cmp = 0 then
                begin
                  Index  := Mid;
                  Result := True;
                  Exit
                end
                else if Cmp < 0 then
                  Hi := Mid - 1
                else
                  Lo := Mid + 1
              end;
              Index  := Lo;
              Result := False
            end;
            property Count: Integer read FCount;
          end;
        ''';

  SrcTStringListUse =
    SrcTStringListBase +
    '''
        var L: TStringList;
        begin
          L := TStringList.Create();
          L.Add('hello');
          L.Add('world')
        end.
        ''';

  SrcTStringListFind =
    SrcTStringListBase +
    '''
        var
          L: TStringList;
          Idx: Integer;
          Found: Boolean;
        begin
          L := TStringList.Create();
          L.Add('alpha');
          L.Add('beta');
          Found := L.Find('alpha', Idx)
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

function TCollectionTests.GenIR(const ASrc: string): string;
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  CG:   TCodeGenQBE;
  Prog: TProgram;
begin
  Lex  := TLexer.Create(ASrc);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse();
  Par.Free();
  Lex.Free();
  SA   := TSemanticAnalyser.Create();
  SA.Analyse(Prog);
  SA.Free();
  CG   := TCodeGenQBE.Create();
  CG.Generate(Prog);
  Result := CG.GetOutput();
  CG.Free();
  Prog.Free();
end;

procedure TCollectionTests.SemanticOK(const ASrc: string);
var
  Lex:  TLexer;
  Par:  TParser;
  SA:   TSemanticAnalyser;
  Prog: TProgram;
begin
  Lex  := TLexer.Create(ASrc);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse();
  Par.Free();
  Lex.Free();
  SA   := TSemanticAnalyser.Create();
  try
    SA.Analyse(Prog);
  finally
    SA.Free();
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ CompareStr / CompareText                                             }
{ ------------------------------------------------------------------ }

procedure TCollectionTests.TestSemantic_CompareStr_OK;
begin
  SemanticOK(SrcCompareStr);
end;

procedure TCollectionTests.TestSemantic_CompareText_OK;
begin
  SemanticOK(SrcCompareText);
end;

procedure TCollectionTests.TestSemantic_CompareStr_ReturnsInteger;
var
  Lex:    TLexer;
  Par:    TParser;
  SA:     TSemanticAnalyser;
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Lex  := TLexer.Create(SrcCompareStr);
  Par  := TParser.Create(Lex);
  Prog := Par.Parse();
  Par.Free();
  Lex.Free();
  SA := TSemanticAnalyser.Create();
  SA.Analyse(Prog);
  SA.Free();
  Assign := TAssignment(Prog.Block.Stmts[0]);
  AssertEquals('CompareStr returns Integer',
    Ord(tyInteger), Ord(Assign.Expr.ResolvedType.Kind));
  Prog.Free();
end;

procedure TCollectionTests.TestCodegen_CompareStr_CallsRTL;
var
  IR: string;
begin
  IR := GenIR(SrcCompareStr);
  AssertTrue('CompareStr emits _StringCompare call',
    Pos('_StringCompare', IR) > 0);
end;

procedure TCollectionTests.TestCodegen_CompareText_CallsRTL;
var
  IR: string;
begin
  IR := GenIR(SrcCompareText);
  AssertTrue('CompareText emits _StringCompareText call',
    Pos('_StringCompareText', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ ZeroMem                                                              }
{ ------------------------------------------------------------------ }

procedure TCollectionTests.TestSemantic_ZeroMem_OK;
begin
  SemanticOK(SrcZeroMem);
end;

procedure TCollectionTests.TestCodegen_ZeroMem_CallsMemset;
var
  IR: string;
begin
  IR := GenIR(SrcZeroMem);
  AssertTrue('ZeroMem emits memset call', Pos('call $memset', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ TObjectList                                                           }
{ ------------------------------------------------------------------ }

procedure TCollectionTests.TestSemantic_TObjectList_Compiles;
begin
  SemanticOK(SrcTObjectListUse);
end;

procedure TCollectionTests.TestCodegen_TObjectList_AddEmitsStore;
var
  IR: string;
begin
  IR := GenIR(SrcTObjectListUse);
  AssertTrue('TObjectList.Add emits storel for Pointer element',
    Pos('storel', IR) > 0);
end;

procedure TCollectionTests.TestCodegen_TObjectList_GetEmitsLoad;
var
  IR: string;
begin
  IR := GenIR(SrcTObjectListGet);
  AssertTrue('TObjectList.Get emits loadl for Pointer element',
    Pos('loadl', IR) > 0);
end;

procedure TCollectionTests.TestCodegen_TObjectList_GrowEmitsRealloc;
var
  IR: string;
begin
  IR := GenIR(SrcTObjectListUse);
  AssertTrue('TObjectList.Grow() emits _BlaiseReallocMem call',
    Pos('call $_BlaiseReallocMem', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ TStringList                                                           }
{ ------------------------------------------------------------------ }

procedure TCollectionTests.TestSemantic_TStringList_Compiles;
begin
  SemanticOK(SrcTStringListUse);
end;

procedure TCollectionTests.TestCodegen_TStringList_AddEmitsStringStore;
var
  IR: string;
begin
  IR := GenIR(SrcTStringListUse);
  { String ARC: Add must emit _StringAddRef for the stored string }
  AssertTrue('TStringList.Add emits _StringAddRef for stored string',
    Pos('_StringAddRef', IR) > 0);
end;

procedure TCollectionTests.TestCodegen_TStringList_FindEmitsCompare;
var
  IR: string;
begin
  IR := GenIR(SrcTStringListFind);
  AssertTrue('TStringList.Find uses CompareText RTL call',
    Pos('_StringCompareText', IR) > 0);
end;

procedure TCollectionTests.TestCodegen_TStringList_ZeroMemInGrow;
var
  IR: string;
begin
  IR := GenIR(SrcTStringListUse);
  AssertTrue('TStringList.Grow() emits memset for zero-init of new string slots',
    Pos('call $memset', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ TStringList — Text / LoadFromFile / SaveToFile source constants        }
{ ------------------------------------------------------------------ }

const
  { Minimal TStringList with Text property and file methods }
  SrcTStringListTextBase =
    '''
        program P;
        type
          TStringList = class
            FStrings:  ^string;
            FObjects:  ^Pointer;
            FCount:    Integer;
            FCapacity: Integer;
            procedure Grow;
            begin
            end;
            function Add(S: string): Integer;
            begin
              Result := 0
            end;
            procedure Clear;
            begin
              Self.FCount := 0
            end;
            function Get(AIndex: Integer): string;
            var Ptr: ^string;
            begin
              Ptr := Self.FStrings + AIndex * SizeOf(string);
              Result := Ptr^
            end;
            procedure Put(AIndex: Integer; S: string);
            var Ptr: ^string;
            begin
              Ptr := Self.FStrings + AIndex * SizeOf(string);
              Ptr^ := S
            end;
            function GetObject(AIndex: Integer): Pointer;
            var Ptr: ^Pointer;
            begin
              Ptr := Self.FObjects + AIndex * SizeOf(Pointer);
              Result := Ptr^
            end;
            procedure SetObject(AIndex: Integer; AObject: Pointer);
            var Ptr: ^Pointer;
            begin
              Ptr := Self.FObjects + AIndex * SizeOf(Pointer);
              Ptr^ := AObject
            end;
            function GetText: string;
            begin
            end;
            procedure SetText(AText: string);
            begin
              Self.Clear()
            end;
            procedure LoadFromFile(APath: string);
            begin
              Self.SetText(ReadFile(APath))
            end;
            procedure SaveToFile(APath: string);
            begin
              WriteFile(APath, Self.GetText() + #10)
            end;
            property Count: Integer read FCount;
            property Text: string read GetText write SetText;
            property Strings[Index: Integer]: string read Get write Put;
            property Objects[Index: Integer]: Pointer read GetObject write SetObject;
          end;
        ''';

  SrcTextGet =
    SrcTStringListTextBase +
    '''
        var L: TStringList; S: string;
        begin
          L := TStringList.Create();
          S := L.Text
        end.
        ''';

  SrcTextSet =
    SrcTStringListTextBase +
    '''
        var L: TStringList;
        begin
          L := TStringList.Create();
          L.Text := 'hello'
        end.
        ''';

  SrcLoadFromFile =
    SrcTStringListTextBase +
    '''
        var L: TStringList;
        begin
          L := TStringList.Create();
          L.LoadFromFile('/tmp/test.pas')
        end.
        ''';

  SrcSaveToFile =
    SrcTStringListTextBase +
    '''
        var L: TStringList;
        begin
          L := TStringList.Create();
          L.SaveToFile('/tmp/out.txt')
        end.
        ''';

  SrcStringsRead =
    SrcTStringListTextBase +
    '''
        var L: TStringList; S: string;
        begin
          L := TStringList.Create();
          S := L.Strings[0]
        end.
        ''';

  SrcStringsWrite =
    SrcTStringListTextBase +
    '''
        var L: TStringList;
        begin
          L := TStringList.Create();
          L.Strings[0] := 'hello'
        end.
        ''';

  SrcObjectsRead =
    SrcTStringListTextBase +
    '''
        var L: TStringList; P: Pointer;
        begin
          L := TStringList.Create();
          P := L.Objects[0]
        end.
        ''';

  SrcObjectsWrite =
    SrcTStringListTextBase +
    '''
        var L: TStringList; P: Pointer;
        begin
          L := TStringList.Create();
          P := nil;
          L.Objects[0] := P
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Text property                                                        }
{ ------------------------------------------------------------------ }

procedure TCollectionTests.TestSemantic_TStringList_TextPropertyGet;
begin
  SemanticOK(SrcTextGet);
end;

procedure TCollectionTests.TestSemantic_TStringList_TextPropertySet;
begin
  SemanticOK(SrcTextSet);
end;

procedure TCollectionTests.TestSemantic_TStringList_LoadFromFile;
begin
  SemanticOK(SrcLoadFromFile);
end;

procedure TCollectionTests.TestSemantic_TStringList_SaveToFile;
begin
  SemanticOK(SrcSaveToFile);
end;

procedure TCollectionTests.TestCodegen_TStringList_TextGetCallsGetText;
var
  IR: string;
begin
  IR := GenIR(SrcTextGet);
  AssertTrue('Text read emits GetText getter call',
    Pos('TStringList_GetText', IR) > 0);
end;

procedure TCollectionTests.TestCodegen_TStringList_TextSetCallsSetText;
var
  IR: string;
begin
  IR := GenIR(SrcTextSet);
  AssertTrue('Text write emits SetText setter call',
    Pos('TStringList_SetText', IR) > 0);
end;

procedure TCollectionTests.TestCodegen_TStringList_LoadFromFileCallsReadFile;
var
  IR: string;
begin
  IR := GenIR(SrcLoadFromFile);
  AssertTrue('LoadFromFile body calls _ReadFile',
    Pos('_ReadFile', IR) > 0);
end;

procedure TCollectionTests.TestCodegen_TStringList_SaveToFileCallsWriteFile;
var
  IR: string;
begin
  IR := GenIR(SrcSaveToFile);
  AssertTrue('SaveToFile body calls _WriteFile',
    Pos('_WriteFile', IR) > 0);
end;

{ ------------------------------------------------------------------ }
{ Strings[i] / Objects[i] indexed properties                           }
{ ------------------------------------------------------------------ }

procedure TCollectionTests.TestSemantic_TStringList_StringsIndexedRead;
begin
  SemanticOK(SrcStringsRead);
end;

procedure TCollectionTests.TestSemantic_TStringList_StringsIndexedWrite;
begin
  SemanticOK(SrcStringsWrite);
end;

procedure TCollectionTests.TestSemantic_TStringList_ObjectsIndexedRead;
begin
  SemanticOK(SrcObjectsRead);
end;

procedure TCollectionTests.TestSemantic_TStringList_ObjectsIndexedWrite;
begin
  SemanticOK(SrcObjectsWrite);
end;

procedure TCollectionTests.TestCodegen_TStringList_StringsReadCallsGet;
var
  IR: string;
begin
  IR := GenIR(SrcStringsRead);
  AssertTrue('Strings[i] read emits Get getter call',
    Pos('TStringList_Get', IR) > 0);
end;

procedure TCollectionTests.TestCodegen_TStringList_StringsWriteCallsPut;
var
  IR: string;
begin
  IR := GenIR(SrcStringsWrite);
  AssertTrue('Strings[i] write emits Put setter call',
    Pos('TStringList_Put', IR) > 0);
end;

procedure TCollectionTests.TestCodegen_TStringList_ObjectsReadCallsGetObject;
var
  IR: string;
begin
  IR := GenIR(SrcObjectsRead);
  AssertTrue('Objects[i] read emits GetObject getter call',
    Pos('TStringList_GetObject', IR) > 0);
end;

procedure TCollectionTests.TestCodegen_TStringList_ObjectsWriteCallsSetObject;
var
  IR: string;
begin
  IR := GenIR(SrcObjectsWrite);
  AssertTrue('Objects[i] write emits SetObject setter call',
    Pos('TStringList_SetObject', IR) > 0);
end;

initialization
  RegisterTest(TCollectionTests);

end.
