unit cp.test.vtable;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, fpcunit, testregistry,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, uCodeGenQBE;

type
  TVTableTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    function IRContains(const AIR, AFragment: string): Boolean;
    procedure AnalyseExpectOK(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Lexer                                                                }
    { ------------------------------------------------------------------ }
    procedure TestLexer_Virtual_Keyword;
    procedure TestLexer_Override_Keyword;

    { ------------------------------------------------------------------ }
    { Parser                                                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_VirtualMethod;
    procedure TestParse_OverrideMethod;

    { ------------------------------------------------------------------ }
    { Semantic                                                             }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_SubtypeAssign_OK;
    procedure TestSemantic_VirtualMethod_HasSlot;
    procedure TestSemantic_OverrideMethod_InheritsSlot;

    { ------------------------------------------------------------------ }
    { Code generation — vtable data                                        }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_VTableData_Emitted;
    procedure TestCodegen_VTable_ContainsMethodPtr;
    procedure TestCodegen_VTable_Subclass_OverridesEntry;
    procedure TestCodegen_VTable_Subclass_InheritsParentEntry;

    { ------------------------------------------------------------------ }
    { Code generation — object layout                                      }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_Constructor_StoresVTablePtr;
    procedure TestCodegen_MallocSize_IncludesVPtr;
    procedure TestCodegen_FieldOffset_ShiftedByEight;

    { ------------------------------------------------------------------ }
    { Code generation — dispatch                                           }
    { ------------------------------------------------------------------ }
    procedure TestCodegen_VirtualCall_IsIndirect;
    procedure TestCodegen_StaticMethod_IsDirectCall;
  end;

implementation

const
  SrcBase =
    'program P;'                                  + LineEnding +
    'type'                                        + LineEnding +
    '  TAnimal = class'                           + LineEnding +
    '    procedure Speak; virtual; begin end;'    + LineEnding +
    '  end;'                                      + LineEnding +
    'begin end.';

  SrcInherit =
    'program P;'                                  + LineEnding +
    'type'                                        + LineEnding +
    '  TAnimal = class'                           + LineEnding +
    '    procedure Speak; virtual; begin end;'    + LineEnding +
    '  end;'                                      + LineEnding +
    '  TDog = class(TAnimal)'                     + LineEnding +
    '    procedure Speak; override; begin end;'   + LineEnding +
    '  end;'                                      + LineEnding +
    'begin end.';

  SrcBaseWithField =
    'program P;'                                  + LineEnding +
    'type'                                        + LineEnding +
    '  TPoint = class'                            + LineEnding +
    '    X: Integer;'                             + LineEnding +
    '    procedure Reset; virtual; begin end;'    + LineEnding +
    '  end;'                                      + LineEnding +
    'var P: TPoint;'                              + LineEnding +
    'begin'                                       + LineEnding +
    '  P := TPoint.Create;'                       + LineEnding +
    '  P.X := 5'                                  + LineEnding +
    'end.';

  SrcStaticMethod =
    'program P;'                          + LineEnding +
    'type'                                + LineEnding +
    '  TFoo = class'                      + LineEnding +
    '    procedure Bar; begin end;'       + LineEnding +
    '  end;'                              + LineEnding +
    'var F: TFoo;'                        + LineEnding +
    'begin'                               + LineEnding +
    '  F := TFoo.Create;'                 + LineEnding +
    '  F.Bar'                             + LineEnding +
    'end.';

  SrcVirtualCall =
    'program P;'                                  + LineEnding +
    'type'                                        + LineEnding +
    '  TAnimal = class'                           + LineEnding +
    '    procedure Speak; virtual; begin end;'    + LineEnding +
    '  end;'                                      + LineEnding +
    'var A: TAnimal;'                             + LineEnding +
    'begin'                                       + LineEnding +
    '  A := TAnimal.Create;'                      + LineEnding +
    '  A.Speak'                                   + LineEnding +
    'end.';

function TVTableTests.ParseSrc(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  Result := P.Parse;
  P.Free;
  L.Free;
end;

function TVTableTests.GenIR(const ASrc: string): string;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  CG: TCodeGenQBE;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse;
  A  := TSemanticAnalyser.Create;
  try
    A.Analyse(Pr);
  finally
    A.Free;
  end;
  CG := TCodeGenQBE.Create;
  try
    CG.Generate(Pr);
    Result := CG.GetOutput;
  finally
    CG.Free;
    Pr.Free;
    P.Free;
    L.Free;
  end;
end;

function TVTableTests.IRContains(const AIR, AFragment: string): Boolean;
begin
  Result := Pos(AFragment, AIR) > 0;
end;

procedure TVTableTests.AnalyseExpectOK(const ASrc: string);
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse;
  A  := TSemanticAnalyser.Create;
  try
    A.Analyse(Pr);  { must not raise }
  finally
    A.Free;
    Pr.Free;
    P.Free;
    L.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Lexer                                                                }
{ ------------------------------------------------------------------ }

procedure TVTableTests.TestLexer_Virtual_Keyword;
var
  L: TLexer;
  T: TToken;
begin
  L := TLexer.Create('virtual');
  try
    T := L.Next;
    AssertEquals('virtual token', Ord(tkVirtual), Ord(T.Kind));
  finally
    L.Free;
  end;
end;

procedure TVTableTests.TestLexer_Override_Keyword;
var
  L: TLexer;
  T: TToken;
begin
  L := TLexer.Create('override');
  try
    T := L.Next;
    AssertEquals('override token', Ord(tkOverride), Ord(T.Kind));
  finally
    L.Free;
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser                                                               }
{ ------------------------------------------------------------------ }

procedure TVTableTests.TestParse_VirtualMethod;
var
  Prog:  TProgram;
  CDef:  TClassTypeDef;
  MDecl: TMethodDecl;
begin
  Prog  := ParseSrc(SrcBase);
  CDef  := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
  MDecl := TMethodDecl(CDef.Methods[0]);
  AssertTrue('method is virtual', MDecl.IsVirtual);
  Prog.Free;
end;

procedure TVTableTests.TestParse_OverrideMethod;
var
  Prog:  TProgram;
  CDef:  TClassTypeDef;
  MDecl: TMethodDecl;
begin
  Prog  := ParseSrc(SrcInherit);
  CDef  := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[1]).Def);
  MDecl := TMethodDecl(CDef.Methods[0]);
  AssertTrue('method is override', MDecl.IsOverride);
  Prog.Free;
end;

{ ------------------------------------------------------------------ }
{ Semantic                                                             }
{ ------------------------------------------------------------------ }

procedure TVTableTests.TestSemantic_SubtypeAssign_OK;
var
  Src: string;
begin
  Src :=
    'program P;'                          + LineEnding +
    'type'                                + LineEnding +
    '  TBase = class'                     + LineEnding +
    '  end;'                              + LineEnding +
    '  TDerived = class(TBase)'           + LineEnding +
    '  end;'                              + LineEnding +
    'var B: TBase;'                       + LineEnding +
    'var D: TDerived;'                    + LineEnding +
    'begin'                               + LineEnding +
    '  D := TDerived.Create;'             + LineEnding +
    '  B := D'                            + LineEnding +
    'end.';
  AnalyseExpectOK(Src);
end;

procedure TVTableTests.TestSemantic_VirtualMethod_HasSlot;
var
  Prog:  TProgram;
  L:     TLexer;
  P:     TParser;
  A:     TSemanticAnalyser;
  CDef:  TClassTypeDef;
  MDecl: TMethodDecl;
begin
  L    := TLexer.Create(SrcBase);
  P    := TParser.Create(L);
  Prog := P.Parse;
  A    := TSemanticAnalyser.Create;
  try
    A.Analyse(Prog);
  finally
    A.Free;
  end;
  CDef  := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
  MDecl := TMethodDecl(CDef.Methods[0]);
  AssertTrue('virtual method gets slot >= 0', MDecl.VTableSlot >= 0);
  Prog.Free;
  P.Free;
  L.Free;
end;

procedure TVTableTests.TestSemantic_OverrideMethod_InheritsSlot;
var
  Prog:   TProgram;
  L:      TLexer;
  P:      TParser;
  A:      TSemanticAnalyser;
  CBase:  TClassTypeDef;
  CDeriv: TClassTypeDef;
  MBase:  TMethodDecl;
  MDeriv: TMethodDecl;
begin
  L    := TLexer.Create(SrcInherit);
  P    := TParser.Create(L);
  Prog := P.Parse;
  A    := TSemanticAnalyser.Create;
  try
    A.Analyse(Prog);
  finally
    A.Free;
  end;
  CBase  := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
  CDeriv := TClassTypeDef(TTypeDecl(Prog.Block.TypeDecls[1]).Def);
  MBase  := TMethodDecl(CBase.Methods[0]);
  MDeriv := TMethodDecl(CDeriv.Methods[0]);
  AssertEquals('override inherits same slot', MBase.VTableSlot, MDeriv.VTableSlot);
  Prog.Free;
  P.Free;
  L.Free;
end;

{ ------------------------------------------------------------------ }
{ Code generation — vtable data                                        }
{ ------------------------------------------------------------------ }

procedure TVTableTests.TestCodegen_VTableData_Emitted;
var
  IR: string;
begin
  IR := GenIR(SrcBase);
  AssertTrue('vtable data section exists',
    IRContains(IR, 'data $vtable_TAnimal'));
end;

procedure TVTableTests.TestCodegen_VTable_ContainsMethodPtr;
var
  IR: string;
begin
  IR := GenIR(SrcBase);
  AssertTrue('vtable contains method pointer',
    IRContains(IR, '$TAnimal_Speak'));
end;

procedure TVTableTests.TestCodegen_VTable_Subclass_OverridesEntry;
var
  IR: string;
begin
  IR := GenIR(SrcInherit);
  AssertTrue('subclass vtable has overriding method',
    IRContains(IR, '$TDog_Speak'));
  AssertTrue('subclass vtable data section exists',
    IRContains(IR, 'data $vtable_TDog'));
end;

procedure TVTableTests.TestCodegen_VTable_Subclass_InheritsParentEntry;
var
  SrcWith2Virtuals: string;
  IR: string;
begin
  SrcWith2Virtuals :=
    'program P;'                                   + LineEnding +
    'type'                                         + LineEnding +
    '  TAnimal = class'                            + LineEnding +
    '    procedure Speak; virtual; begin end;'     + LineEnding +
    '    procedure Move; virtual; begin end;'      + LineEnding +
    '  end;'                                       + LineEnding +
    '  TDog = class(TAnimal)'                      + LineEnding +
    '    procedure Speak; override; begin end;'    + LineEnding +
    '  end;'                                       + LineEnding +
    'begin end.';
  IR := GenIR(SrcWith2Virtuals);
  AssertTrue('subclass vtable inherits parent Move method',
    IRContains(IR, '$TAnimal_Move'));
end;

{ ------------------------------------------------------------------ }
{ Code generation — object layout                                      }
{ ------------------------------------------------------------------ }

procedure TVTableTests.TestCodegen_Constructor_StoresVTablePtr;
var
  IR: string;
begin
  { SrcVirtualCall constructs TAnimal.Create — vtable ptr must be stored }
  IR := GenIR(SrcVirtualCall);
  AssertTrue('constructor stores vtable ptr',
    IRContains(IR, 'storel $vtable_TAnimal'));
end;

procedure TVTableTests.TestCodegen_MallocSize_IncludesVPtr;
var
  IR: string;
begin
  { TPoint has one Integer field (4 bytes) + vptr (8 bytes) = 12 bytes }
  IR := GenIR(SrcBaseWithField);
  AssertTrue('calloc includes vptr size',
    IRContains(IR, 'call $calloc(l 1, l 12)'));
end;

procedure TVTableTests.TestCodegen_FieldOffset_ShiftedByEight;
var
  IR: string;
begin
  { With vptr at offset 0, first field is at offset 8 not 0 }
  IR := GenIR(SrcBaseWithField);
  AssertTrue('field offset is 8 (after vptr)',
    IRContains(IR, ', 8'));
end;

{ ------------------------------------------------------------------ }
{ Code generation — dispatch                                           }
{ ------------------------------------------------------------------ }

procedure TVTableTests.TestCodegen_VirtualCall_IsIndirect;
var
  IR: string;
begin
  IR := GenIR(SrcVirtualCall);
  { Virtual dispatch loads function pointer from vtable and calls via register }
  AssertTrue('virtual call loads vtable',
    IRContains(IR, 'loadl'));
  AssertTrue('virtual call is indirect (call via temp)',
    IRContains(IR, 'call %'));
end;

procedure TVTableTests.TestCodegen_StaticMethod_IsDirectCall;
var
  IR: string;
begin
  IR := GenIR(SrcStaticMethod);
  AssertTrue('static method call is direct',
    IRContains(IR, 'call $TFoo_Bar'));
end;

initialization
  RegisterTest(TVTableTests);

end.
