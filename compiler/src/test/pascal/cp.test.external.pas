{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.external;

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSemantic, blaise.codegen.qbe;

type
  TExternalTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function ParseUnit(const ASrc: string): TUnit;
    function GenIR(const ASrc: string): string;
    function IRContains(const AIR, AFragment: string): Boolean;
  published
    { Parser — standalone procedure }
    procedure TestParse_ExternalProc_IsExternal;
    procedure TestParse_ExternalProc_ExternalNameEmpty;
    procedure TestParse_ExternalProcNamed_ExternalName;
    { Parser — standalone function }
    procedure TestParse_ExternalFunc_IsExternal;
    procedure TestParse_ExternalFuncNamed_ExternalName;
    { Parser — in unit interface section }
    procedure TestParse_ExternalInUnitInterface;
    { Semantic — external proc is registered and callable }
    procedure TestSemantic_ExternalProc_Callable;
    procedure TestSemantic_ExternalFunc_CallableAsExpr;
    { Codegen — no body emitted for external declarations }
    procedure TestCodegen_ExternalProc_NoBodyEmitted;
    { Codegen — call to external proc generates a call instruction }
    procedure TestCodegen_ExternalProc_CallEmitted;
    { Codegen — call uses C symbol name when 'external name' is given }
    procedure TestCodegen_ExternalProcNamed_UsesExternalName;
    { Codegen — narrow-int FFI returns must be normalised to their
      declared width at the call site.  C ABI leaves the upper bits of
      the return register undefined for sub-int returns, so a caller
      observing the value as a full word (e.g. `if Foo() <> 0 then`)
      would otherwise see garbage upper bits and mis-fire silently. }
    procedure TestCodegen_ExternalByteReturn_MaskedToLowByte;
    procedure TestCodegen_ExternalWordReturn_MaskedToLow16;
    procedure TestCodegen_ExternalSmallIntReturn_SignExtendedFromLow16;
    procedure TestCodegen_ExternalIntegerReturn_NoNormalisation;
    { A double-typed expression (literal, arithmetic result) passed to
      a Single FFI parameter must narrow to 4-byte float on the wire
      before the call.  Without the narrowing, 8 bytes of double go
      into the float-by-value slot and the C `float` callee reads the
      low mantissa half as IEEE-754 single — pure noise. }
    procedure TestCodegen_ExternalSingleParam_DoubleArgNarrowed;
    { A record passed by value to a cdecl external must go through the
      backend's aggregate-by-value mechanism so the callee sees the
      struct contents in registers per the platform C ABI.  Passing
      the record's address in a single integer register would make the
      callee read the low bits of a pointer as struct data — e.g. a
      4-byte RGBA struct given to ClearBackground would clear the
      window to whatever colour fell out of the stack frame address. }
    procedure TestCodegen_ExternalRecordParam_PassedAsAggregateType;
  end;

implementation

function TExternalTests.ParseSrc(const ASrc: string): TProgram;
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

function TExternalTests.ParseUnit(const ASrc: string): TUnit;
var
  L: TLexer;
  P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.ParseUnit();
  finally
    P.Free();
    L.Free();
  end;
end;

function TExternalTests.GenIR(const ASrc: string): string;
var
  L:  TLexer;
  P:  TParser;
  Pr: TProgram;
  A:  TSemanticAnalyser;
  CG: TCodeGenQBE;
begin
  L  := TLexer.Create(ASrc);
  P  := TParser.Create(L);
  Pr := P.Parse();
  A  := TSemanticAnalyser.Create();
  try
    A.Analyse(Pr);
  finally
    A.Free();
  end;
  CG := TCodeGenQBE.Create();
  try
    CG.Generate(Pr);
    Result := CG.GetOutput();
  finally
    CG.Free();
    Pr.Free();
    P.Free();
    L.Free();
  end;
end;

function TExternalTests.IRContains(const AIR, AFragment: string): Boolean;
begin
  Result := Pos(AFragment, AIR) > 0;
end;

{ ── Parser tests ─────────────────────────────────────────────────────────── }

procedure TExternalTests.TestParse_ExternalProc_IsExternal;
var
  Prog: TProgram;
  Decl: TMethodDecl;
begin
  Prog := ParseSrc(
    '''
        program Test;
        procedure Foo; external;
        begin
        end.
        '''
  );
  try
    AssertEquals('Should have one proc decl', 1, Prog.Block.ProcDecls.Count);
    Decl := TMethodDecl(Prog.Block.ProcDecls.Items[0]);
    AssertTrue('IsExternal should be True', Decl.IsExternal);
  finally
    Prog.Free();
  end;
end;

procedure TExternalTests.TestParse_ExternalProc_ExternalNameEmpty;
var
  Prog: TProgram;
  Decl: TMethodDecl;
begin
  Prog := ParseSrc(
    '''
        program Test;
        procedure Foo; external;
        begin
        end.
        '''
  );
  try
    Decl := TMethodDecl(Prog.Block.ProcDecls.Items[0]);
    AssertEquals('ExternalName should be empty when no name given',
      '', Decl.ExternalName);
  finally
    Prog.Free();
  end;
end;

procedure TExternalTests.TestParse_ExternalProcNamed_ExternalName;
var
  Prog: TProgram;
  Decl: TMethodDecl;
begin
  Prog := ParseSrc(
    '''
        program Test;
        procedure Foo; external name 'c_foo';
        begin
        end.
        '''
  );
  try
    Decl := TMethodDecl(Prog.Block.ProcDecls.Items[0]);
    AssertTrue('IsExternal should be True', Decl.IsExternal);
    AssertEquals('ExternalName should be c_foo', 'c_foo', Decl.ExternalName);
  finally
    Prog.Free();
  end;
end;

procedure TExternalTests.TestParse_ExternalFunc_IsExternal;
var
  Prog: TProgram;
  Decl: TMethodDecl;
begin
  Prog := ParseSrc(
    '''
        program Test;
        function Bar: Integer; external;
        begin
        end.
        '''
  );
  try
    AssertEquals('Should have one func decl', 1, Prog.Block.ProcDecls.Count);
    Decl := TMethodDecl(Prog.Block.ProcDecls.Items[0]);
    AssertTrue('IsExternal should be True', Decl.IsExternal);
  finally
    Prog.Free();
  end;
end;

procedure TExternalTests.TestParse_ExternalFuncNamed_ExternalName;
var
  Prog: TProgram;
  Decl: TMethodDecl;
begin
  Prog := ParseSrc(
    '''
        program Test;
        function Bar: Integer; external name 'c_bar';
        begin
        end.
        '''
  );
  try
    Decl := TMethodDecl(Prog.Block.ProcDecls.Items[0]);
    AssertEquals('ExternalName should be c_bar', 'c_bar', Decl.ExternalName);
  finally
    Prog.Free();
  end;
end;

procedure TExternalTests.TestParse_ExternalInUnitInterface;
var
  U: TUnit;
begin
  U := ParseUnit(
    '''
        unit MyLib;
        interface
        procedure Foo; external;
        function Bar: Integer; external;
        implementation
        end.
        '''
  );
  try
    AssertEquals('Interface should have 2 proc decls',
      2, U.IntfBlock.ProcDecls.Count);
    AssertTrue('Foo should be external',
      TMethodDecl(U.IntfBlock.ProcDecls.Items[0]).IsExternal);
    AssertTrue('Bar should be external',
      TMethodDecl(U.IntfBlock.ProcDecls.Items[1]).IsExternal);
  finally
    U.Free();
  end;
end;

{ ── Semantic tests ───────────────────────────────────────────────────────── }

procedure TExternalTests.TestSemantic_ExternalProc_Callable;
var
  Prog: TProgram;
  SA:   TSemanticAnalyser;
begin
  Prog := ParseSrc(
    '''
        program Test;
        procedure Foo; external;
        begin
          Foo()
        end.
        '''
  );
  SA := TSemanticAnalyser.Create();
  try
    SA.Analyse(Prog);
    AssertNotNull('Program should analyse without error', Prog.SymbolTable);
  finally
    SA.Free();
    Prog.Free();
  end;
end;

procedure TExternalTests.TestSemantic_ExternalFunc_CallableAsExpr;
var
  Prog: TProgram;
  SA:   TSemanticAnalyser;
begin
  Prog := ParseSrc(
    '''
        program Test;
        function Bar: Integer; external;
        var x: Integer;
        begin
          x := Bar()
        end.
        '''
  );
  SA := TSemanticAnalyser.Create();
  try
    SA.Analyse(Prog);
    AssertNotNull('Program should analyse without error', Prog.SymbolTable);
  finally
    SA.Free();
    Prog.Free();
  end;
end;

{ ── Codegen tests ────────────────────────────────────────────────────────── }

procedure TExternalTests.TestCodegen_ExternalProc_NoBodyEmitted;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        procedure Foo; external;
        begin
        end.
        '''
  );
  { An external declaration must NOT emit a QBE function body for Foo }
  AssertFalse('External proc must not emit a function body',
    IRContains(IR, 'function $Foo'));
end;

procedure TExternalTests.TestCodegen_ExternalProc_CallEmitted;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        procedure Foo; external;
        begin
          Foo()
        end.
        '''
  );
  AssertTrue('Call to external proc should appear in IR',
    IRContains(IR, 'call $Foo'));
end;

procedure TExternalTests.TestCodegen_ExternalProcNamed_UsesExternalName;
var
  IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        procedure Foo; external name 'c_foo';
        begin
          Foo()
        end.
        '''
  );
  { Call site must use the C symbol name, not the Pascal name }
  AssertTrue('Call should use C symbol name',
    IRContains(IR, 'call $c_foo'));
  AssertFalse('Call must not use Pascal name when external name is given',
    IRContains(IR, 'call $Foo'));
end;

procedure TExternalTests.TestCodegen_ExternalByteReturn_MaskedToLowByte;
var IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        function Foo: Byte; external;
        var b: Byte;
        begin
          b := Foo();
          if Foo() <> 0 then
            b := 1;
        end.
        '''
  );
  AssertTrue('Byte FFI return must be masked to 8 bits',
    IRContains(IR, 'and ') and IRContains(IR, ', 255'));
end;

procedure TExternalTests.TestCodegen_ExternalWordReturn_MaskedToLow16;
var IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        function Foo: Word; external;
        var w: Word;
        begin
          w := Foo();
        end.
        '''
  );
  AssertTrue('Word FFI return must be masked to 16 bits',
    IRContains(IR, 'and ') and IRContains(IR, ', 65535'));
end;

procedure TExternalTests.TestCodegen_ExternalSmallIntReturn_SignExtendedFromLow16;
var IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        function Foo: SmallInt; external;
        var s: SmallInt;
        begin
          s := Foo();
        end.
        '''
  );
  { Sign-extend low 16 bits: shl 16 then sar 16 }
  AssertTrue('SmallInt FFI return must shl 16 to set up sign-extend',
    IRContains(IR, 'shl ') and IRContains(IR, ', 16'));
  AssertTrue('SmallInt FFI return must sar 16 to complete sign-extend',
    IRContains(IR, 'sar '));
end;

procedure TExternalTests.TestCodegen_ExternalIntegerReturn_NoNormalisation;
var IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        function Foo: Integer; external;
        var i: Integer;
        begin
          i := Foo();
        end.
        '''
  );
  { Full-width returns need no fix-up — must not emit a stray mask. }
  AssertFalse('Integer FFI return must not be masked',
    IRContains(IR, ', 255') or IRContains(IR, ', 65535'));
end;

procedure TExternalTests.TestCodegen_ExternalSingleParam_DoubleArgNarrowed;
var IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        function sinf(x: Single): Single; cdecl; external name 'sinf';
        var s: Single;
        begin
          s := sinf(1.5707964);
        end.
        '''
  );
  { Double literal narrowed to single via truncd before the arg slot. }
  AssertTrue('Double-typed arg narrowed to Single before FFI call',
    IRContains(IR, '=s truncd'));
end;

procedure TExternalTests.TestCodegen_ExternalRecordParam_PassedAsAggregateType;
var IR: string;
begin
  IR := GenIR(
    '''
        program Test;
        type
          TColor = record r, g, b, a: Byte; end;
        procedure CheckColor(c: TColor); cdecl; external name 'check_color';
        var c: TColor;
        begin
          c.r := 18; c.g := 18; c.b := 24; c.a := 255;
          CheckColor(c);
        end.
        '''
  );
  { Aggregate type decl emitted at module scope with one entry per field. }
  AssertTrue('Record type decl emitted for FFI call',
    IRContains(IR, 'type :_ffi_TColor = align 1 { b, b, b, b }'));
  { Call passes the record through the aggregate type, not as a bare 'l'
    pointer.  The aggregate type triggers ABI-correct register packing
    in the backend; 'l <addr>' would pass the *address* in a single
    integer register, which the C callee would read as struct data. }
  AssertTrue('Call uses :_ffi_TColor aggregate type, not l pointer',
    IRContains(IR, 'call $check_color(:_ffi_TColor '));
end;

initialization
  RegisterTest(TExternalTests);

end.
