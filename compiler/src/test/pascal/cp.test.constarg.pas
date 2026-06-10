{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.constarg;

{ IR tests for shape-aware const-string argument handling (QBE backend).

  Const string params skip the callee-side retain/release pair (5a5b5d4);
  the caller protects the argument for the duration of the call.  The
  protection depends on the argument's shape:

    borrowed  — string literals, named string consts (immortal data) and
                plain non-captured, non-address-taken local/param
                variables: NO AddRef/Release pair is emitted at all.
    consume   — function/method/getter returns (+1 owned temps): no
                AddRef, ONE Release after the call consumes the temp
                (previously these leaked).
    pin       — everything aliasable or unowned: globals, fields, concat
                results (rc=0), captured or address-taken locals, and any
                local in a call whose signature has a var/out string
                param (F(L, L) aliasing) — AddRef before, Release after. }

interface

uses
  Classes, SysUtils, blaise.testing, uStrCompat,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe;

type
  TConstArgTests = class(TTestCase)
  private
    function GenIR(const ASrc: string): string;
    { Extract the body of one emitted function (from 'function ... $Name('
      to the closing brace) so ARC assertions are not polluted by other
      functions' codegen. }
    function FuncRegion(const AIR, AName: string): string;
  published
    procedure TestConstArg_ParamForward_NoArcOps;
    procedure TestConstArg_LocalVar_NoPin;
    procedure TestConstArg_AddrTakenLocal_Pins;
    procedure TestConstArg_CapturedLocal_Pins;
    procedure TestConstArg_Literal_NoPin;
    procedure TestConstArg_GlobalVar_Pins;
    procedure TestConstArg_OwnedReturn_ConsumeOnly;
    procedure TestConstArg_Concat_Pins;
    procedure TestConstArg_VarStringSibling_Pins;
  end;

implementation

function TConstArgTests.GenIR(const ASrc: string): string;
var
  L:    TLexer;
  P:    TParser;
  Prog: TProgram;
  A:    TSemanticAnalyser;
  CG:   TCodeGenQBE;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Prog := P.Parse();
  finally
    P.Free(); L.Free();
  end;
  try
    A := TSemanticAnalyser.Create();
    try
      A.Analyse(Prog);
    finally
      A.Free();
    end;
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

function TConstArgTests.FuncRegion(const AIR, AName: string): string;
var
  StartP, EndP: Integer;
  Marker: string;
begin
  Marker := '$' + AName + '(';
  StartP := Pos(Marker, AIR);
  AssertTrue('function ' + AName + ' present in IR', StartP >= 0);
  EndP := StrPos('}', StrCopyTail(AIR, StartP));
  AssertTrue('function ' + AName + ' closed', EndP >= 0);
  Result := StrCopyFrom(AIR, StartP, EndP);
end;

procedure TConstArgTests.TestConstArg_ParamForward_NoArcOps;
const
  Src = '''
      program P;
      procedure Sink(const S: string);
      begin
      end;
      procedure Caller(const T: string);
      begin
        Sink(T)
      end;
      var L: string;
      begin
        L := 'x';
        Caller(L)
      end.
      ''';
var
  Region: string;
begin
  { Forwarding a const param to a const param: borrowed all the way —
    the Caller body must contain no string ARC ops at all. }
  Region := FuncRegion(GenIR(Src), 'Caller');
  AssertEquals('no AddRef in Caller', -1, Pos('_StringAddRef', Region));
  AssertEquals('no Release in Caller', -1, Pos('_StringRelease', Region));
end;

procedure TConstArgTests.TestConstArg_LocalVar_NoPin;
const
  Src = '''
      program P;
      procedure Sink(const S: string);
      begin
      end;
      function Mk: string;
      begin
        Result := IntToStr(7)
      end;
      procedure Caller;
      var
        L: string;
      begin
        L := Mk();
        Sink(L)
      end;
      begin
        Caller()
      end.
      ''';
var
  Region: string;
  RelCount, I: Integer;
begin
  { L := Mk() consumes the owned return (no AddRef) but still releases L's
    previous value; Sink(L) borrows L (no pin).  Releases in Caller:
    assignment release-old + L's scope-exit release.  A pinned call would
    make it three. }
  Region := FuncRegion(GenIR(Src), 'Caller');
  AssertEquals('no AddRef in Caller', -1, Pos('_StringAddRef', Region));
  RelCount := 0;
  I := Pos('_StringRelease', Region);
  while I >= 0 do
  begin
    RelCount := RelCount + 1;
    I := PosEx('_StringRelease', Region, I + 1);
  end;
  AssertEquals('two Releases (assign old + scope exit), no call pin',
    2, RelCount);
end;

procedure TConstArgTests.TestConstArg_Literal_NoPin;
const
  Src = '''
      program P;
      procedure Sink(const S: string);
      begin
      end;
      procedure Caller;
      begin
        Sink('hello')
      end;
      begin
        Caller()
      end.
      ''';
var
  Region: string;
begin
  Region := FuncRegion(GenIR(Src), 'Caller');
  AssertEquals('no AddRef for literal arg', -1, Pos('_StringAddRef', Region));
  AssertEquals('no Release for literal arg', -1, Pos('_StringRelease', Region));
end;

procedure TConstArgTests.TestConstArg_GlobalVar_Pins;
const
  Src = '''
      program P;
      var G: string;
      procedure Sink(const S: string);
      begin
      end;
      procedure Caller;
      begin
        Sink(G)
      end;
      begin
        G := 'x';
        Caller()
      end.
      ''';
var
  Region: string;
begin
  { A global can be reassigned by the callee (through its own name), which
    would release the buffer the borrowed argument points at — must pin. }
  Region := FuncRegion(GenIR(Src), 'Caller');
  AssertTrue('AddRef pins global arg', Pos('_StringAddRef', Region) >= 0);
  AssertTrue('Release unpins global arg', Pos('_StringRelease', Region) >= 0);
end;

procedure TConstArgTests.TestConstArg_OwnedReturn_ConsumeOnly;
const
  Src = '''
      program P;
      procedure Sink(const S: string);
      begin
      end;
      function Mk: string;
      begin
        Result := IntToStr(7)
      end;
      procedure Caller;
      begin
        Sink(Mk())
      end;
      begin
        Caller()
      end.
      ''';
var
  Region: string;
begin
  { Mk() hands over a +1 temp; the post-call Release consumes it (this
    used to leak — the pin pair netted to zero and nobody released). }
  Region := FuncRegion(GenIR(Src), 'Caller');
  AssertEquals('no AddRef for owned-return arg', -1,
    Pos('_StringAddRef', Region));
  AssertTrue('Release consumes the owned temp',
    Pos('_StringRelease', Region) >= 0);
end;

procedure TConstArgTests.TestConstArg_Concat_Pins;
const
  Src = '''
      program P;
      procedure Sink(const S: string);
      begin
      end;
      procedure Caller(const T: string);
      begin
        Sink('a' + T)
      end;
      var L: string;
      begin
        L := 'x';
        Caller(L)
      end.
      ''';
var
  Region: string;
begin
  { _StringConcat returns an rc=0 transient: the AddRef/Release pair both
    protects it during the call and frees it afterwards. }
  Region := FuncRegion(GenIR(Src), 'Caller');
  AssertTrue('AddRef pins concat temp', Pos('_StringAddRef', Region) >= 0);
  AssertTrue('Release frees concat temp', Pos('_StringRelease', Region) >= 0);
end;

procedure TConstArgTests.TestConstArg_VarStringSibling_Pins;
const
  Src = '''
      program P;
      procedure Swapish(const A: string; var B: string);
      begin
        B := 'new'
      end;
      procedure Caller;
      var
        L: string;
      begin
        L := IntToStr(7);
        Swapish(L, L)
      end;
      begin
        Caller()
      end.
      ''';
var
  Region: string;
begin
  { B aliases L itself: the callee's write to B releases L's buffer while
    A still borrows it — A must be pinned (variable shapes always pin). }
  Region := FuncRegion(GenIR(Src), 'Caller');
  AssertTrue('AddRef pins despite local shape',
    Pos('_StringAddRef', Region) >= 0);
end;

procedure TConstArgTests.TestConstArg_AddrTakenLocal_Pins;
const
  Src = '''
      program P;
      procedure Sink(const S: string);
      begin
      end;
      procedure Caller;
      var
        L: string;
        PS: ^string;
      begin
        L := IntToStr(7);
        PS := @L;
        Sink(L);
        PS^ := 'x'
      end;
      begin
        Caller()
      end.
      ''';
var
  Region: string;
begin
  { @L escapes: a callee could release L's buffer through the pointer
    while the argument borrows it — address-taken locals must pin. }
  Region := FuncRegion(GenIR(Src), 'Caller');
  AssertTrue('AddRef pins address-taken local',
    Pos('_StringAddRef', Region) >= 0);
end;

procedure TConstArgTests.TestConstArg_CapturedLocal_Pins;
const
  Src = '''
      program P;
      procedure Sink(const S: string);
      begin
      end;
      procedure Caller;
      var
        L: string;
        procedure Nested;
        begin
          L := 'changed'
        end;
      begin
        L := IntToStr(7);
        Sink(L);
        Nested()
      end;
      begin
        Caller()
      end.
      ''';
var
  Region: string;
begin
  { L is captured by Nested, which can reassign it — a callee reachable
    from Sink could do the same through the capture; must pin. }
  Region := FuncRegion(GenIR(Src), 'Caller');
  AssertTrue('AddRef pins captured local',
    Pos('_StringAddRef', Region) >= 0);
end;

initialization
  RegisterTest(TConstArgTests);

end.
