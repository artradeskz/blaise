{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.driver;

{ Unit tests for the backend-driver option contract (Steps 2-5 of
  docs/backend-options-design.adoc).

  These exercise the real registered driver singletons (the QBE and native
  drivers, pulled in via the uses clause so their initialization blocks
  register them).  A test-only stub driver is deliberately avoided: it would
  need a slot in the fixed array[0..1] registry and muddy the real
  singletons.  Testing the actual drivers is both possible and more honest. }

interface

uses
  SysUtils, Classes, blaise.testing,
  blaise.codegen.driver,
  blaise.codegen.qbe.driver,      { registers the QBE driver }
  blaise.codegen.native.driver;   { registers the native driver }

type
  TBackendDriverContractTests = class(TTestCase)
  published
    { ClaimsEmitIR selection policy. }
    procedure TestQBE_ClaimsEmitIR_True;
    procedure TestNative_ClaimsEmitIR_False;

    { Native owns --assembler via AcceptOption. }
    procedure TestNative_AcceptInternal_ConsumesValue_SetsFlag;
    procedure TestNative_AcceptExternal_ConsumesValue_ClearsFlag;
    procedure TestNative_AcceptBogus_ConsumesValue_FlagsBad;
    procedure TestNative_AcceptUnknownFlag_Unknown;

    { QBE does not own --assembler. }
    procedure TestQBE_AcceptAssembler_Unknown;

    { ValidateOptions. }
    procedure TestNative_Validate_BadValue_NonEmpty;
    procedure TestNative_Validate_GoodValue_Empty;

    { DescribeOptions surfaces the native flag. }
    procedure TestNative_DescribeOptions_MentionsAssembler;

    { FormatFlagLine column helper. }
    procedure TestFormatFlagLine_Indents_And_Pads;
  end;

implementation

procedure TBackendDriverContractTests.TestQBE_ClaimsEmitIR_True;
begin
  AssertTrue('QBE must claim --emit-ir',
    GetDriver(bkQBE).ClaimsEmitIR());
end;

procedure TBackendDriverContractTests.TestNative_ClaimsEmitIR_False;
begin
  AssertFalse('native must not claim --emit-ir (its IR is --emit-asm)',
    GetDriver(bkNative).ClaimsEmitIR());
end;

procedure TBackendDriverContractTests.TestNative_AcceptInternal_ConsumesValue_SetsFlag;
var
  Opts: TBackendOpts;
  R: TOptionAccept;
begin
  Opts := TBackendOpts.Create();
  try
    R := GetDriver(bkNative).AcceptOption('--assembler', 'internal', Opts);
    AssertEquals('internal must consume a value', Ord(oaConsumedValue), Ord(R));
    AssertTrue('internal must set UseInternalAsm', Opts.UseInternalAsm);
    AssertFalse('internal is a valid value', Opts.AssemblerChoiceBad);
  finally
    Opts.Free();
  end;
end;

procedure TBackendDriverContractTests.TestNative_AcceptExternal_ConsumesValue_ClearsFlag;
var
  Opts: TBackendOpts;
  R: TOptionAccept;
begin
  Opts := TBackendOpts.Create();
  try
    R := GetDriver(bkNative).AcceptOption('--assembler', 'external', Opts);
    AssertEquals('external must consume a value', Ord(oaConsumedValue), Ord(R));
    AssertFalse('external must clear UseInternalAsm', Opts.UseInternalAsm);
    AssertFalse('external is a valid value', Opts.AssemblerChoiceBad);
  finally
    Opts.Free();
  end;
end;

procedure TBackendDriverContractTests.TestNative_AcceptBogus_ConsumesValue_FlagsBad;
var
  Opts: TBackendOpts;
  R: TOptionAccept;
begin
  Opts := TBackendOpts.Create();
  try
    { A bad value is still CONSUMED here; ValidateOptions rejects it later. }
    R := GetDriver(bkNative).AcceptOption('--assembler', 'bogus', Opts);
    AssertEquals('bogus must consume a value', Ord(oaConsumedValue), Ord(R));
    AssertTrue('bogus must be flagged bad', Opts.AssemblerChoiceBad);
  finally
    Opts.Free();
  end;
end;

procedure TBackendDriverContractTests.TestNative_AcceptUnknownFlag_Unknown;
var
  Opts: TBackendOpts;
begin
  Opts := TBackendOpts.Create();
  try
    AssertEquals('an unowned flag is oaUnknown', Ord(oaUnknown),
      Ord(GetDriver(bkNative).AcceptOption('--nope', '', Opts)));
  finally
    Opts.Free();
  end;
end;

procedure TBackendDriverContractTests.TestQBE_AcceptAssembler_Unknown;
var
  Opts: TBackendOpts;
begin
  Opts := TBackendOpts.Create();
  try
    { QBE does not own --assembler — Chain-of-Responsibility asymmetry. }
    AssertEquals('QBE must not own --assembler', Ord(oaUnknown),
      Ord(GetDriver(bkQBE).AcceptOption('--assembler', 'internal', Opts)));
  finally
    Opts.Free();
  end;
end;

procedure TBackendDriverContractTests.TestNative_Validate_BadValue_NonEmpty;
var
  Opts: TBackendOpts;
begin
  Opts := TBackendOpts.Create();
  try
    GetDriver(bkNative).AcceptOption('--assembler', 'bogus', Opts);
    AssertTrue('bad --assembler must produce a diagnostic',
      GetDriver(bkNative).ValidateOptions(Opts) <> '');
  finally
    Opts.Free();
  end;
end;

procedure TBackendDriverContractTests.TestNative_Validate_GoodValue_Empty;
var
  Opts: TBackendOpts;
begin
  Opts := TBackendOpts.Create();
  try
    GetDriver(bkNative).AcceptOption('--assembler', 'internal', Opts);
    AssertEquals('valid --assembler must validate clean', '',
      GetDriver(bkNative).ValidateOptions(Opts));
  finally
    Opts.Free();
  end;
end;

procedure TBackendDriverContractTests.TestNative_DescribeOptions_MentionsAssembler;
var
  Lines: TStringList;
  I: Integer;
  Found: Boolean;
begin
  Lines := TStringList.Create();
  try
    GetDriver(bkNative).DescribeOptions(Lines);
    Found := False;
    for I := 0 to Lines.Count - 1 do
      if Pos('--assembler', Lines.Strings[I]) >= 0 then
        Found := True;
    AssertTrue('native DescribeOptions must mention --assembler', Found);
  finally
    Lines.Free();
  end;
end;

procedure TBackendDriverContractTests.TestFormatFlagLine_Indents_And_Pads;
var
  Line: string;
begin
  Line := FormatFlagLine('--x <v>', 'a description');
  { Two-space indent, flag, then the description after column padding. }
  AssertEquals('must start with two-space indent', '  ', Copy(Line, 0, 2));
  AssertTrue('must contain the flag', Pos('--x <v>', Line) >= 0);
  AssertTrue('must contain the description', Pos('a description', Line) >= 0);
  AssertTrue('description must come after the flag',
    Pos('a description', Line) > Pos('--x <v>', Line));
end;

{ ---- Registration ---- }

initialization
  RegisterTest(TBackendDriverContractTests);

end.
