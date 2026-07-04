{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.caseenum;

{ E2E tests for case statements and enum types. }

interface

uses
  blaise.testing, classes, cp.test.e2e.base;

type
  [Threaded]
  TE2ECaseEnumTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_Case_IntegerBranch;
    procedure TestRun_Case_ElseBranch;
    procedure TestRun_Enum_OrdinalValues;
    procedure TestRun_Enum_InCase;
    procedure TestRun_Enum_ExplicitOrdinals;
    procedure TestRun_Enum_AutoContinueAfterExplicit;
    procedure TestRun_Enum_ExplicitInCase;
  end;

implementation

procedure TE2ECaseEnumTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-caseenum');
end;

const
  SrcCaseInt =
    '''
        program P;
        var N: Integer;
        begin
          N := 2;
          case N of
            1: WriteLn(11);
            2: WriteLn(22);
            3: WriteLn(33)
          end
        end.
        ''';

  SrcCaseElse =
    '''
        program P;
        var N: Integer;
        begin
          N := 7;
          case N of
            1: WriteLn(1);
            2: WriteLn(2)
          else
            WriteLn(99)
          end
        end.
        ''';

  SrcEnumOrdinal =
    '''
        program P;
        type
          TColor = (cRed, cGreen, cBlue);
        var C: TColor;
        begin
          C := cRed;   WriteLn(C);
          C := cGreen; WriteLn(C);
          C := cBlue;  WriteLn(C)
        end.
        ''';

  SrcEnumCase =
    '''
        program P;
        type
          TDir = (dNorth, dSouth, dEast, dWest);
        var D: TDir;
        begin
          D := dEast;
          case D of
            dNorth: WriteLn(0);
            dSouth: WriteLn(1);
            dEast:  WriteLn(2);
            dWest:  WriteLn(3)
          end
        end.
        ''';

procedure TE2ECaseEnumTests.TestRun_Case_IntegerBranch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcCaseInt, '22' + LineEnding, 0);
end;

procedure TE2ECaseEnumTests.TestRun_Case_ElseBranch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcCaseElse, '99' + LineEnding, 0);
end;

procedure TE2ECaseEnumTests.TestRun_Enum_OrdinalValues;
var Output: string; RCode: Integer; Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcEnumOrdinal, Output, RCode));
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('cRed=0',   '0', Lines.Strings[0]);
    AssertEquals('cGreen=1', '1', Lines.Strings[1]);
    AssertEquals('cBlue=2',  '2', Lines.Strings[2]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ECaseEnumTests.TestRun_Enum_InCase;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcEnumCase, '2' + LineEnding, 0);
end;

const
  SrcExplicitOrdinals =
    '''
        program P;
        type
          TStatus = (Idle=10, Running=20, Done=30);
        var S: TStatus;
        begin
          S := Idle;    WriteLn(S);
          S := Running; WriteLn(S);
          S := Done;    WriteLn(S)
        end.
        ''';

  SrcAutoContinue =
    '''
        program P;
        type
          TCode = (A=100, B, C);
        var X: TCode;
        begin
          X := A; WriteLn(X);
          X := B; WriteLn(X);
          X := C; WriteLn(X)
        end.
        ''';

  SrcExplicitInCase =
    '''
        program P;
        type
          THTTPStatus = (OK=200, NotFound=404, ServerError=500);
        var S: THTTPStatus;
        begin
          S := NotFound;
          case S of
            200: WriteLn('ok');
            404: WriteLn('not found');
            500: WriteLn('server error')
          else
            WriteLn('unknown')
          end
        end.
        ''';

procedure TE2ECaseEnumTests.TestRun_Enum_ExplicitOrdinals;
var
  Output: string;
  RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcExplicitOrdinals, Output, RCode));
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Idle=10',    '10', Lines.Strings[0]);
    AssertEquals('Running=20', '20', Lines.Strings[1]);
    AssertEquals('Done=30',    '30', Lines.Strings[2]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ECaseEnumTests.TestRun_Enum_AutoContinueAfterExplicit;
var
  Output: string;
  RCode: Integer;
  Lines: TStringList;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcAutoContinue, Output, RCode));
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('A=100', '100', Lines.Strings[0]);
    AssertEquals('B=101', '101', Lines.Strings[1]);
    AssertEquals('C=102', '102', Lines.Strings[2]);
  finally
    Lines.Free();
  end;
end;

procedure TE2ECaseEnumTests.TestRun_Enum_ExplicitInCase;
var
  Output: string;
  RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcExplicitInCase, Output, RCode));
  AssertEquals('NotFound=404 matches case 404', 'not found', Trim(Output));
end;

initialization
  RegisterTest(TE2ECaseEnumTests);

end.
