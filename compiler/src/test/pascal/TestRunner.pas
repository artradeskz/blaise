{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: BSD-3-Clause
  See LICENSE file in the project root for full license terms.
}

program TestRunner;

{$mode objfpc}{$H+}

uses
  {$IFDEF UNIX}
  cthreads,
  {$ENDIF}
  Classes,
  fpcunit,
  testregistry,
  consoletestrunner,
  cp.test.lexer,
  cp.test.parser,
  cp.test.codegen,
  cp.test.symtable,
  cp.test.semantic,
  cp.test.records,
  cp.test.classes,
  cp.test.arc,
  cp.test.methods,
  cp.test.functions,
  cp.test.procs,
  cp.test.control,
  cp.test.inherit,
  cp.test.forloop,
  cp.test.exceptions,
  cp.test.units,
  cp.test.varparams,
  cp.test.vtable,
  cp.test.typetests,
  cp.test.interfaces,
  cp.test.generics,
  cp.test.properties,
  cp.test.genericfuncs,
  cp.test.pointers,
  cp.test.tlist,
  cp.test.genericintfs,
  cp.test.genericdefaults,
  cp.test.genericmethodimpls,
  cp.test.tdictionary,
  cp.test.booleanops,
  cp.test.flowjumps,
  cp.test.multiwrite,
  cp.test.chainedfields,
  cp.test.genericconstraints,
  cp.test.weakref,
  cp.test.e2e;

var
  Application: TTestRunner;

begin
  Application := TTestRunner.Create(nil);
  try
    Application.Initialize;
    Application.Title := 'Blaise Compiler Unit Tests';
    Application.Run;
  finally
    Application.Free;
  end;
end.
