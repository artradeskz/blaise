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
  cp.test.generics;

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
