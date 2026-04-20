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
  cp.test.semantic;

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
