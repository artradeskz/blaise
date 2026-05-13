{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

program TestRunner;

{$mode objfpc}{$H+}

uses
  bcl.testing,
  bcl.testing.runner.text,
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
  cp.test.repeatloop,
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
  cp.test.pchar,
  cp.test.tlist,
  cp.test.genericintfs,
  cp.test.genericdefaults,
  cp.test.genericmethodimpls,
  cp.test.tdictionary,
  cp.test.tstack,
  cp.test.tqueue,
  cp.test.tset,
  cp.test.tordereddictionary,
  cp.test.imap,
  cp.test.booleanops,
  cp.test.flowjumps,
  cp.test.multiwrite,
  cp.test.chainedfields,
  cp.test.genericconstraints,
  cp.test.weakref,
  cp.test.stringops,
  cp.test.collections,
  cp.test.caseenum,
  cp.test.sets,
  cp.test.selfhosting,
  cp.test.process,
  cp.test.openarray,
  cp.test.staticarray,
  cp.test.e2e,
  cp.test.e2e.base,
  cp.test.e2e.tstack,
  cp.test.e2e.tqueue,
  cp.test.e2e.tset,
  cp.test.e2e.tordereddictionary,
  cp.test.e2e.imap,
  cp.test.e2e.tstringlist,
  cp.test.e2e.openarray,
  cp.test.e2e.staticarray,
  cp.test.multifile,
  cp.test.constants,
  cp.test.external,
  cp.test.opdf,
  cp.test.forin,
  cp.test.genericforin,
  cp.test.proctypes,
  cp.test.overload,
  cp.test.classof,
  cp.test.publishedrtti,
  cp.test.proctypes_ofobject,
  cp.test.textblock,
  cp.test.tokenkindname;

begin
  Halt(RunAll);
end.
