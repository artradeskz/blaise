{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uCodeGen;

{ Backend-neutral code-generator contract.

  Both the QBE backend (uCodeGenQBE.TCodeGenQBE) and the native backend
  (blaise.codegen.native.TCodeGenNative) implement ICodeGen, so the
  driver in Blaise.pas runs one codegen sequence against the interface
  rather than branching per backend.

  ICodeGen covers only what the driver invokes polymorphically.  Backend-
  specific configuration (e.g. the native backend's SetTarget) stays on the
  concrete class and is applied before the object is assigned to an ICodeGen
  variable.

  Lifetime: ICodeGen is ARC-managed.  Assign a freshly-created concrete
  codegen to an ICodeGen variable and let it go out of scope — no manual
  Free.  (Mixing an explicit Free with ARC would double-free.) }

interface

uses
  uAST, uSymbolTable;

type
  ICodeGen = interface
    { Single-file program compilation: reset output and emit all IR. }
    procedure Generate(AProg: TProgram);

    { Single-unit compilation in isolation. }
    procedure GenerateUnit(AUnit: TUnit);

    { Provide the global symbol table before AppendUnit/AppendProgram so
      class typeinfo, vtable, and field-cleanup data can be emitted. }
    procedure SetSymbolTable(ASymTable: TSymbolTable);

    { Enable backend debug/leak-tracking behaviour. }
    procedure SetDebugMode(AEnabled: Boolean);

    { Enable OPDF-debug code shaping.  When on, the backend emits class vtables
      as exported (global) symbols so the separately-assembled .opdf section can
      reference them across object files (the OPDF class record stores each
      class's VMTAddress for runtime dynamic-type resolution).  Off by default,
      so normal builds are byte-for-byte unchanged. }
    procedure SetOpdfMode(AEnabled: Boolean);

    { Multi-unit compilation: append unit IR to existing output without
      resetting the output buffer or string-literal table. }
    procedure AppendUnit(AUnit: TUnit);

    { Append program IR after one or more AppendUnit calls. }
    procedure AppendProgram(AProg: TProgram);

    { Retrieve the complete generated output (QBE IR text for the QBE
      backend; target assembly text for the native backend). }
    function GetOutput: string;
  end;

implementation

end.
