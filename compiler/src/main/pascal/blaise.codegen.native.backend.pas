{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.native.backend;

{ Abstract per-architecture machine-code lowering base for the native code
  generator.

  Lives in its own unit (separate from blaise.codegen.native) so the concrete
  per-CPU backends — blaise.codegen.native.x86_64 etc. — can subclass it
  without a circular dependency back to the driver unit that constructs them.

  A concrete subclass implements instruction selection, register allocation,
  ABI lowering, and assembly printing for one target CPU.  Shared, non-abstract
  helpers (the naive stack-slot allocator, cross-target emit utilities) will be
  added here as the backend grows. }

interface

uses
  SysUtils, blaise.codegen.target;

type
  ENativeCodeGenError = class(Exception);

  TNativeBackend = class
  protected
    FTarget: TTargetDesc;
  public
    constructor Create(const ATarget: TTargetDesc); virtual;
    property Target: TTargetDesc read FTarget;
  end;

  TNativeBackendClass = class of TNativeBackend;

implementation

constructor TNativeBackend.Create(const ATarget: TTargetDesc);
begin
  inherited Create;
  FTarget := ATarget;
end;

end.
