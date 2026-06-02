{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.codegen.native.x86_64;

{ x86_64 (System V AMD64 ABI) backend for the native code generator.

  Emits AT&T-syntax assembly text (fed to `as`/`cc`, like QBE's .s output),
  using a naive stack-slot register allocator first for correctness, with
  optimisation deferred behind the same seam.

  Currently a SHELL (milestone M0b): the class exists and registers via
  blaise.codegen.native.CreateNativeBackend so target selection resolves, but
  instruction selection / register allocation / assembly emission are not yet
  implemented. }

interface

uses
  blaise.codegen.native.backend, blaise.codegen.target;

type
  TX86_64Backend = class(TNativeBackend)
  public
    constructor Create(const ATarget: TTargetDesc); override;
  end;

implementation

constructor TX86_64Backend.Create(const ATarget: TTargetDesc);
begin
  inherited Create(ATarget);
end;

end.
