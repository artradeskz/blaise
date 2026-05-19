{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Build driver for blaise_weak.pas — used only by the RTL Makefile to compile
  the unit into an object file for inclusion in blaise_rtl.a.  The program
  body is stripped from the IR before assembly; only the unit functions are
  archived. }

program blaise_weak_build_driver;

uses
  blaise_weak;

begin
end.
