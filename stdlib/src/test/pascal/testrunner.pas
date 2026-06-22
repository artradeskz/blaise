{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Test runner for the Blaise standard library.

  Pulls in every test unit via Test.Registry (each self-registers via its
  initialization section), then runs them all with the text runner.  Exits 0
  when everything passes, 1 otherwise, so it is CI-friendly.

  Build (from the repo root):
    blaise --source stdlib/src/test/pascal/testrunner.pas --output testrunner \
      --unit-path stdlib/src/main/pascal \
      --unit-path runtime/src/main/pascal \
      \
      --unit-path stdlib/src/test/pascal
    ./testrunner

  Supports --suite <Class> / --suite <Class.Method> filtering (handled by RunAll). }

program TestRunner;

uses
  blaise.testing,
  blaise.testing.runner.text,
  Test.Registry;

begin
  Halt(RunAll());
end.
