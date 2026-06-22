{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Central registry of stdlib test units.

  Each test unit self-registers its TTestCase class in its own initialization
  section.  This unit simply pulls them all in via the uses clause, so the test
  runner program only needs to depend on this one unit.

  To add a new test suite: write a 'Foo.Tests' unit with an
  'initialization RegisterTest(TFooTests)' section, then add it to the uses
  clause below. }

unit Test.Registry;

interface

uses
  Json.Tests,
  Base64.Tests,
  Crypto.Tests,
  Sockets.Tests,
  WebSockets.Tests,
  HttpServer.Tests,
  Guid.Tests;

implementation

end.
