{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.streams;

{ E2E tests for the Streams RTL unit (Phase 1).
  Covers file and memory streams, virtual dispatch through abstract
  bases, and ISeekable capability discovery.  Each test compiles a
  small Blaise program against the real Streams unit and verifies
  stdout. }

interface

uses
  bcl.testing, cp.test.e2e.base;

type
  TE2EStreamsTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_MemoryOutputStream_WriteAndReadBack;
    procedure TestRun_MemoryInputStream_ReadsBytesBack;
    procedure TestRun_FileStream_RoundTrip;
    procedure TestRun_VirtualDispatch_ThroughAbstractBase;
    procedure TestRun_ISeekable_Supports;
    procedure TestRun_BufferedFile_RoundTrip;
    procedure TestRun_BufferedOutput_FlushOnClose;
    procedure TestRun_FileOpen_MissingFile_Raises;
  end;

implementation

procedure TE2EStreamsTests.SetUp;
begin
  inherited SetUp;
  SetUpScratch('compiler/target/test-e2e-streams')
end;

const
  LE = #10;

  SrcMemOutRoundTrip = '''
    program P;
    uses Streams;
    var M: TMemoryOutputStream;
        Buf: array[0..4] of Byte;
    begin
      Buf[0] := 72;  Buf[1] := 101; Buf[2] := 108;
      Buf[3] := 108; Buf[4] := 111;
      M := TMemoryOutputStream.Create;
      try
        M.Write(@Buf[0], 5);
        WriteLn(M.ToString);
      finally
        M.Free
      end
    end.
    ''';

  SrcMemInRoundTrip = '''
    program P;
    uses Streams;
    var M: TMemoryInputStream;
        Buf: array[0..3] of Byte;
        N: Integer;
    begin
      M := TMemoryInputStream.Create('ABC');
      try
        N := M.Read(@Buf[0], 3);
        WriteLn(N);
        WriteLn(Buf[0]);
        WriteLn(Buf[1]);
        WriteLn(Buf[2]);
      finally
        M.Free
      end
    end.
    ''';

  { Round-trip 5 bytes through TFileOutputStream and TFileInputStream
    via the system temp directory.  Uses /tmp directly to avoid pulling
    in SysUtils path helpers from this small program. }
  SrcFileRoundTrip = '''
    program P;
    uses Streams;
    var Fout: TFileOutputStream;
        Fin:  TFileInputStream;
        Buf:  array[0..15] of Byte;
        N:    Integer;
        I:    Integer;
    begin
      for I := 0 to 4 do Buf[I] := 65 + I;
      Fout := TFileOutputStream.Create('/tmp/blaise_streams_e2e.txt');
      try
        Fout.Write(@Buf[0], 5);
      finally
        Fout.Close;
        Fout.Free
      end;
      for I := 0 to 15 do Buf[I] := 0;
      Fin := TFileInputStream.Create('/tmp/blaise_streams_e2e.txt');
      try
        N := Fin.Read(@Buf[0], 16);
        WriteLn(N);
        for I := 0 to N - 1 do WriteLn(Buf[I]);
      finally
        Fin.Close;
        Fin.Free
      end
    end.
    ''';

  { Demonstrate virtual dispatch through an abstract base.  TOutputStream
    declares Write as `virtual; abstract`; TMemoryOutputStream overrides
    it.  Calling Write on a TOutputStream-typed variable that actually
    holds a TMemoryOutputStream must reach the concrete implementation,
    not the abstract stub. }
  SrcVirtualDispatch = '''
    program P;
    uses Streams;
    var M:    TMemoryOutputStream;
        Base: TOutputStream;
        Buf:  array[0..3] of Byte;
    begin
      Buf[0] := 49; Buf[1] := 50; Buf[2] := 51; Buf[3] := 52;
      M := TMemoryOutputStream.Create;
      try
        Base := M;
        Base.Write(@Buf[0], 4);
        WriteLn(M.ToString);
      finally
        M.Free
      end
    end.
    ''';

  { Buffered round-trip through file: write 10 bytes through
    TBufferedOutputStream → TFileOutputStream, read them back through
    TBufferedInputStream → TFileInputStream.  Verifies the wrappers
    correctly forward to the inner via virtual dispatch (the abstract
    TInputStream/TOutputStream slots route through the vtable to the
    file impls). }
  SrcBufferedFileRoundTrip = '''
    program P;
    uses Streams;
    var Fout: TFileOutputStream;
        Bout: TBufferedOutputStream;
        Fin:  TFileInputStream;
        Bin:  TBufferedInputStream;
        Buf:  array[0..31] of Byte;
        N, I: Integer;
    begin
      for I := 0 to 9 do Buf[I] := 65 + I;
      Fout := TFileOutputStream.Create('/tmp/blaise_buf_e2e.txt');
      Bout := TBufferedOutputStream.Create(Fout);
      try
        Bout.Write(@Buf[0], 10);
      finally
        Bout.Close;
        Bout.Free
      end;
      for I := 0 to 31 do Buf[I] := 0;
      Fin := TFileInputStream.Create('/tmp/blaise_buf_e2e.txt');
      Bin := TBufferedInputStream.Create(Fin);
      try
        N := Bin.Read(@Buf[0], 32);
        WriteLn(N);
        for I := 0 to N - 1 do WriteLn(Buf[I])
      finally
        Bin.Close;
        Bin.Free
      end
    end.
    ''';

  { Buffered output with the default 8 KiB buffer; the 5 bytes never
    fill the buffer, so they only reach the file when Close fires
    Flush.  Confirms Close-flushes-on-exit. }
  SrcBufferedFlushOnClose = '''
    program P;
    uses Streams;
    var Fout: TFileOutputStream;
        Bout: TBufferedOutputStream;
        Fin:  TFileInputStream;
        Buf:  array[0..7] of Byte;
        N, I: Integer;
    begin
      Buf[0] := 1; Buf[1] := 2; Buf[2] := 3;
      Buf[3] := 4; Buf[4] := 5;
      Fout := TFileOutputStream.Create('/tmp/blaise_flush_e2e.bin');
      Bout := TBufferedOutputStream.Create(Fout);
      try
        Bout.Write(@Buf[0], 5)
        { intentionally no explicit Flush — Close must drain the buffer }
      finally
        Bout.Close;
        Bout.Free
      end;
      for I := 0 to 7 do Buf[I] := 0;
      Fin := TFileInputStream.Create('/tmp/blaise_flush_e2e.bin');
      try
        N := Fin.Read(@Buf[0], 8);
        WriteLn(N);
        for I := 0 to N - 1 do WriteLn(Buf[I])
      finally
        Fin.Close;
        Fin.Free
      end
    end.
    ''';

  { Opening a non-existent file for reading must raise EStreamError;
    the exception handler prints a recognisable token. }
  SrcOpenMissingRaises = '''
    program P;
    uses Streams, SysUtils;
    var Fin: TFileInputStream;
    begin
      try
        Fin := TFileInputStream.Create('/tmp/blaise_does_not_exist_x42.bin');
        WriteLn('unreachable');
        Fin.Free
      except
        on E: EStreamError do
          WriteLn('caught')
      end
    end.
    ''';

  { TMemoryOutputStream implements ISeekable; Supports() must return
    True and let us query the buffered byte count. }
  SrcSupportsISeekable = '''
    program P;
    uses Streams;
    var M:   TMemoryOutputStream;
        Sk:  ISeekable;
        Buf: array[0..7] of Byte;
    begin
      Buf[0] := 1; Buf[1] := 2; Buf[2] := 3;
      M := TMemoryOutputStream.Create;
      try
        M.Write(@Buf[0], 3);
        if Supports(M, ISeekable, Sk) then
          WriteLn(Sk.Size)
        else
          WriteLn('no');
      finally
        M.Free
      end
    end.
    ''';

procedure TE2EStreamsTests.TestRun_MemoryOutputStream_WriteAndReadBack;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcMemOutRoundTrip, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('memory stream round-trip', 'Hello' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_MemoryInputStream_ReadsBytesBack;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcMemInRoundTrip, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('read 3 bytes A B C',
    '3' + LE + '65' + LE + '66' + LE + '67' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_FileStream_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcFileRoundTrip, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('file round-trip ABCDE',
    '5' + LE + '65' + LE + '66' + LE + '67' + LE + '68' + LE + '69' + LE,
    Output)
end;

procedure TE2EStreamsTests.TestRun_VirtualDispatch_ThroughAbstractBase;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcVirtualDispatch, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('virtual dispatch reaches concrete Write', '1234' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_ISeekable_Supports;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcSupportsISeekable, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('ISeekable.Size = 3', '3' + LE, Output)
end;

procedure TE2EStreamsTests.TestRun_BufferedFile_RoundTrip;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcBufferedFileRoundTrip, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('buffered round-trip A..J',
    '10' + LE + '65' + LE + '66' + LE + '67' + LE + '68' + LE + '69' + LE +
    '70' + LE + '71' + LE + '72' + LE + '73' + LE + '74' + LE,
    Output)
end;

procedure TE2EStreamsTests.TestRun_BufferedOutput_FlushOnClose;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcBufferedFlushOnClose, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('Close drained the buffer',
    '5' + LE + '1' + LE + '2' + LE + '3' + LE + '4' + LE + '5' + LE,
    Output)
end;

procedure TE2EStreamsTests.TestRun_FileOpen_MissingFile_Raises;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcOpenMissingRaises, Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('EStreamError caught', 'caught' + LE, Output)
end;

initialization
  RegisterTest(TE2EStreamsTests)

end.
