{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit rtl.platform;

// Blaise RTL — platform abstraction layer.
//
// TRtlPlatform is the abstract base class defining all OS-level operations.
// No {$IFDEF} directives appear anywhere in this unit or its concrete
// implementations.  Platform-specific behaviour is expressed by subclassing
// TRtlPlatform and assigning the instance to GRtlPlatform at program start.
//
// Each supported platform provides a single concrete subclass:
//   - TRtlPlatformPosix  (Linux, FreeBSD)
//   - TRtlPlatformDarwin (macOS)  — future
//   - TRtlPlatformWin32  (Windows) — future

interface

type
  TRtlPlatform = class
  public
    { File operations }
    function FileExists(const APath: string): Boolean; virtual; abstract;
    procedure DeleteFile(const APath: string); virtual; abstract;
    function RenameFile(const AOldPath, ANewPath: string): Boolean; virtual; abstract;
    function ReadFile(const APath: string): string; virtual; abstract;
    procedure WriteFile(const APath, AContent: string); virtual; abstract;
    procedure AppendFile(const APath, AContent: string); virtual; abstract;

    { Directory operations }
    function DirectoryExists(const APath: string): Boolean; virtual; abstract;
    function ForceDirectories(const APath: string): Boolean; virtual; abstract;
    function RemoveDir(const APath: string): Boolean; virtual; abstract;
    function GetCurrentDir: string; virtual; abstract;
    function SetCurrentDir(const APath: string): Boolean; virtual; abstract;

    { OS utilities }
    function GetTempDir: string; virtual; abstract;
    function GetTempFileName(const ADir, APrefix: string): string; virtual; abstract;
    function GetProcessID: Integer; virtual; abstract;
    function GetEnvVar(const AName: string): string; virtual; abstract;
    procedure Sleep(AMilliseconds: Integer); virtual; abstract;
    procedure Halt(AExitCode: Integer); virtual; abstract;

    { Process }
    function Exec(const ACmd: string): Integer; virtual; abstract;
    function ParamCount: Integer; virtual; abstract;
    function ParamStr(AIndex: Integer): string; virtual; abstract;

    { Console I/O — used by compiler-emitted WriteLn/Write }
    procedure SysWriteStr(Fd: Integer; S: Pointer); virtual; abstract;
    procedure SysWriteInt(Fd: Integer; N: Integer); virtual; abstract;
    procedure SysWriteInt64(Fd: Integer; N: Int64); virtual; abstract;
    procedure SysWriteUInt64(Fd: Integer; N: UInt64); virtual; abstract;
    procedure SysWriteDouble(Fd: Integer; V: Double); virtual; abstract;
    procedure SysWriteSingle(Fd: Integer; V: Single); virtual; abstract;
    procedure SysWriteBool(Fd: Integer; B: Boolean); virtual; abstract;
    procedure SysWriteNewline(Fd: Integer); virtual; abstract;

    { File-descriptor primitives — used by streams }
    function FdOpenRead(Path: Pointer): Integer; virtual; abstract;
    function FdOpenWrite(Path: Pointer): Integer; virtual; abstract;
    function FdOpenAppend(Path: Pointer): Integer; virtual; abstract;
    function FdRead(Fd: Integer; Buf: Pointer; Count: Integer): Integer; virtual; abstract;
    function FdWrite(Fd: Integer; Buf: Pointer; Count: Integer): Integer; virtual; abstract;
    function FdSeek(Fd: Integer; Offset: Int64; Origin: Integer): Int64; virtual; abstract;
    function FdSize(Fd: Integer): Int64; virtual; abstract;
    procedure FdClose(Fd: Integer); virtual; abstract;

    { Date/Time }
    function TimeNow: Int64; virtual; abstract;
    function TimeLocalOffsetSecs: Integer; virtual; abstract;
    procedure TimeSplit(Nanos: Int64;
      out Year, Month, Day, Hour, Min, Sec, NSec: Integer); virtual; abstract;
    function TimeJoin(Year, Month, Day,
      Hour, Min, Sec, NSec: Integer): Int64; virtual; abstract;
    function TimeIsLeapYear(Year: Integer): Integer; virtual; abstract;
    function TimeDaysInMonth(Year, Month: Integer): Integer; virtual; abstract;

    { Process management — fork/exec/pipe }
    function ProcessCreate: Pointer; virtual; abstract;
    procedure ProcessSetExe(Proc: Pointer; ExeStr: Pointer); virtual; abstract;
    procedure ProcessAddArg(Proc: Pointer; ArgStr: Pointer); virtual; abstract;
    procedure ProcessExecute(Proc: Pointer); virtual; abstract;
    function ProcessRunning(Proc: Pointer): Integer; virtual; abstract;
    function ProcessReadOutput(Proc: Pointer): Pointer; virtual; abstract;
    procedure ProcessWaitOnExit(Proc: Pointer); virtual; abstract;
    function ProcessExitCode(Proc: Pointer): Integer; virtual; abstract;
    procedure ProcessFree(Proc: Pointer); virtual; abstract;
  end;

var
  GRtlPlatform: TRtlPlatform;

implementation

end.
