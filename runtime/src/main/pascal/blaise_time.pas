{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{
  Blaise RTL — date/time primitives.

  Replaces blaise_time.c with direct POSIX libc bindings.
  All arithmetic is in UTC; timezone-offset application is done in Pascal
  (dateutils.pas in stdlib/).
}

unit blaise_time;

{$mode objfpc}{$H+}

interface

function _TimeNow: Int64;
function _TimeLocalOffsetSecs: Integer;
procedure _TimeSplit(Nanos: Int64;
                     out Year, Month, Day: Integer;
                     out Hour, Min, Sec: Integer;
                     out NSec: Integer);
function _TimeJoin(Year, Month, Day: Integer;
                   Hour, Min, Sec: Integer;
                   NSec: Integer): Int64;
function _TimeIsLeapYear(Year: Integer): Integer;
function _TimeDaysInMonth(Year, Month: Integer): Integer;

{ All POSIX libc bindings in the interface section (Blaise requirement). }

type
  TTimeSpec = record
    Sec:  Int64;
    NSec: Int64;
  end;

  { struct tm — POSIX layout on Linux x86_64 }
  TTm = record
    Sec:     Integer;   { tm_sec   }
    Min:     Integer;   { tm_min   }
    Hour:    Integer;   { tm_hour  }
    MDay:    Integer;   { tm_mday  }
    Mon:     Integer;   { tm_mon   }
    Year:    Integer;   { tm_year  }
    WDay:    Integer;   { tm_wday  }
    YDay:    Integer;   { tm_yday  }
    IsDST:   Integer;   { tm_isdst }
    GmtOff:  Int64;     { tm_gmtoff (POSIX extension) }
    Zone:    Pointer;   { tm_zone  }
  end;
  PTm = ^TTm;

{ POSIX: CLOCK_REALTIME = 0 }
function  libc_clock_gettime(ClockId: Integer; Ts: Pointer): Integer; external name 'clock_gettime';
function  libc_time(T: Pointer): Int64;                                external name 'time';
function  libc_localtime_r(T: Pointer; Tm: PTm): PTm;                 external name 'localtime_r';
function  libc_gmtime_r(T: Pointer; Tm: PTm): PTm;                    external name 'gmtime_r';
function  libc_timegm(Tm: PTm): Int64;                                 external name 'timegm';

implementation

const
  NS_PER_SEC    = 1000000000;
  CLOCK_REALTIME = 0;

function _TimeNow: Int64;
var
  Ts: TTimeSpec;
begin
  libc_clock_gettime(CLOCK_REALTIME, @Ts);
  Result := Ts.Sec * NS_PER_SEC + Ts.NSec;
end;

function _TimeLocalOffsetSecs: Integer;
var
  T:  Int64;
  Lt: TTm;
begin
  T := libc_time(nil);
  libc_localtime_r(@T, @Lt);
  Result := Integer(Lt.GmtOff);
end;

procedure _TimeSplit(Nanos: Int64;
                     out Year, Month, Day: Integer;
                     out Hour, Min, Sec: Integer;
                     out NSec: Integer);
var
  WholeSec: Int64;
  NanoPart: Integer;
  T:        Int64;
  Tm:       TTm;
begin
  WholeSec := Nanos div NS_PER_SEC;
  NanoPart := Integer(Nanos mod NS_PER_SEC);
  if NanoPart < 0 then
  begin
    Dec(WholeSec);
    Inc(NanoPart, Integer(NS_PER_SEC));
  end;
  T := WholeSec;
  libc_gmtime_r(@T, @Tm);
  Year  := Tm.Year + 1900;
  Month := Tm.Mon  + 1;
  Day   := Tm.MDay;
  Hour  := Tm.Hour;
  Min   := Tm.Min;
  Sec   := Tm.Sec;
  NSec  := NanoPart;
end;

function _TimeJoin(Year, Month, Day: Integer;
                   Hour, Min, Sec: Integer;
                   NSec: Integer): Int64;
var
  Tm:    TTm;
  Epoch: Int64;
  I:     Integer;
  TB:    PChar;
begin
  { zero-fill the record }
  TB := PChar(@Tm);
  for I := 0 to SizeOf(TTm) - 1 do TB[I] := #0;
  Tm.Year  := Year  - 1900;
  Tm.Mon   := Month - 1;
  Tm.MDay  := Day;
  Tm.Hour  := Hour;
  Tm.Min   := Min;
  Tm.Sec   := Sec;
  Epoch := libc_timegm(@Tm);
  Result := Epoch * NS_PER_SEC + Int64(NSec);
end;

function _TimeIsLeapYear(Year: Integer): Integer;
begin
  if ((Year mod 4 = 0) and ((Year mod 100 <> 0) or (Year mod 400 = 0))) then
    Result := 1
  else
    Result := 0;
end;

function _TimeDaysInMonth(Year, Month: Integer): Integer;
const
  Days: array[1..12] of Integer = (31,28,31,30,31,30,31,31,30,31,30,31);
begin
  if (Month = 2) and (_TimeIsLeapYear(Year) = 1) then
    Result := 29
  else
    Result := Days[Month];
end;

end.
