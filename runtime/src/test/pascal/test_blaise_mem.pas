{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ punit tests for blaise_mem — the Pascal memory allocator.

  These tests exercise the allocator at the raw pointer level, below
  the string and ARC subsystems.  punit is the correct framework here
  because blaise_mem has zero dependency on stdlib or ARC.

  Build:
    blaise --source runtime/src/test/pascal/test_blaise_mem.pas \
           --unit-path runtime/src/main/pascal \
           --unit-path runtime/src/test/pascal \
           --emit-ir > /tmp/test_mem.ssa
    vendor/qbe/qbe -o /tmp/test_mem.s /tmp/test_mem.ssa
    gcc -o /tmp/test_mem /tmp/test_mem.s compiler/target/blaise_rtl.a
    /tmp/test_mem -v
}

program test_blaise_mem;

uses
  punit, blaise_mem;

{ ------------------------------------------------------------------ }
{ Test: basic GetMem returns non-nil                                   }
{ ------------------------------------------------------------------ }
function Test_GetMem_Basic: string;
var
  P: Pointer;
begin
  P := _BlaiseGetMem(64);
  AssertNotNull('GetMem(64) returns non-nil', P);
  _BlaiseFreeMem(P);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: GetMem(0) returns nil                                          }
{ ------------------------------------------------------------------ }
function Test_GetMem_Zero: string;
var
  P: Pointer;
begin
  P := _BlaiseGetMem(0);
  AssertNull('GetMem(0) returns nil', P);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: allocated memory is writable and readable                      }
{ ------------------------------------------------------------------ }
function Test_ReadWrite: string;
var
  P: PChar;
begin
  P := PChar(_BlaiseGetMem(16));
  AssertNotNull('alloc for read/write', Pointer(P));
  P[0] := 65;
  P[1] := 66;
  P[2] := 67;
  P[3] := 0;
  AssertEquals('written byte 0', 65, Integer(P[0]));
  AssertEquals('written byte 1', 66, Integer(P[1]));
  AssertEquals('written byte 2', 67, Integer(P[2]));
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: multiple allocations return distinct pointers                  }
{ ------------------------------------------------------------------ }
function Test_Distinct_Pointers: string;
var
  A, B, C: Pointer;
begin
  A := _BlaiseGetMem(32);
  B := _BlaiseGetMem(32);
  C := _BlaiseGetMem(32);
  AssertNotNull('A non-nil', A);
  AssertNotNull('B non-nil', B);
  AssertNotNull('C non-nil', C);
  AssertDiffers('A <> B', A, B);
  AssertDiffers('A <> C', A, C);
  AssertDiffers('B <> C', B, C);
  _BlaiseFreeMem(C);
  _BlaiseFreeMem(B);
  _BlaiseFreeMem(A);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: FreeMem(nil) is safe (no-op)                                   }
{ ------------------------------------------------------------------ }
function Test_FreeMem_Nil: string;
begin
  _BlaiseFreeMem(nil);
  AssertPassed;
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: ReallocMem grows allocation                                    }
{ ------------------------------------------------------------------ }
function Test_ReallocMem_Grow: string;
var
  P: PChar;
begin
  P := PChar(_BlaiseGetMem(8));
  AssertNotNull('initial alloc', Pointer(P));
  P[0] := 72;
  P[1] := 73;
  P := PChar(_BlaiseReallocMem(Pointer(P), 64));
  AssertNotNull('realloc result', Pointer(P));
  AssertEquals('byte 0 preserved', 72, Integer(P[0]));
  AssertEquals('byte 1 preserved', 73, Integer(P[1]));
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: ReallocMem(nil, N) acts like GetMem                            }
{ ------------------------------------------------------------------ }
function Test_ReallocMem_FromNil: string;
var
  P: Pointer;
begin
  P := _BlaiseReallocMem(nil, 32);
  AssertNotNull('realloc from nil', P);
  _BlaiseFreeMem(P);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: ReallocMem(P, 0) acts like FreeMem                             }
{ ------------------------------------------------------------------ }
function Test_ReallocMem_ToZero: string;
var
  P: Pointer;
begin
  P := _BlaiseGetMem(32);
  AssertNotNull('initial alloc', P);
  P := _BlaiseReallocMem(P, 0);
  AssertNull('realloc to 0 returns nil', P);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: small allocation (8 bytes) — exercises small-block path        }
{ ------------------------------------------------------------------ }
function Test_Small_Alloc: string;
var
  P: PChar;
begin
  P := PChar(_BlaiseGetMem(8));
  AssertNotNull('small alloc', Pointer(P));
  P[0] := 42;
  AssertEquals('small alloc writable', 42, Integer(P[0]));
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: large allocation (1 MB) — exercises mmap direct path           }
{ ------------------------------------------------------------------ }
function Test_Large_Alloc: string;
var
  P: PChar;
  Size: Integer;
begin
  Size := 1024 * 1024;
  P := PChar(_BlaiseGetMem(Size));
  AssertNotNull('large alloc', Pointer(P));
  P[0] := 1;
  P[Size - 1] := 2;
  AssertEquals('large alloc first byte', 1, Integer(P[0]));
  AssertEquals('large alloc last byte', 2, Integer(P[Size - 1]));
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: alloc-free-alloc reuse (freelist)                               }
{ ------------------------------------------------------------------ }
function Test_Reuse_After_Free: string;
var
  A, B: Pointer;
begin
  A := _BlaiseGetMem(64);
  _BlaiseFreeMem(A);
  B := _BlaiseGetMem(64);
  AssertNotNull('reuse alloc', B);
  _BlaiseFreeMem(B);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: many small allocations (stress test)                            }
{ ------------------------------------------------------------------ }
function Test_Many_Small_Allocs: string;
const
  Count = 1000;
var
  I: Integer;
  P: Pointer;
begin
  for I := 0 to Count - 1 do
  begin
    P := _BlaiseGetMem(24);
    AssertNotNull('alloc ' + IntToStr(I), P);
    _BlaiseFreeMem(P);
  end;
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: various size classes                                            }
{ ------------------------------------------------------------------ }
function Test_Size_Classes: string;
var
  P: Pointer;
begin
  P := _BlaiseGetMem(1);
  AssertNotNull('1 byte', P);
  _BlaiseFreeMem(P);

  P := _BlaiseGetMem(16);
  AssertNotNull('16 bytes', P);
  _BlaiseFreeMem(P);

  P := _BlaiseGetMem(128);
  AssertNotNull('128 bytes', P);
  _BlaiseFreeMem(P);

  P := _BlaiseGetMem(1024);
  AssertNotNull('1024 bytes', P);
  _BlaiseFreeMem(P);

  P := _BlaiseGetMem(4096);
  AssertNotNull('4096 bytes', P);
  _BlaiseFreeMem(P);

  P := _BlaiseGetMem(65536);
  AssertNotNull('65536 bytes', P);
  _BlaiseFreeMem(P);

  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: alignment — returned pointer is 8-byte aligned                 }
{ ------------------------------------------------------------------ }
function Test_Alignment: string;
var
  P: Pointer;
  Addr: PtrUInt;
begin
  P := _BlaiseGetMem(7);
  AssertNotNull('alloc for alignment test', P);
  Addr := PtrUInt(P);
  AssertEquals('8-byte aligned', 0, Integer(Addr and 7));
  _BlaiseFreeMem(P);

  P := _BlaiseGetMem(1);
  AssertNotNull('alloc for alignment test (1 byte)', P);
  Addr := PtrUInt(P);
  AssertEquals('8-byte aligned (1 byte)', 0, Integer(Addr and 7));
  _BlaiseFreeMem(P);

  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Helper: fill N bytes of P with a known pattern based on Seed         }
{ ------------------------------------------------------------------ }
procedure FillPattern(P: PChar; N: Integer; Seed: Integer);
var
  I, V: Integer;
begin
  for I := 0 to N - 1 do
  begin
    V := (I + Seed) and $FF;
    P[I] := V;
  end;
end;

{ ------------------------------------------------------------------ }
{ Helper: check first N bytes of P match the pattern                   }
{ ------------------------------------------------------------------ }
function CheckPattern(P: PChar; N: Integer; Seed: Integer): Integer;
var
  I: Integer;
begin
  Result := -1;
  for I := 0 to N - 1 do
    if Integer(P[I]) <> ((I + Seed) and $FF) then
    begin
      Result := I;
      Exit;
    end;
end;

{ ------------------------------------------------------------------ }
{ Test: size-class boundaries — every boundary, +1 over, -1 under     }
{ ------------------------------------------------------------------ }
function Test_SizeClass_Boundaries: string;
var
  Classes: array[0..7] of Integer;
  I: Integer;
  P: Pointer;
  Size: Integer;
begin
  Classes[0] := 16; Classes[1] := 32; Classes[2] := 64; Classes[3] := 128;
  Classes[4] := 256; Classes[5] := 512; Classes[6] := 1024; Classes[7] := 2048;
  for I := 0 to 7 do
  begin
    Size := Classes[I];
    P := _BlaiseGetMem(Size);
    AssertNotNull('exact ' + IntToStr(Size), P);
    _BlaiseFreeMem(P);

    if Size > 1 then
    begin
      P := _BlaiseGetMem(Size - 1);
      AssertNotNull('exact-1 ' + IntToStr(Size - 1), P);
      _BlaiseFreeMem(P);
    end;

    P := _BlaiseGetMem(Size + 1);
    AssertNotNull('exact+1 ' + IntToStr(Size + 1), P);
    _BlaiseFreeMem(P);
  end;
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: realloc within same size class preserves bytes and is cheap    }
{ ------------------------------------------------------------------ }
function Test_Realloc_SameClass: string;
var
  P: PChar;
  Bad: Integer;
begin
  P := PChar(_BlaiseGetMem(16));
  AssertNotNull('alloc 16', Pointer(P));
  FillPattern(P, 16, 11);
  P := PChar(_BlaiseReallocMem(Pointer(P), 12));
  AssertNotNull('shrink within class', Pointer(P));
  Bad := CheckPattern(P, 12, 11);
  AssertEquals('shrink preserves bytes', -1, Bad);
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: realloc shrink across classes preserves bytes                  }
{ ------------------------------------------------------------------ }
function Test_Realloc_Shrink: string;
var
  P: PChar;
  Bad: Integer;
begin
  P := PChar(_BlaiseGetMem(256));
  AssertNotNull('alloc 256', Pointer(P));
  FillPattern(P, 256, 7);
  P := PChar(_BlaiseReallocMem(Pointer(P), 64));
  AssertNotNull('shrink to 64', Pointer(P));
  Bad := CheckPattern(P, 64, 7);
  AssertEquals('shrink preserves first 64 bytes', -1, Bad);
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: realloc growth across size classes preserves bytes             }
{ ------------------------------------------------------------------ }
function Test_Realloc_Grow_Steps: string;
var
  P: PChar;
  Bad: Integer;
begin
  P := PChar(_BlaiseGetMem(16));
  AssertNotNull('alloc 16', Pointer(P));
  FillPattern(P, 16, 3);

  P := PChar(_BlaiseReallocMem(Pointer(P), 32));
  Bad := CheckPattern(P, 16, 3);
  AssertEquals('after grow 16->32', -1, Bad);

  P := PChar(_BlaiseReallocMem(Pointer(P), 64));
  Bad := CheckPattern(P, 16, 3);
  AssertEquals('after grow 32->64', -1, Bad);

  P := PChar(_BlaiseReallocMem(Pointer(P), 128));
  Bad := CheckPattern(P, 16, 3);
  AssertEquals('after grow 64->128', -1, Bad);

  P := PChar(_BlaiseReallocMem(Pointer(P), 256));
  Bad := CheckPattern(P, 16, 3);
  AssertEquals('after grow 128->256', -1, Bad);

  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: realloc small -> large crosses LARGE_THRESHOLD                 }
{ ------------------------------------------------------------------ }
function Test_Realloc_SmallToLarge: string;
var
  P: PChar;
  Bad: Integer;
begin
  P := PChar(_BlaiseGetMem(1024));
  AssertNotNull('alloc 1024', Pointer(P));
  FillPattern(P, 1024, 5);
  P := PChar(_BlaiseReallocMem(Pointer(P), 8192));
  AssertNotNull('grow to 8192', Pointer(P));
  Bad := CheckPattern(P, 1024, 5);
  AssertEquals('small->large preserves first 1024 bytes', -1, Bad);
  P[8191] := 99;
  AssertEquals('last byte writable', 99, Integer(P[8191]));
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: realloc large -> small crosses LARGE_THRESHOLD downward        }
{ ------------------------------------------------------------------ }
function Test_Realloc_LargeToSmall: string;
var
  P: PChar;
  Bad: Integer;
begin
  P := PChar(_BlaiseGetMem(8192));
  AssertNotNull('alloc 8192', Pointer(P));
  FillPattern(P, 8192, 9);
  P := PChar(_BlaiseReallocMem(Pointer(P), 128));
  AssertNotNull('shrink to 128', Pointer(P));
  Bad := CheckPattern(P, 128, 9);
  AssertEquals('large->small preserves first 128 bytes', -1, Bad);
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: realloc large -> large within same page count                  }
{ ------------------------------------------------------------------ }
function Test_Realloc_Large_SamePage: string;
var
  P: PChar;
  Bad: Integer;
begin
  P := PChar(_BlaiseGetMem(3000));
  AssertNotNull('alloc 3000', Pointer(P));
  FillPattern(P, 3000, 13);
  P := PChar(_BlaiseReallocMem(Pointer(P), 3500));
  AssertNotNull('grow to 3500', Pointer(P));
  Bad := CheckPattern(P, 3000, 13);
  AssertEquals('large same-page preserves bytes', -1, Bad);
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: realloc large -> large across page boundary (mremap path)      }
{ ------------------------------------------------------------------ }
function Test_Realloc_Large_GrowPages: string;
var
  P: PChar;
  Bad: Integer;
begin
  P := PChar(_BlaiseGetMem(4000));
  AssertNotNull('alloc 4000', Pointer(P));
  FillPattern(P, 4000, 17);
  P := PChar(_BlaiseReallocMem(Pointer(P), 16384));
  AssertNotNull('grow to 16384', Pointer(P));
  Bad := CheckPattern(P, 4000, 17);
  AssertEquals('large grow-pages preserves bytes', -1, Bad);
  P[16383] := 123;
  AssertEquals('last byte writable', 123, Integer(P[16383]));
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: LIFO cache reuses recently freed large block                   }
{ ------------------------------------------------------------------ }
function Test_Large_Cache_Reuse: string;
var
  A, B: Pointer;
begin
  A := _BlaiseGetMem(65536);
  AssertNotNull('first large', A);
  _BlaiseFreeMem(A);
  B := _BlaiseGetMem(65536);
  AssertNotNull('second large', B);
  AssertEquals('cache returns same block', PtrUInt(A), PtrUInt(B));
  _BlaiseFreeMem(B);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: large cache eviction beyond LARGE_CACHE_MAX                    }
{ ------------------------------------------------------------------ }
function Test_Large_Cache_Eviction: string;
const
  Count = 64;
var
  Blocks: array[0..63] of Pointer;
  I: Integer;
begin
  for I := 0 to Count - 1 do
  begin
    Blocks[I] := _BlaiseGetMem(8192);
    AssertNotNull('alloc ' + IntToStr(I), Blocks[I]);
  end;
  for I := 0 to Count - 1 do
    _BlaiseFreeMem(Blocks[I]);
  for I := 0 to Count - 1 do
  begin
    Blocks[I] := _BlaiseGetMem(8192);
    AssertNotNull('realloc ' + IntToStr(I), Blocks[I]);
  end;
  for I := 0 to Count - 1 do
    _BlaiseFreeMem(Blocks[I]);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: many small allocs retained at once (no double-handout)         }
{ ------------------------------------------------------------------ }
function Test_Retain_Many_Small: string;
const
  Count = 200;
var
  Blocks: array[0..199] of Pointer;
  I, J, V: Integer;
  P: PChar;
  Bad: Integer;
begin
  for I := 0 to Count - 1 do
  begin
    P := PChar(_BlaiseGetMem(32));
    AssertNotNull('alloc ' + IntToStr(I), Pointer(P));
    for J := 0 to 31 do
    begin
      V := (J + I) and $FF;
      P[J] := V;
    end;
    Blocks[I] := Pointer(P);
  end;
  Bad := -1;
  for I := 0 to Count - 1 do
  begin
    P := PChar(Blocks[I]);
    for J := 0 to 31 do
      if Integer(P[J]) <> ((J + I) and $FF) then
      begin
        Bad := I * 100 + J;
        Break;
      end;
    if Bad <> -1 then Break;
  end;
  AssertEquals('all blocks intact', -1, Bad);
  for I := 0 to Count - 1 do
    _BlaiseFreeMem(Blocks[I]);
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: interleaved small + large workload                             }
{ ------------------------------------------------------------------ }
function Test_Interleaved_Mixed: string;
const
  Count = 500;
var
  Small, Large: Pointer;
  I, Sz: Integer;
begin
  for I := 0 to Count - 1 do
  begin
    Sz := 8 + (I mod 64);
    Small := _BlaiseGetMem(Sz);
    AssertNotNull('small ' + IntToStr(I), Small);
    Large := _BlaiseGetMem(4096 + (I mod 7) * 1024);
    AssertNotNull('large ' + IntToStr(I), Large);
    _BlaiseFreeMem(Small);
    _BlaiseFreeMem(Large);
  end;
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: realloc churn — repeated grow+shrink                           }
{ ------------------------------------------------------------------ }
function Test_Realloc_Churn: string;
const
  Count = 200;
var
  P: PChar;
  I, Bad: Integer;
begin
  P := PChar(_BlaiseGetMem(16));
  FillPattern(P, 16, 42);
  for I := 1 to Count do
  begin
    P := PChar(_BlaiseReallocMem(Pointer(P), 16 + (I mod 256)));
    AssertNotNull('churn ' + IntToStr(I), Pointer(P));
    Bad := CheckPattern(P, 16, 42);
    AssertEquals('churn ' + IntToStr(I) + ' bytes intact', -1, Bad);
  end;
  _BlaiseFreeMem(Pointer(P));
  Result := '';
end;

{ ------------------------------------------------------------------ }
{ Test: alignment for every size class                                 }
{ ------------------------------------------------------------------ }
function Test_Alignment_All_Classes: string;
var
  Classes: array[0..7] of Integer;
  I: Integer;
  P: Pointer;
  Addr: PtrUInt;
begin
  Classes[0] := 16; Classes[1] := 32; Classes[2] := 64; Classes[3] := 128;
  Classes[4] := 256; Classes[5] := 512; Classes[6] := 1024; Classes[7] := 2048;
  for I := 0 to 7 do
  begin
    P := _BlaiseGetMem(Classes[I]);
    AssertNotNull('class ' + IntToStr(Classes[I]), P);
    Addr := PtrUInt(P);
    AssertEquals('class ' + IntToStr(Classes[I]) + ' aligned',
                 0, Integer(Addr and 7));
    _BlaiseFreeMem(P);
  end;
  P := _BlaiseGetMem(65536);
  AssertNotNull('large alloc', P);
  AssertEquals('large aligned', 0, Integer(PtrUInt(P) and 7));
  _BlaiseFreeMem(P);
  Result := '';
end;

begin
  AddSuite('blaise_mem', nil);
  AddTest('GetMem_Basic',           @Test_GetMem_Basic,           'blaise_mem');
  AddTest('GetMem_Zero',            @Test_GetMem_Zero,            'blaise_mem');
  AddTest('ReadWrite',              @Test_ReadWrite,              'blaise_mem');
  AddTest('Distinct_Pointers',      @Test_Distinct_Pointers,      'blaise_mem');
  AddTest('FreeMem_Nil',            @Test_FreeMem_Nil,            'blaise_mem');
  AddTest('ReallocMem_Grow',        @Test_ReallocMem_Grow,        'blaise_mem');
  AddTest('ReallocMem_FromNil',     @Test_ReallocMem_FromNil,     'blaise_mem');
  AddTest('ReallocMem_ToZero',      @Test_ReallocMem_ToZero,      'blaise_mem');
  AddTest('Small_Alloc',            @Test_Small_Alloc,            'blaise_mem');
  AddTest('Large_Alloc',            @Test_Large_Alloc,            'blaise_mem');
  AddTest('Reuse_After_Free',       @Test_Reuse_After_Free,       'blaise_mem');
  AddTest('Many_Small_Allocs',      @Test_Many_Small_Allocs,      'blaise_mem');
  AddTest('Size_Classes',           @Test_Size_Classes,           'blaise_mem');
  AddTest('Alignment',              @Test_Alignment,              'blaise_mem');
  AddTest('SizeClass_Boundaries',   @Test_SizeClass_Boundaries,   'blaise_mem');
  AddTest('Realloc_SameClass',      @Test_Realloc_SameClass,      'blaise_mem');
  AddTest('Realloc_Shrink',         @Test_Realloc_Shrink,         'blaise_mem');
  AddTest('Realloc_Grow_Steps',     @Test_Realloc_Grow_Steps,     'blaise_mem');
  AddTest('Realloc_SmallToLarge',   @Test_Realloc_SmallToLarge,   'blaise_mem');
  AddTest('Realloc_LargeToSmall',   @Test_Realloc_LargeToSmall,   'blaise_mem');
  AddTest('Realloc_Large_SamePage', @Test_Realloc_Large_SamePage, 'blaise_mem');
  AddTest('Realloc_Large_GrowPages',@Test_Realloc_Large_GrowPages,'blaise_mem');
  AddTest('Large_Cache_Reuse',      @Test_Large_Cache_Reuse,      'blaise_mem');
  AddTest('Large_Cache_Eviction',   @Test_Large_Cache_Eviction,   'blaise_mem');
  AddTest('Retain_Many_Small',      @Test_Retain_Many_Small,      'blaise_mem');
  AddTest('Interleaved_Mixed',      @Test_Interleaved_Mixed,      'blaise_mem');
  AddTest('Realloc_Churn',          @Test_Realloc_Churn,          'blaise_mem');
  AddTest('Alignment_All_Classes',  @Test_Alignment_All_Classes,  'blaise_mem');
  RunAllSysTests;
end.
