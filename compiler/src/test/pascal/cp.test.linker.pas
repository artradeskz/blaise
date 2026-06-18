{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.linker;

{ Tests for the internal linker:
  Phase A — blaise.elfreader (ELF relocatable-object parsing and
  ar-archive parsing with GNU long-name support) and TSectionMerger.
  Phase B — TLinker symbol resolution, static PC-relative relocations,
  and non-PIE ET_EXEC emission, including a hand-written syscall-only
  fixture that is linked internally, run, and asserted. }

interface

uses
  SysUtils, process, blaise.testing, Generics.Collections,
  blaise.elfreader, blaise.linker.elf, blaise.assembler.x86_64;

type
  TElfReaderTests = class(TTestCase)
  private
    function ProjectRoot: string;
    function PadField(const AVal: string; AWidth: Integer): string;
  published
    procedure TestParse_TextSectionBytes;
    procedure TestParse_GlobalFuncSymbol;
    procedure TestParse_QuadRelocation;
    procedure TestParse_BssNoData;
    procedure TestParse_BadMagic_Raises;
    procedure TestArchive_SyntheticLongNames;
    procedure TestArchive_BadMagic_Raises;
    procedure TestArchive_ParsesRTL;
  end;

  TSectionMergerTests = class(TTestCase)
  published
    procedure TestMerge_ConcatenatesText;
    procedure TestMerge_AlignmentPadding;
    procedure TestMerge_BssSizesAccumulate;
    procedure TestMerge_SkipsBookkeepingSections;
  end;

  TLinkerTests = class(TTestCase)
  private
    function LinkObjs(AObjAsm: array of string;
      const AEntry: string; out ABytes: string): TLinker;
  published
    { Symbol resolution }
    procedure TestSym_GlobalResolvesToVaddr;
    procedure TestSym_TwoGlobalsDuplicate_Raises;
    procedure TestSym_StrongUndefined_Raises;
    procedure TestSym_WeakUndefinedResolvesToZero;
    procedure TestSym_SynthesisedSymbolsDefined;
    { Static relocations }
    procedure TestReloc_PC32CrossObjectCall;
    procedure TestReloc_Quad64_Raises;
    { Executable structure }
    procedure TestExe_ElfHeaderIsExec;
    procedure TestExe_EntryPointMatchesSymbol;
    procedure TestExe_MissingEntry_Raises;
  end;

  TLinkerE2ETests = class(TTestCase)
  private
    FScratch: string;
    function ProjectRoot: string;
    function RunBin(const AExe: string; out AStdout: string): Integer;
  protected
    procedure SetUp; override;
  published
    procedure TestRun_SyscallHelloWorld;
  end;

implementation

function TElfReaderTests.ProjectRoot: string;
var
  Dir, Parent: string;
  Steps: Integer;
begin
  Result := GetEnvironmentVariable('BLAISE_PROJECT_ROOT');
  if Result <> '' then
  begin
    Result := IncludeTrailingPathDelimiter(Result);
    Exit;
  end;
  Dir := GetCurrentDir();
  for Steps := 0 to 5 do
  begin
    if DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'vendor/qbe') and
       DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'runtime') then
    begin
      Result := IncludeTrailingPathDelimiter(Dir);
      Exit;
    end;
    Parent := ExtractFileDir(Dir);
    if (Parent = '') or (Parent = Dir) then Break;
    Dir := Parent;
  end;
  Result := IncludeTrailingPathDelimiter(GetCurrentDir());
end;

function TElfReaderTests.PadField(const AVal: string; AWidth: Integer): string;
begin
  Result := AVal;
  while Length(Result) < AWidth do
    Result := Result + ' ';
end;

procedure TElfReaderTests.TestParse_TextSectionBytes;
var
  Obj: TElfObjectFile;
  Sec: TRdSection;
begin
  Obj := ParseElfObject(AssembleToBytes(
    'movq %rcx, (%rax)' + LineEnding + 'ret' + LineEnding), 'test.o');
  try
    Sec := Obj.FindSection('.text');
    AssertTrue('.text section missing', Sec <> nil);
    AssertEquals(4, Integer(Sec.Size));
    AssertEquals(Chr($48) + Chr($89) + Chr($08) + Chr($C3), Sec.Data);
    AssertEquals(SHT_PROGBITS, Sec.ShType);
    AssertTrue('SHF_EXECINSTR missing',
      (Sec.Flags and SHF_EXECINSTR) <> 0);
  finally
    Obj.Free();
  end;
end;

procedure TElfReaderTests.TestParse_GlobalFuncSymbol;
var
  Obj: TElfObjectFile;
  I: Integer;
  Sym: TRdSymbol;
  Found: TRdSymbol;
begin
  Obj := ParseElfObject(AssembleToBytes(
    '.globl entry' + LineEnding +
    '.type entry, @function' + LineEnding +
    'entry:' + LineEnding + 'ret' + LineEnding), 'test.o');
  try
    Found := nil;
    for I := 0 to Obj.Symbols.Count - 1 do
    begin
      Sym := Obj.Symbols.Get(I);
      if Sym.Name = 'entry' then Found := Sym;
    end;
    AssertTrue('symbol entry missing', Found <> nil);
    AssertEquals(STB_GLOBAL, Found.Bind);
    AssertEquals(STT_FUNC, Found.SymType);
    AssertEquals(Obj.SectionIndexOf('.text'), Found.Shndx);
    AssertEquals(0, Integer(Found.Value));
  finally
    Obj.Free();
  end;
end;

procedure TElfReaderTests.TestParse_QuadRelocation;
var
  Obj: TElfObjectFile;
  Rel: TRdReloc;
begin
  Obj := ParseElfObject(AssembleToBytes(
    '.data' + LineEnding +
    'vt:' + LineEnding +
    '.quad some_method + 16' + LineEnding), 'test.o');
  try
    AssertEquals(1, Obj.Relocs.Count);
    Rel := Obj.Relocs.Get(0);
    AssertEquals(R_X86_64_64, Rel.RelocType);
    AssertEquals(Obj.SectionIndexOf('.data'), Rel.TargetSection);
    AssertEquals(0, Integer(Rel.Offset));
    AssertEquals(16, Integer(Rel.Addend));
    AssertEquals('some_method', Obj.Symbols.Get(Rel.SymIndex).Name);
  finally
    Obj.Free();
  end;
end;

procedure TElfReaderTests.TestParse_BssNoData;
var
  Obj: TElfObjectFile;
  Sec: TRdSection;
begin
  Obj := ParseElfObject(AssembleToBytes(
    '.section .bss' + LineEnding +
    'buf:' + LineEnding +
    '.skip 64' + LineEnding), 'test.o');
  try
    Sec := Obj.FindSection('.bss');
    AssertTrue('.bss section missing', Sec <> nil);
    AssertEquals(SHT_NOBITS, Sec.ShType);
    AssertEquals(64, Integer(Sec.Size));
    AssertEquals(0, Length(Sec.Data));
  finally
    Obj.Free();
  end;
end;

procedure TElfReaderTests.TestParse_BadMagic_Raises;
var
  Raised: Boolean;
  Obj: TElfObjectFile;
begin
  Raised := False;
  try
    Obj := ParseElfObject('this is definitely not an ELF file, '
      + 'but it is at least 64 bytes long for the header check....', 'junk');
    Obj.Free();
  except
    on E: EElfReader do
      Raised := True;
  end;
  AssertTrue('bad magic must raise EElfReader', Raised);
end;

procedure TElfReaderTests.TestArchive_SyntheticLongNames;
var
  LongTab: string;
  Ar: string;
  Members: TList<TArchiveMember>;
  I: Integer;
begin
  { Two members: one via the GNU long-name table, one short-named.
    Member data is arbitrary bytes — ParseArchive does not interpret
    member contents. }
  LongTab := 'a_very_long_member_name_indeed.o/' + #10;
  Ar := '!<arch>' + #10
    + PadField('//', 16) + PadField('', 12) + PadField('', 6)
    + PadField('', 6) + PadField('', 8)
    + PadField(IntToStr(Length(LongTab)), 10) + '`' + #10
    + LongTab                          { 34 bytes — already even, no pad }
    + PadField('/0', 16) + PadField('0', 12) + PadField('0', 6)
    + PadField('0', 6) + PadField('644', 8)
    + PadField('5', 10) + '`' + #10
    + 'HELLO' + #10                                    { pad to even }
    + PadField('short.o/', 16) + PadField('0', 12) + PadField('0', 6)
    + PadField('0', 6) + PadField('644', 8)
    + PadField('4', 10) + '`' + #10
    + 'DATA';
  Members := TList<TArchiveMember>.Create();
  try
    ParseArchive(Ar, 'synthetic.a', Members);
    AssertEquals(2, Members.Count);
    AssertEquals('a_very_long_member_name_indeed.o', Members.Get(0).Name);
    AssertEquals('HELLO', Members.Get(0).Data);
    AssertEquals('short.o', Members.Get(1).Name);
    AssertEquals('DATA', Members.Get(1).Data);
  finally
    for I := 0 to Members.Count - 1 do
      Members.Get(I).Free();
    Members.Free();
  end;
end;

procedure TElfReaderTests.TestArchive_BadMagic_Raises;
var
  Raised: Boolean;
  Members: TList<TArchiveMember>;
begin
  Raised := False;
  Members := TList<TArchiveMember>.Create();
  try
    try
      ParseArchive('!<arch !<arch !<arch', 'junk.a', Members);
    except
      on E: EElfReader do
        Raised := True;
    end;
  finally
    Members.Free();
  end;
  AssertTrue('bad archive magic must raise EElfReader', Raised);
end;

procedure TElfReaderTests.TestArchive_ParsesRTL;
var
  RTLPath: string;
  Members: TList<TArchiveMember>;
  I: Integer;
  M: TArchiveMember;
  Obj: TElfObjectFile;
  SawSetjmp: Boolean;
begin
  RTLPath := ProjectRoot() + 'compiler/target/blaise_rtl.a';
  if not FileExists(RTLPath) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  Members := TList<TArchiveMember>.Create();
  try
    ReadArchiveFile(RTLPath, Members);
    AssertTrue('expected several RTL members, got '
      + IntToStr(Members.Count), Members.Count >= 5);
    SawSetjmp := False;
    for I := 0 to Members.Count - 1 do
    begin
      M := Members.Get(I);
      if M.Name = 'blaise_setjmp_x86_64.o' then
        SawSetjmp := True;
      { Every member must parse as a valid x86-64 relocatable object
        with at least its NULL section + one real section. }
      Obj := ParseElfObject(M.Data, M.Name);
      try
        AssertTrue(M.Name + ': too few sections', Obj.Sections.Count > 1);
        AssertTrue(M.Name + ': no symbols', Obj.Symbols.Count > 0);
      finally
        Obj.Free();
      end;
    end;
    AssertTrue('long-named member blaise_setjmp_x86_64.o not found '
      + '(GNU long-name table mishandled?)', SawSetjmp);
  finally
    for I := 0 to Members.Count - 1 do
      Members.Get(I).Free();
    Members.Free();
  end;
end;

{ ---- TSectionMergerTests ---- }

procedure TSectionMergerTests.TestMerge_ConcatenatesText;
var
  O1, O2: TElfObjectFile;
  Mg: TSectionMerger;
  M: TMergedSection;
  P: TSectionPlacement;
begin
  O1 := ParseElfObject(AssembleToBytes('ret' + LineEnding), 'a.o');
  O2 := ParseElfObject(AssembleToBytes('nop' + LineEnding
    + 'ret' + LineEnding), 'b.o');
  Mg := TSectionMerger.Create();
  try
    Mg.AddObject(0, O1);
    Mg.AddObject(1, O2);
    M := Mg.FindMerged('.text');
    AssertTrue('.text missing', M <> nil);
    AssertEquals(Chr($C3) + Chr($90) + Chr($C3), M.Data);
    AssertEquals(3, Integer(M.Size));
    P := Mg.PlacementOf(0, O1.SectionIndexOf('.text'));
    AssertTrue('placement 0 missing', P <> nil);
    AssertEquals(0, Integer(P.Offset));
    P := Mg.PlacementOf(1, O2.SectionIndexOf('.text'));
    AssertTrue('placement 1 missing', P <> nil);
    AssertEquals(1, Integer(P.Offset));
  finally
    Mg.Free();
    O2.Free();
    O1.Free();
  end;
end;

procedure TSectionMergerTests.TestMerge_AlignmentPadding;
var
  O1, O2: TElfObjectFile;
  Mg: TSectionMerger;
  M: TMergedSection;
  P: TSectionPlacement;
begin
  { First object contributes 1 byte of .data; the second declares
    .balign 8, so its contribution must start at offset 8 with zero
    padding in between. }
  O1 := ParseElfObject(AssembleToBytes('.data' + LineEnding
    + '.byte 17' + LineEnding), 'a.o');
  O2 := ParseElfObject(AssembleToBytes('.data' + LineEnding
    + '.balign 8' + LineEnding + '.byte 34' + LineEnding), 'b.o');
  Mg := TSectionMerger.Create();
  try
    Mg.AddObject(0, O1);
    Mg.AddObject(1, O2);
    M := Mg.FindMerged('.data');
    AssertTrue('.data missing', M <> nil);
    AssertEquals(9, Integer(M.Size));
    AssertEquals(8, Integer(M.Align));
    AssertEquals(17, Ord(M.Data[0]));
    AssertEquals(0, Ord(M.Data[1]));
    AssertEquals(34, Ord(M.Data[8]));
    P := Mg.PlacementOf(1, O2.SectionIndexOf('.data'));
    AssertTrue('placement missing', P <> nil);
    AssertEquals(8, Integer(P.Offset));
  finally
    Mg.Free();
    O2.Free();
    O1.Free();
  end;
end;

procedure TSectionMergerTests.TestMerge_BssSizesAccumulate;
var
  O1, O2: TElfObjectFile;
  Mg: TSectionMerger;
  M: TMergedSection;
begin
  O1 := ParseElfObject(AssembleToBytes('.section .bss' + LineEnding
    + '.skip 24' + LineEnding), 'a.o');
  O2 := ParseElfObject(AssembleToBytes('.section .bss' + LineEnding
    + '.skip 40' + LineEnding), 'b.o');
  Mg := TSectionMerger.Create();
  try
    Mg.AddObject(0, O1);
    Mg.AddObject(1, O2);
    M := Mg.FindMerged('.bss');
    AssertTrue('.bss missing', M <> nil);
    AssertEquals(SHT_NOBITS, M.ShType);
    AssertEquals(64, Integer(M.Size));
    AssertEquals(0, Length(M.Data));
  finally
    Mg.Free();
    O2.Free();
    O1.Free();
  end;
end;

procedure TSectionMergerTests.TestMerge_SkipsBookkeepingSections;
var
  O1: TElfObjectFile;
  Mg: TSectionMerger;
begin
  O1 := ParseElfObject(AssembleToBytes('ret' + LineEnding), 'a.o');
  Mg := TSectionMerger.Create();
  try
    Mg.AddObject(0, O1);
    AssertTrue('.symtab must not merge', Mg.FindMerged('.symtab') = nil);
    AssertTrue('.strtab must not merge', Mg.FindMerged('.strtab') = nil);
    AssertTrue('.shstrtab must not merge', Mg.FindMerged('.shstrtab') = nil);
    AssertTrue('.note.GNU-stack must not merge',
      Mg.FindMerged('.note.GNU-stack') = nil);
  finally
    Mg.Free();
    O1.Free();
  end;
end;

{ ---- TLinkerTests ---- }

{ Assemble each asm string to a relocatable object, hand them all to a
  fresh TLinker (which takes ownership), link to bytes, and return the
  linker so the caller can query resolved addresses.  Caller frees. }
function TLinkerTests.LinkObjs(AObjAsm: array of string;
  const AEntry: string; out ABytes: string): TLinker;
var
  Lk: TLinker;
  I: Integer;
  Obj: TElfObjectFile;
begin
  Lk := TLinker.Create();
  try
    for I := 0 to High(AObjAsm) do
    begin
      Obj := ParseElfObject(AssembleToBytes(AObjAsm[I]),
        'obj' + IntToStr(I) + '.o');
      Lk.AddOwnedObject(Obj);
    end;
    ABytes := Lk.LinkToBytes(AEntry);
    Result := Lk;
  except
    Lk.Free();
    raise;
  end;
end;

procedure TLinkerTests.TestSym_GlobalResolvesToVaddr;
var
  Lk: TLinker;
  Bytes: string;
  Addr: Int64;
begin
  Lk := LinkObjs(
    ['.globl _start' + LineEnding + '_start:' + LineEnding + 'ret' + LineEnding],
    '_start', Bytes);
  try
    Addr := Lk.AddrOfSymbol('_start');
    { _start lands in the executable run just past ELF + 2 phdrs at base
      0x400000; its exact value is layout-dependent but must be a real
      mapped code address above the base. }
    AssertTrue('_start resolved', Addr > $400000);
  finally
    Lk.Free();
  end;
end;

procedure TLinkerTests.TestSym_TwoGlobalsDuplicate_Raises;
var
  Lk: TLinker;
  Bytes: string;
  Raised: Boolean;
begin
  Raised := False;
  Lk := nil;
  try
    Lk := LinkObjs(
      ['.globl dup' + LineEnding + 'dup:' + LineEnding + 'ret' + LineEnding,
       '.globl dup' + LineEnding + 'dup:' + LineEnding + 'ret' + LineEnding +
       '.globl _start' + LineEnding + '_start:' + LineEnding + 'ret' + LineEnding],
      '_start', Bytes);
  except
    on E: ELinker do
      Raised := True;
  end;
  Lk.Free();
  AssertTrue('duplicate global symbol must raise ELinker', Raised);
end;

procedure TLinkerTests.TestSym_StrongUndefined_Raises;
var
  Lk: TLinker;
  Bytes: string;
  Raised: Boolean;
begin
  Raised := False;
  Lk := nil;
  try
    { _start calls an undefined strong symbol. }
    Lk := LinkObjs(
      ['.globl _start' + LineEnding + '_start:' + LineEnding +
       'callq missing_fn' + LineEnding + 'ret' + LineEnding],
      '_start', Bytes);
  except
    on E: ELinker do
      Raised := True;
  end;
  Lk.Free();
  AssertTrue('strong undefined reference must raise ELinker', Raised);
end;

procedure TLinkerTests.TestSym_WeakUndefinedResolvesToZero;
var
  Lk: TLinker;
  Obj: TElfObjectFile;
  Sec: TRdSection;
  SymNull, SymStart, SymWeak: TRdSymbol;
  Rel: TRdReloc;
  TextSec: TMergedSection;
  StartAddr: Int64;
  PatchOff, Disp: Integer;
  Expected: Int64;
begin
  { The internal assembler always emits an undefined reference as
    STB_GLOBAL (no STB_WEAK support yet), so weak handling is exercised
    with a hand-built object: a .text holding `E8 00 00 00 00` (a call
    with a zero displacement) plus a PC32 reloc against a weak-undef
    symbol.  A strong undef would raise; the weak one must resolve to 0,
    giving disp = 0 + (-4) - P. }
  Obj := TElfObjectFile.Create();
  Obj.SourceName := 'weak.o';
  { Section 0 is the reserved ELF NULL section, mirroring real objects
    (so a symbol's Shndx=0 means SHN_UNDEF, not "the first section"). }
  Sec := TRdSection.Create();
  Sec.Name := '';
  Sec.ShType := SHT_NULL;
  Obj.Sections.Add(Sec);                 { section index 0 = NULL }

  Sec := TRdSection.Create();
  Sec.Name := '.text';
  Sec.ShType := SHT_PROGBITS;
  Sec.Flags := SHF_ALLOC or SHF_EXECINSTR;
  Sec.AddrAlign := 1;
  Sec.Data := Chr($E8) + Chr(0) + Chr(0) + Chr(0) + Chr(0) + Chr($C3);
  Sec.Size := 6;
  Obj.Sections.Add(Sec);                 { section index 1 = .text }

  SymNull := TRdSymbol.Create();
  SymNull.Name := '';
  Obj.Symbols.Add(SymNull);              { symtab[0] reserved }

  SymStart := TRdSymbol.Create();
  SymStart.Name := '_start';
  SymStart.Bind := STB_GLOBAL;
  SymStart.SymType := STT_FUNC;
  SymStart.Shndx := 1;                   { defined in .text }
  SymStart.Value := 0;
  Obj.Symbols.Add(SymStart);             { symtab[1] }

  SymWeak := TRdSymbol.Create();
  SymWeak.Name := 'maybe_absent';
  SymWeak.Bind := STB_WEAK;
  SymWeak.Shndx := SHN_UNDEF;
  Obj.Symbols.Add(SymWeak);              { symtab[2] }

  Rel := TRdReloc.Create();
  Rel.TargetSection := 1;                { patches .text (section 1) }
  Rel.Offset := 1;                       { displacement after 0xE8 }
  Rel.SymIndex := 2;                     { -> maybe_absent }
  Rel.RelocType := R_X86_64_PC32;
  Rel.Addend := -4;
  Obj.Relocs.Add(Rel);

  Lk := TLinker.Create();
  try
    Lk.AddOwnedObject(Obj);
    Lk.LinkToBytes('_start');           { must NOT raise }
    StartAddr := Lk.AddrOfSymbol('_start');
    TextSec := Lk.FindMergedText();
    PatchOff := 1;                       { only object, .text offset 1 }
    Disp := (Ord(TextSec.Data[PatchOff]) and $FF)
         or ((Ord(TextSec.Data[PatchOff + 1]) and $FF) shl 8)
         or ((Ord(TextSec.Data[PatchOff + 2]) and $FF) shl 16)
         or ((Ord(TextSec.Data[PatchOff + 3]) and $FF) shl 24);
    { S=0, A=-4, P = StartAddr+1 → disp = -4 - (StartAddr+1). }
    Expected := Int64(0) - 4 - (StartAddr + 1);
    AssertEquals('weak-undef PC32 disp (S=0)',
      Integer(Expected and $FFFFFFFF), Disp);
  finally
    Lk.Free();
  end;
end;

procedure TLinkerTests.TestSym_SynthesisedSymbolsDefined;
var
  Lk: TLinker;
  Bytes: string;
begin
  Lk := LinkObjs(
    ['.data' + LineEnding + '.globl gv' + LineEnding + 'gv:' + LineEnding +
     '.quad 7' + LineEnding +
     '.text' + LineEnding + '.globl _start' + LineEnding + '_start:' +
     LineEnding + 'ret' + LineEnding],
    '_start', Bytes);
  try
    AssertTrue('__bss_start defined', Lk.AddrOfSymbol('__bss_start') > 0);
    AssertTrue('_edata defined', Lk.AddrOfSymbol('_edata') > 0);
    AssertTrue('_end defined', Lk.AddrOfSymbol('_end') > 0);
    AssertTrue('_GLOBAL_OFFSET_TABLE_ defined',
      Lk.AddrOfSymbol('_GLOBAL_OFFSET_TABLE_') > 0);
    { _edata (end of .data) must not exceed _end (end of bss). }
    AssertTrue('_edata <= _end',
      Lk.AddrOfSymbol('_edata') <= Lk.AddrOfSymbol('_end'));
  finally
    Lk.Free();
  end;
end;

procedure TLinkerTests.TestReloc_PC32CrossObjectCall;
var
  Lk: TLinker;
  Bytes: string;
  TextSec: TMergedSection;
  CalleeAddr, StartAddr: Int64;
  CallSiteVaddr, CallEnd: Int64;
  PatchOff: Integer;
  Disp: Integer;
  Expected: Int64;
begin
  { Object 0 defines callee; object 1's _start does `call callee`.
    The 4-byte displacement after the 0xE8 opcode must equal
    callee - (addr_of_displacement + 4). }
  Lk := LinkObjs(
    ['.globl callee' + LineEnding + 'callee:' + LineEnding + 'ret' + LineEnding,
     '.globl _start' + LineEnding + '_start:' + LineEnding +
     'callq callee' + LineEnding + 'ret' + LineEnding],
    '_start', Bytes);
  try
    CalleeAddr := Lk.AddrOfSymbol('callee');
    StartAddr  := Lk.AddrOfSymbol('_start');
    AssertTrue('callee resolved', CalleeAddr > 0);
    AssertTrue('_start resolved', StartAddr > 0);

    { The call opcode (0xE8) is the first byte of _start; the 4-byte
      relative displacement follows it.  The patched bytes live in the
      merged .text data at an offset relative to .text's own base —
      callee is the first thing in .text, so its address is that base. }
    TextSec := Lk.FindMergedText();
    AssertTrue('.text present', TextSec <> nil);
    CallSiteVaddr := StartAddr;           { 0xE8 here }
    CallEnd := CallSiteVaddr + 5;         { next insn after the 5-byte call }
    Expected := CalleeAddr - CallEnd;

    PatchOff := Integer(StartAddr - CalleeAddr) + 1; { skip 0xE8 }
    Disp := (Ord(TextSec.Data[PatchOff]) and $FF)
         or ((Ord(TextSec.Data[PatchOff + 1]) and $FF) shl 8)
         or ((Ord(TextSec.Data[PatchOff + 2]) and $FF) shl 16)
         or ((Ord(TextSec.Data[PatchOff + 3]) and $FF) shl 24);
    AssertEquals('PC32 call displacement', Integer(Expected and $FFFFFFFF), Disp);
  finally
    Lk.Free();
  end;
end;

procedure TLinkerTests.TestReloc_Quad64_Raises;
var
  Lk: TLinker;
  Bytes: string;
  Raised: Boolean;
begin
  { An absolute 64-bit pointer to a symbol needs dynamic linking under
    a real PIE; Phase B rejects R_X86_64_64 explicitly. }
  Raised := False;
  Lk := nil;
  try
    Lk := LinkObjs(
      ['.data' + LineEnding + 'ptr:' + LineEnding + '.quad target' + LineEnding +
       '.text' + LineEnding + '.globl target' + LineEnding + 'target:' +
       LineEnding + 'ret' + LineEnding +
       '.globl _start' + LineEnding + '_start:' + LineEnding + 'ret' + LineEnding],
      '_start', Bytes);
  except
    on E: ELinker do
      Raised := True;
  end;
  Lk.Free();
  AssertTrue('R_X86_64_64 must raise ELinker in Phase B', Raised);
end;

procedure TLinkerTests.TestExe_ElfHeaderIsExec;
var
  Lk: TLinker;
  Bytes: string;
begin
  Lk := LinkObjs(
    ['.globl _start' + LineEnding + '_start:' + LineEnding + 'ret' + LineEnding],
    '_start', Bytes);
  try
    AssertTrue('output too small', Length(Bytes) >= 64);
    AssertEquals('ELF magic 0', $7F, Ord(Bytes[0]));
    AssertEquals('ELF magic E', Ord('E'), Ord(Bytes[1]));
    AssertEquals('ELFCLASS64', 2, Ord(Bytes[4]));
    AssertEquals('little-endian', 1, Ord(Bytes[5]));
    { e_type at offset 16 must be ET_EXEC (2). }
    AssertEquals('e_type ET_EXEC', 2,
      (Ord(Bytes[16]) and $FF) or ((Ord(Bytes[17]) and $FF) shl 8));
    { e_machine at offset 18 must be EM_X86_64 (62). }
    AssertEquals('e_machine x86-64', 62,
      (Ord(Bytes[18]) and $FF) or ((Ord(Bytes[19]) and $FF) shl 8));
  finally
    Lk.Free();
  end;
end;

procedure TLinkerTests.TestExe_EntryPointMatchesSymbol;
var
  Lk: TLinker;
  Bytes: string;
  Entry, I: Int64;
begin
  Lk := LinkObjs(
    ['.globl _start' + LineEnding + '_start:' + LineEnding + 'ret' + LineEnding],
    '_start', Bytes);
  try
    { e_entry is an 8-byte LE field at offset 24. }
    Entry := 0;
    for I := 0 to 7 do
      Entry := Entry or (Int64(Ord(Bytes[24 + Integer(I)]) and $FF) shl (I * 8));
    AssertEquals('e_entry == addr(_start)', Lk.AddrOfSymbol('_start'), Entry);
  finally
    Lk.Free();
  end;
end;

procedure TLinkerTests.TestExe_MissingEntry_Raises;
var
  Lk: TLinker;
  Bytes: string;
  Raised: Boolean;
begin
  Raised := False;
  Lk := nil;
  try
    Lk := LinkObjs(
      ['.globl _start' + LineEnding + '_start:' + LineEnding + 'ret' + LineEnding],
      'no_such_entry', Bytes);
  except
    on E: ELinker do
      Raised := True;
  end;
  Lk.Free();
  AssertTrue('missing entry symbol must raise ELinker', Raised);
end;

{ ---- TLinkerE2ETests ---- }

function TLinkerE2ETests.ProjectRoot: string;
var
  Dir, Parent: string;
  Steps: Integer;
begin
  Result := GetEnvironmentVariable('BLAISE_PROJECT_ROOT');
  if Result <> '' then
  begin
    Result := IncludeTrailingPathDelimiter(Result);
    Exit;
  end;
  Dir := GetCurrentDir();
  for Steps := 0 to 5 do
  begin
    if DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'vendor/qbe') and
       DirectoryExists(IncludeTrailingPathDelimiter(Dir) + 'runtime') then
    begin
      Result := IncludeTrailingPathDelimiter(Dir);
      Exit;
    end;
    Parent := ExtractFileDir(Dir);
    if (Parent = '') or (Parent = Dir) then Break;
    Dir := Parent;
  end;
  Result := IncludeTrailingPathDelimiter(GetCurrentDir());
end;

procedure TLinkerE2ETests.SetUp;
begin
  inherited SetUp();
  FScratch := ProjectRoot() + 'compiler/target/linker-e2e';
  ForceDirectories(FScratch);
end;

function TLinkerE2ETests.RunBin(const AExe: string;
  out AStdout: string): Integer;
var
  Proc:  TProcess;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    Proc.Execute();
    AStdout := '';
    repeat
      Chunk := Proc.ReadOutput();
      AStdout := AStdout + Chunk;
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    Result := Proc.ExitCode;
  finally
    Proc.Free();
  end;
end;

procedure TLinkerE2ETests.TestRun_SyscallHelloWorld;
const
  { A freestanding program that talks straight to the kernel: it needs
    no libc, no RTL, and no dynamic linker, so Phase B links and runs
    it on its own.  write(1, msg, 14); exit(7).  The exit code (7)
    plus the stdout both prove the executable loaded and ran with the
    correct entry point, segment permissions, and a PC-relative
    `leaq msg(%rip)` resolved against the merged .rodata. }
  FixtureAsm =
    '.text' + LineEnding +
    '.globl _start' + LineEnding +
    '_start:' + LineEnding +
    '  movq $1, %rax' + LineEnding +        { SYS_write }
    '  movq $1, %rdi' + LineEnding +        { fd = stdout }
    '  leaq msg(%rip), %rsi' + LineEnding + { buf (PC-relative) }
    '  movq $15, %rdx' + LineEnding +       { count (14 chars + newline) }
    '  .byte 15' + LineEnding + '  .byte 5' + LineEnding +  { syscall }
    '  movq $60, %rax' + LineEnding +       { SYS_exit }
    '  movq $7, %rdi' + LineEnding +        { exit code }
    '  .byte 15' + LineEnding + '  .byte 5' + LineEnding +  { syscall }
    '.section .rodata' + LineEnding +
    'msg:' + LineEnding +
    '  .ascii "Hello, linker!\n"' + LineEnding;
var
  Lk: TLinker;
  Obj: TElfObjectFile;
  BinPath, Output: string;
  Rc: Integer;
begin
  BinPath := FScratch + '/hello_syscall';
  Lk := TLinker.Create();
  try
    Obj := ParseElfObject(AssembleToBytes(FixtureAsm), 'hello.o');
    Lk.AddOwnedObject(Obj);
    Lk.Link('_start', BinPath);
  finally
    Lk.Free();
  end;

  AssertTrue('linked binary missing', FileExists(BinPath));
  Rc := RunBin(BinPath, Output);
  AssertEquals('exit code from internally-linked binary', 7, Rc);
  AssertEquals('stdout from internally-linked binary',
    'Hello, linker!' + Chr(10), Output);
end;

initialization
  RegisterTest(TElfReaderTests);
  RegisterTest(TSectionMergerTests);
  RegisterTest(TLinkerTests);
  RegisterTest(TLinkerE2ETests);

end.
