{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.linker;

{ Tests for the internal linker's input layer (Phase A):
  blaise.elfreader — ELF relocatable-object parsing and ar-archive
  parsing with GNU long-name support. }

interface

uses
  SysUtils, blaise.testing, Generics.Collections,
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

initialization
  RegisterTest(TElfReaderTests);
  RegisterTest(TSectionMergerTests);

end.
