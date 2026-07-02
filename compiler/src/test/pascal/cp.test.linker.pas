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
  classes, SysUtils, process, blaise.testing, Generics.Collections,
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
    procedure TestSym_TwoGlobalsDuplicate_FirstWins;
    procedure TestSym_StrongUndefined_Raises;
    procedure TestSym_WeakUndefinedResolvesToZero;
    procedure TestSym_SynthesisedSymbolsDefined;
    { Static relocations }
    procedure TestReloc_PC32CrossObjectCall;
    procedure TestReloc_Quad64_ResolvesToAbsoluteAddr;
    procedure TestReloc_Abs32_ResolvesInStaticMode;
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
    { Linking with the FreeBSD target stamps EI_OSABI = 9 (ELFOSABI_FREEBSD)
      in the ELF header and keeps the static ET_EXEC / _start shape.  The
      FreeBSD binary cannot execute on the Linux test host (different syscall
      numbers), so this asserts the emitted header shape only — the structural
      check the cross-compile lane relies on. }
    procedure TestLink_FreeBSDTarget_StampsOSABI;
    { Step 3: linking the freestanding FreeBSD _start with the FreeBSD target
      yields a static ET_EXEC whose entry point is _start and which has no
      PT_INTERP — the Strategy-B shape a cross-compiled FreeBSD binary needs.
      Asserts header shape only (it cannot run on the Linux host). }
    procedure TestLink_FreeBSDStart_StaticExecShape;
    { Step 4a: a fixture that mirrors the runtime.syscall.freebsd file/process
      leaves (open/read/write/mmap/stat) links under the FreeBSD target with the
      bare POSIX symbols DEFINED, and the linked .text carries the FreeBSD
      ino64 syscall NUMBERS (open=5, write=4, mmap=477, fstatat=552) plus the
      CF-error-translation idiom (jae + negq).  Standalone — no FreeBSD
      emulation, header/byte shape only. }
    procedure TestLink_FreeBSDSyscallLeaf_SymbolsAndNumbers;
    { Step 4b: the FreeBSD leaf additions — getrandom uses the FreeBSD number
      (563, not Linux's 318) and the mremap stub is a plain function that returns
      MAP_FAILED (-1) so runtime.mem takes its alloc-copy-free grow fallback (no
      in-place remap syscall on FreeBSD).  Standalone byte/symbol shape. }
    procedure TestLink_FreeBSDSyscallLeaf_GetrandomAndMremapStub;
    { Step 4c: the FreeBSD threads/TLS leaf — thr_new (455), _umtx_op (454) and
      thr_exit (431) link under the FreeBSD target with their FreeBSD syscall
      numbers present in the linked .text, and NOT Linux's clone (56) / futex
      (202).  Standalone byte/symbol shape. }
    procedure TestLink_FreeBSDThreadLeaf_SyscallNumbers;
  end;

  TDynLinkerTests = class(TTestCase)
  private
    function ProjectRoot: string;
  published
    procedure TestDyn_CollectsExternals;
    procedure TestDyn_PieHeaderEmitted;
  end;

  TDynLinkerE2ETests = class(TTestCase)
  private
    FScratch: string;
    function ProjectRoot: string;
    function RunBin(const AExe: string; out AStdout: string): Integer;
  protected
    procedure SetUp; override;
  published
    procedure TestRun_DynHelloWorld;
  end;

  TInternalLinkerE2ETests = class(TTestCase)
  private
    FScratch: string;
    FCompiler: string;
    FRTLPath: string;
    FStdlibPath: string;
    FCounter: Integer;
    function ProjectRoot: string;
    function CompilerAvailable: Boolean;
    function RunProc(const AExe: string; AArgs: array of string;
      out AStdout: string): Integer;
    function RunProcNoArgs(const AExe: string;
      out AStdout: string): Integer;
    function CompileAndRun(const ASrc: string;
      out AStdout: string; out AExitCode: Integer): Boolean;
  protected
    procedure SetUp; override;
  published
    procedure TestRun_HelloWorld;
    procedure TestRun_StringOps;
    procedure TestRun_ExceptionHandling;
    procedure TestRun_ClassAndVirtual;
    procedure TestLink_MissingRTL_FailsLoudly;
    { Step 6: a full compiler-CLI cross-compile with --target freebsd-x86_64
      selects the FreeBSD RTL adapter set (BuildRTLUnitList) and emits a static,
      freestanding FreeBSD ET_EXEC — EI_OSABI = 9, no PT_INTERP, entry _start —
      with no external tools.  The binary cannot run on the Linux host, so this
      asserts the emitted ELF shape only. }
    procedure TestCompile_FreeBSDTarget_EmitsStaticFreeBSDExe;
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
  Root, ObjDir, ArPath, ScriptOut: string;
  Compiler: string;
  Members: TList<TArchiveMember>;
  ObjList: TStringList;
  Proc: TProcess;
  Chunk: string;
  I: Integer;
  M: TArchiveMember;
  Obj: TElfObjectFile;
  SawLongName: Boolean;
begin
  { The shipped blaise_rtl.a is gone (RTL-unification Stage 3).  To still
    exercise the archive parser — including the GNU long-name (//) table on the
    >15-char member rtl.platform.layout.linux.o — build the RTL objects from
    source and bundle them into a THROWAWAY .a with `ar` just for this test.
    `ar` is a test-time dependency only; the product/bootstrap no longer use it. }
  Root     := ProjectRoot();
  Compiler := Root + 'compiler/target/blaise';
  if (not FileExists(Compiler))
     or (not FileExists(Root + 'compiler/src/main/pascal/runtime.arc.pas')) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  ObjDir := Root + 'compiler/target/test-archive-rtl';
  ScriptOut := '';
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := Root + 'scripts/build-rtl-objects.sh';
    Proc.Parameters.Add(Compiler);
    Proc.Parameters.Add(ObjDir);
    Proc.Parameters.Add('--with-startup');
    Proc.Execute();
    repeat
      Chunk := Proc.ReadOutput();
      ScriptOut := ScriptOut + Chunk
    until (Chunk = '') and not Proc.Running;
    Proc.WaitOnExit();
    if Proc.ExitCode <> 0 then
    begin
      Ignore('<toolchain-missing>');
      Exit;
    end;
  finally
    Proc.Free();
  end;

  { Bundle the built objects into a temp archive with ar.  Split the script's
    stdout (one object path per line) via TStringList. }
  ArPath := IncludeTrailingPathDelimiter(ObjDir) + 'rtl_test.a';
  DeleteFile(ArPath);
  ObjList := TStringList.Create();
  Proc := TProcess.Create(nil);
  try
    ObjList.Text := ScriptOut;
    Proc.Executable := 'ar';
    Proc.Parameters.Add('rcs');
    Proc.Parameters.Add(ArPath);
    for I := 0 to ObjList.Count - 1 do
      if Trim(ObjList.Strings[I]) <> '' then
        Proc.Parameters.Add(Trim(ObjList.Strings[I]));
    Proc.Execute();
    Proc.WaitOnExit();
    if (Proc.ExitCode <> 0) or (not FileExists(ArPath)) then
    begin
      Ignore('<toolchain-missing>');
      Exit;
    end;
  finally
    Proc.Free();
    ObjList.Free();
  end;

  Members := TList<TArchiveMember>.Create();
  try
    ReadArchiveFile(ArPath, Members);
    AssertTrue('expected several RTL members, got '
      + IntToStr(Members.Count), Members.Count >= 5);
    { A member whose name exceeds 15 chars exercises the GNU long-name (//)
      table.  rtl.platform.layout.linux.o is the longest current RTL member. }
    SawLongName := False;
    for I := 0 to Members.Count - 1 do
    begin
      M := Members.Get(I);
      if M.Name = 'rtl.platform.layout.linux.o' then
        SawLongName := True;
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
    AssertTrue('long-named member rtl.platform.layout.linux.o not found '
      + '(GNU long-name table mishandled?)', SawLongName);
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

procedure TLinkerTests.TestSym_TwoGlobalsDuplicate_FirstWins;
var
  Lk: TLinker;
  Bytes: string;
begin
  Lk := LinkObjs(
    ['.globl dup' + LineEnding + 'dup:' + LineEnding + 'ret' + LineEnding,
     '.globl dup' + LineEnding + 'dup:' + LineEnding + 'ret' + LineEnding +
     '.globl _start' + LineEnding + '_start:' + LineEnding + 'ret' + LineEnding],
    '_start', Bytes);
  Lk.Free();
  AssertTrue('first-wins duplicate linking must succeed', True);
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

procedure TLinkerTests.TestReloc_Quad64_ResolvesToAbsoluteAddr;
var
  Lk: TLinker;
  Bytes: string;
begin
  { An absolute 64-bit pointer to a symbol (`.quad target`, R_X86_64_64) is
    resolvable at link time in a non-PIE ET_EXEC: every symbol has a fixed load
    address.  The static linker must patch the slot with target's absolute
    address (no dynamic relocation) — this is what makes a freestanding static
    --static link possible (docs/linux-syscall-migration.adoc). }
  Lk := LinkObjs(
    ['.data' + LineEnding + 'ptr:' + LineEnding + '.quad target' + LineEnding +
     '.text' + LineEnding + '.globl target' + LineEnding + 'target:' +
     LineEnding + 'ret' + LineEnding +
     '.globl _start' + LineEnding + '_start:' + LineEnding + 'ret' + LineEnding],
    '_start', Bytes);
  try
    { The link must succeed and produce a valid ET_EXEC. }
    AssertTrue('static R_X86_64_64 link produced no output', Length(Bytes) >= 64);
    AssertEquals('e_type ET_EXEC', 2,
      (Ord(Bytes[16]) and $FF) or ((Ord(Bytes[17]) and $FF) shl 8));
  finally
    Lk.Free();
  end;
end;

procedure TLinkerTests.TestReloc_Abs32_ResolvesInStaticMode;
var
  Lk: TLinker;
  Bytes: string;
  Addr, Got: Int64;
  I, Slot: Integer;
begin
  { An absolute 32-bit data reference (.long target, R_X86_64_32) is
    resolvable at link time in a non-PIE ET_EXEC: the image is linked at a
    fixed base (0x400000) and every mapped address fits in 32 bits.  The
    OPDF emitter uses exactly this form (.long label) inside the .opdf
    section, so a static FreeBSD link with debug info must accept it.
    A marker word (0xDEADBEEF as decimal) precedes the slot so the test can
    locate the patched bytes in the flat image. }
  Lk := LinkObjs(
    ['.data' + LineEnding +
     'marker:' + LineEnding + '.long 3735928559' + LineEnding +
     'ptr32:' + LineEnding + '.long target' + LineEnding +
     '.text' + LineEnding + '.globl target' + LineEnding + 'target:' +
     LineEnding + 'ret' + LineEnding +
     '.globl _start' + LineEnding + '_start:' + LineEnding + 'ret' + LineEnding],
    '_start', Bytes);
  try
    Addr := Lk.AddrOfSymbol('target');
    AssertTrue('target resolved above base', Addr > $400000);
    { Find the marker; the patched abs32 slot follows it. }
    Slot := -1;
    for I := 0 to Length(Bytes) - 9 do
      if (OrdAt(Bytes, I) = $EF) and (OrdAt(Bytes, I + 1) = $BE) and
         (OrdAt(Bytes, I + 2) = $AD) and (OrdAt(Bytes, I + 3) = $DE) then
      begin
        Slot := I + 4;
        Break;
      end;
    AssertTrue('marker found in image', Slot >= 0);
    Got := OrdAt(Bytes, Slot) or (OrdAt(Bytes, Slot + 1) shl 8) or
           (OrdAt(Bytes, Slot + 2) shl 16) or (OrdAt(Bytes, Slot + 3) shl 24);
    AssertEquals('abs32 slot patched with target address', Addr, Got);
  finally
    Lk.Free();
  end;
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

procedure TLinkerE2ETests.TestLink_FreeBSDTarget_StampsOSABI;
const
  FixtureAsm =
    '.text' + LineEnding +
    '.globl _start' + LineEnding +
    '_start:' + LineEnding +
    '  movq $1, %rax' + LineEnding +
    '  movq $1, %rdi' + LineEnding +
    '  movq $60, %rax' + LineEnding +
    '  movq $0, %rdi' + LineEnding +
    '  .byte 15' + LineEnding + '  .byte 5' + LineEnding;
var
  Lk: TLinker;
  Obj: TElfObjectFile;
  BinPath, Bytes: string;
begin
  BinPath := FScratch + '/freebsd_osabi';
  { Build the linker with the FreeBSD link target (OSABI = 9). }
  Lk := TLinker.Create(FreeBSDX86_64Target());
  try
    Obj := ParseElfObject(AssembleToBytes(FixtureAsm), 'fb.o');
    Lk.AddOwnedObject(Obj);
    Lk.Link('_start', BinPath);
  finally
    Lk.Free();
  end;

  AssertTrue('linked FreeBSD binary missing', FileExists(BinPath));
  Bytes := ReadFile(BinPath);
  AssertTrue('output too small to be an ELF', Length(Bytes) >= 8);
  { ELF magic 0x7F 'E' 'L' 'F' at [0..3]; EI_OSABI is byte [7]. }
  AssertEquals('ELF magic byte 0', $7F, OrdAt(Bytes, 0));
  AssertEquals('EI_CLASS = ELFCLASS64', 2, OrdAt(Bytes, 4));
  AssertEquals('EI_OSABI = ELFOSABI_FREEBSD (9)', 9, OrdAt(Bytes, 7));
end;

procedure TLinkerE2ETests.TestLink_FreeBSDStart_StaticExecShape;
const
  { A self-contained FreeBSD _start: capture the stack, then exit(0) via
    SYS_exit = 1.  Mirrors runtime.start.static.freebsd's entry shape without
    pulling in main/_SetArgs, so it links with no undefined symbols. }
  FixtureAsm =
    '.text' + LineEnding +
    '.globl _start' + LineEnding +
    '_start:' + LineEnding +
    '  endbr64' + LineEnding +
    '  xorl %ebp, %ebp' + LineEnding +
    '  movq %rsp, %rdi' + LineEnding +
    '  xorl %edi, %edi' + LineEnding +
    '  movq $1, %rax' + LineEnding +       { SYS_exit }
    '  syscall' + LineEnding +
    '  hlt' + LineEnding;
var
  Lk: TLinker;
  Obj: TElfObjectFile;
  Bytes: string;
  Entry, StartAddr: Int64;
  PhOff, PhEntSz, PhCount, J, PType: Integer;
  FoundInterp: Boolean;
begin
  { LinkToBytes returns the binary in memory — ReadFile would truncate at the
    first NUL, which an ELF header hits at byte 8. }
  Lk := TLinker.Create(FreeBSDX86_64Target());
  try
    Obj := ParseElfObject(AssembleToBytes(FixtureAsm), 'fbstart.o');
    Lk.AddOwnedObject(Obj);
    Bytes := Lk.LinkToBytes('_start');
    StartAddr := Lk.AddrOfSymbol('_start');
  finally
    Lk.Free();
  end;

  AssertTrue('output too small to be an ELF', Length(Bytes) >= 64);

  { e_type at offset 16 must be ET_EXEC (2) — a static, non-PIE executable. }
  AssertEquals('e_type ET_EXEC', 2, OrdAt(Bytes, 16) or (OrdAt(Bytes, 17) shl 8));
  { EI_OSABI byte 7 = ELFOSABI_FREEBSD. }
  AssertEquals('EI_OSABI FreeBSD', 9, OrdAt(Bytes, 7));

  { e_entry (offset 24, 8 bytes LE) must equal the address of _start. }
  Entry := Int64(OrdAt(Bytes, 24)) or (Int64(OrdAt(Bytes, 25)) shl 8) or
           (Int64(OrdAt(Bytes, 26)) shl 16) or (Int64(OrdAt(Bytes, 27)) shl 24) or
           (Int64(OrdAt(Bytes, 28)) shl 32) or (Int64(OrdAt(Bytes, 29)) shl 40) or
           (Int64(OrdAt(Bytes, 30)) shl 48) or (Int64(OrdAt(Bytes, 31)) shl 56);
  AssertEquals('entry point is _start', StartAddr, Entry);

  { No PT_INTERP (type 3) among the program headers — a freestanding binary has
    no dynamic loader. }
  PhOff := OrdAt(Bytes, 32) or (OrdAt(Bytes, 33) shl 8) or
           (OrdAt(Bytes, 34) shl 16) or (OrdAt(Bytes, 35) shl 24);
  PhEntSz := OrdAt(Bytes, 54) or (OrdAt(Bytes, 55) shl 8);
  PhCount := OrdAt(Bytes, 56) or (OrdAt(Bytes, 57) shl 8);
  FoundInterp := False;
  for J := 0 to PhCount - 1 do
  begin
    PType := OrdAt(Bytes, PhOff + J * PhEntSz) or
             (OrdAt(Bytes, PhOff + J * PhEntSz + 1) shl 8) or
             (OrdAt(Bytes, PhOff + J * PhEntSz + 2) shl 16) or
             (OrdAt(Bytes, PhOff + J * PhEntSz + 3) shl 24);
    if PType = 3 then FoundInterp := True;
  end;
  AssertTrue('static ET_EXEC must have no PT_INTERP', not FoundInterp);
end;

procedure TLinkerE2ETests.TestLink_FreeBSDSyscallLeaf_SymbolsAndNumbers;
const
  { Mirrors the runtime.syscall.freebsd leaf bodies byte-for-byte (a handful of
    representative leaves): each is `movq $N, %rax; syscall; jae ok; negq %rax;
    ok: ret`, with mmap's `movq %rcx, %r10` and stat lowered to
    fstatat(AT_FDCWD, path, buf, 0).  Names are the bare POSIX symbols posix
    imports.  A leading _start keeps the linker's entry resolvable. }
  FixtureAsm =
    '.text' + LineEnding +
    '.globl _start' + LineEnding +
    '_start:' + LineEnding +
    '  callq open' + LineEnding +
    '  callq read' + LineEnding +
    '  callq write' + LineEnding +
    '  callq mmap' + LineEnding +
    '  callq stat' + LineEnding +
    '  xorl %edi, %edi' + LineEnding +
    '  movq $1, %rax' + LineEnding +        { SYS_exit }
    '  syscall' + LineEnding +
    '  hlt' + LineEnding +
    '.globl open' + LineEnding +
    'open:' + LineEnding +
    '  movq $5, %rax' + LineEnding +        { SYS_open }
    '  syscall' + LineEnding +
    '  jae .Lok_open' + LineEnding +
    '  negq %rax' + LineEnding +
    '.Lok_open:' + LineEnding +
    '  ret' + LineEnding +
    '.globl read' + LineEnding +
    'read:' + LineEnding +
    '  movq $3, %rax' + LineEnding +        { SYS_read }
    '  syscall' + LineEnding +
    '  jae .Lok_read' + LineEnding +
    '  negq %rax' + LineEnding +
    '.Lok_read:' + LineEnding +
    '  ret' + LineEnding +
    '.globl write' + LineEnding +
    'write:' + LineEnding +
    '  movq $4, %rax' + LineEnding +        { SYS_write }
    '  syscall' + LineEnding +
    '  jae .Lok_write' + LineEnding +
    '  negq %rax' + LineEnding +
    '.Lok_write:' + LineEnding +
    '  ret' + LineEnding +
    '.globl mmap' + LineEnding +
    'mmap:' + LineEnding +
    '  movq %rcx, %r10' + LineEnding +
    '  movq $477, %rax' + LineEnding +      { SYS_mmap (ino64) }
    '  syscall' + LineEnding +
    '  jae .Lok_mmap' + LineEnding +
    '  negq %rax' + LineEnding +
    '.Lok_mmap:' + LineEnding +
    '  ret' + LineEnding +
    '.globl stat' + LineEnding +
    'stat:' + LineEnding +
    '  movq %rsi, %rdx' + LineEnding +
    '  movq %rdi, %rsi' + LineEnding +
    '  movq $-100, %rdi' + LineEnding +     { AT_FDCWD }
    '  xorq %r10, %r10' + LineEnding +
    '  movq $552, %rax' + LineEnding +      { SYS_fstatat (ino64) }
    '  syscall' + LineEnding +
    '  jae .Lok_stat' + LineEnding +
    '  negq %rax' + LineEnding +
    '.Lok_stat:' + LineEnding +
    '  ret' + LineEnding;
  { Encoded `movq $imm32, %rax` = 48 C7 C0 <imm32-LE>.  These byte strings must
    appear in the linked .text if the correct syscall number was emitted. }
  function MovRaxImm(AImm: Integer): string;
  begin
    Result := Chr($48) + Chr($C7) + Chr($C0) +
              Chr(AImm and $FF) + Chr((AImm shr 8) and $FF) +
              Chr((AImm shr 16) and $FF) + Chr((AImm shr 24) and $FF);
  end;
var
  Lk: TLinker;
  Obj: TElfObjectFile;
  Bytes: string;
begin
  Lk := TLinker.Create(FreeBSDX86_64Target());
  try
    Obj := ParseElfObject(AssembleToBytes(FixtureAsm), 'fbsys.o');
    Lk.AddOwnedObject(Obj);
    Bytes := Lk.LinkToBytes('_start');

    { 1. The bare POSIX leaf symbols must be DEFINED (non-zero address). }
    AssertTrue('open defined',  Lk.AddrOfSymbol('open') > 0);
    AssertTrue('read defined',  Lk.AddrOfSymbol('read') > 0);
    AssertTrue('write defined', Lk.AddrOfSymbol('write') > 0);
    AssertTrue('mmap defined',  Lk.AddrOfSymbol('mmap') > 0);
    AssertTrue('stat defined',  Lk.AddrOfSymbol('stat') > 0);
  finally
    Lk.Free();
  end;

  { 2. FreeBSD ino64 syscall NUMBERS present in the linked .text as the
    `movq $N, %rax` encoding — NOT Linux's numbers. }
  AssertTrue('SYS_open=5 movq imm present',   Pos(MovRaxImm(5), Bytes) >= 0);
  AssertTrue('SYS_read=3 movq imm present',   Pos(MovRaxImm(3), Bytes) >= 0);
  AssertTrue('SYS_write=4 movq imm present',  Pos(MovRaxImm(4), Bytes) >= 0);
  AssertTrue('SYS_mmap=477 movq imm present', Pos(MovRaxImm(477), Bytes) >= 0);
  AssertTrue('SYS_fstatat=552 movq imm present (stat via fstatat)',
    Pos(MovRaxImm(552), Bytes) >= 0);

  { 3. The CF-error-translation idiom: negq %rax (48 F7 D8) must appear.  This
    is the FreeBSD-specific errno translation the Linux leaf does not emit. }
  AssertTrue('negq %rax (CF translation) present',
    Pos(Chr($48) + Chr($F7) + Chr($D8), Bytes) >= 0);
  { mmap's arg4 shuffle: movq %rcx, %r10 (49 89 CA). }
  AssertTrue('movq %rcx,%r10 (mmap arg4) present',
    Pos(Chr($49) + Chr($89) + Chr($CA), Bytes) >= 0);
end;

procedure TLinkerE2ETests.TestLink_FreeBSDSyscallLeaf_GetrandomAndMremapStub;
const
  { getrandom is a raw syscall with the FreeBSD number 563 (Linux's is 318).
    mremap has no FreeBSD syscall, so the leaf's stub just returns MAP_FAILED
    (-1) — a mov of -1 into %rax then ret; runtime.mem's realloc path treats
    that as "grow the slow way".  A leading _start keeps the entry resolvable. }
  FixtureAsm =
    '.text' + LineEnding +
    '.globl _start' + LineEnding +
    '_start:' + LineEnding +
    '  callq getrandom' + LineEnding +
    '  callq mremap' + LineEnding +
    '  xorl %edi, %edi' + LineEnding +
    '  movq $1, %rax' + LineEnding +        { SYS_exit }
    '  syscall' + LineEnding +
    '  hlt' + LineEnding +
    '.globl getrandom' + LineEnding +
    'getrandom:' + LineEnding +
    '  movq $563, %rax' + LineEnding +      { SYS_getrandom (FreeBSD) }
    '  syscall' + LineEnding +
    '  jae .Lok_gr' + LineEnding +
    '  negq %rax' + LineEnding +
    '.Lok_gr:' + LineEnding +
    '  ret' + LineEnding +
    '.globl mremap' + LineEnding +
    'mremap:' + LineEnding +
    '  movq $-1, %rax' + LineEnding +       { MAP_FAILED — no FreeBSD mremap }
    '  ret' + LineEnding;
  function MovRaxImm(AImm: Integer): string;
  begin
    Result := Chr($48) + Chr($C7) + Chr($C0) +
              Chr(AImm and $FF) + Chr((AImm shr 8) and $FF) +
              Chr((AImm shr 16) and $FF) + Chr((AImm shr 24) and $FF);
  end;
var
  Lk: TLinker;
  Obj: TElfObjectFile;
  Bytes: string;
begin
  Lk := TLinker.Create(FreeBSDX86_64Target());
  try
    Obj := ParseElfObject(AssembleToBytes(FixtureAsm), 'fbsys2.o');
    Lk.AddOwnedObject(Obj);
    Bytes := Lk.LinkToBytes('_start');
    AssertTrue('getrandom defined', Lk.AddrOfSymbol('getrandom') > 0);
    AssertTrue('mremap defined',    Lk.AddrOfSymbol('mremap') > 0);
  finally
    Lk.Free();
  end;
  { getrandom uses the FreeBSD number 563 — NOT Linux's 318. }
  AssertTrue('SYS_getrandom=563 movq imm present', Pos(MovRaxImm(563), Bytes) >= 0);
  AssertTrue('Linux SYS_getrandom=318 NOT present', Pos(MovRaxImm(318), Bytes) < 0);
  { mremap stub loads -1 (movq $-1,%rax = 48 C7 C0 FF FF FF FF). }
  AssertTrue('mremap stub returns -1 (MAP_FAILED)', Pos(MovRaxImm(-1), Bytes) >= 0);
end;

procedure TLinkerE2ETests.TestLink_FreeBSDThreadLeaf_SyscallNumbers;
const
  { Mirrors the runtime.syscall.freebsd threads/TLS leaf bodies: thr_new (455),
    _umtx_op (454, with its arg4 %rcx->%r10 shuffle) and thr_exit (431).  These
    are the FreeBSD analogues of Linux's clone (56) / futex (202) / exit (60);
    the numbers MUST be FreeBSD's, not Linux's.  A leading _start keeps the
    linker's entry resolvable. }
  FixtureAsm =
    '.text' + LineEnding +
    '.globl _start' + LineEnding +
    '_start:' + LineEnding +
    '  callq thr_new' + LineEnding +
    '  callq _umtx_op' + LineEnding +
    '  callq thr_exit' + LineEnding +
    '  xorl %edi, %edi' + LineEnding +
    '  movq $1, %rax' + LineEnding +        { SYS_exit }
    '  syscall' + LineEnding +
    '  hlt' + LineEnding +
    '.globl thr_new' + LineEnding +
    'thr_new:' + LineEnding +
    '  movq $455, %rax' + LineEnding +      { SYS_thr_new }
    '  syscall' + LineEnding +
    '  jae .Lok_thr_new' + LineEnding +
    '  negq %rax' + LineEnding +
    '.Lok_thr_new:' + LineEnding +
    '  ret' + LineEnding +
    '.globl _umtx_op' + LineEnding +
    '_umtx_op:' + LineEnding +
    '  movq %rcx, %r10' + LineEnding +
    '  movq $454, %rax' + LineEnding +      { SYS__umtx_op }
    '  syscall' + LineEnding +
    '  jae .Lok_umtx' + LineEnding +
    '  negq %rax' + LineEnding +
    '.Lok_umtx:' + LineEnding +
    '  ret' + LineEnding +
    '.globl thr_exit' + LineEnding +
    'thr_exit:' + LineEnding +
    '  movq $431, %rax' + LineEnding +      { SYS_thr_exit }
    '  syscall' + LineEnding +
    '  ret' + LineEnding;
  { Encoded `movq $imm32, %rax` = 48 C7 C0 <imm32-LE>. }
  function MovRaxImm(AImm: Integer): string;
  begin
    Result := Chr($48) + Chr($C7) + Chr($C0) +
              Chr(AImm and $FF) + Chr((AImm shr 8) and $FF) +
              Chr((AImm shr 16) and $FF) + Chr((AImm shr 24) and $FF);
  end;
var
  Lk: TLinker;
  Obj: TElfObjectFile;
  Bytes: string;
begin
  Lk := TLinker.Create(FreeBSDX86_64Target());
  try
    Obj := ParseElfObject(AssembleToBytes(FixtureAsm), 'fbthr.o');
    Lk.AddOwnedObject(Obj);
    Bytes := Lk.LinkToBytes('_start');
    { The bare thread-primitive symbols must be DEFINED (non-zero address). }
    AssertTrue('thr_new defined',  Lk.AddrOfSymbol('thr_new') > 0);
    AssertTrue('_umtx_op defined', Lk.AddrOfSymbol('_umtx_op') > 0);
    AssertTrue('thr_exit defined', Lk.AddrOfSymbol('thr_exit') > 0);
  finally
    Lk.Free();
  end;
  { FreeBSD thread syscall NUMBERS present in the linked .text. }
  AssertTrue('SYS_thr_new=455 movq imm present',  Pos(MovRaxImm(455), Bytes) >= 0);
  AssertTrue('SYS__umtx_op=454 movq imm present', Pos(MovRaxImm(454), Bytes) >= 0);
  AssertTrue('SYS_thr_exit=431 movq imm present', Pos(MovRaxImm(431), Bytes) >= 0);
  { NOT Linux's clone (56) / futex (202) — those numbers must be absent. }
  AssertTrue('Linux SYS_clone=56 NOT present',  Pos(MovRaxImm(56), Bytes) < 0);
  AssertTrue('Linux SYS_futex=202 NOT present', Pos(MovRaxImm(202), Bytes) < 0);
  { _umtx_op's arg4 shuffle: movq %rcx, %r10 (49 89 CA). }
  AssertTrue('movq %rcx,%r10 (_umtx_op arg4) present',
    Pos(Chr($49) + Chr($89) + Chr($CA), Bytes) >= 0);
end;

{ ---- TDynLinkerTests ---- }

function TDynLinkerTests.ProjectRoot: string;
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

procedure TDynLinkerTests.TestDyn_CollectsExternals;
const
  MainAsm =
    '.text' + LineEnding +
    '.globl main' + LineEnding +
    'main:' + LineEnding +
    '  callq write' + LineEnding +
    '  xorl %eax, %eax' + LineEnding +
    '  ret' + LineEnding;
var
  Lk: TLinker;
  Obj: TElfObjectFile;
  Bytes: string;
begin
  Lk := TLinker.Create();
  try
    Lk.SetDynamic(True);
    Obj := ParseElfObject(AssembleToBytes(MainAsm), 'main.o');
    Lk.AddOwnedObject(Obj);
    Bytes := Lk.LinkToBytes('main');
    AssertTrue('output should be non-empty', Length(Bytes) > 64);
    { e_type at offset 16 must be ET_DYN (3). }
    AssertEquals('e_type ET_DYN', 3,
      (Ord(Bytes[16]) and $FF) or ((Ord(Bytes[17]) and $FF) shl 8));
  finally
    Lk.Free();
  end;
end;

procedure TDynLinkerTests.TestDyn_PieHeaderEmitted;
const
  MainAsm =
    '.text' + LineEnding +
    '.globl main' + LineEnding +
    'main:' + LineEnding +
    '  xorl %eax, %eax' + LineEnding +
    '  ret' + LineEnding;
var
  Lk: TLinker;
  Obj: TElfObjectFile;
  Bytes: string;
  PhOff, PhCount, PhEntSz: Integer;
  J, PType: Integer;
  FoundInterp, FoundDynamic: Boolean;
begin
  Lk := TLinker.Create();
  try
    Lk.SetDynamic(True);
    Obj := ParseElfObject(AssembleToBytes(MainAsm), 'main.o');
    Lk.AddOwnedObject(Obj);
    Bytes := Lk.LinkToBytes('main');

    { Parse e_phoff (offset 32, 8 bytes LE), e_phentsize (54, 2 bytes),
      e_phnum (56, 2 bytes). }
    PhOff := Ord(Bytes[32]) or (Ord(Bytes[33]) shl 8) or
             (Ord(Bytes[34]) shl 16) or (Ord(Bytes[35]) shl 24);
    PhEntSz := Ord(Bytes[54]) or (Ord(Bytes[55]) shl 8);
    PhCount := Ord(Bytes[56]) or (Ord(Bytes[57]) shl 8);
    AssertTrue('should have at least 4 phdrs', PhCount >= 4);
    AssertEquals('phdr entry size', 56, PhEntSz);

    FoundInterp := False;
    FoundDynamic := False;
    for J := 0 to PhCount - 1 do
    begin
      PType := Ord(Bytes[PhOff + J * PhEntSz]) or
               (Ord(Bytes[PhOff + J * PhEntSz + 1]) shl 8) or
               (Ord(Bytes[PhOff + J * PhEntSz + 2]) shl 16) or
               (Ord(Bytes[PhOff + J * PhEntSz + 3]) shl 24);
      if PType = 3 then FoundInterp := True;    { PT_INTERP }
      if PType = 2 then FoundDynamic := True;   { PT_DYNAMIC }
    end;
    AssertTrue('PT_INTERP present', FoundInterp);
    AssertTrue('PT_DYNAMIC present', FoundDynamic);
  finally
    Lk.Free();
  end;
end;

{ ---- TDynLinkerE2ETests ---- }

function TDynLinkerE2ETests.ProjectRoot: string;
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

procedure TDynLinkerE2ETests.SetUp;
begin
  inherited SetUp();
  FScratch := ProjectRoot() + 'compiler/target/linker-e2e';
  ForceDirectories(FScratch);
end;

function TDynLinkerE2ETests.RunBin(const AExe: string;
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

procedure TDynLinkerE2ETests.TestRun_DynHelloWorld;
const
  { A minimal main() that calls write(1, msg, 15) via PLT and returns 42.
    Scrt1.o provides _start which calls __libc_start_main(main,...). }
  MainAsm =
    '.text' + LineEnding +
    '.globl main' + LineEnding +
    'main:' + LineEnding +
    '  subq $8, %rsp' + LineEnding +
    '  movl $1, %edi' + LineEnding +
    '  leaq msg(%rip), %rsi' + LineEnding +
    '  movl $16, %edx' + LineEnding +
    '  callq write' + LineEnding +
    '  movl $42, %eax' + LineEnding +
    '  addq $8, %rsp' + LineEnding +
    '  ret' + LineEnding +
    '.section .rodata' + LineEnding +
    'msg:' + LineEnding +
    '  .ascii "Hello, dynlink!\n"' + LineEnding;
var
  Lk: TLinker;
  Obj: TElfObjectFile;
  BinPath, Output: string;
  Rc: Integer;
  Crt1, Crti, Crtn, CrtBegin, CrtEnd: string;
begin
  BinPath := FScratch + '/hello_dyn';

  { Locate CRT objects. }
  Crt1 := '/usr/lib/x86_64-linux-gnu/Scrt1.o';
  Crti := '/usr/lib/x86_64-linux-gnu/crti.o';
  Crtn := '/usr/lib/x86_64-linux-gnu/crtn.o';
  CrtBegin := '/usr/lib/gcc/x86_64-linux-gnu/13/crtbeginS.o';
  CrtEnd := '/usr/lib/gcc/x86_64-linux-gnu/13/crtendS.o';

  if not FileExists(Crt1) then
  begin
    { Try GCC 14. }
    CrtBegin := '/usr/lib/gcc/x86_64-linux-gnu/14/crtbeginS.o';
    CrtEnd := '/usr/lib/gcc/x86_64-linux-gnu/14/crtendS.o';
  end;

  if not FileExists(Crt1) or not FileExists(CrtBegin) then
    Exit;

  Lk := TLinker.Create();
  try
    Lk.SetDynamic(True);
    Lk.AddCrtObject(Crt1);
    Lk.AddCrtObject(Crti);
    Lk.AddCrtObject(CrtBegin);
    Obj := ParseElfObject(AssembleToBytes(MainAsm), 'main.o');
    Lk.AddOwnedObject(Obj);
    Lk.AddCrtObject(CrtEnd);
    Lk.AddCrtObject(Crtn);
    Lk.Link('_start', BinPath);
  finally
    Lk.Free();
  end;

  AssertTrue('linked binary missing', FileExists(BinPath));
  Rc := RunBin(BinPath, Output);
  AssertEquals('exit code', 42, Rc);
  AssertEquals('stdout', 'Hello, dynlink!' + Chr(10), Output);
end;

{ ---- TInternalLinkerE2ETests ---- }

{ symlink(2): point the isolated-dir compiler name at the real binary so
  CompilerBinDir() resolves to the isolated dir (no blaise_rtl.a beside it),
  without copying ~3 MB.  Returns 0 on success. }
function _test_symlink(ATarget, ALinkPath: PChar): Integer;
  external name 'symlink';

var
  GIntLinkSkipNoted: Boolean = False;

function TInternalLinkerE2ETests.ProjectRoot: string;
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

procedure TInternalLinkerE2ETests.SetUp;
begin
  inherited SetUp();
  FCompiler := ProjectRoot() + 'compiler/target/blaise';
  FRTLPath := ProjectRoot() + 'compiler/src/main/pascal';
  FStdlibPath := ProjectRoot() + 'stdlib/src/main/pascal';
  FScratch := ProjectRoot() + 'compiler/target/intlink_scratch/';
  ForceDirectories(FScratch);
  FCounter := 0;
end;

function TInternalLinkerE2ETests.CompilerAvailable: Boolean;
begin
  { The compiler source-builds the RTL itself (no blaise_rtl.a); only the binary
    and the RTL source need to be present. }
  Result := FileExists(FCompiler) and
            FileExists(FRTLPath + '/runtime.arc.pas');
  if (not Result) and (not GIntLinkSkipNoted) then
  begin
    GIntLinkSkipNoted := True;
    WriteLn(StdErr, 'note: TInternalLinkerE2ETests skipped — compiler binary "',
            FCompiler, '" or RTL source not found');
  end;
end;

function TInternalLinkerE2ETests.RunProc(const AExe: string;
  AArgs: array of string; out AStdout: string): Integer;
var
  Proc: TProcess;
  I: Integer;
  Chunk: string;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    for I := 0 to High(AArgs) do
      Proc.Parameters.Add(AArgs[I]);
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

function TInternalLinkerE2ETests.RunProcNoArgs(const AExe: string;
  out AStdout: string): Integer;
var
  Proc: TProcess;
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

function TInternalLinkerE2ETests.CompileAndRun(const ASrc: string;
  out AStdout: string; out AExitCode: Integer): Boolean;
var
  SrcFile, OutFile, CompOut: string;
  Rc: Integer;
begin
  Result := False;
  if not Self.CompilerAvailable() then Exit;

  FCounter := FCounter + 1;
  SrcFile := FScratch + 'test_il_' + IntToStr(FCounter) + '.pas';
  OutFile := FScratch + 'test_il_' + IntToStr(FCounter);

  WriteFile(SrcFile, ASrc);

  Rc := Self.RunProc(FCompiler, [
    '--source', SrcFile,
    '--unit-path', FRTLPath,
    '--unit-path', FStdlibPath,
    '--output', OutFile,
    '--backend', 'native',
    '--assembler', 'internal',
    '--linker', 'internal'
  ], CompOut);
  if Rc <> 0 then
    Fail('compile failed (rc=' + IntToStr(Rc) + '): ' + CompOut);

  AExitCode := Self.RunProcNoArgs(OutFile, AStdout);
  Result := True;
end;

procedure TInternalLinkerE2ETests.TestRun_HelloWorld;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_hello;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(''Hello from internal linker'')' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals('exit code', 0, EC);
  AssertEquals('stdout', 'Hello from internal linker' + LineEnding, Out_);
end;

procedure TInternalLinkerE2ETests.TestRun_StringOps;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_str;' + LineEnding +
    'uses SysUtils;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(UpperCase(''hello''));' + LineEnding +
    '  WriteLn(IntToStr(42));' + LineEnding +
    '  WriteLn(Format(''%d+%d=%d'', [1, 2, 3]))' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals('exit code', 0, EC);
  AssertEquals('stdout',
    'HELLO' + LineEnding +
    '42' + LineEnding +
    '1+2=3' + LineEnding, Out_);
end;

procedure TInternalLinkerE2ETests.TestRun_ExceptionHandling;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_exc;' + LineEnding +
    'uses SysUtils;' + LineEnding +
    'begin' + LineEnding +
    '  try' + LineEnding +
    '    raise Exception.Create(''boom'');' + LineEnding +
    '  except' + LineEnding +
    '    on E: Exception do' + LineEnding +
    '      WriteLn(E.Message);' + LineEnding +
    '  end;' + LineEnding +
    '  WriteLn(''OK'')' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals('exit code', 0, EC);
  AssertEquals('stdout', 'boom' + LineEnding + 'OK' + LineEnding, Out_);
end;

procedure TInternalLinkerE2ETests.TestRun_ClassAndVirtual;
var
  Out_: string;
  EC: Integer;
begin
  if not CompileAndRun(
    'program test_cls;' + LineEnding +
    'type' + LineEnding +
    '  TBase = class' + LineEnding +
    '    function Name: string; virtual;' + LineEnding +
    '  end;' + LineEnding +
    '  TChild = class(TBase)' + LineEnding +
    '    function Name: string; override;' + LineEnding +
    '  end;' + LineEnding +
    'function TBase.Name: string;' + LineEnding +
    'begin' + LineEnding +
    '  Result := ''base'';' + LineEnding +
    'end;' + LineEnding +
    'function TChild.Name: string;' + LineEnding +
    'begin' + LineEnding +
    '  Result := ''child'';' + LineEnding +
    'end;' + LineEnding +
    'var' + LineEnding +
    '  B: TBase;' + LineEnding +
    'begin' + LineEnding +
    '  B := TChild.Create();' + LineEnding +
    '  try' + LineEnding +
    '    WriteLn(B.Name())' + LineEnding +
    '  finally' + LineEnding +
    '    B.Free()' + LineEnding +
    '  end' + LineEnding +
    'end.',
    Out_, EC) then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;
  AssertEquals('exit code', 0, EC);
  AssertEquals('stdout', 'child' + LineEnding, Out_);
end;

{ Regression: when blaise_rtl.a cannot be found beside the compiler binary
  (and BLAISE_RTL is unset), the compiler must REFUSE to link rather than
  silently emit a binary with every RTL symbol left as an undefined dynamic
  import — that broken-but-runnable binary dies at run time with
  `undefined symbol: _SetArgs`.  A mismatched carried-RTL name in
  rolling-bootstrap surfaced exactly this.  We reproduce by running a COPY of
  the compiler from a scratch dir that has no blaise_rtl.a beside it. }
procedure TInternalLinkerE2ETests.TestLink_MissingRTL_FailsLoudly;
var
  IsoDir, IsoCompiler, SrcFile, OutFile, CompOut: string;
  Rc: Integer;
begin
  if not Self.CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;

  FCounter := FCounter + 1;
  IsoDir := FScratch + 'no_rtl_' + IntToStr(FCounter) + '/';
  ForceDirectories(IsoDir);
  IsoCompiler := FCompiler;

  SrcFile := IsoDir + 'prog.pas';
  OutFile := IsoDir + 'prog';
  WriteFile(SrcFile,
    'program test_no_rtl;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(6 * 7)' + LineEnding +
    'end.');

  { The RTL is now compiled from SOURCE by the compiler at link time (no prebuilt
    blaise_rtl.a).  Point --rtl-src at a nonexistent directory so the RTL source
    is unreachable: the driver must fail loudly rather than emit a broken binary. }
  Rc := Self.RunProc(IsoCompiler, [
    '--source', SrcFile,
    '--unit-path', FStdlibPath,
    '--output', OutFile,
    '--backend', 'native',
    '--assembler', 'internal',
    '--linker', 'internal',
    '--rtl-src', IsoDir + 'no_such_rtl_src'
  ], CompOut);

  AssertTrue('compiler must FAIL when the RTL source is unreachable (got rc=0)',
    Rc <> 0);
  AssertTrue('error must name the missing RTL source: ' + CompOut,
    Pos('RTL source', CompOut) >= 0);
  AssertFalse('no output binary should be produced on RTL-missing failure',
    FileExists(OutFile));
end;

procedure TInternalLinkerE2ETests.TestCompile_FreeBSDTarget_EmitsStaticFreeBSDExe;
var
  SrcFile, OutFile, CompOut, Bytes: string;
  Rc, PhOff, PhEntSz, PhCount, J, PType: Integer;
  FoundInterp: Boolean;
begin
  if not Self.CompilerAvailable() then
  begin
    Ignore('<toolchain-missing>');
    Exit;
  end;

  FCounter := FCounter + 1;
  SrcFile := FScratch + 'test_fbsd_' + IntToStr(FCounter) + '.pas';
  OutFile := FScratch + 'test_fbsd_' + IntToStr(FCounter);
  WriteFile(SrcFile,
    'program test_fbsd;' + LineEnding +
    'begin' + LineEnding +
    '  WriteLn(''Hello'')' + LineEnding +
    'end.');

  { Full compiler-CLI cross-compile.  --target freebsd-x86_64 must select the
    FreeBSD RTL adapter set and drive the static, freestanding link with no
    external tools (internal assembler + linker). }
  Rc := Self.RunProc(FCompiler, [
    '--source', SrcFile,
    '--unit-path', FRTLPath,
    '--unit-path', FStdlibPath,
    '--output', OutFile,
    '--backend', 'native',
    '--assembler', 'internal',
    '--linker', 'internal',
    '--target', 'freebsd-x86_64'
  ], CompOut);
  if Rc <> 0 then
    Fail('--target freebsd-x86_64 compile failed (rc=' + IntToStr(Rc) + '): ' +
         CompOut);
  AssertTrue('FreeBSD binary was produced', FileExists(OutFile));

  { The FreeBSD binary cannot run on the Linux host — assert its ELF shape.
    ReadWholeFile is NUL-safe (unlike the RTL ReadFile, which stops at the
    first NUL — an ELF header hits one at byte 8). }
  Bytes := ReadWholeFile(OutFile);
  AssertTrue('output too small to be an ELF', Length(Bytes) >= 64);

  { EI_OSABI byte 7 = ELFOSABI_FREEBSD (9). }
  AssertEquals('EI_OSABI FreeBSD', 9, OrdAt(Bytes, 7));
  { e_type at offset 16 = ET_EXEC (2) — static, non-PIE. }
  AssertEquals('e_type ET_EXEC', 2, OrdAt(Bytes, 16) or (OrdAt(Bytes, 17) shl 8));

  { No PT_INTERP (program-header type 3): a freestanding binary has no dynamic
    loader. }
  PhOff := OrdAt(Bytes, 32) or (OrdAt(Bytes, 33) shl 8) or
           (OrdAt(Bytes, 34) shl 16) or (OrdAt(Bytes, 35) shl 24);
  PhEntSz := OrdAt(Bytes, 54) or (OrdAt(Bytes, 55) shl 8);
  PhCount := OrdAt(Bytes, 56) or (OrdAt(Bytes, 57) shl 8);
  FoundInterp := False;
  for J := 0 to PhCount - 1 do
  begin
    PType := OrdAt(Bytes, PhOff + J * PhEntSz) or
             (OrdAt(Bytes, PhOff + J * PhEntSz + 1) shl 8) or
             (OrdAt(Bytes, PhOff + J * PhEntSz + 2) shl 16) or
             (OrdAt(Bytes, PhOff + J * PhEntSz + 3) shl 24);
    if PType = 3 then FoundInterp := True;
  end;
  AssertFalse('freestanding FreeBSD exe must have no PT_INTERP', FoundInterp);
end;

initialization
  RegisterTest(TElfReaderTests);
  RegisterTest(TSectionMergerTests);
  RegisterTest(TLinkerTests);
  RegisterTest(TLinkerE2ETests);
  RegisterTest(TDynLinkerTests);
  RegisterTest(TDynLinkerE2ETests);
  RegisterTest(TInternalLinkerE2ETests);

end.
