{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.linker.elf;

{ Internal ELF linker — section merging (Phase A) plus symbol
  resolution, static relocations, and non-PIE ET_EXEC emission
  (Phase B of docs/internal-linker-design.adoc).

  Phase A — TSectionMerger concatenates like-named allocatable
  sections from a set of parsed input objects, padding each
  contribution to its section's alignment, and records a placement
  (merged section + offset) for every input section.  Placements are
  the basis for symbol and relocation rebasing: a symbol's final
  offset is its object-local value plus its section's placement
  offset.

  SHT_NOBITS contributions advance the merged size without adding
  bytes; mixing NOBITS and PROGBITS under one name is rejected.
  Non-allocatable bookkeeping sections (symtab, strtab, rela,
  .note.GNU-stack, .comment) are skipped — the linker rebuilds those
  itself.  Non-alloc .opdf.* debug sections ARE kept: they must ride
  through into the final executable for the OPDF debugger.

  Phase B — TLinker takes a set of parsed objects, merges their
  sections, assigns virtual addresses at a fixed base (non-PIE
  ET_EXEC, no GOT/PLT, no dynamic linking), builds a global symbol
  table, resolves intra-program PC-relative relocations
  (R_X86_64_PC32, R_X86_64_PLT32), and writes a runnable executable.
  This is the standalone-program path of the design: every real
  Blaise program reaches libc through the RTL and needs Phase C's
  dynamic linker, but a hand-written object that talks to the kernel
  through raw syscalls links and runs with Phase B alone.

  Relocation types that require dynamic linking (R_X86_64_64 in a
  PIE, GOT/PLT/TLS forms) and absolute 32-bit symbol references
  (R_X86_64_32 / R_X86_64_32S, which a static ET_EXEC could in
  principle take but the native backend does not emit for symbol
  references) are rejected with a diagnostic — they belong to later
  phases or are codegen bugs. }

interface

uses
  SysUtils, Generics.Collections, streams, blaise.elfreader;

type
  ELinker = class(Exception);

  { Platform/architecture parameters for one link target.

    Phase B fills this for Linux x86-64 ELF only, but every value that
    differs across the roadmap targets (i386/x86-64, Linux/FreeBSD,
    later Windows) lives here rather than hard-coded in the emitter,
    so adding a target is a new record value plus, where the container
    differs (PE/Mach-O), a sibling writer behind the same TLinker
    symbol/relocation core.  See the "Platform Parameterisation"
    section of docs/internal-linker-design.adoc.

    The pointer width (Is64) drives ELF class, header sizes, address
    arithmetic and the relocation set; OSABI/BaseAddr/PageSize are the
    per-OS knobs.  Container format (ELF vs PE/Mach-O) is implied by
    which writer is invoked; only ELF targets are modelled here. }
  TLinkArch = (laX86_64, laI386);

  TLinkTarget = class
  public
    Arch:      TLinkArch;
    Is64:      Boolean;       { 64-bit pointers/addresses }
    OSABI:     Integer;       { EI_OSABI: 0 = SysV/Linux, 9 = FreeBSD }
    EMachine:  Integer;       { e_machine: EM_X86_64 / EM_386 }
    BaseAddr:  Int64;         { fixed load base for non-PIE ET_EXEC }
    PageSize:  Int64;         { segment alignment }
    constructor Create;
  end;

  { Linux x86-64 ELF, non-PIE ET_EXEC.  Caller frees. }
function LinuxX86_64Target: TLinkTarget;

type
  { One output section accumulating contributions from input objects. }
  TMergedSection = class
  public
    Name:   string;
    ShType: Integer;
    Flags:  Int64;
    Align:  Int64;
    Data:   string;     { concatenated bytes; empty for SHT_NOBITS }
    Size:   Int64;      { total size including NOBITS reservations }
  end;

  { Where one input section landed: merged section + byte offset. }
  TSectionPlacement = class
  public
    ObjIndex: Integer;        { caller-assigned input object index }
    SecIndex: Integer;        { ELF section index within that object }
    Merged:   TMergedSection; { destination (not owned) }
    Offset:   Int64;          { offset of the contribution }
  end;

  TSectionMerger = class
  private
    FMerged:     TList<TMergedSection>;
    FPlacements: TList<TSectionPlacement>;
    function GetOrCreate(ASec: TRdSection): TMergedSection;
    function WantSection(ASec: TRdSection): Boolean;
  public
    constructor Create;
    destructor Destroy; override;

    { Merge every wanted section of AObj.  AObjIndex tags the
      placements; callers number their inputs sequentially. }
    procedure AddObject(AObjIndex: Integer; AObj: TElfObjectFile);

    function FindMerged(const AName: string): TMergedSection;
    { Placement of input object AObjIndex's section ASecIndex, or nil
      if that section was skipped. }
    function PlacementOf(AObjIndex, ASecIndex: Integer): TSectionPlacement;

    property Merged: TList<TMergedSection> read FMerged;
    property Placements: TList<TSectionPlacement> read FPlacements;
  end;

  { A resolved global symbol: name plus final virtual address.  Built
    after layout, so Addr is absolute for the chosen load base. }
  TLinkSymbol = class
  public
    Name:       string;
    Addr:       Int64;     { final virtual address (0 for weak-undef) }
    Defined:    Boolean;   { False = weak undefined resolved to 0 }
    IsFunc:     Boolean;
    IsWeakSlot: Boolean;   { defined only by a STB_WEAK symbol so far }
  end;

  { Phase B linker: merge → layout → resolve symbols → relocate →
    emit a non-PIE ET_EXEC.  One instance links one executable.

    Lifecycle: AddObject* for each input, then Link(entry, output).
    The merger, layout addresses, symbol table and patched section
    bytes are all owned by the linker and freed with it. }
  TLinker = class
  private
    FTarget:   TLinkTarget;
    FOwnTarget: Boolean;
    FObjects:  TList<TElfObjectFile>;
    FOwned:    TList<TElfObjectFile>;   { objects we must free }
    FMerger:   TSectionMerger;
    FSymbols:  TList<TLinkSymbol>;
    FSecAddr:  TList<TMergedSection>;   { merged sections, in layout order }
    FAddrOf:   TList<Int64>;            { virtual base addr per FSecAddr entry }
    FEntry:    Int64;

    function MergedAddr(AMerged: TMergedSection): Int64;
    function SectionOfPlacement(AObjIdx, ASecIdx: Integer): TMergedSection;
    function PlacementBaseAddr(AObjIdx, ASecIdx: Integer): Int64;
    function FileOffset(AAddr: Int64): Integer;
    procedure PlaceSection(AM: TMergedSection; var AAddr: Int64);
    procedure LayoutSections;
    procedure BuildSymbols;
    function FindSymbol(const AName: string): TLinkSymbol;
    procedure AddSynthSymbol(const AName: string; AAddr: Int64);
    procedure DefineSynthSymbols;
    procedure ApplyRelocations;
    function ResolveSymbolAddr(AObj: TElfObjectFile; ASymIdx: Integer;
      const AContext: string): Int64;
    function EmitExecutable(AEntry: Int64): string;
  public
    constructor Create; overload;
    constructor Create(ATarget: TLinkTarget); overload;  { borrows target }
    destructor Destroy; override;

    { Add a parsed object the caller owns (not freed by the linker). }
    procedure AddObject(AObj: TElfObjectFile);
    { Add an object the linker takes ownership of and frees. }
    procedure AddOwnedObject(AObj: TElfObjectFile);

    { Merge, lay out, resolve, relocate and write an ET_EXEC whose
      entry point is the symbol AEntryName.  Raises ELinker on any
      unresolved symbol, duplicate definition, or unsupported
      relocation. }
    procedure Link(const AEntryName, AOutputPath: string);

    { Same pipeline, returning the executable bytes instead of writing
      a file (used by tests for structural assertions). }
    function LinkToBytes(const AEntryName: string): string;

    { Address a global symbol resolved to (valid only after Link/
      LinkToBytes).  -1 if absent. }
    function AddrOfSymbol(const AName: string): Int64;

    { Merged section by name (e.g. '.text'), or nil — exposes the
      relocated bytes for tests/inspection.  Valid after Link. }
    function FindMerged(const AName: string): TMergedSection;
    function FindMergedText: TMergedSection;

    property Target: TLinkTarget read FTarget;
  end;

{ Mark a file user+group+other readable/executable (0755).  Used to
  make the linked output runnable. }
procedure MakeFileExecutable(const APath: string);

implementation

function LkAlignUp(AVal: Int64; AAlign: Int64): Int64;
var
  Rem: Int64;
begin
  if AAlign <= 1 then
  begin
    Result := AVal;
    Exit;
  end;
  Rem := AVal mod AAlign;
  if Rem = 0 then
    Result := AVal
  else
    Result := AVal + (AAlign - Rem);
end;

function LkZeros(ACount: Int64): string;
var
  I: Int64;
begin
  Result := '';
  I := 0;
  while I < ACount do
  begin
    Result := Result + Chr(0);
    I := I + 1;
  end;
end;

constructor TSectionMerger.Create;
begin
  inherited Create();
  FMerged := TList<TMergedSection>.Create();
  FPlacements := TList<TSectionPlacement>.Create();
end;

destructor TSectionMerger.Destroy;
var
  I: Integer;
begin
  for I := 0 to FMerged.Count - 1 do
    FMerged.Get(I).Free();
  FMerged.Free();
  for I := 0 to FPlacements.Count - 1 do
    FPlacements.Get(I).Free();
  FPlacements.Free();
  inherited Destroy();
end;

function TSectionMerger.WantSection(ASec: TRdSection): Boolean;
begin
  { Bookkeeping sections are rebuilt by the linker, never merged. }
  if (ASec.ShType = SHT_NULL) or (ASec.ShType = SHT_SYMTAB) or
     (ASec.ShType = SHT_STRTAB) or (ASec.ShType = SHT_RELA) then
  begin
    Result := False;
    Exit;
  end;
  if (ASec.Name = '.note.GNU-stack') or (ASec.Name = '.comment') then
  begin
    Result := False;
    Exit;
  end;
  { Allocatable sections always merge; non-alloc only for the OPDF
    debug pass-through. }
  if (ASec.Flags and SHF_ALLOC) <> 0 then
    Result := True
  else
    Result := Pos('.opdf', ASec.Name) = 0;
end;

function TSectionMerger.GetOrCreate(ASec: TRdSection): TMergedSection;
var
  I: Integer;
  M: TMergedSection;
begin
  for I := 0 to FMerged.Count - 1 do
  begin
    M := FMerged.Get(I);
    if M.Name = ASec.Name then
    begin
      if (M.ShType = SHT_NOBITS) <> (ASec.ShType = SHT_NOBITS) then
        raise ELinker.Create('section ' + ASec.Name
          + ': NOBITS and PROGBITS contributions cannot be merged');
      Result := M;
      Exit;
    end;
  end;
  M := TMergedSection.Create();
  M.Name := ASec.Name;
  M.ShType := ASec.ShType;
  M.Flags := ASec.Flags;
  M.Align := 1;
  M.Data := '';
  M.Size := 0;
  FMerged.Add(M);
  Result := M;
end;

procedure TSectionMerger.AddObject(AObjIndex: Integer; AObj: TElfObjectFile);
var
  I: Integer;
  Sec: TRdSection;
  M: TMergedSection;
  P: TSectionPlacement;
  Aligned: Int64;
  SecAlign: Int64;
begin
  for I := 0 to AObj.Sections.Count - 1 do
  begin
    Sec := AObj.Sections.Get(I);
    if not Self.WantSection(Sec) then Continue;

    M := Self.GetOrCreate(Sec);
    SecAlign := Sec.AddrAlign;
    if SecAlign < 1 then SecAlign := 1;
    if SecAlign > M.Align then M.Align := SecAlign;

    Aligned := LkAlignUp(M.Size, SecAlign);
    if M.ShType <> SHT_NOBITS then
    begin
      if Aligned > M.Size then
        M.Data := M.Data + LkZeros(Aligned - M.Size);
      M.Data := M.Data + Sec.Data;
    end;
    P := TSectionPlacement.Create();
    P.ObjIndex := AObjIndex;
    P.SecIndex := I;
    P.Merged := M;
    P.Offset := Aligned;
    FPlacements.Add(P);
    M.Size := Aligned + Sec.Size;
  end;
end;

function TSectionMerger.FindMerged(const AName: string): TMergedSection;
var
  I: Integer;
begin
  for I := 0 to FMerged.Count - 1 do
    if FMerged.Get(I).Name = AName then
    begin
      Result := FMerged.Get(I);
      Exit;
    end;
  Result := nil;
end;

function TSectionMerger.PlacementOf(AObjIndex,
  ASecIndex: Integer): TSectionPlacement;
var
  I: Integer;
  P: TSectionPlacement;
begin
  for I := 0 to FPlacements.Count - 1 do
  begin
    P := FPlacements.Get(I);
    if (P.ObjIndex = AObjIndex) and (P.SecIndex = ASecIndex) then
    begin
      Result := P;
      Exit;
    end;
  end;
  Result := nil;
end;

{ ---- ELF executable constants (Phase B) ------------------------------- }

const
  ET_EXEC = 2;
  EM_386  = 3;

  ELFOSABI_SYSV    = 0;
  ELFOSABI_FREEBSD = 9;

  PT_LOAD   = 1;
  PF_X = 1;
  PF_W = 2;
  PF_R = 4;

  EI_NIDENT = 16;

{ ---- Little-endian byte writers --------------------------------------- }

{ Blaise codegen does not support assigning to a string element through
  a var-string parameter (`ABuf[i] := c` on a var param), so every
  encoder here RETURNS the bytes and callers append them; fixed-offset
  patching is done with memcpy (a pointer write, which is fine). }

{ N-byte little-endian encoding of AVal. }
function LkLE(AVal: Int64; ANBytes: Integer): string;
var
  I: Integer;
begin
  Result := '';
  for I := 0 to ANBytes - 1 do
    Result := Result + Chr(Integer((AVal shr (I * 8)) and $FF));
end;

{ Overwrite ABuf[AOff..] in place with ASrc's bytes (ABuf already large
  enough).  Blaise rejects `ABuf[i] := c` and `@ABuf[i]`, so writes go
  through a local PChar — the one idiom the native backend accepts for
  in-place string mutation (see ZeroBuf in uElfObject.pas). }
procedure LkCopyInto(var ABuf: string; AOff: Integer; const ASrc: string);
var
  P: PChar;
  I: Integer;
begin
  P := PChar(ABuf);
  for I := 0 to Length(ASrc) - 1 do
    P[AOff + I] := ASrc[I];
end;

{ Patch a 32-bit LE value at AOff. }
procedure LkPatch32(var ABuf: string; AOff: Integer; AVal: Int64);
begin
  LkCopyInto(ABuf, AOff, LkLE(AVal, 4));
end;

{ ---- chmod binding ----------------------------------------------------- }

function _lk_chmod(APath: PChar; AMode: Integer): Integer;
  external name 'chmod';

procedure MakeFileExecutable(const APath: string);
begin
  { 0o755 = rwxr-xr-x }
  _lk_chmod(PChar(APath), 493);
end;

{ ---- TLinkTarget ------------------------------------------------------- }

constructor TLinkTarget.Create;
begin
  inherited Create();
  Arch := laX86_64;
  Is64 := True;
  OSABI := ELFOSABI_SYSV;
  EMachine := EM_X86_64;
  BaseAddr := $400000;
  PageSize := $1000;
end;

function LinuxX86_64Target: TLinkTarget;
begin
  Result := TLinkTarget.Create();
  { defaults already describe Linux x86-64 }
end;

{ ---- TLinker ----------------------------------------------------------- }

constructor TLinker.Create;
begin
  Self.Create(LinuxX86_64Target());
  FOwnTarget := True;
end;

constructor TLinker.Create(ATarget: TLinkTarget);
begin
  inherited Create();
  FTarget := ATarget;
  FOwnTarget := False;
  FObjects := TList<TElfObjectFile>.Create();
  FOwned := TList<TElfObjectFile>.Create();
  FMerger := TSectionMerger.Create();
  FSymbols := TList<TLinkSymbol>.Create();
  FSecAddr := TList<TMergedSection>.Create();
  FAddrOf := TList<Int64>.Create();
  FEntry := 0;
end;

destructor TLinker.Destroy;
var
  I: Integer;
begin
  for I := 0 to FSymbols.Count - 1 do
    FSymbols.Get(I).Free();
  FSymbols.Free();
  FAddrOf.Free();
  FSecAddr.Free();           { sections owned by FMerger }
  FMerger.Free();
  for I := 0 to FOwned.Count - 1 do
    FOwned.Get(I).Free();
  FOwned.Free();
  FObjects.Free();
  if FOwnTarget then
    FTarget.Free();
  inherited Destroy();
end;

procedure TLinker.AddObject(AObj: TElfObjectFile);
begin
  FMerger.AddObject(FObjects.Count, AObj);
  FObjects.Add(AObj);
end;

procedure TLinker.AddOwnedObject(AObj: TElfObjectFile);
begin
  FOwned.Add(AObj);
  Self.AddObject(AObj);
end;

{ Virtual base address assigned to a merged section, or -1 if it was
  not laid out (e.g. a non-alloc debug section). }
function TLinker.MergedAddr(AMerged: TMergedSection): Int64;
var
  I: Integer;
begin
  for I := 0 to FSecAddr.Count - 1 do
    if FSecAddr.Get(I) = AMerged then
    begin
      Result := FAddrOf.Get(I);
      Exit;
    end;
  Result := -1;
end;

{ File offset for a virtual address in a laid-out section: the file
  image mirrors the virtual layout shifted down by the load base. }
function TLinker.FileOffset(AAddr: Int64): Integer;
begin
  Result := Integer(AAddr - FTarget.BaseAddr);
end;

function TLinker.SectionOfPlacement(AObjIdx,
  ASecIdx: Integer): TMergedSection;
var
  P: TSectionPlacement;
begin
  P := FMerger.PlacementOf(AObjIdx, ASecIdx);
  if P = nil then
    Result := nil
  else
    Result := P.Merged;
end;

function TLinker.PlacementBaseAddr(AObjIdx, ASecIdx: Integer): Int64;
var
  P: TSectionPlacement;
  Base: Int64;
begin
  P := FMerger.PlacementOf(AObjIdx, ASecIdx);
  if P = nil then
  begin
    Result := -1;
    Exit;
  end;
  Base := Self.MergedAddr(P.Merged);
  if Base < 0 then
  begin
    Result := -1;
    Exit;
  end;
  Result := Base + P.Offset;
end;

{ Assign virtual addresses.  Allocatable PROGBITS/NOBITS sections are
  grouped by permission into two loadable runs — executable (text +
  rodata) then writable (data + bss) — each starting on a fresh page.
  The first run begins after the ELF header + program headers, with
  p_vaddr congruent to p_offset modulo PageSize, as the loader
  requires.  Non-allocatable sections (.opdf.*) are not assigned an
  address; they ride through unmapped. }
procedure TLinker.PlaceSection(AM: TMergedSection; var AAddr: Int64);
var
  Al: Int64;
begin
  Al := AM.Align;
  if Al < 1 then Al := 1;
  AAddr := LkAlignUp(AAddr, Al);
  FSecAddr.Add(AM);
  FAddrOf.Add(AAddr);
  AAddr := AAddr + AM.Size;
end;

procedure TLinker.LayoutSections;
var
  I: Integer;
  M: TMergedSection;
  Addr: Int64;
  HdrBytes: Int64;
  IsAlloc, IsExec, IsWrite: Boolean;
begin
  { Program-header count is known: PT_LOAD x2 (exec run, write run).
    Reserve header space so the first section's file offset — which
    equals (addr - base) — clears the headers.  Elf64_Phdr = 56. }
  HdrBytes := ELF64_EHDR_SIZE + 2 * 56;

  { Executable run: header bytes share its first page. }
  Addr := FTarget.BaseAddr + HdrBytes;
  for I := 0 to FMerger.Merged.Count - 1 do
  begin
    M := FMerger.Merged.Get(I);
    IsAlloc := (M.Flags and SHF_ALLOC) <> 0;
    IsExec  := (M.Flags and SHF_EXECINSTR) <> 0;
    if IsAlloc and IsExec then Self.PlaceSection(M, Addr);
  end;
  { Read-only non-exec (rodata) joins the executable run. }
  for I := 0 to FMerger.Merged.Count - 1 do
  begin
    M := FMerger.Merged.Get(I);
    IsAlloc := (M.Flags and SHF_ALLOC) <> 0;
    IsExec  := (M.Flags and SHF_EXECINSTR) <> 0;
    IsWrite := (M.Flags and SHF_WRITE) <> 0;
    if IsAlloc and (not IsExec) and (not IsWrite) then
      Self.PlaceSection(M, Addr);
  end;

  { Writable run starts on a fresh page. }
  Addr := LkAlignUp(Addr, FTarget.PageSize);
  for I := 0 to FMerger.Merged.Count - 1 do
  begin
    M := FMerger.Merged.Get(I);
    IsAlloc := (M.Flags and SHF_ALLOC) <> 0;
    IsWrite := (M.Flags and SHF_WRITE) <> 0;
    if IsAlloc and IsWrite and (M.ShType <> SHT_NOBITS) then
      Self.PlaceSection(M, Addr);
  end;
  for I := 0 to FMerger.Merged.Count - 1 do
  begin
    M := FMerger.Merged.Get(I);
    IsAlloc := (M.Flags and SHF_ALLOC) <> 0;
    IsWrite := (M.Flags and SHF_WRITE) <> 0;
    if IsAlloc and IsWrite and (M.ShType = SHT_NOBITS) then
      Self.PlaceSection(M, Addr);
  end;
end;

function TLinker.FindSymbol(const AName: string): TLinkSymbol;
var
  I: Integer;
begin
  for I := 0 to FSymbols.Count - 1 do
    if FSymbols.Get(I).Name = AName then
    begin
      Result := FSymbols.Get(I);
      Exit;
    end;
  Result := nil;
end;

procedure TLinker.AddSynthSymbol(const AName: string; AAddr: Int64);
var
  S: TLinkSymbol;
begin
  S := Self.FindSymbol(AName);
  if S <> nil then Exit;     { a real definition wins over the synth one }
  S := TLinkSymbol.Create();
  S.Name := AName;
  S.Addr := AAddr;
  S.Defined := True;
  S.IsFunc := False;
  FSymbols.Add(S);
end;

{ Build the global symbol table from every input object.  Only
  STB_GLOBAL / STB_WEAK symbols with a real definition (section index
  not SHN_UNDEF, not ABS/COMMON) are entered; a second STB_GLOBAL
  definition of the same name is a duplicate-symbol error, while a
  STB_GLOBAL overrides a previously seen STB_WEAK.  LayoutSections
  must have run so addresses are known. }
procedure TLinker.BuildSymbols;
var
  Oi, Si: Integer;
  Obj: TElfObjectFile;
  Sym: TRdSymbol;
  Existing: TLinkSymbol;
  NewSym: TLinkSymbol;
  Base: Int64;
begin
  for Oi := 0 to FObjects.Count - 1 do
  begin
    Obj := FObjects.Get(Oi);
    for Si := 0 to Obj.Symbols.Count - 1 do
    begin
      Sym := Obj.Symbols.Get(Si);
      if (Sym.Bind <> STB_GLOBAL) and (Sym.Bind <> STB_WEAK) then Continue;
      if Sym.Name = '' then Continue;
      if Sym.Shndx = SHN_UNDEF then Continue;
      if (Sym.Shndx = SHN_ABS) or (Sym.Shndx = SHN_COMMON) then Continue;

      Base := Self.PlacementBaseAddr(Oi, Sym.Shndx);
      if Base < 0 then Continue;   { defined in a section we did not lay out }

      Existing := Self.FindSymbol(Sym.Name);
      if Existing <> nil then
      begin
        { Both strong → duplicate.  Strong over weak → replace. }
        if (Sym.Bind = STB_GLOBAL) and Existing.Defined
           and (not Existing.IsWeakSlot) then
          raise ELinker.Create('duplicate symbol: ' + Sym.Name);
        if Sym.Bind = STB_GLOBAL then
        begin
          Existing.Addr := Base + Sym.Value;
          Existing.Defined := True;
          Existing.IsFunc := Sym.SymType = STT_FUNC;
          Existing.IsWeakSlot := False;
        end;
        Continue;
      end;

      NewSym := TLinkSymbol.Create();
      NewSym.Name := Sym.Name;
      NewSym.Addr := Base + Sym.Value;
      NewSym.Defined := True;
      NewSym.IsFunc := Sym.SymType = STT_FUNC;
      NewSym.IsWeakSlot := Sym.Bind = STB_WEAK;
      FSymbols.Add(NewSym);
    end;
  end;
end;

{ Linker-synthesised symbols.  Phase B has no GOT, so
  _GLOBAL_OFFSET_TABLE_ resolves to the writable run base (harmless
  for the standalone path that does not touch it); __bss_start/_edata/
  _end mark the data/bss boundaries; __TMC_END__ resolves to _end.
  Only defined if not already provided by an input object. }
procedure TLinker.DefineSynthSymbols;
var
  I: Integer;
  M: TMergedSection;
  DataEnd, BssStart, BssEnd, WritableBase: Int64;
  A: Int64;
begin
  DataEnd := FTarget.BaseAddr;
  BssStart := -1;
  BssEnd := FTarget.BaseAddr;
  WritableBase := -1;

  for I := 0 to FSecAddr.Count - 1 do
  begin
    M := FSecAddr.Get(I);
    A := FAddrOf.Get(I);
    if (M.Flags and SHF_WRITE) <> 0 then
    begin
      if WritableBase < 0 then WritableBase := A;
      if M.ShType = SHT_NOBITS then
      begin
        if BssStart < 0 then BssStart := A;
        if A + M.Size > BssEnd then BssEnd := A + M.Size;
      end
      else
      begin
        if A + M.Size > DataEnd then DataEnd := A + M.Size;
        if A + M.Size > BssEnd then BssEnd := A + M.Size;
      end;
    end;
  end;
  if BssStart < 0 then BssStart := DataEnd;
  if WritableBase < 0 then WritableBase := DataEnd;

  Self.AddSynthSymbol('_GLOBAL_OFFSET_TABLE_', WritableBase);
  Self.AddSynthSymbol('__bss_start', BssStart);
  Self.AddSynthSymbol('_edata', DataEnd);
  Self.AddSynthSymbol('_end', BssEnd);
  Self.AddSynthSymbol('__TMC_END__', BssEnd);
end;

{ Resolve a relocation's symbol to its final virtual address.  A
  reference to a STB_LOCAL section/symbol resolves through that
  object's own section placement; a global reference goes through the
  resolved symbol table.  A strong undefined symbol with no definition
  is a link error; a weak undefined resolves to 0. }
function TLinker.ResolveSymbolAddr(AObj: TElfObjectFile; ASymIdx: Integer;
  const AContext: string): Int64;
var
  Sym: TRdSymbol;
  Oi: Integer;
  Base: Int64;
  G: TLinkSymbol;
begin
  if (ASymIdx < 0) or (ASymIdx >= AObj.Symbols.Count) then
    raise ELinker.Create(AContext + ': relocation symbol index out of range');
  Sym := AObj.Symbols.Get(ASymIdx);

  { Locally-defined (any binding) symbol: resolve via its section. }
  if (Sym.Shndx <> SHN_UNDEF) and (Sym.Shndx <> SHN_ABS)
     and (Sym.Shndx <> SHN_COMMON) then
  begin
    Oi := FObjects.IndexOf(AObj);
    Base := Self.PlacementBaseAddr(Oi, Sym.Shndx);
    if Base < 0 then
      raise ELinker.Create(AContext + ': symbol ' + Sym.Name
        + ' defined in an unlaid-out section');
    Result := Base + Sym.Value;
    Exit;
  end;

  if Sym.Shndx = SHN_ABS then
  begin
    Result := Sym.Value;
    Exit;
  end;

  { Undefined here — look up the global table. }
  G := Self.FindSymbol(Sym.Name);
  if (G <> nil) and G.Defined and (not G.IsWeakSlot) then
  begin
    Result := G.Addr;
    Exit;
  end;
  if (G <> nil) and G.Defined then   { resolved weak slot }
  begin
    Result := G.Addr;
    Exit;
  end;
  { Weak undefined resolves to 0; strong undefined is an error. }
  if Sym.Bind = STB_WEAK then
  begin
    Result := 0;
    Exit;
  end;
  raise ELinker.Create('undefined reference to `' + Sym.Name + '''');
end;

{ Patch the merged section bytes for every relocation.  Phase B
  supports the intra-program PC-relative forms only. }
procedure TLinker.ApplyRelocations;
var
  Oi, Ri: Integer;
  Obj: TElfObjectFile;
  Rel: TRdReloc;
  M: TMergedSection;
  P: TSectionPlacement;
  PAddr: Int64;     { virtual address of the patched bytes (P) }
  PFileOff: Integer; { offset of the patched bytes within M.Data }
  S, Val: Int64;
  Ctx: string;
begin
  for Oi := 0 to FObjects.Count - 1 do
  begin
    Obj := FObjects.Get(Oi);
    for Ri := 0 to Obj.Relocs.Count - 1 do
    begin
      Rel := Obj.Relocs.Get(Ri);
      P := FMerger.PlacementOf(Oi, Rel.TargetSection);
      if P = nil then Continue;   { reloc in a dropped section }
      M := P.Merged;
      if Self.MergedAddr(M) < 0 then Continue;

      Ctx := Obj.SourceName;
      PFileOff := Integer(P.Offset + Rel.Offset);
      PAddr := Self.MergedAddr(M) + P.Offset + Rel.Offset;
      S := Self.ResolveSymbolAddr(Obj, Rel.SymIndex, Ctx);

      case Rel.RelocType of
        R_X86_64_NONE: ;
        R_X86_64_PC32, R_X86_64_PLT32:
          begin
            { Intra-program PC-relative: S + A - P.  A PLT32 against an
              internally-defined symbol relaxes to the same direct
              computation (no PLT in Phase B). }
            Val := S + Rel.Addend - PAddr;
            if M.ShType = SHT_NOBITS then
              raise ELinker.Create(Ctx
                + ': relocation into a NOBITS section');
            LkPatch32(M.Data, PFileOff, Val and $FFFFFFFF);
          end;
        R_X86_64_64:
          raise ELinker.Create(Ctx + ': R_X86_64_64 relocation against `'
            + Obj.Symbols.Get(Rel.SymIndex).Name
            + ''' needs dynamic linking (Phase C)');
        R_X86_64_32, R_X86_64_32S:
          raise ELinker.Create(Ctx
            + ': absolute 32-bit relocation is unsupported (Phase B is '
            + 'PC-relative only)');
        R_X86_64_GOTPCREL, R_X86_64_GOTPCRELX, R_X86_64_REX_GOTPCRELX,
        R_X86_64_TPOFF32:
          raise ELinker.Create(Ctx
            + ': GOT/TLS relocation needs dynamic linking (Phase C)');
      else
        raise ELinker.Create(Ctx + ': unsupported relocation type '
          + IntToStr(Rel.RelocType));
      end;
    end;
  end;
end;

{ Build the ET_EXEC byte image: ELF header, two PT_LOAD program
  headers (exec run, write run), section payloads at file offsets that
  match (vaddr - base), then a minimal section-header table so
  readelf/objdump can inspect the result. }
function TLinker.EmitExecutable(AEntry: Int64): string;
var
  Buf: string;
  I: Integer;
  M: TMergedSection;
  A: Int64;
  Base, PageSz: Int64;
  ExecLo, ExecHi, WriteLo, WriteMemHi, WriteFileHi: Int64;
  PhOff, FirstSecFileEnd: Integer;
  ShStr: string;
  ShStrOff: TList<Integer>;
  SecCount, ShTabOff: Integer;
  NamePos: Integer;
begin
  Base := FTarget.BaseAddr;
  PageSz := FTarget.PageSize;

  { Compute the address extents of each run. }
  ExecLo := -1; ExecHi := Base;
  WriteLo := -1; WriteMemHi := Base; WriteFileHi := Base;
  for I := 0 to FSecAddr.Count - 1 do
  begin
    M := FSecAddr.Get(I);
    A := FAddrOf.Get(I);
    if (M.Flags and SHF_WRITE) <> 0 then
    begin
      if WriteLo < 0 then WriteLo := A;
      if A + M.Size > WriteMemHi then WriteMemHi := A + M.Size;
      if (M.ShType <> SHT_NOBITS) and (A + M.Size > WriteFileHi) then
        WriteFileHi := A + M.Size;
    end
    else
    begin
      if ExecLo < 0 then ExecLo := A;
      if A + M.Size > ExecHi then ExecHi := A + M.Size;
    end;
  end;
  if ExecLo < 0 then ExecLo := Base + ELF64_EHDR_SIZE;
  if WriteLo < 0 then begin WriteLo := ExecHi; WriteFileHi := ExecHi;
    WriteMemHi := ExecHi; end;

  { ---- ELF header + program headers (assembled front-to-back) ---- }
  PhOff := ELF64_EHDR_SIZE;
  Buf := '';
  Buf := Buf + Chr($7F) + 'ELF';            { e_ident magic }
  Buf := Buf + Chr(ELFCLASS64) + Chr(ELFDATA2LSB) + Chr(EV_CURRENT)
             + Chr(FTarget.OSABI);
  Buf := Buf + LkZeros(8);                   { e_ident[8..15] }
  Buf := Buf + LkLE(ET_EXEC, 2);             { e_type }
  Buf := Buf + LkLE(FTarget.EMachine, 2);    { e_machine }
  Buf := Buf + LkLE(EV_CURRENT, 4);          { e_version }
  Buf := Buf + LkLE(AEntry, 8);              { e_entry }
  Buf := Buf + LkLE(PhOff, 8);               { e_phoff }
  Buf := Buf + LkLE(0, 8);                   { e_shoff (patched later) }
  Buf := Buf + LkLE(0, 4);                   { e_flags }
  Buf := Buf + LkLE(ELF64_EHDR_SIZE, 2);     { e_ehsize }
  Buf := Buf + LkLE(56, 2);                  { e_phentsize }
  Buf := Buf + LkLE(2, 2);                   { e_phnum (2 PT_LOAD) }
  Buf := Buf + LkLE(ELF64_SHDR_SIZE, 2);     { e_shentsize }
  Buf := Buf + LkLE(0, 2);                   { e_shnum (patched later) }
  Buf := Buf + LkLE(0, 2);                   { e_shstrndx (patched later) }

  { PT_LOAD #0 — executable run; covers the headers (file offset 0). }
  Buf := Buf + LkLE(PT_LOAD, 4) + LkLE(PF_R or PF_X, 4);
  Buf := Buf + LkLE(0, 8);                    { p_offset }
  Buf := Buf + LkLE(Base, 8);                 { p_vaddr }
  Buf := Buf + LkLE(Base, 8);                 { p_paddr }
  Buf := Buf + LkLE(Self.FileOffset(ExecHi), 8);    { p_filesz }
  Buf := Buf + LkLE(ExecHi - Base, 8);        { p_memsz }
  Buf := Buf + LkLE(PageSz, 8);               { p_align }

  { PT_LOAD #1 — writable run (data + bss). }
  Buf := Buf + LkLE(PT_LOAD, 4) + LkLE(PF_R or PF_W, 4);
  Buf := Buf + LkLE(Self.FileOffset(WriteLo), 8);   { p_offset }
  Buf := Buf + LkLE(WriteLo, 8);              { p_vaddr }
  Buf := Buf + LkLE(WriteLo, 8);              { p_paddr }
  Buf := Buf + LkLE(WriteFileHi - WriteLo, 8);{ p_filesz }
  Buf := Buf + LkLE(WriteMemHi - WriteLo, 8); { p_memsz }
  Buf := Buf + LkLE(PageSz, 8);               { p_align }

  { Pad headers out to the first section's file offset (the exec run's
    first byte sits at Self.FileOffset(ExecLo)). }
  if Length(Buf) < Self.FileOffset(ExecLo) then
    Buf := Buf + LkZeros(Self.FileOffset(ExecLo) - Length(Buf));

  { ---- section payloads ---- }
  { Grow the image to the end of writable file data, then splat every
    PROGBITS section at its file offset (= vaddr - Base). }
  FirstSecFileEnd := Self.FileOffset(WriteFileHi);
  if Length(Buf) < FirstSecFileEnd then
    Buf := Buf + LkZeros(FirstSecFileEnd - Length(Buf));
  for I := 0 to FSecAddr.Count - 1 do
  begin
    M := FSecAddr.Get(I);
    A := FAddrOf.Get(I);
    if M.ShType = SHT_NOBITS then Continue;
    if Length(M.Data) > 0 then
      LkCopyInto(Buf, Self.FileOffset(A), M.Data);
  end;

  { ---- section header table (for tooling) ---- }
  { .shstrtab: NULL, one name per laid-out section, then .shstrtab. }
  ShStr := Chr(0);
  ShStrOff := TList<Integer>.Create();
  try
    for I := 0 to FSecAddr.Count - 1 do
    begin
      ShStrOff.Add(Length(ShStr));
      ShStr := ShStr + FSecAddr.Get(I).Name + Chr(0);
    end;
    NamePos := Length(ShStr);
    ShStr := ShStr + '.shstrtab' + Chr(0);

    ShTabOff := Length(Buf);
    Buf := Buf + ShStr;

    SecCount := FSecAddr.Count + 2;     { NULL + sections + .shstrtab }
    while (Length(Buf) and 7) <> 0 do Buf := Buf + Chr(0);

    { Patch e_shoff / e_shnum / e_shstrndx now that the table offset is
      known.  e_shoff @40, e_shnum @60, e_shstrndx @62. }
    LkCopyInto(Buf, 40, LkLE(Length(Buf), 8));
    LkCopyInto(Buf, 60, LkLE(SecCount, 2));
    LkCopyInto(Buf, 62, LkLE(SecCount - 1, 2));

    { SHT_NULL header. }
    Buf := Buf + LkZeros(ELF64_SHDR_SIZE);

    for I := 0 to FSecAddr.Count - 1 do
    begin
      M := FSecAddr.Get(I);
      A := FAddrOf.Get(I);
      Buf := Buf + LkLE(ShStrOff.Get(I), 4);    { sh_name }
      Buf := Buf + LkLE(M.ShType, 4);           { sh_type }
      Buf := Buf + LkLE(M.Flags, 8);            { sh_flags }
      Buf := Buf + LkLE(A, 8);                  { sh_addr }
      if M.ShType = SHT_NOBITS then
        Buf := Buf + LkLE(Self.FileOffset(WriteFileHi), 8)   { sh_offset }
      else
        Buf := Buf + LkLE(Self.FileOffset(A), 8);
      Buf := Buf + LkLE(M.Size, 8);             { sh_size }
      Buf := Buf + LkLE(0, 4);                  { sh_link }
      Buf := Buf + LkLE(0, 4);                  { sh_info }
      Buf := Buf + LkLE(M.Align, 8);            { sh_addralign }
      Buf := Buf + LkLE(0, 8);                  { sh_entsize }
    end;

    { .shstrtab section header. }
    Buf := Buf + LkLE(NamePos, 4);
    Buf := Buf + LkLE(SHT_STRTAB, 4);
    Buf := Buf + LkLE(0, 8);
    Buf := Buf + LkLE(0, 8);
    Buf := Buf + LkLE(ShTabOff, 8);
    Buf := Buf + LkLE(Length(ShStr), 8);
    Buf := Buf + LkLE(0, 4);
    Buf := Buf + LkLE(0, 4);
    Buf := Buf + LkLE(1, 8);
    Buf := Buf + LkLE(0, 8);
  finally
    ShStrOff.Free();
  end;

  Result := Buf;
end;

function TLinker.LinkToBytes(const AEntryName: string): string;
var
  Sym: TLinkSymbol;
begin
  Self.LayoutSections();
  Self.BuildSymbols();
  Self.DefineSynthSymbols();
  Self.ApplyRelocations();

  Sym := Self.FindSymbol(AEntryName);
  if (Sym = nil) or (not Sym.Defined) or Sym.IsWeakSlot then
    raise ELinker.Create('entry symbol not found: ' + AEntryName);
  FEntry := Sym.Addr;
  Result := Self.EmitExecutable(FEntry);
end;

procedure TLinker.Link(const AEntryName, AOutputPath: string);
var
  Bytes: string;
  FOut: TFileOutputStream;
begin
  Bytes := Self.LinkToBytes(AEntryName);
  FOut := TFileOutputStream.Create(AOutputPath);
  try
    FOut.Write(PChar(Bytes), Length(Bytes));
    FOut.Flush();
  finally
    FOut.Close();
    FOut.Free();
  end;
  MakeFileExecutable(AOutputPath);
end;

function TLinker.AddrOfSymbol(const AName: string): Int64;
var
  S: TLinkSymbol;
begin
  S := Self.FindSymbol(AName);
  if S = nil then
    Result := -1
  else
    Result := S.Addr;
end;

function TLinker.FindMerged(const AName: string): TMergedSection;
begin
  Result := FMerger.FindMerged(AName);
end;

function TLinker.FindMergedText: TMergedSection;
begin
  Result := FMerger.FindMerged('.text');
end;

end.
