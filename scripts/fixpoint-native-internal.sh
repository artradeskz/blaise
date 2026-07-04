#!/bin/bash
# Internal-toolchain conformance check for the Blaise self-hosting toolchain.
#
# WHAT IT GUARDS:
#   The DEFAULT native pipeline since v0.12.0 is the in-process internal
#   assembler (blaise.assembler.x86_64) + internal linker (blaise.linker.elf):
#   source -> native .s -> internal assembler -> .o -> internal linker ->
#   executable, with zero external tools (only distro CRT objects are read).
#   This script asserts that the fully-internal pipeline produces a binary
#   that BEHAVES identically to the trusted all-external (gcc assemble + gcc
#   link) reference.
#
# WHY IT EXISTS, separately from fixpoint-native.sh:
#   fixpoint-native.sh validates native CODEGEN by diffing the emitted .s
#   text, but it assembles + links that text with EXTERNAL gcc.  Neither the
#   internal assembler nor the internal linker is on that path, so a defect
#   in either silently passes both fixpoints (this is exactly how the
#   sret-Result field-read bug hid; see bugs.txt 2026-06-16).  This script is
#   the only fixpoint-level guard that drives both internal tools end to end.
#
# WHY IT IS A DIFFERENTIAL CHECK, NOT A SELF-HOSTING FIXPOINT:
#   The internal assembler currently buffers the whole assembly + ELF
#   object in memory, so assembling the compiler's own ~631k-line .s needs
#   ~53 GB and OOM-kills.  A true "compile the compiler with itself via the
#   internal toolchain" fixpoint is therefore not feasible until the internal
#   assembler streams its output.  Instead we compile a representative program
#   that exercises the bug-prone paths (record-return sret-Result field reads,
#   immutable string literals) BOTH ways and assert the internal-toolchain
#   binary BEHAVES identically (stdout + exit code) to the all-external
#   reference.  Note: the internal and external tools may emit
#   different-but-valid encodings / section layouts, so a byte-level compare
#   would false-positive; behavioural equivalence is the sound invariant.
#
# Requires: a native compiler at compiler/target/blaise (run the QBE
# fixpoint or `pasbuild compile` first) and compiler/target/blaise_rtl.a.

set -e

if [ ! -f "compiler/src/main/pascal/Blaise.pas" ]; then
  echo "Run this script from the project root: ./scripts/fixpoint-native-internal.sh" >&2
  exit 1
fi

COMPILER="${1:-compiler/target/blaise}"
if [ ! -x "$COMPILER" ]; then
  echo "Compiler not found: $COMPILER" >&2
  echo "Build it first: pasbuild compile -m blaise-compiler --compiler ..." >&2
  exit 10
fi

if [ -f compiler/target/blaise_rtl.a ]; then
  RTL_ARCHIVE=compiler/target/blaise_rtl.a
elif [ -f runtime/target/blaise_rtl.a ]; then
  RTL_ARCHIVE=runtime/target/blaise_rtl.a
else
  echo "blaise_rtl.a not found — build the runtime first" >&2
  exit 11
fi
# FindRTL looks for blaise_rtl.a beside the compiler binary.
cp "$RTL_ARCHIVE" "$(dirname "$COMPILER")/blaise_rtl.a" 2>/dev/null || true

UNIT_ARGS="--unit-path runtime/src/main/pascal --unit-path stdlib/src/main/pascal"
PROBE=/tmp/fpni_probe.pas

# Representative program.  Exercises the sret-Result field-read path (a
# record-returning function reads one Result field into another) plus many
# immutable string literals (each emits a `.long -1` header the internal
# assembler must encode correctly).
cat > "$PROBE" <<'PROBE_EOF'
program fpni_probe;

type
  TPoint = record
    X: Int64;
    Y: Int64;
    Name: string;
  end;

function MakePoint(AX, AY: Int64; const AName: string): TPoint;
begin
  Result.X := AX;
  Result.Y := AY;
  Result.Name := AName;
  if Result.X >= Result.Y then
    Result.Name := AName + '-wide'
  else
    Result.Name := AName + '-tall';
end;

var
  P: TPoint;
  I: Integer;
  Total: Int64;
begin
  Total := 0;
  for I := 0 to 4 do
  begin
    P := MakePoint(I, I * 2, 'pt');
    Total := Total + P.X + P.Y;
    WriteLn(P.Name, ' ', P.X, ',', P.Y);
  end;
  WriteLn('total=', Total);
  WriteLn('immutable string literals and record return survived');
end.
PROBE_EOF

echo "compiler: $COMPILER"

echo "[1/3] compile probe with INTERNAL assembler + INTERNAL linker (default pipeline)"
if ! "$COMPILER" --source "$PROBE" $UNIT_ARGS \
     --backend native --assembler internal --linker internal \
     --output /tmp/fpni_int 2>/tmp/fpni_int.err; then
  echo "INTERNAL_COMPILE_FAIL"; head -5 /tmp/fpni_int.err; exit 2
fi

echo "[2/3] compile probe with EXTERNAL assembler + EXTERNAL linker (reference)"
if ! "$COMPILER" --source "$PROBE" $UNIT_ARGS \
     --backend native --assembler external --linker external \
     --output /tmp/fpni_ext 2>/tmp/fpni_ext.err; then
  echo "EXTERNAL_COMPILE_FAIL"; head -5 /tmp/fpni_ext.err; exit 3
fi

echo "[3/3] run both and compare stdout + exit code"
# Behavioural equivalence is the sound invariant: the internal and external
# toolchains may emit DIFFERENT-but-valid encodings / section layouts (so a
# byte-level .text/.rodata compare would false-positive), but a binary built
# by the internal assembler + internal linker must BEHAVE identically to the
# all-external reference.  The sret-Result bug broke exactly this (corrupted
# string headers => wrong / garbage output), so stdout + exit code catch it.
# Disable -e around the runs: a miscompiled internal binary may crash
# (e.g. SIGSEGV from a corrupted string header), and we must REPORT that as
# a guard failure rather than let -e abort the script mid-diagnostic.
set +e
/tmp/fpni_int > /tmp/fpni_int.out 2>&1; INT_RC=$?
/tmp/fpni_ext > /tmp/fpni_ext.out 2>&1; EXT_RC=$?
set -e
if [ "$INT_RC" -ne "$EXT_RC" ]; then
  echo "EXIT_MISMATCH internal=$INT_RC external=$EXT_RC"
  echo "  (internal-assembler binary misbehaved — likely a codegen/assembler regression)"
  echo "--- internal stdout ---"; cat /tmp/fpni_int.out
  echo "--- external stdout ---"; cat /tmp/fpni_ext.out
  exit 6
fi
if ! diff -q /tmp/fpni_int.out /tmp/fpni_ext.out >/dev/null; then
  echo "OUTPUT_MISMATCH (internal assembler produced a binary that behaves differently)"
  echo "--- internal ---"; cat /tmp/fpni_int.out
  echo "--- external ---"; cat /tmp/fpni_ext.out
  exit 6
fi

echo "NATIVE_INTERNAL_OK"
exit 0
