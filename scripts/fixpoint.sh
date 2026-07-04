#!/bin/bash
# Fixpoint test for the Blaise self-hosting check.
#
# Uses the most recent release binary as stage-1 (no FPC dependency).
#
# Steps:
#   1. Find stage-1 binary (latest release or explicit $STAGE1).
#   2. Rebuild + install RTL (cheap when nothing changed).
#   3. stage-1 -> stage-2 IR.
#   4. Assemble + link stage-2 binary via QBE + gcc.
#   5. stage-2 -> stage-3 IR (5-minute timeout).
#   6. diff stage-2.ssa stage-3.ssa  => empty = clean fixpoint.
#
# If stage-2 != stage-3 (expected when stage-1 has older codegen),
# the script automatically builds stage-3, generates stage-4 IR,
# and checks stage-3 == stage-4 as the true fixpoint.

set -e

if [ ! -f "compiler/src/main/pascal/Blaise.pas" ]; then
  echo "Run this script from the project root: ./scripts/fixpoint.sh" >&2
  exit 1
fi

# Stage-1 binary: honour $STAGE1, otherwise pick the latest release.
if [ -n "$STAGE1" ]; then
  STAGE1_BIN="$STAGE1"
elif [ -d releases ]; then
  LATEST=$(ls -d releases/v* 2>/dev/null | sort -V | tail -1)
  STAGE1_BIN="$LATEST/blaise"
fi

if [ ! -x "$STAGE1_BIN" ]; then
  echo "No stage-1 binary found. Set STAGE1=/path/to/blaise or add a release." >&2
  exit 10
fi
echo "stage-1: $STAGE1_BIN"

# The runtime Makefile defaults BLAISE to ../compiler/target/blaise, which may
# not exist yet — e.g. straight after scripts/rolling-bootstrap.sh, which
# installs only to releases/ and leaves the live compiler/target/ empty.
# Drive the runtime build with the stage-1 binary explicitly so fixpoint never
# depends on a pre-existing compiler/target/blaise. make runs inside runtime/,
# so BLAISE must be an absolute path.
ABS_STAGE1=$(readlink -f "$STAGE1_BIN")

echo "[1/5] rebuild + install runtime (BLAISE=$ABS_STAGE1)"
( cd runtime && make clean > /tmp/fp_rtl.log 2>&1 \
             && make BLAISE="$ABS_STAGE1" >> /tmp/fp_rtl.log 2>&1 \
             && make BLAISE="$ABS_STAGE1" install >> /tmp/fp_rtl.log 2>&1 ) || {
  if [ -f compiler/target/blaise_rtl.a ]; then
    echo "      stage-1 too old for runtime; using existing blaise_rtl.a"
  else
    echo "RUNTIME_FAIL"; tail -5 /tmp/fp_rtl.log; exit 11;
  fi
}

# Resolve the RTL archive for the link steps below.  `make install` copies it
# to compiler/target/, but fall back to the runtime build dir so the link
# never fails on a tree where compiler/target/ was not populated.
if [ -f compiler/target/blaise_rtl.a ]; then
  RTL_ARCHIVE=compiler/target/blaise_rtl.a
elif [ -f runtime/target/blaise_rtl.a ]; then
  RTL_ARCHIVE=runtime/target/blaise_rtl.a
else
  echo "RUNTIME_FAIL: blaise_rtl.a not found after runtime build"; exit 11
fi

echo "[2/5] stage-1 -> stage-2 IR"
"$STAGE1_BIN" --source compiler/src/main/pascal/Blaise.pas \
  --unit-path compiler/src/main/pascal --unit-path runtime/src/main/pascal --unit-path stdlib/src/main/pascal \
  --emit-ir > /tmp/fp_stage2.ssa 2>/tmp/fp_stage2.err
if [ ! -s /tmp/fp_stage2.ssa ] || head -1 /tmp/fp_stage2.ssa | grep -qi 'error\|exception'; then
  echo "STAGE2_IR_FAIL"
  head -3 /tmp/fp_stage2.ssa
  head -3 /tmp/fp_stage2.err
  exit 1
fi
echo "      stage-2 IR: $(wc -l < /tmp/fp_stage2.ssa) lines"

echo "[3/5] assemble + link stage-2 binary"
vendor/qbe/qbe -o /tmp/fp_stage2.s /tmp/fp_stage2.ssa 2>/tmp/fp_qbe.err || {
  echo "QBE_FAIL"; cat /tmp/fp_qbe.err; exit 2;
}
gcc -o /tmp/fp_blaise2 /tmp/fp_stage2.s "$RTL_ARCHIVE" 2>/tmp/fp_gcc.err || {
  echo "GCC_FAIL"; cat /tmp/fp_gcc.err; exit 3;
}

echo "[4/5] stage-2 -> stage-3 IR (5min timeout)"
timeout 300 /tmp/fp_blaise2 --source compiler/src/main/pascal/Blaise.pas \
  --unit-path compiler/src/main/pascal --unit-path runtime/src/main/pascal --unit-path stdlib/src/main/pascal \
  --emit-ir > /tmp/fp_stage3.ssa 2>/tmp/fp_stage3.err
RC=$?
if [ $RC -eq 124 ]; then
  echo "STAGE3_TIMEOUT"
  exit 4
elif [ $RC -eq 139 ]; then
  echo "STAGE3_SEGFAULT"
  exit 4
elif [ $RC -ne 0 ]; then
  echo "STAGE3_FAIL rc=$RC"
  head -3 /tmp/fp_stage3.err
  exit 5
fi
echo "      stage-3 IR: $(wc -l < /tmp/fp_stage3.ssa) lines"

echo "[5/5] compare stage-2 vs stage-3"
DIFFLINES=$(diff /tmp/fp_stage2.ssa /tmp/fp_stage3.ssa | wc -l)
if [ $DIFFLINES -eq 0 ]; then
  echo "FIXPOINT_OK"
  exit 0
fi

echo "stage-2 != stage-3 ($DIFFLINES diff lines) — bootstrap gap from older stage-1"
echo "      extending to stage-4 for true fixpoint check..."

echo "[+1] assemble + link stage-3 binary"
vendor/qbe/qbe -o /tmp/fp_stage3.s /tmp/fp_stage3.ssa 2>/tmp/fp_qbe3.err || {
  echo "QBE3_FAIL"; cat /tmp/fp_qbe3.err; exit 2;
}
gcc -o /tmp/fp_blaise3 /tmp/fp_stage3.s "$RTL_ARCHIVE" 2>/tmp/fp_gcc3.err || {
  echo "GCC3_FAIL"; cat /tmp/fp_gcc3.err; exit 3;
}

echo "[+2] stage-3 -> stage-4 IR (5min timeout)"
timeout 300 /tmp/fp_blaise3 --source compiler/src/main/pascal/Blaise.pas \
  --unit-path compiler/src/main/pascal --unit-path runtime/src/main/pascal --unit-path stdlib/src/main/pascal \
  --emit-ir > /tmp/fp_stage4.ssa 2>/tmp/fp_stage4.err
RC=$?
if [ $RC -eq 124 ]; then
  echo "STAGE4_TIMEOUT"
  exit 4
elif [ $RC -eq 139 ]; then
  echo "STAGE4_SEGFAULT"
  exit 4
elif [ $RC -ne 0 ]; then
  echo "STAGE4_FAIL rc=$RC"
  head -3 /tmp/fp_stage4.err
  exit 5
fi
echo "      stage-4 IR: $(wc -l < /tmp/fp_stage4.ssa) lines"

echo "[+3] compare stage-3 vs stage-4"
DIFFLINES=$(diff /tmp/fp_stage3.ssa /tmp/fp_stage4.ssa | wc -l)
if [ $DIFFLINES -eq 0 ]; then
  echo "FIXPOINT_OK (achieved at stage-3/stage-4)"
  exit 0
else
  echo "FIXPOINT_DIFF lines=$DIFFLINES"
  diff /tmp/fp_stage3.ssa /tmp/fp_stage4.ssa | head -20
  exit 6
fi
