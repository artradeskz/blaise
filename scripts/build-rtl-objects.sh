#!/bin/bash
# Build the implicit RTL object files from source, mirroring the compiler's
# own TBackendDriver.EnsureRTLObjects.  Used by the fixpoint / bootstrap
# scripts to link a self-hosted compiler binary WITHOUT the legacy
# blaise_rtl.a archive (RTL-unification Stage 3).
#
# Usage:
#   scripts/build-rtl-objects.sh <blaise-binary> <out-dir> [options]
# Options:
#   --with-startup            include runtime.start (its bare _start)
#   --exclude-defined-by FILE omit any RTL object that defines a symbol FILE
#                             already defines (FILE is the main program object)
#
# Builds each RTL unit into <out-dir>/<unit>.o and prints, one per line on
# stdout, the object paths to put on the link line.  By default runtime.start
# (the bare _start entry) is OMITTED — a gcc/cc link line gets _start from libc
# and calls main.  Pass --with-startup to include it (a -nostartfiles / native
# internal link that owns the entry point).
#
# --exclude-defined-by handles the self-host link: a whole-program --emit-ir
# dump INLINES the RTL units the compiler transitively uses (runtime.arc via
# `uses classes`, etc.), so the program object already defines their symbols.
# Linking our standalone copy too would double-define them; this option drops
# the redundant objects, mirroring the compiler driver's own dedup.
#
# The build goes through a --unit-cache so each unit references its RTL deps'
# globals externally instead of re-defining them (the archive's member
# selection used to hide those duplicate definitions; explicit .o files do not).
# RTL units carry inline asm, so the native backend + internal assembler is
# mandatory.  Build order is leaf-first so each unit's deps are already cached.

set -e

BLAISE="$1"
OUTDIR="$2"
shift 2 || true
WITH_STARTUP=0
EXCLUDE_OBJ=""
while [ $# -gt 0 ]; do
  case "$1" in
    --with-startup)       WITH_STARTUP=1; shift ;;
    --exclude-defined-by) EXCLUDE_OBJ="$2"; shift 2 ;;
    *) echo "build-rtl-objects: unknown option $1" >&2; exit 2 ;;
  esac
done

if [ -z "$BLAISE" ] || [ -z "$OUTDIR" ]; then
  echo "usage: build-rtl-objects.sh <blaise-binary> <out-dir> [--with-startup] [--exclude-defined-by FILE]" >&2
  exit 2
fi
if [ ! -x "$BLAISE" ]; then
  echo "build-rtl-objects: compiler binary not found: $BLAISE" >&2
  exit 2
fi

# Resolve the RTL source relative to THIS script (scripts/ is a sibling of
# compiler/), so the script works regardless of the caller's CWD — the fixpoint
# scripts run from the project root, the test runner from compiler/.
SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
SRC="$SCRIPT_DIR/../compiler/src/main/pascal"
if [ ! -f "$SRC/runtime.arc.pas" ]; then
  # Fall back to a CWD-relative path (e.g. an unusual invocation layout).
  SRC=compiler/src/main/pascal
fi
if [ ! -f "$SRC/runtime.arc.pas" ]; then
  echo "build-rtl-objects: RTL source not found under $SRC" >&2
  exit 2
fi

mkdir -p "$OUTDIR"

# Leaf-first link order.  rtl.platform owns the shared globals (GPlatformLayout,
# GRtlPlatform) that layout.linux + posix reference externally, so it is built
# first and linked once.
RTL_UNITS=(
  rtl.platform
  runtime.start runtime.atomic runtime.setjmp runtime.utf8
  runtime.mem runtime.str runtime.set runtime.arc
  runtime.weak runtime.float runtime.thread runtime.exc
  rtl.platform.layout.linux rtl.platform.posix
)

# Symbols the main program object already defines (for --exclude-defined-by).
EXCL_DEFS=""
if [ -n "$EXCLUDE_OBJ" ]; then
  EXCL_DEFS=$(nm "$EXCLUDE_OBJ" 2>/dev/null | grep -E ' [TDBR] ' | awk '{print $3}' | sort -u)
fi

OBJS=()
for u in "${RTL_UNITS[@]}"; do
  obj="$OUTDIR/$u.o"
  src="$SRC/$u.pas"
  # Rebuild only when the cached object is missing or older than its source, so
  # a persistent $OUTDIR (e.g. reused across a test suite) builds the RTL once.
  if [ ! -f "$obj" ] || [ "$src" -nt "$obj" ]; then
    "$BLAISE" --backend native --assembler internal \
      --source "$src" \
      --unit-path "$SRC" --unit-cache "$OUTDIR" \
      --output "$obj" >/dev/null 2>"$OUTDIR/$u.build.err" || {
        echo "build-rtl-objects: failed to build $u" >&2
        tail -5 "$OUTDIR/$u.build.err" >&2
        exit 1
      }
    # Cache this object's defined symbols so repeated --exclude-defined-by calls
    # (e.g. one per test in a suite) don't re-run nm on the stable RTL objects.
    nm "$obj" 2>/dev/null | grep -E ' [TDBR] ' | awk '{print $3}' | sort -u \
      > "$obj.syms"
  fi
  if [ "$u" = "runtime.start" ] && [ "$WITH_STARTUP" -eq 0 ]; then
    continue
  fi
  # Drop this object if it re-defines any symbol the main program already owns
  # (it was inlined into the program) — otherwise the loose .o collides.
  if [ -n "$EXCL_DEFS" ] && [ -f "$obj.syms" ] && [ -s "$obj.syms" ]; then
    if [ -n "$(comm -12 "$obj.syms" <(printf '%s\n' "$EXCL_DEFS"))" ]; then
      continue
    fi
  fi
  OBJS+=("$obj")
done

printf '%s\n' "${OBJS[@]}"
