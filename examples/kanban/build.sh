#!/bin/bash
# Build the Kanban TUI app.
# Usage: ./build.sh [path-to-blaise-compiler]
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

# Use the main tree for compiler/QBE/RTL (worktrees don't have build artefacts)
MAIN_ROOT="/data/devel/new-pascal-compiler"
BLAISE="${1:-$MAIN_ROOT/compiler/target/blaise}"
QBE="$MAIN_ROOT/vendor/qbe/qbe"
RTL="$MAIN_ROOT/compiler/target/blaise_rtl.a"

echo "=== Building Kanban TUI ==="
echo "Compiler: $BLAISE"
echo ""

# Compile Blaise source to QBE IR
echo "[1/3] Compiling Blaise source..."
"$BLAISE" \
  --source "$SCRIPT_DIR/kanban_app.pas" \
  --unit-path "$SCRIPT_DIR" \
  --unit-path "$PROJECT_ROOT/runtime/src/main/pascal" \
  --unit-path "$PROJECT_ROOT/stdlib/src/main/pascal" \
  --emit-ir > "$SCRIPT_DIR/kanban_app.ssa"

# QBE: IR -> assembly
echo "[2/3] QBE assembling..."
"$QBE" -o "$SCRIPT_DIR/kanban_app.s" "$SCRIPT_DIR/kanban_app.ssa"

# Link
echo "[3/3] Linking..."
gcc -o "$SCRIPT_DIR/kanban" \
  "$SCRIPT_DIR/kanban_app.s" \
  "$RTL"

echo ""
echo "Build successful: $SCRIPT_DIR/kanban"
echo "Run: $SCRIPT_DIR/kanban [board.kanban]"
