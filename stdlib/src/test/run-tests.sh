#!/usr/bin/env bash
# Build and run the Blaise stdlib test suite.
#
# Usage:  stdlib/src/test/run-tests.sh [blaise-binary] [-- runner-args...]
#   blaise-binary defaults to the newest release under releases/.
#   Anything after '--' is passed to the runner (e.g. --suite TJsonTests).
set -euo pipefail

# Repo root = two levels up from this script's dir (stdlib/src/test -> repo).
ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"

BLAISE="${1:-$ROOT/releases/v0.12.0-pre/blaise}"
[ "${1:-}" != "" ] && shift || true
# Drop a leading '--' separator if present.
[ "${1:-}" = "--" ] && shift || true

CACHE="$(mktemp -d)"
OUT="$CACHE/testrunner"

"$BLAISE" \
  --source "$ROOT/stdlib/src/test/pascal/testrunner.pas" \
  --output "$OUT" \
  --unit-path "$ROOT/stdlib/src/main/pascal" \
  --unit-path "$ROOT/runtime/src/main/pascal" \
  --unit-path "$ROOT/stdlib/src/test/pascal" \
  --unit-cache "$CACHE"

"$OUT" "$@"
RC=$?
rm -rf "$CACHE"
exit $RC
