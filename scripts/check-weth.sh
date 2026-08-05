#!/usr/bin/env bash
# WETH fixture suite (non-vacuity arc, ~/plans/non-vacuity.md): runs the five
# committed fixtures in scripts/fixtures/weth/ through Jaune's fixture runner
# at network Prague. Every fixture's WETH account carries Blanc.wethCode —
# exactly the bytes Blanc.wethCode_compile witnesses as Prog.compile weth's
# output — as its code, and every expectation was filled by the pinned frozen
# EELS oracle's t8n (scripts/gen-weth-fixtures.py), never hand-computed. This
# is external adjudication: Jaune and the frozen oracle agreeing on the exact
# artifact the flagship solvency theorems are about.
#
# Before running any fixture (fmint-hygiene Step 3, ~/plans/fmint-hygiene.md):
# every fixture's WETH account's code is compared byte-for-byte against the
# committed Blanc.wethCode literal (scripts/check-runtime-bytes.py, shared
# with check-fmint.sh) -- not merely the length-based identification the
# generator and coverage scripts use. A parse failure on the Lean literal or
# a byte mismatch is a REGRESSION, distinct from a fixture FAIL.
#
# Usage: scripts/check-weth.sh [--no-build]
#
# --no-build skips `lake build jaune/jaune` and requires the runner binary to
# already exist (permitted only after a successful build at the same source
# commit, per scripts/GATES.md).
#
# CLI contract: exit 0 if and only if the runtime byte-equality gate passes
# AND every fixture PASSes. Output ends with one verdict line per fixture
# plus a single unambiguous summary line, after a version-and-pins line
# identifying exactly what was checked.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
FIXTURES_DIR="$ROOT/scripts/fixtures/weth"
BIN="$ROOT/.lake/packages/jaune/.lake/build/bin/jaune"
NETWORK="Prague"

BUILD=1
while [ $# -gt 0 ]; do
  case "$1" in
    --no-build) BUILD=0 ;;
    *) echo "usage: scripts/check-weth.sh [--no-build]" >&2; exit 2 ;;
  esac
  shift
done

if [ "$BUILD" -eq 1 ]; then
  if ! (cd "$ROOT" && lake build jaune/jaune); then
    echo "REGRESSION — weth fixtures: lake build jaune/jaune failed"
    exit 1
  fi
fi

if [ ! -x "$BIN" ]; then
  echo "REGRESSION — weth fixtures: runner binary not found at $BIN" \
    "(build it with 'lake build jaune/jaune' or drop --no-build)" >&2
  exit 1
fi

PY="python3"
if ! command -v "$PY" >/dev/null 2>&1; then
  echo "REGRESSION — weth fixtures: python3 not found on PATH" >&2
  exit 1
fi

BLANC_COMMIT="$(cd "$ROOT" && git rev-parse HEAD 2>/dev/null || echo unknown)"
JAUNE_PIN="$(cd "$ROOT" && git -C .lake/packages/jaune rev-parse HEAD 2>/dev/null || echo unknown)"
ORACLE_PIN="$(cd "$HOME/execution-specs" && git rev-parse HEAD 2>/dev/null || echo unknown)"

echo "weth fixtures — blanc $BLANC_COMMIT, jaune pin $JAUNE_PIN, oracle $ORACLE_PIN, network $NETWORK"

FILES=("$FIXTURES_DIR"/*.json)
if [ ! -e "${FILES[0]}" ]; then
  echo "REGRESSION — weth fixtures: no fixture files found in $FIXTURES_DIR" >&2
  exit 1
fi

# ---- the runtime byte-equality gate ----------------------------------------
RUNTIME_CHECK_OUT="$("$PY" "$SCRIPT_DIR/check-runtime-bytes.py" \
  --lean "$ROOT/Blanc/WethCode.lean" --def wethCode \
  --fixtures-dir "$FIXTURES_DIR" --label weth 2>&1)"
RUNTIME_CHECK_STATUS=$?
printf '%s\n' "$RUNTIME_CHECK_OUT"
if [ "$RUNTIME_CHECK_STATUS" -ne 0 ]; then
  echo "REGRESSION — weth fixtures: runtime byte-equality gate failed"
  exit 1
fi

FAIL=0
TOTAL=0
OUT="$(mktemp)"
trap 'rm -f "$OUT"' EXIT
for f in "${FILES[@]}"; do
  TOTAL=$((TOTAL + 1))
  NAME="$(basename "$f")"
  if "$BIN" "$f" --network "$NETWORK" >"$OUT" 2>&1; then
    echo "PASS  $NAME"
  else
    echo "FAIL  $NAME"
    sed 's/^/      /' "$OUT"
    FAIL=$((FAIL + 1))
  fi
done

if [ "$FAIL" -eq 0 ]; then
  echo "OK — weth fixtures: $TOTAL/$TOTAL PASS"
  exit 0
else
  echo "REGRESSION — weth fixtures: $((TOTAL - FAIL))/$TOTAL PASS, $FAIL FAIL"
  exit 1
fi
