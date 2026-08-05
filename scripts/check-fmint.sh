#!/usr/bin/env bash
# fmint fixture suite (fmint-code Step 2, ~/plans/fmint-code.md; program
# source of truth ~/plans/flashmint-proposal.md): runs the fixtures in
# scripts/fixtures/fmint/ through Jaune's fixture runner at network Prague,
# the sibling of check-weth.sh. Every fixture's fmint account carries
# Blanc.fmintCode -- exactly the bytes Blanc.fmintCode_compile witnesses as
# Prog.compile Fmint.fmint's output -- and every expectation was filled by
# the pinned frozen EELS oracle's t8n (scripts/gen-fmint-fixtures.py), never
# hand-computed.
#
# Beyond check-weth.sh's PASS/FAIL loop, this harness additionally
# cross-checks the generator's scenario MANIFEST
# (scripts/fixtures/fmint/manifest.json) against the fixture directory --
# the anti-vacuity acceptance criterion from the evidence plan: "a generated
# scenario manifest... cross-checked by the harness against the fixture
# directory, so a deleted or never-generated case can never yield 'all
# PASS' via globbing." A manifest row with no matching file, or a fixture
# file with no matching manifest row, is a REGRESSION -- distinct from a
# fixture that merely fails to PASS.
#
# Also beyond check-weth.sh's PASS/FAIL loop (fmint-hygiene Step 3,
# ~/plans/fmint-hygiene.md): before running any fixture, every fixture's
# fmint account's code is compared byte-for-byte against the committed
# Blanc.fmintCode literal (scripts/check-runtime-bytes.py, shared with
# check-weth.sh) -- not merely the length-based identification the
# generator and coverage scripts use. A parse failure on the Lean literal or
# a byte mismatch is a REGRESSION, distinct from both the manifest
# cross-check and a fixture FAIL.
#
# Usage: scripts/check-fmint.sh [--no-build]
#
# --no-build skips `lake build jaune/jaune` and requires the runner binary to
# already exist (permitted only after a successful build at the same source
# commit, per scripts/GATES.md).
#
# CLI contract: exit 0 if and only if the manifest cross-check passes AND
# the runtime byte-equality gate passes AND every fixture PASSes. Output
# ends with one verdict line per fixture plus a single unambiguous summary
# line, after a version-and-pins line identifying exactly what was checked.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
FIXTURES_DIR="$ROOT/scripts/fixtures/fmint"
MANIFEST="$FIXTURES_DIR/manifest.json"
BIN="$ROOT/.lake/packages/jaune/.lake/build/bin/jaune"
NETWORK="Prague"

BUILD=1
while [ $# -gt 0 ]; do
  case "$1" in
    --no-build) BUILD=0 ;;
    *) echo "usage: scripts/check-fmint.sh [--no-build]" >&2; exit 2 ;;
  esac
  shift
done

if [ "$BUILD" -eq 1 ]; then
  if ! (cd "$ROOT" && lake build jaune/jaune); then
    echo "REGRESSION — fmint fixtures: lake build jaune/jaune failed"
    exit 1
  fi
fi

if [ ! -x "$BIN" ]; then
  echo "REGRESSION — fmint fixtures: runner binary not found at $BIN" \
    "(build it with 'lake build jaune/jaune' or drop --no-build)" >&2
  exit 1
fi

PY="python3"
if ! command -v "$PY" >/dev/null 2>&1; then
  echo "REGRESSION — fmint fixtures: python3 not found on PATH" >&2
  exit 1
fi

BLANC_COMMIT="$(cd "$ROOT" && git rev-parse HEAD 2>/dev/null || echo unknown)"
JAUNE_PIN="$(cd "$ROOT" && git -C .lake/packages/jaune rev-parse HEAD 2>/dev/null || echo unknown)"

echo "fmint fixtures — blanc $BLANC_COMMIT, jaune pin $JAUNE_PIN, network $NETWORK"

if [ ! -f "$MANIFEST" ]; then
  echo "REGRESSION — fmint fixtures: manifest not found at $MANIFEST" \
    "(regenerate with scripts/gen-fmint-fixtures.py)" >&2
  exit 1
fi

# ---- the manifest cross-check ---------------------------------------------
# Every manifest row must have a matching fixture file, and every fixture
# file (other than the manifest itself) must have a matching manifest row.
# Run with the frozen oracle's plain python3 -- this check is pure JSON/
# filesystem comparison and needs neither the oracle venv nor Lean.
CROSS_CHECK_OUT="$("$PY" - "$FIXTURES_DIR" "$MANIFEST" <<'PYEOF'
import json, os, sys
fixtures_dir, manifest_path = sys.argv[1], sys.argv[2]

with open(manifest_path) as f:
    manifest = json.load(f)
if not isinstance(manifest, list) or not manifest:
    print("MANIFEST-ERROR empty or malformed manifest")
    sys.exit(1)

names = []
for row in manifest:
    if not isinstance(row, dict) or "name" not in row or "outcome" not in row \
            or "assertions" not in row:
        print(f"MANIFEST-ERROR malformed row: {row!r}")
        sys.exit(1)
    if not isinstance(row["assertions"], int) or row["assertions"] < 1:
        print(f"MANIFEST-ERROR row {row['name']!r} has a non-positive "
              f"assertion count ({row['assertions']!r}) -- a vacuous case")
        sys.exit(1)
    names.append(row["name"])
if len(set(names)) != len(names):
    print("MANIFEST-ERROR duplicate scenario name in manifest")
    sys.exit(1)

on_disk = sorted(
    n[:-5] for n in os.listdir(fixtures_dir)
    if n.endswith(".json") and n != "manifest.json")

manifest_set, disk_set = set(names), set(on_disk)
missing = sorted(manifest_set - disk_set)   # manifested but no file
orphaned = sorted(disk_set - manifest_set)  # file but not manifested
for m in missing:
    print(f"MANIFEST-MISSING {m} -- listed in manifest.json, no fixture file")
for o in orphaned:
    print(f"MANIFEST-ORPHAN {o} -- fixture file present, not in manifest.json")
if missing or orphaned:
    sys.exit(1)

print(f"MANIFEST-OK {len(names)} scenario(s) cross-checked, "
      f"{sum(r['assertions'] for r in manifest)} total assertions")
sys.exit(0)
PYEOF
)"
CROSS_CHECK_STATUS=$?
printf '%s\n' "$CROSS_CHECK_OUT"
if [ "$CROSS_CHECK_STATUS" -ne 0 ]; then
  echo "REGRESSION — fmint fixtures: manifest cross-check failed"
  exit 1
fi

# ---- the runtime byte-equality gate ----------------------------------------
# Every fixture's fmint account must carry code byte-identical to the
# committed Blanc.fmintCode literal (Blanc/FmintCode.lean), not merely code
# of the right length -- see scripts/check-runtime-bytes.py, shared with
# check-weth.sh. Pure source/JSON comparison; no Lean/lake dependency.
RUNTIME_CHECK_OUT="$("$PY" "$SCRIPT_DIR/check-runtime-bytes.py" \
  --lean "$ROOT/Blanc/FmintCode.lean" --def fmintCode \
  --fixtures-dir "$FIXTURES_DIR" --label fmint 2>&1)"
RUNTIME_CHECK_STATUS=$?
printf '%s\n' "$RUNTIME_CHECK_OUT"
if [ "$RUNTIME_CHECK_STATUS" -ne 0 ]; then
  echo "REGRESSION — fmint fixtures: runtime byte-equality gate failed"
  exit 1
fi

FILES=("$FIXTURES_DIR"/*.json)
RUN_FILES=()
for f in "${FILES[@]}"; do
  [ "$(basename "$f")" = "manifest.json" ] && continue
  RUN_FILES+=("$f")
done
if [ "${#RUN_FILES[@]}" -eq 0 ]; then
  echo "REGRESSION — fmint fixtures: no fixture files found in $FIXTURES_DIR" >&2
  exit 1
fi

FAIL=0
TOTAL=0
OUT="$(mktemp)"
trap 'rm -f "$OUT"' EXIT
for f in "${RUN_FILES[@]}"; do
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
  echo "OK — fmint fixtures: $TOTAL/$TOTAL PASS, manifest cross-check clean"
  exit 0
else
  echo "REGRESSION — fmint fixtures: $((TOTAL - FAIL))/$TOTAL PASS, $FAIL FAIL"
  exit 1
fi
