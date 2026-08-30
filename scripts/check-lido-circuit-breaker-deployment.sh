#!/usr/bin/env bash
# Fail-closed universal/source and finite replay assurance for the official
# direct Lido Circuit Breaker deployment root. Generated replay products are
# temporary and never become Lean premises or committed goldens.

set -eu

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
EELS_ROOT="${EELS_ROOT:-$HOME/execution-specs}"
EELS_PY="$EELS_ROOT/venv/bin/python"
JAUNE_BIN="$ROOT/.lake/packages/jaune/.lake/build/bin/jaune"
EELS_PIN="4198b9c5996713b268aed602739d5aa40e277694"
TMP_DIR="$(mktemp -d)"
ARTIFACTS="$TMP_DIR/artifacts.txt"
FIXTURE="$TMP_DIR/deployment.json"
METADATA="$TMP_DIR/metadata.json"
LOG="$TMP_DIR/gate.log"
trap 'rm -rf "$TMP_DIR"' EXIT

fail() {
  if [ -s "$LOG" ]; then
    cat "$LOG" >&2
  fi
  echo "REGRESSION — Lido CircuitBreaker deployment root: $1" >&2
  exit 1
}

if [ ! -x "$EELS_PY" ]; then
  fail "pinned EELS interpreter not found at $EELS_PY"
fi
if [ ! -x "$JAUNE_BIN" ]; then
  fail "Jaune runner not found at $JAUNE_BIN; run the catalogue build first"
fi
if [ "$(git -C "$EELS_ROOT" rev-parse HEAD 2>"$LOG")" != "$EELS_PIN" ]; then
  fail "EELS checkout is not at $EELS_PIN"
fi
if [ -n "$(git -C "$EELS_ROOT" status --porcelain 2>"$LOG")" ]; then
  fail "EELS checkout is dirty"
fi

if ! (cd "$ROOT" && lake env lean \
    scripts/eval-lido-circuit-breaker-deployment.lean \
    >"$ARTIFACTS" 2>"$LOG"); then
  fail "production artifact evaluation failed"
fi
if ! PYTHONPATH="$EELS_ROOT/src" "$EELS_PY" \
    "$SCRIPT_DIR/gen-lido-circuit-breaker-deployment-fixture.py" \
    --eels-root "$EELS_ROOT" --artifacts "$ARTIFACTS" \
    --fixture "$FIXTURE" --metadata "$METADATA" >"$LOG" 2>&1; then
  fail "strict pinned-EELS fixture generation or live projection controls failed"
fi
if ! "$EELS_PY" -c '
import json, sys
m = json.load(open(sys.argv[1]))
assert m["schema"] == "blanc-lido-circuit-breaker-deployment-fixture-v1"
assert m["channel"] == "finite-eels-jaune-not-a-lean-premise"
assert m["transactionCount"] == 1 and m["transactionType"] == 2
assert m["receiptSucceeded"] is True and m["logCount"] == 3
assert m["requestsHash"] == m["expectedEmptyRequestsHash"]
assert m["assertionCount"] == 18
assert len(m["liveRejectedControls"]) == 26
' "$METADATA" >"$LOG" 2>&1; then
  fail "finite fixture metadata, assertion count, or mutation count drifted"
fi
if ! python3 "$SCRIPT_DIR/check-lido-circuit-breaker-deployment.py" \
    >"$LOG" 2>&1; then
  fail "public declaration, premise, or trust assurance failed"
fi
if ! "$SCRIPT_DIR/check.sh" --no-build >"$LOG" 2>&1; then
  fail "exact per-declaration axiom audit failed"
fi
if ! python3 "$SCRIPT_DIR/test-lido-circuit-breaker-deployment-falsifiers.py" \
    >"$LOG" 2>&1; then
  fail "deployment source/Lean falsifier controls failed"
fi
if ! "$JAUNE_BIN" "$FIXTURE" --network Prague >"$LOG" 2>&1; then
  fail "strict Jaune replay of the pinned-EELS fixture failed"
fi

echo "OK — Lido CircuitBreaker direct deployment root (21 pins; 13 reduction certificates; 213 fragments; 164 exact axiom probes; 64 source mutants + 2 Lean controls; 18 finite assertions + 26 finite mutants; 1 strict block)"
