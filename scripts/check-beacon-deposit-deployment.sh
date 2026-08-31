#!/usr/bin/env bash
# Closed finite control for the exact BeaconDeposit direct deployment root.
# All generated products are temporary and are never admitted as Lean input.

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
  echo "REGRESSION — BeaconDeposit deployment control: $1" >&2
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
    scripts/eval-beacon-deposit-deployment.lean \
    >"$ARTIFACTS" 2>"$LOG"); then
  fail "production deployment evaluation failed"
fi
if ! PYTHONPATH="$EELS_ROOT/src" "$EELS_PY" \
    "$SCRIPT_DIR/gen-beacon-deposit-deployment-fixture.py" \
    --eels-root "$EELS_ROOT" --artifacts "$ARTIFACTS" \
    --fixture "$FIXTURE" --metadata "$METADATA" >"$LOG" 2>&1; then
  fail "pinned-EELS fixture generation or mandatory mutants failed"
fi
if ! "$EELS_PY" -c '
import json, sys
m = json.load(open(sys.argv[1]))
assert m["schema"] == "blanc-beacon-deposit-deployment-control-v1"
assert m["channel"] == "finite-eels-jaune-not-a-lean-premise"
assert m["eelsPin"] == "4198b9c5996713b268aed602739d5aa40e277694"
assert m["transactionCount"] == 1 and m["transactionType"] == 2
assert m["creationBytes"] == 3037
assert m["creationSha256"] == "3f3af51d0674c1afb7679dbcc60720bbd3f3d61adc9bd319da025064c0521c59"
assert m["runtimeBytes"] == 2891
assert m["runtimeSha256"] == "8f2474c60f85dce94e97403369d64d94d7cce4bbb44e620175bd43a5990f0c48"
assert m["constructorStorageWords"] == 31
assert m["createMessageGas"] == 1276573
assert m["transactionGas"] == m["transactionIntrinsicGas"] + m["createMessageGas"]
assert m["transactionCalldataFloorGas"] <= m["transactionGas"]
assert m["receiptSucceeded"] is True and m["logCount"] == 0
assert m["requestsHash"] == m["expectedEmptyRequestsHash"]
assert m["assertionCount"] == 15 and m["reversionAssertionCount"] == 15
assert m["mandatoryMutants"] == {
    "wrong-target-derivation": "CREATE target derivation boundary",
    "wrong-installed-runtime": "installed runtime boundary",
    "wrong-constructor-storage": "constructor storage boundary",
}
' "$METADATA" >"$LOG" 2>&1; then
  fail "metadata, envelope, projection, mutant, or reversion count drifted"
fi
if ! "$JAUNE_BIN" "$FIXTURE" --network Prague >"$LOG" 2>&1; then
  fail "strict Jaune replay of the independently generated block failed"
fi

echo "OK — BeaconDeposit direct deployment control (15 finite assertions; exact 3,037/2,891-byte artifacts; 31 independently reconstructed storage words; 3 intended-boundary mutants + green reversion; 1 strict Prague block)"
