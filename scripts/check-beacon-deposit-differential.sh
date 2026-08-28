#!/usr/bin/env bash
# Execute the pinned deployed beacon-deposit runtime and Blanc's evaluated
# runtime through the clean pinned EELS Prague interpreter.  This gate is
# offline and fail-closed: it never fetches EELS, rewrites reference inputs,
# or invents an artifact when the Lean evaluator is absent.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
EELS_ROOT="${EELS_ROOT:-$HOME/execution-specs}"
EELS_PY="$EELS_ROOT/venv/bin/python"
ARTIFACTS="$(mktemp)"
ERRORS="$(mktemp)"
trap 'rm -f "$ARTIFACTS" "$ERRORS"' EXIT

# This wrapper independently owns the public matrix contract.  The Python
# runner must agree before Lean or EELS execution, so a self-consistent
# weakening in the generator alone cannot silently redefine the gate.
WRAPPER_SCHEMA=2
WRAPPER_CHANNELS="status,returndata,state-projection,eth,logs,sha-staticcall"
WRAPPER_TAGS="selector-deposit,selector-get-deposit-root,selector-get-deposit-count,selector-supports-interface,no-match,malformed-abi,abi-reordered-tails-accepted,abi-overlapping-tails-accepted,abi-dirty-padding-accepted,abi-trailing-data-accepted,abi-all-tails-structural-before-source-guard,nonpayable-root-value,nonpayable-count-value,nonpayable-supports-value,guard-01-invalid-pubkey,guard-02-invalid-withdrawal-credentials,guard-03-invalid-signature,guard-04-value-too-low,guard-05-value-not-gwei,guard-06-value-too-high,guard-07-root-mismatch,guard-08-cap,guard-precedence,value-edge-ether-minus-one,value-edge-one-ether,value-edge-ether-plus-one,value-edge-next-gwei,value-edge-uint64-max,value-edge-above-uint64,chained-counts,root-readback,count-readback,byte-exact-log,byte-exact-revert,sha-staticcall-trace,disabled-precompile-failed-payload,disabled-precompile-failed-empty,disabled-precompile-failed-long,disabled-precompile-short-success,disabled-precompile-long-success-first-word,sha-output-buffer-trace,oog-common-gas-before-first-call,oog-common-gas-child-failure,oog-common-gas-first-success,seeded-cap-layouts,gas-recorded-every-path"
WRAPPER_CHANNEL_FALSIFIERS=6
WRAPPER_MANIFEST_FALSIFIERS=10
WRAPPER_STATIC_FALSIFIERS=4
WRAPPER_ARGS=(
  --wrapper-schema "$WRAPPER_SCHEMA"
  --wrapper-channels "$WRAPPER_CHANNELS"
  --wrapper-tags "$WRAPPER_TAGS"
  --wrapper-channel-falsifiers "$WRAPPER_CHANNEL_FALSIFIERS"
  --wrapper-manifest-falsifiers "$WRAPPER_MANIFEST_FALSIFIERS"
  --wrapper-static-falsifiers "$WRAPPER_STATIC_FALSIFIERS"
)

if [ ! -x "$EELS_PY" ]; then
  echo "REGRESSION — beacon-deposit differential: pinned EELS python not found at $EELS_PY" >&2
  exit 1
fi

if ! PYTHONDONTWRITEBYTECODE=1 "$EELS_PY" \
  "$SCRIPT_DIR/gen-beacon-deposit-differential.py" \
  --static-self-check "${WRAPPER_ARGS[@]}"; then
  echo "REGRESSION — beacon-deposit differential: wrapper/Python matrix contract failed" >&2
  exit 1
fi

if ! (cd "$ROOT" && lake env lean \
  scripts/eval-beacon-deposit-differential-code.lean \
  >"$ARTIFACTS" 2>"$ERRORS"); then
  cat "$ERRORS" >&2
  echo "REGRESSION — beacon-deposit differential: Blanc artifact evaluation failed" >&2
  exit 1
fi

PYTHONDONTWRITEBYTECODE=1 PYTHONPATH="$EELS_ROOT/src" "$EELS_PY" \
  "$SCRIPT_DIR/gen-beacon-deposit-differential.py" \
  --eels-root "$EELS_ROOT" --blanc-artifacts "$ARTIFACTS" \
  "${WRAPPER_ARGS[@]}" "$@"
