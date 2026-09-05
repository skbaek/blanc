#!/usr/bin/env bash
# Offline Solidity/Blanc Lido CircuitBreaker differential through pinned EELS.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
EELS_ROOT="${EELS_ROOT:-$HOME/execution-specs}"
EELS_PY="$EELS_ROOT/venv/bin/python"
export PYTHONDONTWRITEBYTECODE=1
export PYTHONPYCACHEPREFIX=/dev/null
ARTIFACTS="$(mktemp)"
ERRORS="$(mktemp)"
GENERATOR_OUT="$(mktemp)"
trap 'rm -f "$ARTIFACTS" "$ERRORS" "$GENERATOR_OUT"' EXIT

if [ ! -x "$EELS_PY" ]; then
  echo "REGRESSION — Lido CircuitBreaker differential: pinned EELS python not found at $EELS_PY"
  exit 1
fi

if ! (cd "$ROOT" && lake env lean scripts/eval-lido-circuit-breaker-artifacts.lean >"$ARTIFACTS" 2>"$ERRORS"); then
  echo "REGRESSION — Lido CircuitBreaker differential: Blanc artifact evaluation failed"
  exit 1
fi

if ! PYTHONDONTWRITEBYTECODE=1 "$EELS_PY" -I -s -B -X pycache_prefix=/dev/null \
  "$SCRIPT_DIR/run-isolated-python.py" "$EELS_ROOT" "gen-lido-circuit-breaker-differential.py" \
  --eels-root "$EELS_ROOT" --blanc-artifacts "$ARTIFACTS" "$@" >"$GENERATOR_OUT"; then
  exit 1
fi

for argument in "$@"; do
  if [ "$argument" = "--experiment-summary" ]; then
    cat "$GENERATOR_OUT"
    exit 0
  fi
done

# Independent fail-closed ownership for the exact AC9 required-tag set.  This
# digest is intentionally outside the mutable case generator and covers the
# ordered 77-tag list plus a terminating newline.
MANIFEST="$SCRIPT_DIR/fixtures/lido-circuit-breaker/manifest.json"
EXPECTED_REQUIRED_TAGS_SHA256="c54962c0811e6ac20eb7d069fac549ff7a703ca2705d40c89f51d838c8c2877e"
TAG_INFO="$($EELS_PY -c 'import hashlib,json,sys; p=json.load(open(sys.argv[1])); tags=p["coverage"]["requiredTags"]; payload=("\n".join(tags)+"\n").encode(); print(p["schema"],len(tags),hashlib.sha256(payload).hexdigest())' "$MANIFEST")"
if [ "$TAG_INFO" != "2 77 $EXPECTED_REQUIRED_TAGS_SHA256" ]; then
  echo "REGRESSION — Lido CircuitBreaker differential: manifest schema or exact required-tag ownership drifted"
  exit 1
fi

if ! PYTHONDONTWRITEBYTECODE=1 "$EELS_PY" \
  "$SCRIPT_DIR/lido_circuit_breaker_resource_schema.py" "$MANIFEST" >/dev/null; then
  exit 1
fi

if ! PYTHONDONTWRITEBYTECODE=1 "$EELS_PY" \
  "$SCRIPT_DIR/test-lido-circuit-breaker-resource-falsifiers.py" >/dev/null; then
  exit 1
fi

cat "$GENERATOR_OUT"
