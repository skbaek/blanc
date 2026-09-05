#!/usr/bin/env bash
# Exact compiler-byte and pinned-EELS dispatcher frontier for W3/O4.

set -u

DISPATCH_SELECTION_STAGE="${LIDO_DISPATCHER_SELECTION_STAGE:-selected}"
case "$DISPATCH_SELECTION_STAGE" in
  pending|selected) ;;
  *)
    echo "REGRESSION — Lido CircuitBreaker dispatcher: invalid selection lifecycle"
    exit 2
    ;;
esac
if [ "$#" -eq 0 ]; then
  if [ "$DISPATCH_SELECTION_STAGE" = "selected" ]; then
    DISPATCH_MODE="full-vector"
  else
    DISPATCH_MODE="focused"
  fi
elif [ "$#" -eq 1 ] && [ "$1" = "--full-vector" ]; then
  DISPATCH_MODE="full-vector"
else
  echo "usage: $0 [--full-vector]"
  exit 2
fi
if [ "$DISPATCH_SELECTION_STAGE" = "selected" ] && \
    [ "$DISPATCH_MODE" != "full-vector" ]; then
  echo "REGRESSION — Lido CircuitBreaker dispatcher: selected lifecycle requires --full-vector"
  exit 2
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
EELS_ROOT="${EELS_ROOT:-$HOME/execution-specs}"
EELS_PY="$EELS_ROOT/venv/bin/python"
export PYTHONDONTWRITEBYTECODE=1
export PYTHONPYCACHEPREFIX=/dev/null
BLANC_ARTIFACTS="$(mktemp)"
DISPATCH_ARTIFACTS="$(mktemp)"
PROFILE="$(mktemp)"
trap 'rm -f "$BLANC_ARTIFACTS" "$DISPATCH_ARTIFACTS" "$PROFILE"' EXIT

if [ ! -x "$EELS_PY" ]; then
  echo "REGRESSION — Lido CircuitBreaker dispatcher: pinned EELS python not found"
  exit 1
fi

if ! (cd "$ROOT" && lake env lean scripts/eval-lido-circuit-breaker-artifacts.lean \
    >"$BLANC_ARTIFACTS"); then
  echo "REGRESSION — Lido CircuitBreaker dispatcher: production artifact evaluation failed"
  exit 1
fi

if ! (cd "$ROOT" && lake env lean scripts/eval-lido-circuit-breaker-dispatchers.lean \
    >"$DISPATCH_ARTIFACTS"); then
  echo "REGRESSION — Lido CircuitBreaker dispatcher: candidate evaluation failed"
  exit 1
fi

if ! PYTHONDONTWRITEBYTECODE=1 "$EELS_PY" -I -s -B -X pycache_prefix=/dev/null "$SCRIPT_DIR/run-isolated-python.py" "$EELS_ROOT" "check-lido-circuit-breaker-dispatchers.py" \
    --eels-root "$EELS_ROOT" \
    --blanc-artifacts "$BLANC_ARTIFACTS" \
    --dispatcher-artifacts "$DISPATCH_ARTIFACTS" \
    --mode "$DISPATCH_MODE" \
    --selection-stage "$DISPATCH_SELECTION_STAGE" >"$PROFILE"; then
  exit 1
fi

if ! SUMMARY="$("$EELS_PY" -c 'import json,sys
p=json.load(open(sys.argv[1], encoding="utf-8")); label=p["selection"]["selected"]
c=p["candidates"][label]; f=p["fullVector"]["candidates"][label]; s=f["runtimeSummary"]
print(f"OK — Lido CircuitBreaker dispatcher: {len(p['"'"'candidateOrder'"'"'])} legal .branch candidates; selected {label} at {c['"'"'byteLength'"'"']} bytes; {len(c['"'"'directRows'"'"'])} focused rows + {len(c['"'"'reachableEndpoints'"'"'])} endpoint cases + {f['"'"'caseCount'"'"']}-case/{f['"'"'boundaryCount'"'"']}-boundary replay; {s['"'"'adequacyCounts'"'"']['"'"'adequate'"'"']} adequate runtime boundaries cheaper, {s['"'"'adequacyCounts'"'"']['"'"'oog-control'"'"']} equal OOG, {s['"'"'adequatePositiveDeltaCount'"'"']} positives; dual-world production match; {s['"'"'successfulStrictImprovementCount'"'"']} strict successful improvements")' \
  "$PROFILE" 2>/dev/null)"; then
  echo "REGRESSION — Lido CircuitBreaker dispatcher: checker summary schema drifted"
  exit 1
fi
echo "$SUMMARY"
