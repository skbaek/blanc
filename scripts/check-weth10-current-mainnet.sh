#!/usr/bin/env bash
# WETH10's additive BPO2 consumer of the shared current-mainnet lane.  The
# generator owns fixture/manifest bytes; this wrapper owns the isolated target
# environment, exact Lean artifact evaluators, historical-channel boundary,
# and Jaune replay of every generated block fixture.  It exposes no fork
# override.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
: "${HOME:?HOME is required}"

COMPOSED_PREREQUISITES=0
WRITE=0
STATIC_SELF_CHECK=0
while [ "$#" -gt 0 ]; do
  case "$1" in
    --composed-prerequisites) COMPOSED_PREREQUISITES=1 ;;
    --write) WRITE=1 ;;
    --static-self-check) STATIC_SELF_CHECK=1 ;;
    *)
      echo "usage: scripts/check-weth10-current-mainnet.sh [--composed-prerequisites] [--write] [--static-self-check]" >&2
      exit 2
      ;;
  esac
  shift
done

if [ -n "${JAUNE_T8N_TARGET:-}" ]; then
  TARGET_ROOT="$JAUNE_T8N_TARGET"
else
  TARGET_ROOT="$HOME/execution-specs-t8n-amsterdam"
fi
case "$TARGET_ROOT" in
  "~/"*) TARGET_ROOT="$HOME/${TARGET_ROOT#\~/}" ;;
esac
case "$TARGET_ROOT" in
  /*) ;;
  *)
    echo "REGRESSION — WETH10 current-mainnet: target root must be absolute" >&2
    exit 1
    ;;
esac

TARGET_PYTHON="$TARGET_ROOT/.venv/bin/python"
if [ ! -x "$TARGET_PYTHON" ]; then
  echo "REGRESSION — WETH10 current-mainnet: target Python absent at $TARGET_PYTHON" >&2
  exit 1
fi

HISTORICAL_BOUNDARY="BPO2 credits status, receipt gas, exact returndata, logs, projected storage, and ETH for the canonical 27-selector-plus-receive matrix, reading returndata from the pinned target's own EIP-3155 trace. The preserved Prague differential still owns the 119 rows outside that matrix and the live CALL and STATICCALL traces within it; that remainder is measured migration debt recorded in scripts/current-mainnet-parity.json, not a claim that those behaviours cannot have changed across the fork"
EVIDENCE_BOUNDARY_FALSIFIERS=4

CHILD_ENV=(
  "HOME=$HOME"
  "PATH=$TARGET_ROOT/.venv/bin:/usr/bin:/bin:/usr/sbin:/sbin"
  "PYTHONNOUSERSITE=1"
  "VIRTUAL_ENV=$TARGET_ROOT/.venv"
)
if [ -n "${TMPDIR:-}" ]; then
  CHILD_ENV+=("TMPDIR=$TMPDIR")
fi

if [ "$STATIC_SELF_CHECK" -eq 1 ] &&
    { [ "$COMPOSED_PREREQUISITES" -ne 0 ] || [ "$WRITE" -ne 0 ]; }; then
  echo "REGRESSION — WETH10 current-mainnet: static self-check takes no other option" >&2
  exit 2
fi

# Reject widened APIs, stale inventories, a pre-BPO2 timestamp, or a changed
# historical-channel boundary before any shared t8n, Lean evaluator, or build.
/usr/bin/env -i "${CHILD_ENV[@]}" "$TARGET_PYTHON" -B -s \
  "$SCRIPT_DIR/gen-weth10-current-mainnet.py" \
  --static-self-check \
  --wrapper-historical-boundary "$HISTORICAL_BOUNDARY" \
  --wrapper-evidence-falsifiers "$EVIDENCE_BOUNDARY_FALSIFIERS"
if [ "$STATIC_SELF_CHECK" -eq 1 ]; then
  exit 0
fi

if [ "$COMPOSED_PREREQUISITES" -eq 0 ] &&
    ! "$SCRIPT_DIR/check-current-mainnet.sh"; then
  echo "REGRESSION — WETH10 current-mainnet: shared boundary failed" >&2
  exit 1
fi

ARTIFACT_DIR="$(mktemp -d)"
trap 'rm -rf "$ARTIFACT_DIR"' EXIT
DEPLOYMENT_ARTIFACTS="$ARTIFACT_DIR/deployment.txt"
RUNTIME_ARTIFACTS="$ARTIFACT_DIR/runtime.txt"
DEPLOYMENT_ERRORS="$ARTIFACT_DIR/deployment.err"
RUNTIME_ERRORS="$ARTIFACT_DIR/runtime.err"

if ! (cd "$ROOT" && lake env lean scripts/eval-weth10-deployment-code.lean \
    >"$DEPLOYMENT_ARTIFACTS" 2>"$DEPLOYMENT_ERRORS"); then
  cat "$DEPLOYMENT_ERRORS" >&2
  echo "REGRESSION — WETH10 current-mainnet: deployment artifact evaluation failed" >&2
  exit 1
fi
if ! (cd "$ROOT" && lake env lean scripts/eval-weth10-differential-code.lean \
    >"$RUNTIME_ARTIFACTS" 2>"$RUNTIME_ERRORS"); then
  cat "$RUNTIME_ERRORS" >&2
  echo "REGRESSION — WETH10 current-mainnet: runtime artifact evaluation failed" >&2
  exit 1
fi

GENERATOR_ARGS=(
  --root "$TARGET_ROOT"
  --deployment-artifacts "$DEPLOYMENT_ARTIFACTS"
  --runtime-artifacts "$RUNTIME_ARTIFACTS"
  --wrapper-historical-boundary "$HISTORICAL_BOUNDARY"
  --wrapper-evidence-falsifiers "$EVIDENCE_BOUNDARY_FALSIFIERS"
)
if [ "$WRITE" -eq 1 ]; then
  GENERATOR_ARGS+=(--write)
fi

/usr/bin/env -i "${CHILD_ENV[@]}" "$TARGET_PYTHON" -B -s \
  "$SCRIPT_DIR/gen-weth10-current-mainnet.py" "${GENERATOR_ARGS[@]}"

BIN="$ROOT/.lake/packages/jaune/.lake/build/bin/jaune"
if ! (cd "$ROOT" && lake build jaune/jaune); then
  echo "REGRESSION — WETH10 current-mainnet: lake build jaune/jaune failed" >&2
  exit 1
fi
if [ ! -x "$BIN" ]; then
  echo "REGRESSION — WETH10 current-mainnet: Jaune runner absent at $BIN" >&2
  exit 1
fi

FIXTURE_DIR="$SCRIPT_DIR/fixtures/weth10-current-mainnet"
TOTAL=0
FAIL=0
OUT="$ARTIFACT_DIR/jaune.out"
for fixture in "$FIXTURE_DIR"/*-block.json; do
  if [ ! -f "$fixture" ]; then
    continue
  fi
  TOTAL=$((TOTAL + 1))
  if "$BIN" "$fixture" --network BPO2 >"$OUT" 2>&1; then
    echo "PASS  $(basename "$fixture")"
  else
    echo "FAIL  $(basename "$fixture")"
    sed 's/^/      /' "$OUT"
    FAIL=$((FAIL + 1))
  fi
done
if [ "$TOTAL" -ne 3 ]; then
  echo "REGRESSION — WETH10 current-mainnet: expected exactly three block fixtures, found $TOTAL" >&2
  exit 1
fi
if [ "$FAIL" -ne 0 ]; then
  echo "REGRESSION — WETH10 current-mainnet: $((TOTAL - FAIL))/$TOTAL BPO2 block fixtures replayed" >&2
  exit 1
fi

echo "OK — WETH10 current-mainnet: generator current, 3/3 BPO2 block fixtures replayed, 28 ordinary-call rows credited across 6 channels including exact returndata"
