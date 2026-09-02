#!/usr/bin/env bash
# Recompute the finite CircuitBreaker × TWG BPO2 replay through the registered
# current-mainnet target and byte-compare its committed result.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
: "${HOME:?HOME is required}"

WRAPPER_SCHEMA=2
WRAPPER_SCENARIOS="family-pause-query-finite,family-pause-query-sentinel,composed-public-pause-finite,composed-public-pause-sentinel"
WRAPPER_CHANNELS="status,storage,events,outputs,gas"
WRAPPER_MUTANTS="query-code-empty-return,reentrant-heartbeat-noninterference"
WRAPPER_PROFILE="executionFork=BPO2,logicalCompilerFork=Osaka,testingBackend=cancun"
WRAPPER_TX_GAS_LIMIT=1000000
WRAPPER_RLP_BLOCK_SIZE_CAP=8388608
WRAPPER_RLP_BLOCK_UPPER_BOUND=8435
WRAPPER_ARTIFACTS="circuitBreakerBytes=4282,circuitBreakerSha256=ff8eb66d66f8e4668af9bf5b687dda082c3729f8cd5ffd24a4b14697389d1505,gatewayBytes=15948,gatewaySha256=3b9a9442dd0a33d8fc39471bab2f42aed7189859a2c106709631b2c16e6a22e0,gatewayLocator=0x800"
WRAPPER_LEDGER_SHA256="b92017f766d205b1a49dc210f2f4f322f27fdba427ff433cb90d5457583d4bf0"
WRAPPER_RUNTIME_LOCK_SHA256="9dc5ec960cc35b3eb81ae5c4b2a10401f24d068a0347a501721bfb235ecc5e3c"
WRAPPER_ARGS=(
  --wrapper-schema "$WRAPPER_SCHEMA"
  --wrapper-scenarios "$WRAPPER_SCENARIOS"
  --wrapper-channels "$WRAPPER_CHANNELS"
  --wrapper-mutants "$WRAPPER_MUTANTS"
  --wrapper-profile "$WRAPPER_PROFILE"
  --wrapper-tx-gas-limit "$WRAPPER_TX_GAS_LIMIT"
  --wrapper-rlp-block-size-cap "$WRAPPER_RLP_BLOCK_SIZE_CAP"
  --wrapper-rlp-block-upper-bound "$WRAPPER_RLP_BLOCK_UPPER_BOUND"
  --wrapper-artifacts "$WRAPPER_ARTIFACTS"
  --wrapper-ledger-sha256 "$WRAPPER_LEDGER_SHA256"
  --wrapper-runtime-lock-sha256 "$WRAPPER_RUNTIME_LOCK_SHA256"
)

STATIC_ENV=(
  "HOME=$HOME"
  "PATH=/usr/bin:/bin:/usr/sbin:/sbin"
  "PYTHONNOUSERSITE=1"
)
if [[ -n "${TMPDIR:-}" ]]; then
  STATIC_ENV+=("TMPDIR=$TMPDIR")
fi

if [[ "${1:-}" == "--static-self-check" ]]; then
  if [[ "$#" -ne 1 ]]; then
    echo "REGRESSION — Lido TWG pinned-target current-mainnet: static self-check takes no other arguments" >&2
    exit 2
  fi
  exec /usr/bin/env -i "${STATIC_ENV[@]}" /usr/bin/python3 -B \
    "$SCRIPT_DIR/gen-lido-twg-pinned-target-current-mainnet.py" \
    --static-self-check "${WRAPPER_ARGS[@]}"
fi

COMPOSED_PREREQUISITES=0
WRITE=0
while [[ "$#" -gt 0 ]]; do
  case "$1" in
    --composed-prerequisites) COMPOSED_PREREQUISITES=1 ;;
    --write) WRITE=1 ;;
    *)
      echo "REGRESSION — Lido TWG pinned-target current-mainnet: unsupported argument $1" >&2
      exit 2
      ;;
  esac
  shift
done

/usr/bin/env -i "${STATIC_ENV[@]}" /usr/bin/python3 -B \
  "$SCRIPT_DIR/gen-lido-twg-pinned-target-current-mainnet.py" \
  --static-self-check "${WRAPPER_ARGS[@]}"

if [[ "$COMPOSED_PREREQUISITES" -eq 0 ]] && ! "$SCRIPT_DIR/check-current-mainnet.sh" >/dev/null; then
  echo "REGRESSION — Lido TWG pinned-target current-mainnet: shared boundary failed" >&2
  exit 1
fi

if [[ -n "${JAUNE_T8N_TARGET:-}" ]]; then
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
    echo "REGRESSION — Lido TWG pinned-target current-mainnet: target root must be absolute" >&2
    exit 1
    ;;
esac

TARGET_PYTHON="$TARGET_ROOT/.venv/bin/python"
if [[ ! -x "$TARGET_PYTHON" ]]; then
  echo "REGRESSION — Lido TWG pinned-target current-mainnet: target Python absent at $TARGET_PYTHON" >&2
  exit 1
fi

ARTIFACTS="$(mktemp)"
ERRORS="$(mktemp)"
trap 'rm -f "$ARTIFACTS" "$ERRORS"' EXIT
if ! (cd "$ROOT" && lake env lean \
  scripts/eval-lido-twg-pinned-target-current-mainnet.lean \
  >"$ARTIFACTS" 2>"$ERRORS"); then
  cat "$ERRORS" >&2
  echo "REGRESSION — Lido TWG pinned-target current-mainnet: Blanc artifact evaluation failed" >&2
  exit 1
fi

CHILD_ENV=(
  "HOME=$HOME"
  "PATH=$TARGET_ROOT/.venv/bin:/usr/bin:/bin:/usr/sbin:/sbin"
  "PYTHONNOUSERSITE=1"
  "VIRTUAL_ENV=$TARGET_ROOT/.venv"
)
if [[ -n "${TMPDIR:-}" ]]; then
  CHILD_ENV+=("TMPDIR=$TMPDIR")
fi

GENERATOR_ARGS=(
  --root "$TARGET_ROOT"
  --blanc-artifacts "$ARTIFACTS"
  "${WRAPPER_ARGS[@]}"
)
if [[ "$WRITE" -eq 1 ]]; then
  GENERATOR_ARGS+=(--write)
fi

exec /usr/bin/env -i "${CHILD_ENV[@]}" "$TARGET_PYTHON" -B -s \
  "$SCRIPT_DIR/gen-lido-twg-pinned-target-current-mainnet.py" \
  "${GENERATOR_ARGS[@]}"
