#!/usr/bin/env bash
# Read-only DRIP BPO2 fixture regeneration through the shared current-mainnet
# boundary.  The committed population is authored only by the generator's
# explicit --write mode after a successful target run.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
: "${HOME:?HOME is required}"

COMPOSED_PREREQUISITES=0
if [ "${1:-}" = "--composed-prerequisites" ]; then
  COMPOSED_PREREQUISITES=1
  shift
fi
if [ "$#" -ne 0 ]; then
  echo "usage: scripts/check-drip-current-mainnet.sh [--composed-prerequisites]" >&2
  exit 2
fi

if [ "$COMPOSED_PREREQUISITES" -eq 0 ] && ! "$SCRIPT_DIR/check-current-mainnet.sh"; then
  echo "REGRESSION — DRIP current-mainnet: shared boundary failed" >&2
  exit 1
fi

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
    echo "REGRESSION — DRIP current-mainnet: target root must be absolute" >&2
    exit 1
    ;;
esac

TARGET_PYTHON="$TARGET_ROOT/.venv/bin/python"
if [ ! -x "$TARGET_PYTHON" ]; then
  echo "REGRESSION — DRIP current-mainnet: target Python absent at $TARGET_PYTHON" >&2
  exit 1
fi

CHILD_ENV=(
  "HOME=$HOME"
  "PATH=$TARGET_ROOT/.venv/bin:/usr/bin:/bin:/usr/sbin:/sbin"
  "PYTHONNOUSERSITE=1"
  "VIRTUAL_ENV=$TARGET_ROOT/.venv"
)
if [ -n "${TMPDIR:-}" ]; then
  CHILD_ENV+=("TMPDIR=$TMPDIR")
fi

GENERATOR_OUT="$(/usr/bin/env -i "${CHILD_ENV[@]}" "$TARGET_PYTHON" -B -s \
  "$SCRIPT_DIR/gen-drip-fixtures.py" --check-runtime --root "$TARGET_ROOT" 2>&1)" || {
  printf '%s\n' "$GENERATOR_OUT" >&2
  echo "REGRESSION — DRIP current-mainnet: BPO2 fixture regeneration check failed" >&2
  exit 1
}
printf '%s\n' "$GENERATOR_OUT"
echo "OK — DRIP current-mainnet: generated BPO2 fixture population reproduces"
