#!/usr/bin/env bash
# Regenerate PRORATA's committed BPO2 fixture documents in memory through the
# reusable current-mainnet API and byte-compare them without writing.  The
# ordinary check-prorata.sh gate separately replays those committed blocks and
# deliberately remains runnable in CI without this isolated target checkout.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
: "${HOME:?HOME is required}"

if [ "$#" -ne 0 ]; then
  echo "usage: scripts/check-prorata-current-mainnet.sh" >&2
  exit 2
fi

if ! "$SCRIPT_DIR/check-current-mainnet.sh"; then
  echo "REGRESSION — prorata current-mainnet: shared boundary failed" >&2
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
    echo "REGRESSION — prorata current-mainnet: target root must be absolute" >&2
    exit 1
    ;;
esac

TARGET_PYTHON="$TARGET_ROOT/.venv/bin/python"
if [ ! -x "$TARGET_PYTHON" ]; then
  echo "REGRESSION — prorata current-mainnet: target Python absent at $TARGET_PYTHON" >&2
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
  "$SCRIPT_DIR/gen-prorata-fixtures.py" --root "$TARGET_ROOT" 2>&1)" || {
  printf '%s\n' "$GENERATOR_OUT" >&2
  echo "REGRESSION — prorata current-mainnet: BPO2 regeneration check failed" >&2
  exit 1
}
printf '%s\n' "$GENERATOR_OUT"
echo "OK — prorata current-mainnet: 14 BPO2 scenarios regenerate byte-for-byte"
