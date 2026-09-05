#!/usr/bin/env bash
# Recompute the report-only OssifiableProxy BPO2 transaction replay through
# the shared current-mainnet lane and byte-compare the committed report.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
: "${HOME:?HOME is required}"

COMPOSED_PREREQUISITES=0
if [ "${1:-}" = "--composed-prerequisites" ]; then
  COMPOSED_PREREQUISITES=1
  shift
fi
if [ "$#" -ne 0 ]; then
  echo "usage: scripts/check-lido-ossifiable-proxy-current-mainnet.sh [--composed-prerequisites]" >&2
  exit 2
fi

if [ "$COMPOSED_PREREQUISITES" -eq 0 ] && ! "$SCRIPT_DIR/check-current-mainnet.sh" >/dev/null; then
  echo "REGRESSION — OssifiableProxy BPO2 replay: shared boundary failed" >&2
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
    echo "REGRESSION — OssifiableProxy BPO2 replay: target root must be absolute" >&2
    exit 1
    ;;
esac

TARGET_PYTHON="$TARGET_ROOT/.venv/bin/python"
if [ ! -x "$TARGET_PYTHON" ]; then
  echo "REGRESSION — OssifiableProxy BPO2 replay: target Python absent" >&2
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

REPLAY_OUT="$(/usr/bin/env -i "${CHILD_ENV[@]}" "$TARGET_PYTHON" \
  -I -s -B -X pycache_prefix=/dev/null \
  "$SCRIPT_DIR/run-current-mainnet-isolated.py" "$TARGET_ROOT" \
  "gen-lido-ossifiable-proxy-current-mainnet.py" \
  --root "$TARGET_ROOT" 2>&1)" || {
  printf '%s\n' "$REPLAY_OUT" >&2
  echo "REGRESSION — OssifiableProxy BPO2 replay failed" >&2
  exit 1
}
printf '%s\n' "${REPLAY_OUT##*$'\n'}"
