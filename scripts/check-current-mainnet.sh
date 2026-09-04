#!/bin/bash
# Contract-neutral current-mainnet lane.  The literal arguments below are an
# independent owner of the profile and its semantic controls; current_mainnet.py
# refuses any disagreement.  This wrapper resolves only JAUNE_T8N_TARGET (or its
# declared default) and never inherits an ambient Python environment.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
: "${HOME:?HOME is required}"

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
  *) echo "REGRESSION — current-mainnet lane: target root must be absolute: $TARGET_ROOT" >&2; exit 1 ;;
esac

TARGET_PYTHON="$TARGET_ROOT/.venv/bin/python"
if [[ ! -x "$TARGET_PYTHON" ]]; then
  echo "REGRESSION — current-mainnet lane: isolated target Python is absent: $TARGET_PYTHON" >&2
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

/usr/bin/env -i "${CHILD_ENV[@]}" \
  "$TARGET_PYTHON" -B -X pycache_prefix=/dev/null -s "$SCRIPT_DIR/gen-current-mainnet-runtime-lock.py" \
    --self-check
/usr/bin/env -i "${CHILD_ENV[@]}" \
  "$TARGET_PYTHON" -B -X pycache_prefix=/dev/null -s "$SCRIPT_DIR/gen-current-mainnet-runtime-lock.py" \
    --check --root "$TARGET_ROOT"

exec /usr/bin/env -i "${CHILD_ENV[@]}" \
  "$TARGET_PYTHON" -I -s -B -X pycache_prefix=/dev/null "$SCRIPT_DIR/current_mainnet.py" \
    --check \
    --root "$TARGET_ROOT" \
    --_expected-schema 1 \
    --_expected-name blanc-current-mainnet \
    --_expected-execution-fork BPO2 \
    --_expected-execution-module ethereum.forks.bpo2 \
    --_expected-chain-id 1 \
    --_expected-reward -1 \
    --_expected-logical-compiler Osaka \
    --_expected-testing-backend cancun \
    --_expected-external-solc false \
    --_expected-repository https://github.com/ethereum/execution-specs.git \
    --_expected-upstream 9d6e6f8352a0f76e7e8803722d1a2798fa4f0a96 \
    --_expected-checkout 827a1cad9c9c8528512f90a06888c8bd9171d9ae \
    --_expected-overlay-sha fc0048871d3f0546d95401f1727e4828523ea46269cbea461ceefeaf13042ea8 \
    --_expected-overlay-path packages/testing/src/execution_testing/client_clis/__init__.py \
    --_expected-overlay-path packages/testing/src/execution_testing/client_clis/clis/jaune.py \
    --_expected-overlay-path packages/testing/src/execution_testing/client_clis/tests/test_jaune.py \
    --_expected-overlay-path packages/testing/src/execution_testing/client_clis/transition_tool.py \
    --_expected-root-env JAUNE_T8N_TARGET \
    --_expected-default-root '~/execution-specs-t8n-amsterdam' \
    --_expected-git /usr/bin/git \
    --_expected-venv .venv \
    --_expected-python bin/python \
    --_expected-t8n bin/ethereum-spec-evm \
    --_expected-python-implementation CPython \
    --_expected-python-version 3.11.9 \
    --_expected-runtime-lock current-mainnet-runtime-lock.json \
    --_expected-python-platform 'macos-arm64|Darwin|arm64|~/.local/share/uv/python/cpython-3.11-macos-aarch64-none|~/.local/share/uv/python/cpython-3.11.9-macos-aarch64-none' \
    --_expected-python-platform 'linux-x86_64|Linux|x86_64|~/.local/share/uv/python/cpython-3.11-linux-x86_64-gnu|~/.local/share/uv/python/cpython-3.11.9-linux-x86_64-gnu' \
    --_expected-blob-target 14 \
    --_expected-blob-max 21 \
    --_expected-blob-fraction 11684671 \
    --_expected-canary-opcode BLOBBASEFEE \
    --_expected-canary-program 0x4a5f5500 \
    --_expected-canary-address 0x0000000000000000000000000000000000001000 \
    --_expected-canary-excess 0x5f5e100 \
    --_expected-canary-key 0x0 \
    --_expected-canary-value 0x1459 \
    --_falsifier Prague \
    --_falsifier Osaka \
    --_falsifier BPO1 \
    --_falsifier BPO3 \
    --_falsifier missing
