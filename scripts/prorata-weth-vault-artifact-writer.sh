#!/usr/bin/env bash
# Fixed dispatch to the registered vault artifact writer; never builds imports.
# Prerequisite: build the evaluator's imports through the owned build capability
# at this exact source state. Invoke through the reviewed host workflow on hosts
# that require containment; the writer may replace its registered output only.
set -euo pipefail

if [ "$#" -ne 0 ]; then
  echo 'usage: scripts/prorata-weth-vault-artifact-writer.sh' >&2
  exit 2
fi

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/.."
exec lake env lean scripts/gen-prorata-weth-vault-code.lean
