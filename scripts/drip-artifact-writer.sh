#!/usr/bin/env bash
# Fixed dispatch to the registered DRIP artifact writers; never builds imports.
# Prerequisite: build the selected evaluator's imports through the owned build
# capability at this exact source state. Runtime generation can invalidate the
# creation evaluator's imports: rebuild them before selecting creation.
set -euo pipefail

if [ "$#" -ne 1 ]; then
  echo 'usage: scripts/drip-artifact-writer.sh runtime|creation' >&2
  exit 2
fi
case "$1" in
  runtime) evaluator=scripts/gen-drip-code.lean ;;
  creation) evaluator=scripts/gen-drip-creation-code.lean ;;
  *) echo 'usage: scripts/drip-artifact-writer.sh runtime|creation' >&2; exit 2 ;;
esac

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/.."
exec lake env lean "$evaluator"
