#!/usr/bin/env bash
# Fail-closed proxy-pair upgrade assurance gate. Run from the Blanc checkout
# under test; use --self-test for its isolated enforcement mutations.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/check-proxy-pair-upgrade.py" "$@"
