#!/usr/bin/env bash
# Fail-closed check of docs/DEPLOYED_BYTECODE_CLAIM_MAP.md against the repository: every cited
# declaration, file:line, axiom claim, count, artifact digest and trust-base figure. Offline; it
# elaborates no Lean. The in-memory falsifiers always run.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$SCRIPT_DIR/check-deployed-claim-map.py" --self-test "$@"
