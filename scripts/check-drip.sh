#!/usr/bin/env bash
# DRIP family evidence gate: arithmetic, artifact controls and complete pinned
# Jaune BPO2 replay. Requires an already-built runner; never builds implicitly.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
. "$SCRIPT_DIR/gate-semaphore.sh"
trap 'gate_semaphore_release' EXIT

cd "$ROOT"

# `--self-test` (evidence economy rule 3): the harness's own corruption and
# mocked-protocol suites. Each one mutates a copy or synthesizes its input and
# shows a checker rejects it, which is a property of the checker, not of the
# committed DRIP sources, vectors or fixtures; the default run applies those
# same checkers to the committed tree. Its registry inputs are the harness
# files, so it reruns when a checker or control changes, not on every Lean edit.
# It starts no Lean child and takes no host hold.
case "${1:-}" in
  "") ;;
  --self-test)
    python3 -B scripts/check-drip-oracle.py --self-test
    python3 -B scripts/check-drip-artifacts.py --self-test
    python3 -B scripts/test-check-drip-fixtures.py
    python3 -B scripts/test-check-drip-replay.py
    python3 -B scripts/test-drip-evaluator.py
    python3 -B scripts/test-drip-receipts.py
    python3 -B scripts/test-drip-arithmetic.py
    python3 -B scripts/test-drip-evaluator-identity.py
    python3 -B scripts/test-drip-gate-coordination.py
    echo "OK — DRIP self-test: 2 corruption suites and 7 mocked checker/protocol suites passed"
    exit 0
    ;;
  *)
    echo "usage: scripts/check-drip.sh [--self-test]" >&2
    exit 2
    ;;
esac

python3 -B scripts/gen-drip-oracle-vectors.py
python3 -B scripts/check-drip-oracle.py
python3 -B scripts/check-drip-artifacts.py
gate_semaphore_acquire "DRIP arithmetic, receipt authentication and pinned replay" || exit 2
python3 -B scripts/check-drip-arithmetic.py
python3 -B scripts/check-drip-replay.py
echo "OK — DRIP evidence: vectors, oracle and artifact checks, independent Lean arithmetic and complete pinned Jaune BPO2 replay passed (harness controls: --self-test)"
