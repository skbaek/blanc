#!/usr/bin/env bash
# DRIP family evidence gate: arithmetic, artifact controls and complete pinned
# Jaune BPO2 replay. Requires an already-built runner; never builds implicitly.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

cd "$ROOT"
python3 -B scripts/gen-drip-oracle-vectors.py
python3 -B scripts/check-drip-oracle.py
python3 -B scripts/check-drip-oracle.py --self-test
python3 -B scripts/check-drip-artifacts.py
python3 -B scripts/check-drip-artifacts.py --self-test
python3 -B scripts/test-check-drip-fixtures.py
python3 -B scripts/test-check-drip-replay.py
python3 -B scripts/test-drip-evaluator.py
python3 -B scripts/test-drip-receipts.py
python3 -B scripts/test-drip-arithmetic.py
python3 -B scripts/test-drip-evaluator-identity.py
python3 -B scripts/check-drip-arithmetic.py
python3 -B scripts/check-drip-replay.py
echo "OK — DRIP evidence: artifact checks, mocked evaluator controls, independent Lean arithmetic and complete pinned Jaune BPO2 replay passed"
