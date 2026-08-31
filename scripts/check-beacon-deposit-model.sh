#!/usr/bin/env bash
# Vector-comparison gate for the BeaconDeposit pure model.
#
# Default mode: re-pins the fidelity target (SHA-256 of the committed
# deposit_contract.sol), re-derives the committed golden vectors via
# gen-beacon-deposit-vectors.py --check, runs the Lean evaluator
# (scripts/eval-beacon-deposit-model.lean, keccak-256 and SHA-256
# instantiations) with
# `lake env lean`, and compares its output fail-closed against
# scripts/reference/beacon-deposit/vectors.json. The gate does NOT run
# `lake build`: a stale or missing build is the caller's error and surfaces
# as a REGRESSION. The evaluator takes a few minutes.
#
# Falsifier modes:
#   --falsify-dry  Verify the four mutant patches apply cleanly to
#                  temporary copies of the two Blanc modules. No build.
#   --falsify      Full mutation campaign: per mutant, a temporary git
#                  worktree of HEAD with a cloned build cache when the host
#                  supports it and a portable recursive-copy fallback, a
#                  `lake build` (must succeed — the mutants are
#                  self-consistent by design), an evaluator run, and the
#                  requirement that the vector comparison CATCHES the mutant.
#                  THE CALLER MUST HOLD THE HOST SEMAPHORE'S EXCLUSIVE HARD
#                  HOLD through sibling Creme's `python3 -m creme semaphore`.
#                  If that capability is UNAVAILABLE or refuses the hold, the
#                  campaign must not run; see
#                  `~/creme/docs/guides/execution.md`.
#
# CLI contract: exit 0 if and only if the gate passes; output ends with one
# unambiguous verdict line (OK — ... / REGRESSION — ...).

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

PY="python3"
if ! command -v "$PY" >/dev/null 2>&1; then
  echo "REGRESSION — beacon-deposit model: python3 not found on PATH" >&2
  exit 2
fi

exec "$PY" "$SCRIPT_DIR/check-beacon-deposit-model.py" "$@"
