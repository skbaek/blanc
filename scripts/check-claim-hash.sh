#!/usr/bin/env bash
# Closure hash for the ClaimCheck pins.
#
# scripts/check-claims.sh proves each pinned statement still elaborates against
# the current definitions; it cannot see a definition below the pinned layer
# move, because a pin is a definitional-equality check against whatever those
# definitions now say.  This gate content-hashes the full definitional closure
# of every pin, down to the pinned dependencies (lean-toolchain and the
# lake-manifest.json revs), in one run with an in-run memo, and compares the
# per-constant and per-pin digests with the committed manifest in
# scripts/claim-pin-hash/.  On a mismatch it names the constants whose own
# content moved and the pins they reach, and fails.  See the module docstrings
# of scripts/check-claim-hash.py and scripts/ClaimPinHash.lean for what each
# kind of constant contributes.
#
# It reads the built .olean artifacts and never builds: it first requires the
# exact build certificate (.lake/blanc-build-certificate-v3.json, written after
# an authoritative lake build by scripts/certify-checked-build.sh or the full
# set's lake build row) to match the current sources, and fails otherwise.
#
# USE
#   scripts/check-claim-hash.sh               regenerate and compare
#   scripts/check-claim-hash.sh --self-test   in-memory controls, no Lean
#   scripts/check-claim-hash.sh --generate DIR   write a fresh manifest to DIR
#                                                (adopting it is a user decision)

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"

if [[ "${1:-}" == "--self-test" ]]; then
  exec python3 "$SCRIPT_DIR/check-claim-hash.py" --self-test
fi

. "$SCRIPT_DIR/gate-semaphore.sh"
trap gate_semaphore_release EXIT

gate_semaphore_acquire "the pinned claim closure hash" || exit 2

(cd "$ROOT" && python3 scripts/check-claim-hash.py "$@")
