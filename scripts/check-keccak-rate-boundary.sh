#!/usr/bin/env bash
# Rate-boundary control for Blanc's Keccak sponges and shared-helper adapters.
#
# WHY
#
# Blanc has one canonical pure-Python helper for generators and primary
# checkers, alongside independent schema/oracle sponges that must not depend on
# it.  Every sponge is held to an oracle outside this repository, and the two
# migrated consumers are checked for their exact historical return shapes.
# The comparison has to straddle the sponge rate:
# a `pad10*1` that appends the two pad bits as separate bytes agrees with the
# standard at every message length except `len % 136 == 135`, where the domain
# byte fills the block exactly and the bits must merge into a single `0x81`.
# Eight of the nine former implementations carried exactly that defect until
# 2026-09-07; every surface that pinned a digest agreed with itself and with
# the wrong answer.  Reverting only the repair reddens this control with
# {135, 271, 407, 543} failures in each planted mutant, with adjacent
# lengths and selector digests green, so it is shown to bite.
#
# The driver also compares its declared enumeration against a static scan of
# `scripts/**/*.py`, so a surface that grows a tenth sponge, or loses one,
# fails here rather than silently escaping the control.
#
# This wrapper owns only the catalogue verdict line; the driver and the vectors
# own the comparison.

set -euo pipefail

cd "$(dirname "$0")/.."

summary="$(python3 scripts/test-keccak-rate-boundary.py)"

case "$summary" in
  "OK keccak rate-boundary control: "*) ;;
  *)
    printf 'REGRESSION — keccak-rate-boundary: driver did not report its summary\n' >&2
    printf '%s\n' "$summary" >&2
    exit 1
    ;;
esac

printf 'OK — keccak-rate-boundary: %s\n' "${summary#OK keccak rate-boundary control: }"
