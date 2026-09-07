#!/usr/bin/env bash
# Rate-boundary control for every in-repo Keccak-256 implementation.
#
# WHY
#
# Blanc keeps one pure-Python Keccak-256 sponge per evidence surface on
# purpose, so that no shared helper can make two independent surfaces agree by
# sharing a defect.  Independence only pays if each copy is held to an oracle
# outside this repository, and the comparison has to straddle the sponge rate:
# a `pad10*1` that appends the two pad bits as separate bytes agrees with the
# standard at every message length except `len % 136 == 135`, where the domain
# byte fills the block exactly and the bits must merge into a single `0x81`.
# Eight of the nine implementations carried exactly that defect until
# 2026-09-07; every surface that pinned a digest agreed with itself and with
# the wrong answer.  Reverting only the repair reddens this control with
# 8 x {135, 271, 407, 543} failures, so it is shown to bite.
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
