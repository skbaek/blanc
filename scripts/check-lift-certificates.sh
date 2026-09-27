#!/usr/bin/env bash
# Regeneration gate for lifted deployed-bytecode certificates.
#
# WHY
#
# Every `Blanc/Lift/**/Cert.lean` (and each registered generated `Check.lean`)
# is generated data.  The only registered generator is `scripts/lift/lift.py`;
# its inputs are the committed runtimes under `scripts/lift/inputs/`, each
# pinned by file and runtime SHA-256 in `scripts/lift/certificates.json`.  This
# gate regenerates every registered certificate from those inputs and requires
# the committed Lean files to be byte-identical, so a hand edit, a stale
# regeneration or an unregistered producer change fails here.
#
# On each run the producer also checks its supported-opcode table against the
# arms of `ninstTransfer`/`liftRegularTransfer` (`Blanc/Lift/Transfer.lean`)
# and `regularTransfer` (`Blanc/AbstractStackTransfer.lean`), stack shapes
# included, so an opcode without a lifted transfer cannot be emitted.
#
# The producer is untrusted and this gate proves nothing about the
# certificates: acceptance is each Lean `cert_check`, built by `lake build`.
#
# This wrapper owns only the catalogue verdict line; the producer's registry
# mode owns the comparison.

set -euo pipefail

cd "$(dirname "$0")/.."

summary="$(python3 -B scripts/lift/lift.py --registry scripts/lift/certificates.json --verify)" || {
  printf '%s\n' "$summary" >&2
  printf 'REGRESSION — lift-certificates: the producer refused (opcode table or input) or a registered certificate does not regenerate byte-identically\n' >&2
  exit 1
}

last="$(printf '%s\n' "$summary" | tail -n 1)"
case "$last" in
  "check-lift-certificates: PASS ("*) ;;
  *)
    printf '%s\n' "$summary" >&2
    printf 'REGRESSION — lift-certificates: producer did not report its summary\n' >&2
    exit 1
    ;;
esac

printf '%s\n' "$summary" | sed '$d'
printf 'OK — lift-certificates: %s\n' "${last#check-lift-certificates: PASS }"
