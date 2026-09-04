#!/usr/bin/env bash
# Fork-symmetry containment for every consumer Blanc runs at two forks.
#
# Blanc credits each deployed reference twice: once under the preserved
# historical Prague rules and once under mainnet's current BPO2 rules.  Where
# the BPO2 lane executes fewer rows or credits fewer channels, the omission is
# an assertion that the behaviour did not change across a hard fork -- exactly
# the kind of claim an evidence lane exists to test.  This gate makes every
# such omission carry a registered exception with a real basis, and rejects an
# exception that has outlived the asymmetry it was written for.
#
# It is static.  No Lean build, no t8n, no external checkout, no network.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"

SELF_TEST=0
while [ "$#" -gt 0 ]; do
  case "$1" in
    --self-test) SELF_TEST=1 ;;
    *)
      echo "usage: scripts/check-current-mainnet-parity.sh [--self-test]" >&2
      exit 2
      ;;
  esac
  shift
done

# An independently written third copy of the contract.  The register holds the
# first, the checker holds the second; a weakening in one file alone fails.
WRAPPER_CONSUMERS="weth10,beacon-deposit,lido-ossifiable-proxy"
WRAPPER_EXCEPTION_KINDS="missing-row,missing-channel"
WRAPPER_BASIS_KINDS="measurement,expressibility"

ARGS=(
  --wrapper-consumers "$WRAPPER_CONSUMERS"
  --wrapper-exception-kinds "$WRAPPER_EXCEPTION_KINDS"
  --wrapper-basis-kinds "$WRAPPER_BASIS_KINDS"
)
if [ "$SELF_TEST" -eq 1 ]; then
  ARGS+=(--self-test)
fi

cd "$ROOT"
exec /usr/bin/env -i \
  "HOME=${HOME:?HOME is required}" \
  "PATH=/usr/bin:/bin:/usr/sbin:/sbin" \
  "PYTHONNOUSERSITE=1" \
  ${TMPDIR:+"TMPDIR=$TMPDIR"} \
  /usr/bin/python3 -B "$SCRIPT_DIR/check_current_mainnet_parity.py" "${ARGS[@]}"
