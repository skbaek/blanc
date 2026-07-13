#!/usr/bin/env bash
# Blanc verification gate (REFACTOR.md Phase 0, step 0.3): `lake build`,
# then an axiom audit of the four top solvency theorems via
# scripts/AxiomCheck.lean — failing on sorryAx / ofReduceBool / ofReduceNat.
#
# Usage: scripts/check.sh [--no-build]
#
# CLI contract: exit 0 if and only if the gate passes; output ends with one
# verdict line per top theorem (listing the axioms found) plus a single
# unambiguous summary line.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"

BUILD=1
while [ $# -gt 0 ]; do
  case "$1" in
    --no-build) BUILD=0 ;;
    *) echo "usage: scripts/check.sh [--no-build]" >&2; exit 2 ;;
  esac
  shift
done

if [ "$BUILD" -eq 1 ]; then
  if ! (cd "$ROOT" && lake build); then
    echo "REGRESSION — axiom audit: lake build failed"
    exit 1
  fi
fi

if ! OUT="$(cd "$ROOT" && lake env lean scripts/AxiomCheck.lean 2>&1)"; then
  printf '%s\n' "$OUT"
  echo "REGRESSION — axiom audit: AxiomCheck.lean failed to elaborate"
  exit 1
fi

THEOREMS="weth_inv_solvent stateTransition_inv_solvent chain_inv_solvent addBlockToChain_inv_solvent"
FORBIDDEN='sorryAx|ofReduceBool|ofReduceNat'
NTOTAL=0
NCLEAN=0

for THM in $THEOREMS; do
  NTOTAL=$((NTOTAL + 1))
  AXIOMS="$(printf '%s\n' "$OUT" | awk -v marker="'$THM' depends on axioms:" '
    index($0, marker) == 1 {
      found = 1
      axioms = substr($0, length(marker) + 2)
      if ($0 ~ /]$/) { print axioms; exit }
      next
    }
    found {
      sub(/^[[:space:]]+/, "")
      axioms = axioms " " $0
      if ($0 ~ /]$/) { print axioms; exit }
    }
  ')"
  if [ -z "$AXIOMS" ]; then
    echo "FAIL — $THM: no axiom report found in Lean output"
    continue
  fi
  if printf '%s\n' "$AXIOMS" | grep -qE "$FORBIDDEN"; then
    echo "FAIL — $THM: forbidden axiom present: $AXIOMS"
  else
    echo "OK — $THM: $AXIOMS"
    NCLEAN=$((NCLEAN + 1))
  fi
done

# Belt and braces: AxiomCheck.lean prints nothing but the four axiom sets,
# so a forbidden name anywhere in the output is a failure even if the
# per-line parse above missed it (e.g. an unexpectedly wrapped message).
if printf '%s\n' "$OUT" | grep -qE "$FORBIDDEN"; then
  echo "REGRESSION — axiom audit: forbidden axiom in Lean output ($NCLEAN/$NTOTAL theorems parsed clean)"
  exit 1
fi

if [ "$NCLEAN" -ne "$NTOTAL" ]; then
  echo "REGRESSION — axiom audit: only $NCLEAN/$NTOTAL top theorems clean"
  exit 1
fi
echo "OK — axiom audit: $NCLEAN/$NTOTAL top theorems clean (no sorryAx/ofReduceBool/ofReduceNat)"
exit 0
