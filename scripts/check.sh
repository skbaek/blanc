#!/usr/bin/env bash
# Blanc verification gate (REFACTOR.md Phase 0, step 0.3): `lake build`,
# then an axiom audit of the four top solvency theorems via
# scripts/AxiomCheck.lean — each theorem's axiom closure must equal exactly
# [propext, Classical.choice, Quot.sound], order-insensitive. Any extra
# axiom fails — sorryAx, ofReduceBool/ofReduceNat, and also bv_decide's
# per-declaration `<decl>._native.bv_decide.ax_*` axioms, which add the
# Lean compiler to the trusted code base — and so does any missing axiom.
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

THEOREMS="Blanc.weth_preserves_solvent Blanc.stateTransition_preserves_solvent Blanc.chain_preserves_solvent Blanc.addBlockToChain_preserves_solvent"
EXPECTED_DISPLAY="propext, Classical.choice, Quot.sound"
EXPECTED_SORTED="$(printf '%s\n' propext Classical.choice Quot.sound | LC_ALL=C sort)"
# Secondary net only: the exact-set comparison below is the primary check;
# this pattern catches forbidden names in output the per-theorem parse missed.
FORBIDDEN='sorryAx|ofReduceBool|ofReduceNat|_native\.'
NTOTAL=0
NEXACT=0

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
    if printf '%s\n' "$OUT" | grep -qF "'$THM' does not depend on any axioms"; then
      echo "FAIL — $THM: depends on no axioms; expected exactly [$EXPECTED_DISPLAY]"
    else
      echo "FAIL — $THM: no axiom report found in Lean output"
    fi
    continue
  fi
  ACTUAL_SORTED="$(printf '%s\n' "$AXIOMS" | tr -d '[]' | tr ',' '\n' \
    | sed 's/^[[:space:]]*//; s/[[:space:]]*$//' | grep -v '^$' | LC_ALL=C sort)"
  if [ "$ACTUAL_SORTED" = "$EXPECTED_SORTED" ]; then
    echo "OK — $THM: $AXIOMS"
    NEXACT=$((NEXACT + 1))
  else
    EXTRA="$(LC_ALL=C comm -23 <(printf '%s\n' "$ACTUAL_SORTED") <(printf '%s\n' "$EXPECTED_SORTED") | xargs)"
    MISSING="$(LC_ALL=C comm -13 <(printf '%s\n' "$ACTUAL_SORTED") <(printf '%s\n' "$EXPECTED_SORTED") | xargs)"
    LINE="FAIL — $THM: axioms $AXIOMS differ from expected [$EXPECTED_DISPLAY]"
    [ -n "$EXTRA" ] && LINE="$LINE; extra: $EXTRA"
    [ -n "$MISSING" ] && LINE="$LINE; missing: $MISSING"
    echo "$LINE"
  fi
done

# Belt and braces: AxiomCheck.lean prints nothing but the four axiom sets,
# so a forbidden name anywhere in the output is a failure even if the
# per-line parse above missed it (e.g. an unexpectedly wrapped message).
if printf '%s\n' "$OUT" | grep -qE "$FORBIDDEN"; then
  echo "REGRESSION — axiom audit: forbidden axiom in Lean output ($NEXACT/$NTOTAL theorems exact)"
  exit 1
fi

if [ "$NEXACT" -ne "$NTOTAL" ]; then
  echo "REGRESSION — axiom audit: only $NEXACT/$NTOTAL top theorems have the exact expected axiom set"
  exit 1
fi
echo "OK — axiom audit: $NEXACT/$NTOTAL top theorems depend on exactly [$EXPECTED_DISPLAY]"
exit 0
