#!/usr/bin/env bash
# Blanc verification gate (REFACTOR.md Phase 0, step 0.3): `lake build`,
# then an axiom audit of the nine audited top theorems via
# scripts/AxiomCheck.lean — WETH's seven solvency theorems plus the two
# compile witnesses.
#
# `wethCode_compile` is what keeps the solvency theorems' `Prog.compile weth`
# hypothesis from being vacuous. `fmintCode_compile` is the same equation for
# contract #2, audited from the moment the contract exists rather than from the
# moment something is proved about it: `Blanc/Conserved.lean`'s statements all
# carry the corresponding hypothesis, and they are statements — fmint's
# conservation invariant is unproven, pending Arc B of
# `~/plans/flashmint-proposal.md`. Auditing the witness early is what makes the
# eventual proofs land against a pinned, non-vacuous equation.
#
# Each row carries its OWN pinned expected axiom set (see ROWS below), and a
# theorem's axiom closure must equal its row's set exactly, order-insensitive.
# Any extra axiom fails — sorryAx, ofReduceBool/ofReduceNat, and also
# bv_decide's per-declaration `<decl>._native.bv_decide.ax_*` axioms, which add
# the Lean compiler to the trusted code base — and so does any missing axiom.
# A row is pinned to the set its proof honestly achieves; the pin moves only
# when the proof does, and never in order to make a red gate green.
#
# Usage: scripts/check.sh [--no-build]
#
# CLI contract: exit 0 if and only if the gate passes; output ends with one
# verdict line per audited theorem (listing the axioms found) plus a single
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

# Audited rows: `<fully qualified theorem>|<expected axioms, comma separated>`.
# An empty expectation (nothing after the `|`) means the theorem must depend on
# NO axioms at all; that row then passes on Lean's "does not depend on any
# axioms" report and fails on any axiom whatsoever.
STANDARD="propext, Classical.choice, Quot.sound"
ROWS="\
Blanc.weth_preserves_solvent|$STANDARD
Blanc.stateTransition_preserves_solvent|$STANDARD
Blanc.chain_preserves_solvent|$STANDARD
Blanc.addBlockToChain_preserves_solvent|$STANDARD
Blanc.stateTransitionUsing_preserves_solvent|$STANDARD
Blanc.chainUsing_preserves_solvent|$STANDARD
Blanc.addBlockToChainUsing_preserves_solvent|$STANDARD
Blanc.wethCode_compile|$STANDARD
Blanc.fmintCode_compile|$STANDARD"
# Secondary net only: the exact-set comparison below is the primary check;
# this pattern catches forbidden names in output the per-theorem parse missed.
FORBIDDEN='sorryAx|ofReduceBool|ofReduceNat|_native\.'
NTOTAL=0
NEXACT=0

while IFS= read -r ROW; do
  [ -n "$ROW" ] || continue
  THM="${ROW%%|*}"
  EXPECTED_DISPLAY="${ROW#*|}"
  EXPECTED_SORTED="$(printf '%s\n' "$EXPECTED_DISPLAY" | tr ',' '\n' \
    | sed 's/^[[:space:]]*//; s/[[:space:]]*$//' | grep -v '^$' | LC_ALL=C sort)"
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
      if [ -z "$EXPECTED_SORTED" ]; then
        echo "OK — $THM: depends on no axioms"
        NEXACT=$((NEXACT + 1))
      else
        echo "FAIL — $THM: depends on no axioms; expected exactly [$EXPECTED_DISPLAY]"
      fi
    else
      echo "FAIL — $THM: no axiom report found in Lean output"
    fi
    continue
  fi
  if [ -z "$EXPECTED_SORTED" ]; then
    echo "FAIL — $THM: axioms $AXIOMS; expected no axioms at all"
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
done <<< "$ROWS"

# Belt and braces: AxiomCheck.lean prints nothing but the audited axiom sets,
# so a forbidden name anywhere in the output is a failure even if the
# per-line parse above missed it (e.g. an unexpectedly wrapped message).
if printf '%s\n' "$OUT" | grep -qE "$FORBIDDEN"; then
  echo "REGRESSION — axiom audit: forbidden axiom in Lean output ($NEXACT/$NTOTAL theorems exact)"
  exit 1
fi

if [ "$NEXACT" -ne "$NTOTAL" ]; then
  echo "REGRESSION — axiom audit: only $NEXACT/$NTOTAL audited theorems have their exact pinned axiom set"
  exit 1
fi

# The audit's two halves must agree: every theorem AxiomCheck.lean prints must
# be pinned by a row here, and every pinned row must be printed there. Deleting
# a row from EITHER file is then a gate failure rather than a smaller green
# count — the point of auditing the compile witness at all.
PRINTED="$(grep -oE '^#print axioms[[:space:]]+[A-Za-z0-9_.]+' \
  "$SCRIPT_DIR/AxiomCheck.lean" | awk '{print $3}' | LC_ALL=C sort)"
PINNED="$(printf '%s\n' "$ROWS" | sed 's/|.*//' | grep -v '^$' | LC_ALL=C sort)"
if [ "$PRINTED" != "$PINNED" ]; then
  UNPINNED="$(LC_ALL=C comm -23 <(printf '%s\n' "$PRINTED") <(printf '%s\n' "$PINNED") | xargs)"
  UNPRINTED="$(LC_ALL=C comm -13 <(printf '%s\n' "$PRINTED") <(printf '%s\n' "$PINNED") | xargs)"
  LINE="REGRESSION — axiom audit: scripts/AxiomCheck.lean and scripts/check.sh disagree on the audited set"
  [ -n "$UNPINNED" ] && LINE="$LINE; printed but not pinned: $UNPINNED"
  [ -n "$UNPRINTED" ] && LINE="$LINE; pinned but not printed: $UNPRINTED"
  echo "$LINE"
  exit 1
fi

echo "OK — axiom audit: $NEXACT/$NTOTAL audited theorems depend on exactly their pinned axiom sets"
exit 0
