#!/usr/bin/env bash
# Blanc verification gate (REFACTOR.md Phase 0, step 0.3): `lake build`,
# then an axiom audit of the thirty-nine audited top theorems via
# scripts/AxiomCheck.lean — WETH's seven solvency theorems, fmint's seven
# conservation theorems, fmint's `flashLoan` success spec and its seven
# no-success corollaries, the two compile witnesses, the eleven frame-level
# restoration rows below, the two `RunCompiled`/`exec` bridge rows, and the two
# `totalSupply()` liveness rows.
#
# `wethCode_compile` is what keeps the solvency theorems' `Prog.compile weth`
# hypothesis from being vacuous. `fmintCode_compile` is the same equation for
# contract #2: it was audited from the moment the contract existed rather than
# from the moment something was proved about it, and the conservation theorems
# added by Arc B of `~/plans/flashmint-proposal.md` now land against that
# pinned, non-vacuous equation. Note what the fmint rows do and do not say:
# they are *conservation* — the equality `totalSupply = Σ balances` at every
# observable point — not solvency and not liveness.
#
# The eight `flashLoan` rows added by Arc C are **partial correctness, not
# liveness**: `fmint_flashLoan_spec` factors a successful top-level `Exec` that
# is given as a hypothesis, and the seven `no_success_of_*` rows rule executions
# out. Nothing in them says a `flashLoan` call ever succeeds. They are also
# restricted to canonically encoded calldata and premised on frame freshness —
# `Blanc/FlashSpec.lean`'s headline docstring is the authority on their scope —
# and none of them is a state-restoration claim.
#
# The last eleven rows are the **restoration** family of
# `~/plans/fmint-restoration.md`. Three properties bind all of them and are the
# only safe way to read any one:
#
#   * each names a FRAME, never a transaction. A failed inner call can be caught
#     by its caller while the surrounding transaction succeeds, so "the
#     transaction was rolled back" is a different claim and is frequently false;
#   * none names an error kind. The conclusion is `error.isSome`, never *which*
#     error — the relational layer is `.ok`-level only, and fmint's failure
#     shapes are compiled-byte artefacts a restoration claim must not depend on;
#   * none is a liveness claim. Every premise is in hypothesis position, so
#     nothing here says any frame ever fails, any callback ever reverts, or any
#     `flashLoan` call is ever made. Like every row above, partial correctness.
#
# `ProcessMessage.rollback_of_error` (Step 1) is the generic mechanism, and is
# contract-agnostic and shared-layer: a message frame that settles `.ok` with
# its error flag set has had its state and transient storage rolled back to what
# that message entered with. The frame is `msg`'s own.
#
# `Fmint.rollback_of_callback_failure` (Step 2) instantiates that at fmint's
# callback site: when the `CALL` at `flashLoanFromCall` pushes the failure flag,
# the world fmint resumes with is the world it entered the `CALL` with, so the
# borrower's `onFlashLoan` frame wrote nothing that survives. Read its frame
# carefully. The writes rolled back are the **child** frame's, and the equation
# holds at the resumption point only: at that point the flash mint is still in
# place — it is undone later by fmint's own revert, which is a different frame.
#
# `Fmint.rollback_of_no_success` (Step 3) is the family's core and the arc's
# headline, stated once over an abstract "no successful `Exec` starts here"
# premise: such a frame settles with its error flag set and hands back the state
# and transient storage the message entered with. `..._total` is the same
# statement off `processMessage msg = .ok out`. Two premises are deliberate and
# are argued in the source: `Xlot.Filled`, without which the raw result is
# unconstrained and the clean-success branch cannot be refuted; and an explicit
# exclusion of the precompile entry mode, where there is no `Exec` to contradict
# and the conclusion is genuinely false.
#
# The remaining seven rows instantiate the core at each `no_success_of_*`
# corollary, at fmint's own message frame. They inherit those corollaries'
# restrictions unchanged: canonically encoded calldata throughout
# (`FMINT_DEVIATIONS.md` row 21), the encoded-callback size bound and frame
# freshness where the corollary needs them (the `token`, `receiver` and `amount`
# rows need neither), and the boundary-quantified reading of every callback
# premise — over EVERY boundary the call could open, never "if the receiver's
# code returns X". `Blanc/FlashSpec.lean`'s section banner is the authority.
#
# The two `Prog.*` rows are `Blanc/Compiled.lean`'s bridge between the gas-exact
# relation `Prog.RunCompiled` and Jaune's `exec`. They were built by
# `~/plans/liveness-prelude.md` and audited here by `~/plans/forward-witness.md`
# Step 1, which closed the hole: everything that arc builds rests on them, so
# they are pinned before anything is stacked on top. Read them exactly as
# `Prog.runCompiled_iff_exec`'s own docstring states them — they convert run
# witnesses into executions and back, and by themselves produce a witness for
# no contract at all. They are NOT liveness, they are message-frame level and
# not transaction level, and they are `.ok`-level only.
#
# `Blanc.Prog.exec_of_runCompiledTo` is `Blanc/Reverts.lean`'s outcome-generalised
# sibling of the first of those two, added by `~/plans/error-genre.md` Step 2. It
# is the ONE thing in the row above's list that it lifts: the relation it bridges
# from, `Prog.RunCompiledTo`, ends at an arbitrary `Execution` rather than at
# `.ok`, so instantiating its conclusion at `.error (e, post)` states "this call
# settles with THIS error" — the direction the `.ok`-only note above says the
# older pair cannot reach. Every other restriction on those two carries over
# verbatim and is not weakened by the generalisation: it is still NOT liveness
# (a walk crossing an external call still carries the callee's derivation as an
# `Xlot.Filled` premise), still message-frame and not transaction level, still
# the construction direction only with no converse and no `pcFree`, and still
# says nothing about EXHAUSTIVENESS — a witness shows these conditions reach
# this outcome and never that only these conditions do. `Blanc/Reverts.lean`'s
# own docstrings are the authority. The `Func`-level core is not a row, for the
# same reason `Func.exec_of_runCompiled_core` is not one: it is the induction
# the `Prog` row is built from, not a headline.
#
# The last four rows are the only ones in this file that assert a contract call
# **succeeds**. Every row above them takes a successful execution as a
# hypothesis and factors it; `Blanc.Fmint.totalSupply_runCompiled` and
# `Blanc.weth_balanceOf_runCompiled` construct a gas-exact run from a
# precondition on the frame alone, and `Blanc.Fmint.fmint_totalSupply_succeeds`
# and `Blanc.weth_balanceOf_succeeds` compose those through
# `Prog.exec_of_runCompiled` into a successful `exec`. Read their scope off
# `Blanc/FmintLive.lean`'s and `Blanc/WethLive.lean`'s docstrings, which are the
# authority: one call-free entrypoint of one contract each, at message-call
# altitude and not transaction level, for one fixed selector, with an exact gas
# figure rather than a bound. No entrypoint of either contract that makes an
# external call can have a row of this shape at all — its witness would contain
# the callee's execution as a premise. The WETH pair carries one caveat of its
# own: `balanceOf` uses its argument word as a storage key without validating
# it as an address, so the statement is quantified over that word and asserts
# nothing about what a non-address key means.
#
# `Blanc.Fmint.unknownSelector_runCompiledTo` and
# `Blanc.Fmint.fmint_unknown_selector_reverts` are the same pair one genre over,
# added by `~/plans/error-genre.md` Step 3: the first constructs a gas-exact
# walk, the second composes it through `Prog.exec_of_runCompiledTo` — and both
# land on `.error (.revert, post)` with `Devm.output post = []` rather than on a
# success. They are the first rows in this file asserting that a call **reverts**
# — not that it fails to succeed (the `no_success_of_*` rows), and not that it
# settles with some unnamed error (the `settles_with_error_of_*` rows), but that
# the frame settles with `EvmError.revert` carrying no revert data.
#
# They do NOT subsume the seven `no_success_of_*` rows and are not subsumed by
# them, and no report may say otherwise: those hold with no gas premise, because
# "does not succeed" is not a claim that the frame reaches anything, while
# "reverts" is and therefore needs gas for the whole path. Their other
# restrictions are `Blanc/FmintReverts.lean`'s own docstrings' to state, and
# three bind every row of this shape: they are NOT exhaustiveness (this
# condition reverts, never only this condition reverts), they are message-call
# altitude with an exact frame gas figure and not a transaction, and each fixes
# ONE selector — the dispatch walk decides each fork by evaluating a concrete
# comparison, so nothing here is quantified over selectors.
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
Blanc.fmint_preserves_conserved|$STANDARD
Blanc.stateTransition_preserves_conserved|$STANDARD
Blanc.chain_preserves_conserved|$STANDARD
Blanc.addBlockToChain_preserves_conserved|$STANDARD
Blanc.stateTransitionUsing_preserves_conserved|$STANDARD
Blanc.chainUsing_preserves_conserved|$STANDARD
Blanc.addBlockToChainUsing_preserves_conserved|$STANDARD
Blanc.Fmint.fmint_flashLoan_spec|$STANDARD
Blanc.Fmint.no_success_of_callback_never_magic|$STANDARD
Blanc.Fmint.no_success_of_callback_never_returns_word|$STANDARD
Blanc.Fmint.no_success_of_token_ne_self|$STANDARD
Blanc.Fmint.no_success_of_receiver_not_address|$STANDARD
Blanc.Fmint.no_success_of_amount_over_maxFlashLoan|$STANDARD
Blanc.Fmint.no_success_of_allowance_below_amount|$STANDARD
Blanc.Fmint.no_success_of_balance_below_amount|$STANDARD
Blanc.Fmint.settles_with_error_of_callback_never_magic|$STANDARD
Blanc.Fmint.settles_with_error_of_callback_never_returns_word|$STANDARD
Blanc.Fmint.settles_with_error_of_token_ne_self|$STANDARD
Blanc.Fmint.settles_with_error_of_receiver_not_address|$STANDARD
Blanc.Fmint.settles_with_error_of_amount_over_maxFlashLoan|$STANDARD
Blanc.Fmint.settles_with_error_of_allowance_below_amount|$STANDARD
Blanc.Fmint.settles_with_error_of_balance_below_amount|$STANDARD
Blanc.wethCode_compile|$STANDARD
Blanc.fmintCode_compile|$STANDARD
Blanc.ProcessMessage.rollback_of_error|$STANDARD
Blanc.Fmint.rollback_of_callback_failure|$STANDARD
Blanc.Fmint.rollback_of_no_success|$STANDARD
Blanc.Fmint.rollback_of_no_success_total|$STANDARD
Blanc.Fmint.rollback_of_callback_never_magic|$STANDARD
Blanc.Fmint.rollback_of_callback_never_returns_word|$STANDARD
Blanc.Fmint.rollback_of_token_ne_self|$STANDARD
Blanc.Fmint.rollback_of_receiver_not_address|$STANDARD
Blanc.Fmint.rollback_of_amount_over_maxFlashLoan|$STANDARD
Blanc.Fmint.rollback_of_allowance_below_amount|$STANDARD
Blanc.Fmint.rollback_of_balance_below_amount|$STANDARD
Blanc.Prog.exec_of_runCompiled|$STANDARD
Blanc.Prog.runCompiled_iff_exec|$STANDARD
Blanc.Prog.exec_of_runCompiledTo|$STANDARD
Blanc.Fmint.totalSupply_runCompiled|$STANDARD
Blanc.Fmint.fmint_totalSupply_succeeds|$STANDARD
Blanc.weth_balanceOf_runCompiled|$STANDARD
Blanc.weth_balanceOf_succeeds|$STANDARD
Blanc.weth_balanceOf_gas_exact|$STANDARD
Blanc.weth_balanceOf_gas_of_runCompiled|$STANDARD
Blanc.Fmint.totalSupply_gas_exact|$STANDARD
Blanc.Fmint.totalSupply_gas_of_runCompiled|$STANDARD
Blanc.weth_decimals_runCompiled|$STANDARD
Blanc.weth_decimals_gas_exact|$STANDARD
Blanc.weth_decimals_succeeds|$STANDARD
Blanc.weth_decimals_gas_of_runCompiled|$STANDARD
Blanc.wethGas_eq_with|$STANDARD
Blanc.weth_balanceOf_gas_exact_wethGas|$STANDARD
Blanc.weth_decimals_gas_exact_wethGas|$STANDARD
Blanc.Fmint.decimals_runCompiled|$STANDARD
Blanc.Fmint.decimals_gas_exact|$STANDARD
Blanc.Fmint.fmint_decimals_succeeds|$STANDARD
Blanc.Fmint.decimals_gas_of_runCompiled|$STANDARD
Blanc.Fmint.fmintGas_eq_with|$STANDARD
Blanc.Fmint.totalSupply_gas_exact_fmintGas|$STANDARD
Blanc.Fmint.decimals_gas_exact_fmintGas|$STANDARD
Blanc.weth_balanceOf_gas_of_runCompiled_wethGas|$STANDARD
Blanc.weth_decimals_gas_of_runCompiled_wethGas|$STANDARD
Blanc.Fmint.totalSupply_gas_of_runCompiled_fmintGas|$STANDARD
Blanc.Fmint.decimals_gas_of_runCompiled_fmintGas|$STANDARD
Blanc.weth_balanceOf_warm_runCompiled|$STANDARD
Blanc.weth_balanceOf_warm_gas_exact|$STANDARD
Blanc.wethGasMax_eq_with|$STANDARD
Blanc.wethGas_le_max|$STANDARD
Blanc.Fmint.totalSupply_warm_runCompiled|$STANDARD
Blanc.Fmint.totalSupply_warm_gas_exact|$STANDARD
Blanc.Fmint.fmintGasMax_eq_with|$STANDARD
Blanc.Fmint.fmintGas_le_max|$STANDARD
Blanc.Fmint.unknownSelector_runCompiledTo|$STANDARD
Blanc.Fmint.fmint_unknown_selector_reverts|$STANDARD"
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
