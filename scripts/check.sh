#!/usr/bin/env bash
# Blanc verification gate (REFACTOR.md Phase 0, step 0.3): `lake build`,
# then an axiom audit of the audited top theorems via scripts/AxiomCheck.lean.
# The row list below is the authority on what is audited, grouped by family:
# WETH solvency, fmint conservation, the `flashLoan` spec and its
# corollaries, the compile witnesses, frame-level restoration, the
# `RunCompiled`/`exec` bridges, view-call liveness and gas, error genre, and
# settlement.
#
# `wethCode_compile` is what keeps the solvency theorems' `Prog.compile weth`
# hypothesis from being vacuous. `fmintCode_compile` is the same equation for
# contract #2: it was audited from the moment the contract existed rather than
# from the moment something was proved about it, and the conservation theorems
# added by Arc B of `~/plans/flashmint-proposal.md` now land against that
# pinned, non-vacuous equation. Note what the fmint rows do and do not say:
# they are *conservation* — the equality `totalSupply = Σ balances` at every
# observable point — not solvency and not liveness.
# `Weth10.weth10_compiles` kernel-checks compiler success for every deployment
# parameter pair, and `Weth10.weth10Code_compile` turns that decision into the
# universal equation `Prog.compile (weth10 dp) = some (weth10Code dp)`. Together
# they connect every concrete differential and deployment world to its named
# member of the runtime-byte family; neither declaration says those bytes run
# successfully or satisfy a functional contract property.
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
# `rollback_of_no_success` (Step 3) is the family's shared-layer core and the
# arc's headline, stated once over an abstract "no successful `Exec` starts
# here" premise: such a frame settles with its error flag set and hands back the
# state and transient storage the message entered with. `..._total` is the same
# statement off `processMessage msg = .ok out`. The two `Fmint.*` rows preserve
# the original API with statement-identical wrappers. Two premises are
# deliberate and are argued in the source: `Xlot.Filled`, without which the raw
# result is unconstrained and the clean-success branch cannot be refuted; and an
# explicit exclusion of the precompile entry mode, where there is no `Exec` to
# contradict and the conclusion is genuinely false.
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
# The checkpoint-relative row numbers and words such as "last" or "final" in
# the historical notes below describe the arc tip at which each family landed;
# they are not claims about the current tail of this now-larger audit. The
# authoritative current membership and count are the EXPECTED rows themselves.
#
# At that checkpoint, the next four rows were the only ones in this file that
# assert a contract call
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
# The following four rows were two more pairs of that same shape, one genre over,
# added by `~/plans/error-genre.md` Step 3: `..._runCompiledTo` constructs a
# gas-exact walk and `fmint_*_reverts` composes it through
# `Prog.exec_of_runCompiledTo` — but both land on `.error (.revert, post)` with
# `Devm.output post = []` rather than on a success. They are the first rows in
# this file asserting that a call **reverts** — not that it fails to succeed
# (the `no_success_of_*` rows), and not that it settles with some unnamed error
# (the `settles_with_error_of_*` rows), but that the frame settles with
# `EvmError.revert` carrying no revert data. One is an unrecognised selector,
# reaching `Func.rev` through the dispatcher's fallback slot; the other is
# `flashLoan`'s `token ≠ self` guard, and is the direct counterpart of
# `Blanc.Fmint.no_success_of_token_ne_self` above.
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
# The next two rows, added by `~/plans/error-genre.md` Step 4, lift that pair
# one altitude: from the code frame's `exec` to the frame `processMessage` opens
# for a `Msg`. `Blanc.rollback_revert_of_exec_revert` is the mechanism,
# contract-agnostic and stated once — a frame whose code reverts settles with
# `error = some .revert`, hands back the code's own output, and has had its state
# and transient storage rolled back to what the message entered with.
# `Blanc.rollback_revert_of_runCompiledTo` fuses that mechanism with a
# gas-exact compiled walk and carries the walk's exact output bytes directly to
# the message result; it remains one-frame, message-call-altitude machinery.
# `Blanc.Fmint.rollback_revert_of_token_ne_self` instantiates it at fmint's
# `token ≠ self` guard, so the frame's error kind is named and the returned data
# is `[]`.
#
# These are NEW rows beside `Blanc.Fmint.rollback_of_token_ne_self`, not
# strengthenings of it, and neither theorem subsumes the other: the older row
# holds with NO gas premise, and the newer one cannot be stated without one, for
# the reason given two paragraphs up. Both rows stand and neither was edited.
# Every restriction on the older row carries over verbatim — the frame is `msg`'s
# own and NEVER the transaction, `Xlot.Filled` and the precompile-mode exclusion
# are still premises and still argued in the source, canonical calldata encoding
# still binds (`FMINT_DEVIATIONS.md` row 21) — and so does the non-exhaustiveness
# note: this condition reverts the frame, never only this condition does.
#
# The 86th row, added by `~/plans/adversarial-progress.md` Step 3, is the
# arc's pinned headline: `Blanc.Fmint.fmint_flashLoan_settles`, the guarded
# trichotomy at `exec` altitude — under fmint's own entry conditions (frame
# gas at the closed bound `flashLoanGas`, a non-static caller frame, canonical
# calldata) every outcome of `flashLoan` is a success, a deliberate
# `EvmError.revert`, or an error in the non-consensus channel (`NonConsensus`:
# no `SettledHalt` can store it). There is NO premise about the borrower: its
# code, behaviour, gas use and settlement are quantified by the pre-state
# itself, the callee's derivation being discharged by totality
# (`Xlot.filled_exec`). Three restrictions bind: this is message-call
# altitude, one selector, and a *bound* (`flashLoanGas` is worst-case, never
# exact — no exact post-CALL cost exists across arbitrary borrowers); the
# trichotomy is construction, not exhaustiveness of revert causes; and
# nothing is claimed below `h_gas` — gas starvation of the *caller's own
# frame* is out of scope. The supporting walk lemmas (the `execSat_*` leaves
# and transports, the crossing `flashLoan_execSat_flag`) are internal
# machinery inside this row's closure and are deliberately not rows
# themselves.
#
# The 87th row, added by the same plan's Step 4, lifts that headline to
# fmint's own message frame: `Blanc.Fmint.fmint_flashLoan_frame_settles` says
# that a `processMessage` frame running `flashLoan` under those same entry
# conditions comes back with `out.error = none` or `out.error = some .revert`
# and nothing else — no stored exceptional halt, whatever bytecode answers the
# callback. The non-consensus arm is quarantined here by the shape of the
# standing `.ok out` premise (such an error never reaches a settlement at
# all), not assumed away; `h_static` is inherited as `msg.isStatic` and is a
# premise about fmint's CALLER, not the borrower. Every restriction on the
# 86th row carries over verbatim, and the frame-family restrictions of
# `rollback_revert_of_token_ne_self` carry over too: one frame and never a
# transaction, `Xlot.Filled` and the precompile-mode exclusion still premises,
# canonical calldata still binding, and no exhaustiveness claim anywhere.
#
# Rows 88-91, added by the same plan's Step 4, drop the headline's three guard
# premises. `Blanc.Fmint.receiverNotAddress_runCompiledTo` and
# `Blanc.Fmint.fmint_receiver_not_address_reverts` are guard (1)'s revert walk
# (a `receiver` word with bits above 160) in the two altitudes the error-genre
# arc's E-1/E-2 pair established; `Blanc.Fmint.fmint_amount_over_bound_reverts`
# is guard (2)'s (an `amount` above `2^256 - 1 - totalSupply`), stated at a
# *bound* rather than an exact figure because its `SLOAD` of `supplySlot` is
# warmth-open. Both are NEW rows beside `Blanc.Fmint.no_success_of_*`, not
# strengthenings of them: those hold with no gas premise and these cannot be
# stated without one, so neither side subsumes the other and every row stands.
# `Blanc.Fmint.fmint_flashLoan_settles_of_call` is the 86th row with
# `h_token`/`h_addr`/`h_nof` dropped -- a call failing any guard takes that
# guard's deliberate revert, which is already the trichotomy's second
# disjunct, so the conclusion is unchanged and the statement now holds of
# every `flashLoan` call at that gas. `h_static` stays, and stays a premise
# about fmint's CALLER. Nothing here is an exhaustiveness claim.
#
# Five WETH10 deployment rows pin the public semantic crossing: the exact
# zero-value constructor walk, successful execution of the actual appended-data
# initcode, nonzero-value empty rejection, direct creation-message settlement,
# and its static companion certificate.  The settlement row is deliberately at
# creation-message altitude; transaction/intrinsic-gas execution remains outside
# its statement and the separately named top-level figures remain accounting.
#
# The last twelve rows are the `weth10-redeem-future-v2` family. Read them with
# three restrictions in mind. `AccountedHistory.allowanceTransported_of_compiled`
# and `committedExecAllowanceSound` are the allowance-transport endpoints the
# attribution layer runs on; `hardenedOutflow_le_permanentOutflow` and
# `permanentOutflow_eq_hardenedOutflow_of_noCollision` are a bound and an
# equality, and only the equality takes `NoAllowanceKeyCollision` — a
# trace-local, decidable property of one explicit history's finitely many
# touched pairs, never a global injectivity assumption. The enabledness rows
# (`deployment_reachable_residual_*`, and the `messageEnabled`/
# `transactionEnabled` fields of `FutureRedemptionGuarantee` inside
# `deployment_reachable_future_redeemable`) take no collision hypothesis at all:
# redeemability never rests on an assumption about hash keys, only attribution
# does. The `redeemClaims_anyOrder` pair is message/state-level: it says each
# permutation of an admissible claim list has a successful redemption sequence,
# NOT that any of those messages was included in a block or mined.
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
Blanc.Weth10.weth10_compiles|$STANDARD
Blanc.Weth10.weth10Code_compile|$STANDARD
Blanc.Func.compile_eq_emitUnchecked|$STANDARD
Blanc.Table.compile_eq_emitUnchecked|$STANDARD
Blanc.Prog.compile_eq_emitUnchecked|$STANDARD
Blanc.Func.CompileShape.byteSize_compileShape|propext
Blanc.Func.length_emitByShape|propext
Blanc.Func.getD_emitByShape|propext
Blanc.Func.emitByShape_compileShape|propext
Blanc.Func.CompileShape.locations_compileShapes|propext
Blanc.Table.emitByShape_compileShapes|propext
Blanc.Prog.emitByShape_compileShape|propext
Blanc.Func.exec_of_runCompiled_subcode|$STANDARD
Blanc.Func.exec_of_runCompiled_prefix|$STANDARD
Blanc.Func.exec_of_runCompiledTo_subcode|$STANDARD
Blanc.Func.exec_of_runCompiledTo_prefix|$STANDARD
Blanc.Rinst.runCore_extcodesize_cold_eq_ok|$STANDARD
Blanc.Rinst.runCore_extcodesize_warm_eq_ok|$STANDARD
Blanc.Ninst.runCompiled_extcodesize_cold|$STANDARD
Blanc.Ninst.runCompiled_extcodesize_warm|$STANDARD
Blanc.Func.runCompiledTo_revReturnData|$STANDARD
Blanc.Frame.enter_eq_done_executePrecomp|$STANDARD
Blanc.Xinst.step_statcall|$STANDARD
Blanc.Xinst.step_statcall_spawn|$STANDARD
Blanc.Ninst.runCompiled_statcall_doneFrame|$STANDARD
Blanc.of_run_call_val_with_depth|$STANDARD
Blanc.of_run_statcall_val_with_depth_cause|$STANDARD
Blanc.of_run_statcall_val_with_depth|$STANDARD
Blanc.Weth10.flashFee_runCompiled|$STANDARD
Blanc.Weth10.balanceOf_cold_runCompiled|$STANDARD
Blanc.Weth10.balanceOf_warm_runCompiled|$STANDARD
Blanc.Weth10.totalSupply_cold_runCompiled|$STANDARD
Blanc.Weth10.totalSupply_warm_runCompiled|$STANDARD
Blanc.Weth10.maxFlashLoan_cold_runCompiled|$STANDARD
Blanc.Weth10.maxFlashLoan_warm_runCompiled|$STANDARD
Blanc.Weth10.maxFlashLoan_other_runCompiled|$STANDARD
Blanc.Weth10.name_exec_output|$STANDARD
Blanc.Weth10.symbol_exec_output|$STANDARD
Blanc.Weth10.callbackSuccess_exec_output|$STANDARD
Blanc.Weth10.permitTypehash_exec_output|$STANDARD
Blanc.Weth10.decimals_exec_output|$STANDARD
Blanc.Weth10.deploymentChainId_exec_output|$STANDARD
Blanc.Weth10.domainSeparator_output|$STANDARD
Blanc.Weth10.domainSeparator_exec_output|$STANDARD
Blanc.Weth10.balanceOf_exec_output|$STANDARD
Blanc.Weth10.allowance_exec_output|$STANDARD
Blanc.Weth10.nonces_exec_output|$STANDARD
Blanc.Weth10.flashMinted_exec_output|$STANDARD
Blanc.Weth10.totalSupply_exec_output|$STANDARD
Blanc.Weth10.maxFlashLoan_exec_output|$STANDARD
Blanc.Weth10.flashFee_exec_output|$STANDARD
Blanc.Weth10.approve_exec_effect|$STANDARD
Blanc.Weth10.depositTo_exec_effect|$STANDARD
Blanc.Weth10.deposit_exec_effect|$STANDARD
Blanc.Weth10.receive_exec_effect|$STANDARD
Blanc.Weth10.permit_exec_success_effect|$STANDARD
Blanc.Weth10.permit_exec_expired_no_success|$STANDARD
Blanc.Weth10.permit_exec_invalid_no_success|$STANDARD
Blanc.Weth10.of_flashLoanSuccessTail|$STANDARD
Blanc.Weth10.of_flashSettle_allowance|$STANDARD
Blanc.Weth10.flashBurn_effect|$STANDARD
Blanc.Weth10.flashLoan_successEffect|$STANDARD
Blanc.Weth10.weth10_flashLoan_successEffect|$STANDARD
Blanc.Weth10.weth10_transfer_successEffect|$STANDARD
Blanc.Weth10.weth10_withdraw_successEffect|$STANDARD
Blanc.Weth10.weth10_withdrawTo_successEffect|$STANDARD
Blanc.Weth10.weth10_transferFrom_successEffect|$STANDARD
Blanc.Weth10.weth10_withdrawFrom_successEffect|$STANDARD
Blanc.Weth10.of_spendCallerAllowanceThen_effect|$STANDARD
Blanc.Weth10.transfer_effect_failureOrder|$STANDARD
Blanc.Weth10.transferFrom_effect_failureOrder|$STANDARD
Blanc.Weth10.withdrawal_effect_failureOrder|$STANDARD
Blanc.Weth10.delegatedAllowance_effect_precedence|$STANDARD
Blanc.Weth10.transferThen_callbackPrefix_effect|$STANDARD
Blanc.Weth10.callBoolCallback_successEffect|$STANDARD
Blanc.Weth10.approveAndCall_successEffect|$STANDARD
Blanc.Weth10.weth10_approveAndCall_successEffect|$STANDARD
Blanc.Weth10.depositToAndCall_successEffect|$STANDARD
Blanc.Weth10.weth10_depositToAndCall_successEffect|$STANDARD
Blanc.Weth10.transferAndCall_successEffect|$STANDARD
Blanc.Weth10.weth10_transferAndCall_successEffect|$STANDARD
Blanc.Weth10.erc677_codelessCallback_runCompiledTo|$STANDARD
Blanc.Weth10.erc677_childRevert_runCompiledTo|$STANDARD
Blanc.Weth10.erc677_shortReturn_runCompiledTo|$STANDARD
Blanc.Weth10.lockedErrorGuard_runCompiledTo|$STANDARD
Blanc.Weth10.codelessCallback_runCompiledTo|$STANDARD
Blanc.Weth10.callbackBubble_runCompiledTo|$STANDARD
Blanc.Weth10.callbackShort_runCompiledTo|$STANDARD
Blanc.Weth10.flashCallback_wrongMagic_runCompiledTo|$STANDARD
Blanc.Weth10.nonpayable_runCompiledTo|$STANDARD
Blanc.Weth10.flashFee_wrongToken_runCompiledTo|$STANDARD
Blanc.Weth10.flashLoan_lockedGuardOrder|$STANDARD
Blanc.Weth10.permit_expiredBeforeNonceUpdate|$STANDARD
Blanc.Weth10.transfer_lockedGuardOrder|$STANDARD
Blanc.Weth10.transferFromCore_lockedGuardOrder|$STANDARD
Blanc.Weth10.withdraw_lockedGuardOrder|$STANDARD
Blanc.Weth10.spendCallerAllowanceThen_finitePrecedence|$STANDARD
Blanc.Weth10.flashSettle_finitePrecedence|$STANDARD
Blanc.Weth10.flashCallback_errorPrecedence|$STANDARD
Blanc.Weth10.rollback_revert_of_weth10_runCompiledTo|$STANDARD
Blanc.Weth10.rollback_empty_of_weth10_runCompiledTo|$STANDARD
Blanc.Weth10.rollback_errorData_of_weth10_runCompiledTo|$STANDARD
Blanc.Weth10.rollback_bubbledChild_of_weth10_runCompiledTo|$STANDARD
Blanc.ProcessMessage.rollback_of_error|$STANDARD
Blanc.Fmint.rollback_of_callback_failure|$STANDARD
Blanc.rollback_of_no_success|$STANDARD
Blanc.rollback_of_no_success_total|$STANDARD
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
Blanc.Fmint.fmint_unknown_selector_reverts|$STANDARD
Blanc.Fmint.tokenNeSelf_runCompiledTo|$STANDARD
Blanc.Fmint.fmint_token_ne_self_reverts|$STANDARD
Blanc.rollback_revert_of_exec_revert|$STANDARD
Blanc.rollback_revert_of_runCompiledTo|$STANDARD
Blanc.Fmint.rollback_revert_of_token_ne_self|$STANDARD
Blanc.Fmint.fmint_flashLoan_settles|$STANDARD
Blanc.Fmint.fmint_flashLoan_frame_settles|$STANDARD
Blanc.Fmint.receiverNotAddress_runCompiledTo|$STANDARD
Blanc.Fmint.fmint_receiver_not_address_reverts|$STANDARD
Blanc.Fmint.fmint_amount_over_bound_reverts|$STANDARD
Blanc.Fmint.fmint_flashLoan_settles_of_call|$STANDARD
Blanc.Stor.Weth10Inv.silent|$STANDARD
Blanc.Stor.Weth10Inv.deposit|$STANDARD
Blanc.Stor.Weth10Inv.transfer|$STANDARD
Blanc.Stor.Weth10Inv.flashMint|$STANDARD
Blanc.Stor.Weth10Inv.flashBurn|$STANDARD
Blanc.Stor.Weth10Inv.withdraw|$STANDARD
Blanc.Stor.Weth10Inv.of_empty|$STANDARD
Blanc.Weth10.backedSpec|$STANDARD
Blanc.ContractSpec.post_of_run_dispatch|$STANDARD
Blanc.ContractSpec.sound_of_receive_dispatch|$STANDARD
Blanc.ContractSpec.preserves_of_receive_dispatch|$STANDARD
Blanc.Weth10.mintCaller_storage|$STANDARD
Blanc.Weth10.backedSpec_receiveEther_funcSound|$STANDARD
Blanc.Weth10.backedSpec_deposit_funcSound|$STANDARD
Blanc.Weth10.backedSpec_name_funcSound|$STANDARD
Blanc.Weth10.backedSpec_totalSupply_funcSound|$STANDARD
Blanc.Weth10.backedSpec_permitTypehash_funcSound|$STANDARD
Blanc.Weth10.backedSpec_decimals_funcSound|$STANDARD
Blanc.Weth10.backedSpec_domainSeparator_funcSound|$STANDARD
Blanc.Weth10.backedSpec_maxFlashLoan_funcSound|$STANDARD
Blanc.Weth10.backedSpec_balanceOf_funcSound|$STANDARD
Blanc.Weth10.backedSpec_nonces_funcSound|$STANDARD
Blanc.Weth10.backedSpec_callbackSuccess_funcSound|$STANDARD
Blanc.Weth10.backedSpec_flashMinted_funcSound|$STANDARD
Blanc.Weth10.backedSpec_symbol_funcSound|$STANDARD
Blanc.Weth10.backedSpec_deploymentChainId_funcSound|$STANDARD
Blanc.Weth10.backedSpec_allowance_funcSound|$STANDARD
Blanc.Weth10.backedSpec_flashFee_funcSound|$STANDARD
Blanc.Weth10.backedSpec_approve_funcSound|$STANDARD
Blanc.Weth10.backedSpec_depositTo_funcSound|$STANDARD
Blanc.Weth10.backedSpec_withdraw_funcSound|$STANDARD
Blanc.Weth10.backedSpec_transfer_funcSound|$STANDARD
Blanc.Weth10.backedSpec_withdrawTo_funcSound|$STANDARD
Blanc.Weth10.backedSpec_transferFrom_funcSound|$STANDARD
Blanc.Weth10.backedSpec_withdrawFrom_funcSound|$STANDARD
Blanc.Weth10.backedSpec_depositToAndCall_funcSound|$STANDARD
Blanc.Weth10.backedSpec_approveAndCall_funcSound|$STANDARD
Blanc.Weth10.backedSpec_transferAndCall_funcSound|$STANDARD
Blanc.Weth10.backedSpec_flashLoan_funcSound|$STANDARD
Blanc.Weth10.backedSpec_permit_funcSound|$STANDARD
Blanc.Weth10.weth10Funcs_exactRelFuncSound|$STANDARD
Blanc.Weth10.flashExactDepth|$STANDARD
Blanc.Weth10.weth10Funcs_backed_funcSound|$STANDARD
Blanc.Weth10.backedSpec_sound_of_funcSound_all|$STANDARD
Blanc.Weth10.backedSpec_preserves_of_funcSound_all|$STANDARD
Blanc.Weth10.backedSpec_sound|$STANDARD
Blanc.Weth10.backedSpec_preserves|$STANDARD
Blanc.Weth10.weth10InitFunc_runCompiled_zero|$STANDARD
Blanc.Weth10.weth10Init_exec_zero|$STANDARD
Blanc.Weth10.weth10Init_exec_nonzero|$STANDARD
Blanc.Weth10.processCreateMessage_weth10_success|$STANDARD
Blanc.Weth10.freshDeployment_staticCertificate|$STANDARD
Blanc.Weth10.flashExactSpec_preserves|$STANDARD
Blanc.Weth10.processTransaction_preserves_stable|$STANDARD
Blanc.Weth10.stateTransitionWith_preserves_stable|$STANDARD
Blanc.Weth10.stateTransitionUsing_preserves_stable|$STANDARD
Blanc.Weth10.stateTransition_preserves_stable|$STANDARD
Blanc.Weth10.chainUsing_preserves_stable|$STANDARD
Blanc.Weth10.chain_preserves_stable|$STANDARD
Blanc.Weth10.addBlockToChainWith_preserves_stable|$STANDARD
Blanc.Weth10.addBlockToChainUsing_preserves_stable|$STANDARD
Blanc.Weth10.addBlockToChain_preserves_stable|$STANDARD
Blanc.Weth10.Stable.solvent|$STANDARD
Blanc.Weth10.chain_reachable_backed_and_flash_zero|$STANDARD
Blanc.Weth10.processCreateMessage_establishes_stable|$STANDARD
Blanc.Weth10.prepareCanonicalDeploymentContext|$STANDARD
Blanc.Weth10.canonicalDeploymentMessage_succeeds|$STANDARD
Blanc.Weth10.canonicalDeploymentTransaction_succeeds|$STANDARD
Blanc.Weth10.canonicalDeploymentStep_establishes_root|$STANDARD
Blanc.Weth10.DeploymentRoot.reflReach|$STANDARD
Blanc.Weth10.DeploymentRoot.reachable_stable|$STANDARD
Blanc.Weth10.DeploymentRoot.reachable_code|$STANDARD
Blanc.Weth10.DeploymentRoot.reachable_flashZero|$STANDARD
Blanc.Weth10.DeploymentRoot.reachable_solvent|$STANDARD
Blanc.Xinst.step_call_nonzero_insufficient|$STANDARD
Blanc.Xinst.step_call_nonzero_spawn|$STANDARD
Blanc.Ninst.runCompiled_call_nonzero_codeFree|$STANDARD
Blanc.Weth10.redemptionRuntimeCeiling_eq|propext
Blanc.Weth10.Stable.bookedBalanceNat_le_contractEth|$STANDARD
Blanc.Weth10.withdrawTo_exec|$STANDARD
Blanc.Weth10.withdraw_exec|$STANDARD
Blanc.Weth10.processMessageCall_eq_of_exec|$STANDARD
Blanc.Weth10.Stable.messageRedemption_enabled_of_le|$STANDARD
Blanc.Weth10.Stable.selfRedemption_enabled_of_le|$STANDARD
Blanc.Weth10.AdmissibleRedemptionTx.processTransaction_eq_of_message|$STANDARD
Blanc.Weth10.Stable.transactionRedemption_enabled_of_le|$STANDARD
Blanc.Weth10.outerOkWithFailedReceipt_not_redemptionEnabled|$STANDARD
Blanc.Weth10.compiledBalanceSstoreReverseComplete|$STANDARD
Blanc.Weth10.Exec.weth10BalanceSstoreClassification_of_mem_committedFrames|$STANDARD
Blanc.Weth10.AccountedHistory.flash_pair_totals_eq|$STANDARD
Blanc.Weth10.AccountedHistory.toReachUsing|$STANDARD
Blanc.Weth10.exists_accountedHistory_of_reachUsing|$STANDARD
Blanc.Weth10.AccountedHistory.weth10Flow_eq_of_appliedBlocks_eq|$STANDARD
Blanc.Weth10.committedExecStorageSound|$STANDARD
Blanc.Weth10.committedExecEthSound|$STANDARD
Blanc.Weth10.AccountedHistory.noCommittedCreditWrap|$STANDARD
Blanc.Weth10.AccountedHistory.holderCreditLoss_eq_zero|$STANDARD
Blanc.Weth10.holderFlow_conserved|$STANDARD
Blanc.Weth10.holderFlow_flash_cancelled|$STANDARD
Blanc.Weth10.holderFlow_residual_floor|$STANDARD
Blanc.Weth10.holderFlow_truncated_floor|$STANDARD
Blanc.Weth10.holderFlow_withdrawal_floor|$STANDARD
Blanc.Weth10.committedExecAllowanceSound|$STANDARD
Blanc.Weth10.AccountedHistory.allowanceTransported_of_compiled|$STANDARD
Blanc.Weth10.hardenedOutflow_le_permanentOutflow|$STANDARD
Blanc.Weth10.permanentOutflow_eq_hardenedOutflow_of_noCollision|$STANDARD
Blanc.Weth10.holderFlow_hardened_floor|$STANDARD
Blanc.Weth10.deployment_reachable_residual_messageRedemption_enabled|$STANDARD
Blanc.Weth10.deployment_reachable_residual_transactionRedemption_enabled|$STANDARD
Blanc.Weth10.deployment_reachable_future_redeemable|$STANDARD
Blanc.Weth10.deploymentRoot_allowanceQuiescent|$STANDARD
Blanc.Weth10.deployment_fullWindow_future_redeemable|$STANDARD
Blanc.Weth10.redeemClaims_anyOrder|$STANDARD
Blanc.Weth10.deployment_reachable_redeemClaims_anyOrder|$STANDARD"
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
