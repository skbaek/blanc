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
# reaching `Func.revert` through the dispatcher's fallback slot; the other is
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
# The last sixteen rows are the `weth10-redeem-future-v2` family. Read them with
# three restrictions in mind. `AccountedHistory.allowanceTransported_of_compiled`
# and `committedExecAllowanceSound` are the allowance-transport endpoints the
# attribution layer runs on. Their `...Sound` siblings
# (`AccountedHistory.allowanceTransportedSound_of_compiled`,
# `committedExecAllowanceReadSound`) are a strengthening proved beside them, not
# an amendment to them: each adds entry-read soundness of the same ledger
# against the same entry storage, and scripts/ClaimCheck.lean witnesses that the
# two originals are recovered from the siblings by downgrade, so the published
# statements above are unchanged. `flashSettlement_allowanceEntryRead` is the
# arm-level pin that removes the flash record's exemption from that entry-read
# clause — the flash record is the one whose read is reconstructed from the
# committed post state, and this row pins it at the post-callback settlement
# entry, which is where the runtime performed the read.
# `dormant_holder_balance_monotone` is the family's most legible claim: given
# collision-freedom, checkpoint allowance quiescence for `u`, and no authorizing
# act by `u`, that holder's booked balance cannot fall. It is a monotonicity
# statement about booked balances only — it asserts nothing about the holder's
# ether, and says nothing about holders who did act.
# `hardenedOutflow_le_permanentOutflow` and
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
Blanc.Weth10.weth10MainnetCode_eq|$STANDARD
Blanc.Func.compile_eq_emitUnchecked|$STANDARD
Blanc.Table.compile_eq_emitUnchecked|$STANDARD
Blanc.Prog.compile_eq_emitUnchecked|$STANDARD
Blanc.Frame.raw_commits_of_settlementCommits|$STANDARD
Blanc.Exec.descendantFrames_runOk_of_settlementCommits|$STANDARD
Blanc.Exec.descendantFrames_runOk_of_not_settlementCommits|$STANDARD
Blanc.Exec.descendantFrames_runOk_create_codeDepositRollback|$STANDARD
Blanc.Exec.committedFrames_eq_nil_of_not_commits|$STANDARD
Blanc.ProcessMessage.settlementCommits_of_some_ok_clean|$STANDARD
Blanc.Frame.settlementCommits_ofCall_of_raw_commits|$STANDARD
Blanc.Exec.ninstOccurrence_iff_mem_rawNodes|$STANDARD
Blanc.Exec.SuccessfulSstoreOccurrence.storage_update|$STANDARD
Blanc.Exec.Deriv.ParentPrefix.linear|$STANDARD
Blanc.Exec.Deriv.SourceCursor.Chronology.strictBefore|$STANDARD
Blanc.Exec.Deriv.SourceCursor.toward|$STANDARD
Blanc.Prog.sourceSiteAt_sound|$STANDARD
Blanc.Exec.Frame.successfulSstore_sourceSite|$STANDARD
Blanc.Exec.retainedNodes_sublist_rawNodes|$STANDARD
Blanc.Exec.committedFrameRoots_sublist_retainedNodes|$STANDARD
Blanc.Exec.mem_retainedNodes_iff_committedFrame_parentPrefix|$STANDARD
Blanc.Exec.retainedNodes_runOk_of_settlementCommits|$STANDARD
Blanc.Exec.retainedNodes_runOk_of_not_settlementCommits|$STANDARD
Blanc.Exec.storageReplay_committedPost|$STANDARD
Blanc.Exec.exists_lastRetainedSstore_of_getStor_ne|$STANDARD
Blanc.Prog.acceptsSstoreSite_sound|$STANDARD
Blanc.Exec.Frame.successfulSstore_acceptsSource|$STANDARD
Blanc.Weth10.Exec.Frame.NinstOccurrence.toCommon|$STANDARD
Blanc.Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix|$STANDARD
Blanc.Exec.Deriv.sstore_sourceSite|$STANDARD
Blanc.Exec.Deriv.successfulSstore_sourceSite|$STANDARD
Blanc.Exec.NinstOccurrence.exists_rawFrameRoot_parentPrefix|$STANDARD
Blanc.Exec.NinstOccurrence.sourceSite_of_rawFrameRoot|$STANDARD
Blanc.Exec.Deriv.sstore_acceptsSource|$STANDARD
Blanc.Exec.NinstOccurrence.acceptsSource_of_rawFrameRoot|$STANDARD
Blanc.Func.localSstoreFree_iff|propext
Blanc.Prog.componentSstoreFree_iff|propext, Quot.sound
Blanc.Prog.entrySstoreFree_iff|propext, Quot.sound
Blanc.Prog.entrySstoreFree_sound|propext, Quot.sound
Blanc.Exec.Deriv.SourceCursor.noSstore_of_entrySstoreFree|$STANDARD
Blanc.Exec.NinstOccurrence.instruction_ne_sstore_of_entrySstoreFree|$STANDARD
Blanc.Exec.Deriv.noSstore_of_exactMain_entrySstoreFree|$STANDARD
Blanc.tstore_run_cell|$STANDARD
Blanc.tstore_run_zero|$STANDARD
Blanc.tload_run_cell|$STANDARD
Blanc.directCall_nonzero_spawn|$STANDARD
Blanc.directCall_zero_spawn|$STANDARD
Blanc.directStatcall_spawn|$STANDARD
Blanc.directDelcall_spawn|$STANDARD
Blanc.Xinst.step_spawn_codeAddress_eq_currentTarget|$STANDARD
Blanc.delegatecall_enters_with_parent_as_storage_owner|$STANDARD
Blanc.control_delegatecall_separates_call_fuses|$STANDARD
Blanc.control_delegatecall_inherits_caller_and_value|$STANDARD
Blanc.delegatecall_child_observes_outer_caller_and_value|$STANDARD
Blanc.control_two_window_memory_premise_derivable|$STANDARD
Blanc.control_sliceD_payload_size|$STANDARD
Blanc.caughtCall_childSettlement|$STANDARD
Blanc.cleanCall_childSettlement|$STANDARD
Blanc.preparedTransactionMessage_exists|$STANDARD
Blanc.PreparedTransactionMessage.transientStorage_eq_empty|$STANDARD
Blanc.processMessageCall_error_logs_eq_nil|$STANDARD
Blanc.PreparedTransactionMessage.error_logs_eq_nil|$STANDARD
Blanc.of_run_sstore_not_static|$STANDARD
Blanc.genericCall.step_spawn_isStatic|$STANDARD
Blanc.genericCreate.step_spawn_not_static|$STANDARD
Blanc.Xinst.step_spawn_isStatic|$STANDARD
Blanc.Evm.step_spawn_isStatic|$STANDARD
Blanc.executeCode.enter_inl_isStatic|$STANDARD
Blanc.Frame.enter_run_isStatic|$STANDARD
Blanc.Evm.step_run_isStatic|$STANDARD
Blanc.genericCall.step_spawn_isStatic_of_staticcall|$STANDARD
Blanc.Xinst.step_staticcall_spawn_isStatic|$STANDARD
Blanc.Ninst.step_staticcall_spawn_isStatic|$STANDARD
Blanc.Ninst.step_staticcall_run_isStatic|$STANDARD
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
Blanc.Func.runCompiledTo_revertReturnData|$STANDARD
Blanc.Frame.enter_eq_done_executePrecomp|$STANDARD
Blanc.Xinst.step_staticcall|$STANDARD
Blanc.Xinst.step_staticcall_spawn|$STANDARD
Blanc.Ninst.runCompiled_staticcall_doneFrame|$STANDARD
Blanc.of_run_call_val_with_depth|$STANDARD
Blanc.of_run_staticcall_val_with_depth_cause|$STANDARD
Blanc.of_run_staticcall_val_with_depth|$STANDARD
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
Blanc.Weth10.NonSignatureRedemptionTxEnvelope.admissible_of_recoveredSender|$STANDARD
Blanc.Weth10.Stable.bookedBalanceNat_le_contractEth|$STANDARD
Blanc.Weth10.withdrawTo_exec|$STANDARD
Blanc.Weth10.withdraw_exec|$STANDARD
Blanc.Weth10.processMessageCall_eq_of_exec|$STANDARD
Blanc.Weth10.Stable.messageRedemption_enabled_of_le|$STANDARD
Blanc.Weth10.Stable.selfRedemption_enabled_of_le|$STANDARD
Blanc.Weth10.AdmissibleRedemptionTx.processTransaction_eq_of_message|$STANDARD
Blanc.Weth10.AdmissibleSelfRedemptionTx.processTransaction_eq_of_message|$STANDARD
Blanc.Weth10.Stable.transactionRedemption_enabled_of_le|$STANDARD
Blanc.Weth10.Stable.selfTransactionRedemption_enabled_of_le|$STANDARD
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
Blanc.Weth10.flashSettlement_allowanceEntryRead|$STANDARD
Blanc.Weth10.committedExecAllowanceReadSound|$STANDARD
Blanc.Weth10.AccountedHistory.allowanceTransportedSound_of_compiled|$STANDARD
Blanc.Weth10.viewReadFrame_sameCaller_not_authorizing|propext
Blanc.Weth10.hardenedOutflow_le_permanentOutflow|$STANDARD
Blanc.Weth10.permanentOutflow_eq_hardenedOutflow_of_noCollision|$STANDARD
Blanc.Weth10.holderFlow_hardened_floor|$STANDARD
Blanc.Weth10.dormant_holder_balance_monotone|$STANDARD
Blanc.Weth10.deployment_reachable_residual_messageRedemption_enabled|$STANDARD
Blanc.Weth10.deployment_reachable_residual_transactionRedemption_enabled|$STANDARD
Blanc.Weth10.deployment_reachable_residual_selfMessageRedemption_enabled|$STANDARD
Blanc.Weth10.deployment_reachable_residual_selfTransactionRedemption_enabled|$STANDARD
Blanc.Weth10.deployment_reachable_booked_messageRedemption_enabled|$STANDARD
Blanc.Weth10.deployment_reachable_booked_transactionRedemption_enabled|$STANDARD
Blanc.Weth10.deployment_reachable_booked_selfTransactionRedemption_enabled|$STANDARD
Blanc.Weth10.deployment_reachable_booked_transactionRedemption_enabled_of_recoveredSender|$STANDARD
Blanc.Weth10.deployment_reachable_future_redeemable|$STANDARD
Blanc.Weth10.deployment_reachable_future_dualSelector_redeemable|$STANDARD
Blanc.Weth10.deployment_reachable_future_redeemable_allHolders|$STANDARD
Blanc.Weth10.deploymentRoot_allowanceQuiescent|$STANDARD
Blanc.Weth10.deployment_fullWindow_future_redeemable|$STANDARD
Blanc.Weth10.deployment_fullWindow_attributionRootAt_ne_checkpoint|$STANDARD
Blanc.Weth10.deployment_fullWindow_permanentOutflowAuthorization|$STANDARD
Blanc.Weth10.deployment_fullWindow_hardenedOutflow_only_authorizingRoots|$STANDARD
Blanc.Weth10.deployment_fullWindow_dormant_holder_balance_monotone|$STANDARD
Blanc.Weth10.deployment_reachable_dormant_holder_balance_monotone|$STANDARD
Blanc.Weth10.redeemClaims_anyOrder|$STANDARD
Blanc.Weth10.redeemEveryoneList_anyOrder|$STANDARD
Blanc.Weth10.deployment_reachable_redeemClaims_anyOrder|$STANDARD
Blanc.Weth10.deployment_reachable_redeemEveryoneList_anyOrder|$STANDARD
Blanc.Weth10.mainnet_rulesAt_eq_named|propext
Blanc.Weth10.mainnet_rulesAt_eq_bpo2_of_ge|propext, Quot.sound
Blanc.Weth10.pragueRules_redemptionRuntimeCeiling_gasCap|propext
Blanc.Weth10.osakaRules_redemptionRuntimeCeiling_gasCap|propext
Blanc.Weth10.bpo1Rules_redemptionRuntimeCeiling_gasCap|propext
Blanc.Weth10.bpo2Rules_redemptionRuntimeCeiling_gasCap|propext
Blanc.Weth10.mainnet_checkTransactionGasCap_of_le|propext
Blanc.Weth10.weth10CurrentMainnetCreation_rulesAt|propext
Blanc.Weth10.canonicalMainnetBpo2DeploymentStep_establishes_root|$STANDARD
Blanc.Weth10.chainUsing_preserves_stable_mainnet|$STANDARD
Blanc.Weth10.chain_reachable_backed_and_flash_zero_mainnet|$STANDARD
Blanc.Weth10.deployment_reachable_residual_messageRedemption_enabled_mainnet|$STANDARD
Blanc.Weth10.deployment_reachable_residual_transactionRedemption_enabled_mainnet|$STANDARD
Blanc.Weth10.deployment_reachable_residual_selfMessageRedemption_enabled_mainnet|$STANDARD
Blanc.Weth10.deployment_reachable_residual_selfTransactionRedemption_enabled_mainnet|$STANDARD
Blanc.Weth10.deployment_reachable_booked_messageRedemption_enabled_mainnet|$STANDARD
Blanc.Weth10.deployment_reachable_booked_transactionRedemption_enabled_mainnet|$STANDARD
Blanc.Weth10.deployment_reachable_booked_selfTransactionRedemption_enabled_mainnet|$STANDARD
Blanc.Weth10.deployment_reachable_booked_transactionRedemption_enabled_of_recoveredSender_mainnet|$STANDARD
Blanc.Weth10.deployment_reachable_future_redeemable_mainnet|$STANDARD
Blanc.Weth10.deployment_reachable_future_dualSelector_redeemable_mainnet|$STANDARD
Blanc.Weth10.deployment_reachable_future_redeemable_allHolders_mainnet|$STANDARD
Blanc.Weth10.deploymentRoot_allowanceQuiescent_mainnet|$STANDARD
Blanc.Weth10.deployment_fullWindow_future_redeemable_mainnet|$STANDARD
Blanc.Weth10.deployment_fullWindow_attributionRootAt_ne_checkpoint_mainnet|$STANDARD
Blanc.Weth10.deployment_fullWindow_permanentOutflowAuthorization_mainnet|$STANDARD
Blanc.Weth10.deployment_fullWindow_hardenedOutflow_only_authorizingRoots_mainnet|$STANDARD
Blanc.Weth10.deployment_fullWindow_dormant_holder_balance_monotone_mainnet|$STANDARD
Blanc.Weth10.deployment_reachable_dormant_holder_balance_monotone_mainnet|$STANDARD
Blanc.Weth10.deployment_reachable_redeemClaims_anyOrder_mainnet|$STANDARD
Blanc.Weth10.deployment_reachable_redeemEveryoneList_anyOrder_mainnet|$STANDARD
Blanc.Weth10.AccountedHistory.flash_pair_totals_eq_mainnet|$STANDARD
Blanc.Weth10.AccountedHistory.weth10Flow_eq_of_appliedBlocks_eq_mainnet|$STANDARD
Blanc.Weth10.AccountedHistory.noCommittedCreditWrap_mainnet|$STANDARD
Blanc.Weth10.AccountedHistory.holderCreditLoss_eq_zero_mainnet|$STANDARD
Blanc.Weth10.holderFlow_conserved_mainnet|$STANDARD
Blanc.Weth10.holderFlow_flash_cancelled_mainnet|$STANDARD
Blanc.Weth10.holderFlow_residual_floor_mainnet|$STANDARD
Blanc.Weth10.holderFlow_truncated_floor_mainnet|$STANDARD
Blanc.Weth10.holderFlow_withdrawal_floor_mainnet|$STANDARD
Blanc.Weth10.chainUsing_preserves_stable_prague|$STANDARD
Blanc.Weth10.chain_reachable_backed_and_flash_zero_prague|$STANDARD
Blanc.Weth10.deployment_reachable_residual_messageRedemption_enabled_prague|$STANDARD
Blanc.Weth10.deployment_reachable_residual_transactionRedemption_enabled_prague|$STANDARD
Blanc.Weth10.deployment_reachable_residual_selfMessageRedemption_enabled_prague|$STANDARD
Blanc.Weth10.deployment_reachable_residual_selfTransactionRedemption_enabled_prague|$STANDARD
Blanc.Weth10.deployment_reachable_booked_messageRedemption_enabled_prague|$STANDARD
Blanc.Weth10.deployment_reachable_booked_transactionRedemption_enabled_prague|$STANDARD
Blanc.Weth10.deployment_reachable_booked_selfTransactionRedemption_enabled_prague|$STANDARD
Blanc.Weth10.deployment_reachable_booked_transactionRedemption_enabled_of_recoveredSender_prague|$STANDARD
Blanc.Weth10.deployment_reachable_future_redeemable_prague|$STANDARD
Blanc.Weth10.deployment_reachable_future_dualSelector_redeemable_prague|$STANDARD
Blanc.Weth10.deployment_reachable_future_redeemable_allHolders_prague|$STANDARD
Blanc.Weth10.deploymentRoot_allowanceQuiescent_prague|$STANDARD
Blanc.Weth10.deployment_fullWindow_future_redeemable_prague|$STANDARD
Blanc.Weth10.deployment_fullWindow_attributionRootAt_ne_checkpoint_prague|$STANDARD
Blanc.Weth10.deployment_fullWindow_permanentOutflowAuthorization_prague|$STANDARD
Blanc.Weth10.deployment_fullWindow_hardenedOutflow_only_authorizingRoots_prague|$STANDARD
Blanc.Weth10.deployment_fullWindow_dormant_holder_balance_monotone_prague|$STANDARD
Blanc.Weth10.deployment_reachable_dormant_holder_balance_monotone_prague|$STANDARD
Blanc.Weth10.deployment_reachable_redeemClaims_anyOrder_prague|$STANDARD
Blanc.Weth10.deployment_reachable_redeemEveryoneList_anyOrder_prague|$STANDARD
Blanc.Weth10.AccountedHistory.flash_pair_totals_eq_prague|$STANDARD
Blanc.Weth10.AccountedHistory.weth10Flow_eq_of_appliedBlocks_eq_prague|$STANDARD
Blanc.Weth10.AccountedHistory.noCommittedCreditWrap_prague|$STANDARD
Blanc.Weth10.AccountedHistory.holderCreditLoss_eq_zero_prague|$STANDARD
Blanc.Weth10.holderFlow_conserved_prague|$STANDARD
Blanc.Weth10.holderFlow_flash_cancelled_prague|$STANDARD
Blanc.Weth10.holderFlow_residual_floor_prague|$STANDARD
Blanc.Weth10.holderFlow_truncated_floor_prague|$STANDARD
Blanc.Weth10.holderFlow_withdrawal_floor_prague|$STANDARD
Blanc.LidoCircuitBreaker.emptyWitness|propext, Quot.sound
Blanc.LidoCircuitBreaker.lidoCircuitBreakerCode_compile|$STANDARD
Blanc.LidoCircuitBreaker.funcs_selectors_eq_runtimeEndpoints|$STANDARD
Blanc.LidoCircuitBreaker.runtime_source_sstore_site_count|$STANDARD
Blanc.LidoCircuitBreaker.runtime_source_tstore_site_count|$STANDARD
Blanc.LidoCircuitBreaker.runtime_source_external_call_site_count|$STANDARD
Blanc.LidoCircuitBreaker.sourceInventory_cardinalities|$STANDARD
Blanc.LidoCircuitBreaker.enumeration_entry_sstore_free|$STANDARD
Blanc.LidoCircuitBreaker.enumeration_writing_mutant_rejected|$STANDARD
Blanc.LidoCircuitBreaker.abiEncodeConstructorArgs_length|propext
Blanc.LidoCircuitBreaker.constructor_inventory_cardinalities|
Blanc.LidoCircuitBreaker.creation_template_runtime_suffix|$STANDARD
Blanc.LidoCircuitBreaker.full_create_input_length|$STANDARD
Blanc.LidoCircuitBreaker.slot_toNat_of_region_payload_lt|$STANDARD
Blanc.LidoCircuitBreaker.slot_injective_payload|$STANDARD
Blanc.LidoCircuitBreaker.slot_ne_of_region_ne|$STANDARD
Blanc.LidoCircuitBreaker.RegistryWitness.entries_length_le|$STANDARD
Blanc.LidoCircuitBreaker.setPauser_sourceTrace_refines_model|propext, Quot.sound
Blanc.LidoCircuitBreaker.RegistryWitness.applySetPauserSourceTrace|$STANDARD
Blanc.LidoCircuitBreaker.setPauser_zero_runCompiledTo_pausableZero_noRegistryWrite|$STANDARD
Blanc.LidoCircuitBreaker.setPauser_run_extracts_sourceTrace|$STANDARD
Blanc.LidoCircuitBreaker.setPauserKernel_run_of_exec|$STANDARD
Blanc.LidoCircuitBreaker.setPauserKernel_exec_extracts_sourceTrace|$STANDARD
Blanc.LidoCircuitBreaker.registerPauser_kernel_exec_preserves_registry|$STANDARD
Blanc.LidoCircuitBreaker.registerAfterSet_runCompiledTo_preserves_registry|$STANDARD
Blanc.LidoCircuitBreaker.pause_kernel_exec_reaches_pauseAfterSet|$STANDARD
Blanc.LidoCircuitBreaker.registerPauser_settled_error_restores_registry|$STANDARD
Blanc.LidoCircuitBreaker.pause_settled_error_restores_registry|$STANDARD
Blanc.LidoCircuitBreaker.membershipEquivalence_registerPauser|$STANDARD
Blanc.LidoCircuitBreaker.cleanStateAfterRemoval_registerPauser|$STANDARD
Blanc.LidoCircuitBreaker.globalCountConservation_registerPauser|$STANDARD
Blanc.LidoCircuitBreaker.pause_direct_postWrite_revert_settles_and_restores_registry|$STANDARD
Blanc.LidoCircuitBreaker.directPause_zeroCode_postWrite_error_control|$STANDARD
Blanc.LidoCircuitBreaker.getPausables_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.getPausables_noSstore_occurrence|$STANDARD
Blanc.LidoCircuitBreaker.registryViews_coherent|$STANDARD
Blanc.LidoCircuitBreaker.pauserSet_local_transition|$STANDARD
Blanc.LidoCircuitBreaker.pauserSet_target_zero_no_success|$STANDARD
Blanc.LidoCircuitBreaker.pauserSet_target_zero_error_logs_unchanged|$STANDARD
Blanc.LidoCircuitBreaker.pauserSet_register_success|$STANDARD
Blanc.LidoCircuitBreaker.pauserSet_register_success_committed|$STANDARD
Blanc.LidoCircuitBreaker.pauserSet_settled_error_not_observable|$STANDARD
Blanc.LidoCircuitBreaker.registryObservation_sound|$STANDARD
Blanc.LidoCircuitBreaker.registryStable_iff_stateInv|$STANDARD
Blanc.LidoCircuitBreaker.funcSound_of_storFixed|$STANDARD
Blanc.LidoCircuitBreaker.funcSound_of_registryCore|$STANDARD
Blanc.LidoCircuitBreaker.registrySpec_sound_of_funcSound|$STANDARD
Blanc.LidoCircuitBreaker.funcSound_of_mem_funcs|$STANDARD
Blanc.LidoCircuitBreaker.funcSound_of_mem_nonRegistry|$STANDARD
Blanc.subcode_of_get?_eq_some_appended|$STANDARD
Blanc.Prog.jumpable_of_get?_table_appended|$STANDARD
Blanc.Func.exec_of_runCompiled_appended_core|$STANDARD
Blanc.Prog.exec_of_runCompiled_appended|$STANDARD
Blanc.Func.exec_of_runCompiledTo_appended_core|$STANDARD
Blanc.Prog.exec_of_runCompiledTo_appended|$STANDARD
Blanc.processCreateMessage_msg_getStor_currentTarget|$STANDARD
Blanc.benvAfterTransfer_exists_zero|$STANDARD
Blanc.benvAfterTransfer_stat|$STANDARD
Blanc.processMessage_ok_of_exec|$STANDARD
Blanc.processCreateMessage_ok_of_processMessage_and_charge|$STANDARD
Blanc.processCreateMessage_ok_of_processMessage_error|$STANDARD
Blanc.processUncheckedSystemTransaction_deploymentSystemProgram|$STANDARD
Blanc.processCheckedSystemTransaction_deploymentSystemProgram|$STANDARD
Blanc.canonicalDeploymentSystemPrefix|$STANDARD
Blanc.LidoCircuitBreaker.runtimeTemplateCode_length_exact|$STANDARD
Blanc.LidoCircuitBreaker.constructor_immutable_word_offsets_exact|$STANDARD
Blanc.LidoCircuitBreaker.provisionalConstructorPrefix_length_exact|$STANDARD
Blanc.LidoCircuitBreaker.lidoCircuitBreakerConstructorProgram_compile|$STANDARD
Blanc.LidoCircuitBreaker.lidoCircuitBreakerInitPrefix_length_exact|$STANDARD
Blanc.LidoCircuitBreaker.patchRuntimeTemplate_official|$STANDARD
Blanc.LidoCircuitBreaker.lidoCircuitBreakerCreationTemplate_length_exact|$STANDARD
Blanc.LidoCircuitBreaker.officialFullCreateInput_eq_layout|$STANDARD
Blanc.LidoCircuitBreaker.officialFullCreateInput_length_exact|$STANDARD
Blanc.LidoCircuitBreaker.officialFullCreateInput_slice_constructorArgs|$STANDARD
Blanc.LidoCircuitBreaker.officialFullCreateInput_slice_runtimeTemplate|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorEventScratch_eq|
Blanc.LidoCircuitBreaker.constructorBody_official_eq|$STANDARD
Blanc.LidoCircuitBreaker.lidoCircuitBreakerConstructorProgram_main_official|$STANDARD
Blanc.LidoCircuitBreaker.lidoCircuitBreakerConstructorProgram_aux_official|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorTableCallIndices_exact|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorDecodedMemory_read_argument|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorDecodedMemory_size|propext
Blanc.LidoCircuitBreaker.officialConstructorDecodedMemory_read_memory|propext, Quot.sound
Blanc.LidoCircuitBreaker.officialConstructorCopiedMemory_size|$STANDARD
Blanc.LidoCircuitBreaker.ConstructorPatchInvariant.read_argument|$STANDARD
Blanc.LidoCircuitBreaker.ConstructorPatchInvariant.read_memory|propext, Quot.sound
Blanc.LidoCircuitBreaker.constructorPatchPair_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.ConstructorPatchInvariant.runCompiled_write|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPatchLine1_4_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPatchLine5_8_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPatchLine9_12_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPatchMemory12_eq_patched|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPatchedMemory_size|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPatchedMemory_wf|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPatchedMemory_reads|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPatchedMemory_read_argument|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPauseZeroMemory_wf|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPauseZeroMemory_reads|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPauseZeroMemory_size|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPauseZeroMemory_read_argument|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPauseZeroMemory_read_argument_memory|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPauseMemory_wf|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPauseMemory_reads|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPauseMemory_size|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPauseMemory_read_argument|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPauseMemory_read_argument_memory|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatZeroMemory_wf|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatZeroMemory_reads|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatZeroMemory_size|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatZeroMemory_read_argument|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatZeroMemory_read_argument_memory|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatMemory_wf|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatMemory_reads|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatMemory_size|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatMemory_read_argument|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatMemory_read_argument_memory|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatMemory_eq_final|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorFinalMemory_size|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorFinalMemory_reads|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorFinalMemory_read_runtime|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorFinalMemory_read|$STANDARD
Blanc.LidoCircuitBreaker.Bytes.sliceD_writeAt_pair|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPatchedMemory_read_initializedData|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPatchedMemory_read_initializedMemory|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorColdStore_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatLoggedBase_getStor|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPauseLoggedBase_accessedStorageKeys|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPauseLoggedBase_getStorVal|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatLoggedBase_accessedStorageKeys|$STANDARD
Blanc.LidoCircuitBreaker.not_mem_hashSet_insert|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorEffectBase_getStor|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorEffectBase_logs|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorEffectBase_state|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorEffectBase_refundCounter|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorEffectBase_returnData|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorEffectBase_error|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorEffectBase_accountsToDelete|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorEffectBase_createdAccounts|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorEffectBase_accessedAddresses|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorEffectBase_transientStorage|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorEffectBase_accessedStorageKeys|$STANDARD
Blanc.LidoCircuitBreaker.constructorArgumentSstorePrefix_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.constructorEventLog1Opcode_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.constructorEventLog1Prefix_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.constructorArgumentMstorePrefix_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.constructorZeroMstorePrefix_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.constructorEventLog2Opcode_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.constructorArgumentLog2Prefix_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_eq|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorReturnLine_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorReturn_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_getStor|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_pauseDuration|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_heartbeatInterval|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_logs|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_stack|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_memory|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_gasLeft|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_output|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatSstore_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatStoreLine_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatLogOpcode_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatLogLine_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatScratchValue_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatScratchZero_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatScratchLine_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorHeartbeatSuffix_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPauseStoreLine_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPauseLogLine_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPauseScratchValue_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPauseScratchZero_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPauseScratchLine_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorConfigurationSuffix_eq_prefix|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorConfigurationSuffix_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorInitializedLogOpcode_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorInitializedLogLine_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorCopyPatch_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorEffectBody_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorValidationPrefix_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorProgram_runCompiled_fresh|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructor_exec_fresh|$STANDARD
Blanc.LidoCircuitBreaker.officialCodeDepositGas_eq|$STANDARD
Blanc.LidoCircuitBreaker.officialCreateMessageGasAccounting_eq|$STANDARD
Blanc.LidoCircuitBreaker.prepareCanonicalDeploymentContext|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_state|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_refundCounter|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_returnData|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_error|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_accountsToDelete|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_createdAccounts|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_accessedAddresses|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_accessedStorageKeys|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_transientStorage|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_effectCheckpoints|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorErrorArmLayout|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorExecutionTrace_fresh|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_emptyRegistryWitness|$STANDARD
Blanc.LidoCircuitBreaker.officialConstructorPost_registryCoherent|$STANDARD
Blanc.LidoCircuitBreaker.lidoCircuitBreakerCode_official_length|$STANDARD
Blanc.LidoCircuitBreaker.lidoCircuitBreakerCode_official_cons|$STANDARD
Blanc.LidoCircuitBreaker.processCreateMessage_establishes_officialRegistryStable|$STANDARD
Blanc.LidoCircuitBreaker.processMessageCall_establishes_officialRegistryStable|$STANDARD
Blanc.LidoCircuitBreaker.canonicalDeploymentTransaction_succeeds|$STANDARD
Blanc.LidoCircuitBreaker.canonicalDeploymentSuffix_succeeds|$STANDARD
Blanc.LidoCircuitBreaker.canonicalDeploymentApplyBody_succeeds|$STANDARD
Blanc.LidoCircuitBreaker.canonicalDeploymentStep_establishes_root|$STANDARD
Blanc.LidoCircuitBreaker.DeploymentRoot.reflReach|$STANDARD
Blanc.LidoCircuitBreaker.DeploymentRoot.reachable_registryStable|$STANDARD
Blanc.LidoCircuitBreaker.DeploymentRoot.reachable_code|$STANDARD
Blanc.LidoCircuitBreaker.DeploymentRoot.reachable_installedCode|$STANDARD
Blanc.LidoCircuitBreaker.DeploymentRoot.reachable_witness|$STANDARD
Blanc.LidoCircuitBreaker.DeploymentRoot.reachable_membership|$STANDARD
Blanc.LidoCircuitBreaker.DeploymentRoot.reachable_countConservation|$STANDARD
Blanc.Exec.committedCell_eq_of_noRetainedWriteTo|$STANDARD
Blanc.Exec.Deriv.ParentStep.sevm_eq|$STANDARD
Blanc.Exec.Deriv.ParentPrefix.sevm_eq|$STANDARD
Blanc.Exec.noRetainedWriteTo_of_no_execOccurrence|$STANDARD
Blanc.Exec.noRetainedWriteTo_of_frame_owners_ne|$STANDARD
Blanc.Exec.noRetainedWriteTo_of_sourceSites_no_exec|$STANDARD
Blanc.Func.RunCompiledTo.RouteTo.enteredFunction_of_ne|$STANDARD
Blanc.runCompiledTo_next_elim|$STANDARD
Blanc.runCompiledTo_line_elim|$STANDARD
Blanc.runCompiledTo_call_elim|$STANDARD
Blanc.runCompiledTo_branchLeft_frame_elim|$STANDARD
Blanc.runCompiledTo_branchRight_frame_elim|$STANDARD
Blanc.LidoCircuitBreaker.pauseCall_boundary_with_execution|$STANDARD
Blanc.LidoCircuitBreaker.pauseStat_boundary_with_execution|$STANDARD
Blanc.LidoCircuitBreaker.pauseCallStaging_boundary_operands|$STANDARD
Blanc.LidoCircuitBreaker.pauseStatStaging_boundary_operands|$STANDARD
Blanc.LidoCircuitBreaker.pauseStatStaging_boundary_calldata|$STANDARD
Blanc.LidoCircuitBreaker.pauseLockTest_word|$STANDARD
Blanc.LidoCircuitBreaker.pauseAssignedTest_word|$STANDARD
Blanc.LidoCircuitBreaker.pauseLiveTest_word|$STANDARD
Blanc.LidoCircuitBreaker.pause_to_setPauserCall_any|$STANDARD
Blanc.LidoCircuitBreaker.pause_routeTo_setPauserCall_any|$STANDARD
Blanc.LidoCircuitBreaker.dispatch_to_pause_transient|$STANDARD
Blanc.LidoCircuitBreaker.dispatch_routeTo_pause_transient|$STANDARD
Blanc.LidoCircuitBreaker.runtimeMain_to_pauseKernel_any|$STANDARD
Blanc.LidoCircuitBreaker.runtimeMain_routeTo_pauseKernel_any|$STANDARD
Blanc.LidoCircuitBreaker.setPauserKernel_to_pauseAfterSet_any|$STANDARD
Blanc.LidoCircuitBreaker.setPauserKernel_routeTo_pauseAfterSetCall_any|$STANDARD
Blanc.LidoCircuitBreaker.pauseSuccess_ok_getStorVal_eq_of_ne|$STANDARD
Blanc.LidoCircuitBreaker.pauseSuccess_ok_getStor_eq_of_owner_ne|$STANDARD
Blanc.LidoCircuitBreaker.MemWordAt.acrossPauseCallStagingBoundary|$STANDARD
Blanc.LidoCircuitBreaker.MemWordAt.acrossPauseStatStagingBoundary|$STANDARD
Blanc.LidoCircuitBreaker.pauseAfterSet_codeGuard_arms_windows|$STANDARD
Blanc.LidoCircuitBreaker.pauseAfterCall_arms_windows|$STANDARD
Blanc.LidoCircuitBreaker.pauseAfterCall_ok_depth_ne_zero|$STANDARD
Blanc.LidoCircuitBreaker.PublicPauseEntryPremises.removePreservesCount|$STANDARD
Blanc.LidoCircuitBreaker.publicPause_reaches_pauseAfterSet|$STANDARD
Blanc.LidoCircuitBreaker.pauseAfterSet_boundary_committed_outcomes|$STANDARD
Blanc.LidoCircuitBreaker.publicPause_committed_outcomes|$STANDARD
Blanc.LidoCircuitBreaker.pauseLastWorld_publicPausePremises|$STANDARD
Blanc.LidoCircuitBreaker.pauseLastWorld_publicPauseReach|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.stubProgram_compiles|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.stubProgram_compile|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.stubProgram_pcFree|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.stubProgram_sourceSites_no_exec|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.stub_pauseFor_effect|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.stub_isPaused_truthful|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.stub_lidoPinnedPauseTarget|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.stub_successful_pause_composition|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.benignCallProgram_compiles|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.benignCallProgram_compile|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.benignCall_nonchildless_noninterference|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.wrongBoolProgram_compiles|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.wrongBoolProgram_compile|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.wrongBoolProgram_pcFree|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.wrongBool_paused_query_execution|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.wrongBoolProgram_truthfulness_falsifier|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.wrongBoolReturnShape_falsifier|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.retainedWriteChildProgram_compiles|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.retainedWriteProgram_compiles|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.retainedWriteChildProgram_compile|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.retainedWriteProgram_compile|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.retainedWrite_distinctTarget_descendant_falsifier|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.retainedWriteProgram_noninterference_falsifier|$STANDARD
Blanc.LidoCircuitBreaker.observation_ok_getStorVal_eq_of_ne|$STANDARD
Blanc.LidoCircuitBreaker.observation_ok_getStor_eq_of_owner_ne|$STANDARD
Blanc.LidoCircuitBreaker.stubBoundaryExecutions_of_afterSet_ok|$STANDARD
Blanc.LidoCircuitBreaker.publicPause_pinnedTarget|$STANDARD
Blanc.LidoCircuitBreaker.publicPause_stubPinnedTarget|$STANDARD
Blanc.LidoCircuitBreaker.publicPause_stub_committed_outcomes|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.wrongBoolFixture_nonempty|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.stubPausePost_logs|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.stubPausePost_refundCounter|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.stubPausePost_accountsToDelete|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.stubPausePost_accessedAddresses|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.stubPausePost_accessedStorageKeys|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.stubPausePost_transientStorage|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.stubPausePost_state|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.stubPause_cold_runCompiledTo|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.stubQuery_true_warm_runCompiledTo|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.stubMain_pause_cold_runCompiledTo|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.stubMain_query_true_warm_runCompiledTo|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.stubProgram_pause_cold_runCompiledTo|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.stubProgram_query_true_warm_runCompiledTo|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.sliceD_stagedCalldata|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.sliceD_stagedSelector|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.stubPause_exec|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.stubQuery_exec|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.pauseAfterSet_stub_toSuccess_runCompiled|$STANDARD
Blanc.LidoCircuitBreaker.stubPauseWorldState_get_breaker|$STANDARD
Blanc.LidoCircuitBreaker.stubPauseWorldState_get_target|$STANDARD
Blanc.LidoCircuitBreaker.stubPauseWorld_targetCode|$STANDARD
Blanc.LidoCircuitBreaker.stubPauseWorld_codeBytes|$STANDARD
Blanc.LidoCircuitBreaker.stubPauseWorld_currentTarget|$STANDARD
Blanc.LidoCircuitBreaker.stubPauseWorld_callerWord|$STANDARD
Blanc.LidoCircuitBreaker.stubPauseWorld_getStorVal|$STANDARD
Blanc.LidoCircuitBreaker.stubPauseWorld_targetCodeAt|$STANDARD
Blanc.LidoCircuitBreaker.stubPauseWorld_publicPausePremises|$STANDARD
Blanc.LidoCircuitBreaker.stubPauseWorld_target_ne_owner|$STANDARD
Blanc.LidoCircuitBreaker.stubPauseWorld_closedPublicPause|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.benignCallFixture_nonempty|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetControl.benignCall_nonchildless_noninterference_closed|$STANDARD
Blanc.ProxyPair.implementationSlotLit_eq_slot|$STANDARD
Blanc.ProxyPair.proxyProg_compiles|$STANDARD
Blanc.ProxyPair.proxyProg_compile|$STANDARD
Blanc.ProxyPair.proxyBytes_length|$STANDARD
Blanc.ProxyPair.proxyCode_notDelegation|$STANDARD
Blanc.ProxyPair.implGuardedProg_compiles|$STANDARD
Blanc.ProxyPair.implGuardedProg_compile|$STANDARD
Blanc.ProxyPair.implGuardedBytes_length|$STANDARD
Blanc.ProxyPair.implGuardedCode_notDelegation|$STANDARD
Blanc.ProxyPair.implSlot_ne_implementationSlot|$STANDARD
Blanc.ProxyPair.implSlot_ne_adminSlot|$STANDARD
Blanc.ProxyPair.implSlot_ne_beaconSlot|$STANDARD
Blanc.ProxyPair.implementationSlot_ne_implSlot|$STANDARD
Blanc.ProxyPair.adminSlot_ne_implSlot|$STANDARD
Blanc.ProxyPair.beaconSlot_ne_implSlot|$STANDARD
Blanc.ProxyPair.implBodyGas_eq|
Blanc.ProxyPair.implGuardedSuccessGas_eq|
Blanc.ProxyPair.implGuardedRevertGas_eq|
Blanc.ProxyPair.implGuardedSuccessEntryGas_eq|
Blanc.ProxyPair.implGuardedRevertEntryGas_eq|
Blanc.ProxyPair.implSuccess_runCompiledTo|$STANDARD
Blanc.ProxyPair.implGuarded_runCompiledTo_nonzero|$STANDARD
Blanc.ProxyPair.implGuarded_runCompiledTo_zero|$STANDARD
Blanc.ProxyPair.implGuarded_static_sstore_halt|$STANDARD
Blanc.ProxyPair.implGuarded_static_halt_exec|$STANDARD
Blanc.ProxyPair.proxyAdr_ne_implAdr|
Blanc.ProxyPair.pairState_proxyAcct|$STANDARD
Blanc.ProxyPair.pairState_implAcct|$STANDARD
Blanc.ProxyPair.pairState_proxyCode|$STANDARD
Blanc.ProxyPair.pairState_implCode|$STANDARD
Blanc.ProxyPair.pairState_proxySlot|$STANDARD
Blanc.ProxyPair.pairState_implSlot_zero|$STANDARD
Blanc.ProxyPair.pairState_proxyImplSlot_zero|$STANDARD
Blanc.ProxyPair.successData_length|propext
Blanc.ProxyPair.revertData_length|propext
Blanc.ProxyPair.proxy_call_gas_split|
Blanc.ProxyPair.pairBenv_impl_not_precompile|$STANDARD
Blanc.ProxyPair.proxyMsgSuccess_code|$STANDARD
Blanc.ProxyPair.proxyMsgRevert_code|$STANDARD
Blanc.ProxyPair.proxyMsgSuccess_data|$STANDARD
Blanc.ProxyPair.proxyMsgRevert_data|$STANDARD
Blanc.ProxyPair.proxyMsgSuccess_gas|$STANDARD
Blanc.ProxyPair.proxyMsgRevert_gas|$STANDARD
Blanc.ProxyPair.proxyMsgSuccess_target|$STANDARD
Blanc.ProxyPair.proxyMsgRevert_target|$STANDARD
Blanc.ProxyPair.proxyMsgSuccess_caller|$STANDARD
Blanc.ProxyPair.proxyMsgRevert_caller|$STANDARD
Blanc.ProxyPair.proxyFallback_eq_prefix|$STANDARD
Blanc.ProxyPair.proxySuccessChildMsg_exec|$STANDARD
Blanc.ProxyPair.proxyProg_success_runCompiledTo|$STANDARD
Blanc.ProxyPair.proxyRevertChildMsg_exec|$STANDARD
Blanc.ProxyPair.proxyProg_revert_runCompiledTo|$STANDARD
Blanc.ProxyPair.forwardBudgetWitness_27224|propext
Blanc.ProxyPair.forwardBudget_27224|propext
Blanc.ProxyPair.proxyCorrespondenceMsg_premises|$STANDARD
Blanc.ProxyPair.processMessage_correspondence_premises_satisfiable|$STANDARD
Blanc.ProxyPair.processMessage_correspondence|$STANDARD
Blanc.ProxyPair.processMessage_static_halt_to_revert|$STANDARD
Blanc.ProxyPair.processMessage_property_transport|$STANDARD
Blanc.ProxyPair.settledObservable_rejects_direct_clean_proxy_error|$STANDARD
Blanc.ProxyPair.settledObservable_rejects_direct_error_proxy_clean|$STANDARD
Blanc.ProxyPair.settledObservable_rejects_output_mismatch|$STANDARD
Blanc.ProxyPair.settledObservable_rejects_outer_ok_error|$STANDARD
Blanc.ProxyPair.settledObservable_rejects_outer_error_ok|$STANDARD
Blanc.ProxyPair.settledObservable_rejects_reverse_revert_halt|$STANDARD
Blanc.ProxyPair.proxy_entrySstoreFree|$STANDARD
Blanc.ProxyPair.implGuarded_entrySstoreFree_rejected|$STANDARD
Blanc.ProxyPair.proxyProg_success_successfulSstore_sourceSite|$STANDARD
Blanc.ProxyPair.proxyProg_revert_successfulSstore_sourceSite|$STANDARD
Blanc.ProxyPair.ossifiableCreateMessageGas_eq|
Blanc.ProxyPair.ossifiableConstructorProgram_canonicalEmptyInput_runCompiled|$STANDARD
Blanc.ProxyPair.ossifiableConstructorProgram_canonicalEmptyInput_forward_exact|$STANDARD
Blanc.ProxyPair.processCreateMessage_ossifiable_emptySetup_success|$STANDARD
Blanc.ProxyPair.ossifiableConstructorProgram_nonempty_success|$STANDARD
Blanc.ProxyPair.processCreateMessage_ossifiable_failure_rollback|$STANDARD
Blanc.ProxyPair.OssifiableCreateFixture.message_code|$STANDARD
Blanc.ProxyPair.OssifiableCreateFixture.implementation_code|$STANDARD
Blanc.ProxyPair.OssifiableCreateFixture.message_success|$STANDARD
Blanc.ProxyPair.OssifiableBothSlotFixture.setupMain_compile|$STANDARD
Blanc.ProxyPair.OssifiableBothSlotFixture.setupMain_runCompiledTo|$STANDARD
Blanc.ProxyPair.OssifiableBothSlotFixture.message_success|$STANDARD
Blanc.ProxyPair.OssifiableBothSlotCreateFixture.program_success|$STANDARD
Blanc.ProxyPair.OssifiableBothSlotCreateFixture.bothSlotCreateMessageGas_eq|
Blanc.ProxyPair.OssifiableBothSlotCreateFixture.creationMessage_code|$STANDARD
Blanc.ProxyPair.OssifiableBothSlotCreateFixture.creationMessage_success|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.lidoTwgCode_compile|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.abiEncodeConstructorArgs_length|propext
Blanc.LidoTriggerableWithdrawalsGateway.creation_template_runtime_suffix|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.full_create_input_length|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.pauseFor_absent_role_reverts|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.pauseUntil_absent_role_reverts|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.resume_absent_role_reverts|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.setExitRequestLimit_absent_role_reverts|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.grantRole_absent_role_reverts|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.revokeRole_absent_role_reverts|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.triggerFullWithdrawals_absent_role_reverts|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.triggerFullWithdrawals_authorized_paused_reverts|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.triggerFullWithdrawals_reaches_afterValidation|$STANDARD
Blanc.prorataCode_compile|$STANDARD
Blanc.Prorata.classify_prorata_exec_route|$STANDARD
Blanc.Prorata.classify_prorata_exec_success|$STANDARD
Blanc.Prorata.prorata_deposit_exec_effect|$STANDARD
Blanc.Prorata.prorata_withdraw_exec_effect|$STANDARD
Blanc.Prorata.prorata_convertToShares_exec_effect|$STANDARD
Blanc.Prorata.prorata_convertToAssets_exec_effect|$STANDARD
Blanc.Prorata.prorata_convertToShares_eq_deposit_mint|$STANDARD
Blanc.Prorata.prorata_convertToAssets_eq_withdraw_pay|$STANDARD
Blanc.Prorata.deposit_effect|$STANDARD
Blanc.Prorata.withdraw_settles_before_call|$STANDARD
Blanc.Prorata.withdraw_pays_exactly|$STANDARD
Blanc.Prorata.convertToShares_effect|$STANDARD
Blanc.Prorata.convertToAssets_effect|$STANDARD
Blanc.Prorata.convertToShares_eq_deposit_mint|$STANDARD
Blanc.Prorata.convertToAssets_eq_withdraw_pay|$STANDARD
Blanc.Prorata.deposit_quote_toNat|$STANDARD
Blanc.Prorata.withdraw_quote_toNat|$STANDARD
Blanc.Prorata.mintN_never_overmints|propext
Blanc.Prorata.payN_never_overpays|propext
Blanc.Prorata.payN_le_balance|propext, Quot.sound
Blanc.Prorata.Inv.withdraw_pay_word_le_balance|$STANDARD
Blanc.Prorata.deposit_price_nondecreasing|propext, Quot.sound
Blanc.Prorata.withdraw_price_nondecreasing|propext, Quot.sound
Blanc.Prorata.withdraw_ceil_shares_covers_assets|propext, Quot.sound
Blanc.Prorata.deposit_floor_shares_ceil_assets_le|$STANDARD
Blanc.Prorata.mintN_residue_eq|propext
Blanc.Prorata.payN_residue_eq|propext
Blanc.Prorata.roundtrip_dust_eq|propext, Quot.sound
Blanc.Prorata.immediate_roundtrip_loss_le|$STANDARD
Blanc.Prorata.prorataSpec_sound|$STANDARD
Blanc.Prorata.prorataSpec_preserves|$STANDARD
Blanc.Prorata.DeploymentRoot.reachable_stateInv|$STANDARD
Blanc.Prorata.DeploymentRoot.reachable_accountingInvariant|$STANDARD
Blanc.Prorata.ProrataAccountingPath.prorata_dust_trace_exact|$STANDARD
Blanc.Prorata.retainedMessageCallAccountingReplay|$STANDARD
Blanc.Prorata.retainedTransactionAccountingReplay|$STANDARD
Blanc.Prorata.retainedTransactionListAccountingReplay|$STANDARD
Blanc.Prorata.retainedSystemMessageAccountingReplay|$STANDARD
Blanc.Prorata.retainedRequestsAccountingReplay|$STANDARD
Blanc.Prorata.retainedDirectWithdrawalAccountingReplay|$STANDARD
Blanc.Prorata.retainedBodyAccountingReplay|$STANDARD
Blanc.Prorata.retainedConfiguredBlockAccountingReplay|$STANDARD
Blanc.Prorata.retainedConfiguredHistoryAccountingReplay|$STANDARD
Blanc.Prorata.ProrataTraceRealizes.toReachUsing|$STANDARD
Blanc.Prorata.ProrataTraceRealizes.toAccountingReplay|$STANDARD
Blanc.Prorata.prorataTraceRealizes_exists_of_reachUsing|$STANDARD
Blanc.Prorata.prorata_realized_dust_trace_exact|$STANDARD
Blanc.Prorata.attacker_open_context|$STANDARD
Blanc.Prorata.attacker_no_profit|$STANDARD
Blanc.Prorata.victim_loss_bound|$STANDARD
Blanc.Composition.ProrataWethVault.readTotalAssets_capacity_body_effect|$STANDARD
Blanc.Composition.ProrataWethVault.maxMint_body_effect|$STANDARD
Blanc.Composition.ProrataWethVault.maxDeposit_body_effect|$STANDARD
Blanc.Composition.ProrataWethVault.maxWithdraw_body_effect|$STANDARD
Blanc.Composition.ProrataWethVault.maxMint_compiled_effect|$STANDARD
Blanc.Composition.ProrataWethVault.maxDeposit_compiled_effect|$STANDARD
Blanc.Composition.ProrataWethVault.maxWithdraw_compiled_effect|$STANDARD
Blanc.Composition.ProrataWethVault.maxMint_compiled_effect_stable|$STANDARD
Blanc.Composition.ProrataWethVault.maxDeposit_compiled_effect_stable|$STANDARD
Blanc.Composition.ProrataWethVault.maxWithdraw_compiled_effect_exact|$STANDARD
Blanc.Composition.ProrataWethVault.deposit_compiled_effect|$STANDARD
Blanc.Composition.ProrataWethVault.mint_compiled_effect|$STANDARD
Blanc.Composition.ProrataWethVault.withdraw_compiled_effect|$STANDARD
Blanc.Composition.ProrataWethVault.redeem_compiled_effect|$STANDARD
Blanc.ProrataWethVault.approve_compiled_effect|$STANDARD
Blanc.ProrataWethVault.transfer_compiled_effect|$STANDARD
Blanc.ProrataWethVault.transferFrom_compiled_effect|$STANDARD
Blanc.ProrataWethVault.roundtrip_loss_le|$STANDARD
Blanc.ProrataWethVault.redemption_le_assets|propext, Quot.sound
Blanc.ProrataWethVault.victim_loss_le|$STANDARD
Blanc.ProrataWethVault.victim_loss_le_over_history|$STANDARD
Blanc.ProrataWethVault.dust_trace_exact|$STANDARD
Blanc.ProrataWethVault.depositStep|
Blanc.ProrataWethVault.redeemStep|
Blanc.ProrataWethVault.donationStep|
Blanc.ProrataWethVault.two_le_offsetN|
Blanc.ProrataWethVault.attacker_open_context|$STANDARD
Blanc.ProrataWethVault.attacker_no_profit|$STANDARD
Blanc.ProrataWethVault.victim_loss_bound|$STANDARD
Blanc.ProrataWethVault.attack_carrier_inhabited|$STANDARD
Blanc.ProrataWethVault.transferStaged_storesOrHalts|$STANDARD
Blanc.ProrataWethVault.withdrawBurn_storesOrHalts|$STANDARD
Blanc.ProrataWethVault.redeemBurn_storesOrHalts|$STANDARD
Blanc.ProrataWethVault.callWethTransferFrom_storesOrHalts|$STANDARD
Blanc.ProrataWethVault.finishInbound_storesOrHalts|$STANDARD
Blanc.ProrataWethVault.inboundAfterQuote_storesOrHalts|$STANDARD
Blanc.ProrataWethVault.depositAfterQuote_storesOrHalts|$STANDARD
Blanc.ProrataWethVault.mintAfterQuote_storesOrHalts|$STANDARD
Blanc.ProrataWethVault.depositAfterQuote_not_static|$STANDARD
Blanc.ProrataWethVault.mintAfterQuote_not_static|$STANDARD
Blanc.ProrataWethVault.mint_never_overmints|propext, Quot.sound
Blanc.ProrataWethVault.withdraw_never_overpays|propext, Quot.sound
Blanc.Frame.enter_run_benvStat|$STANDARD
Blanc.RunFrame.benvStat_eq|$STANDARD
Blanc.genericCall.step_spawn_benvStat|$STANDARD
Blanc.genericCreate.step_spawn_benvStat|$STANDARD
Blanc.Xinst.step_spawn_benvStat|$STANDARD
Blanc.Composition.ProrataWethVault.vault_rely_preserves_conserved|$STANDARD
Blanc.Composition.ProrataWethVault.vault_rely_preserves|$STANDARD
Blanc.Composition.ProrataWethVault.inboundEffect_accountingStep|$STANDARD
Blanc.Composition.ProrataWethVault.outboundEffect_accountingStep|$STANDARD
Blanc.Composition.ProrataWethVault.silent_accountingStep|$STANDARD
Blanc.Composition.ProrataWethVault.transferEffect_accountingStep|$STANDARD
Blanc.Composition.ProrataWethVault.approveEffect_accountingStep|$STANDARD
Blanc.Composition.ProrataWethVault.silent_accountingStep_of_view|$STANDARD
Blanc.Composition.ProrataWethVault.readOnlyEffect_accountingStep|$STANDARD
Blanc.Composition.ProrataWethVault.transferFromEffect_accountingStep|$STANDARD
Blanc.Composition.ProrataWethVault.nonflow_message_accountingStep|$STANDARD
Blanc.Composition.ProrataWethVault.deposit_compiled_effect_named|$STANDARD
Blanc.Composition.ProrataWethVault.deposit_message_accountingStep|$STANDARD
Blanc.Composition.ProrataWethVault.redeem_compiled_effect_named|$STANDARD
Blanc.Composition.ProrataWethVault.redeem_message_accountingStep|$STANDARD
Blanc.Composition.ProrataWethVault.SteppedMessages.toPath|$STANDARD
Blanc.Composition.ProrataWethVault.SteppedMessages.victim_loss_le|$STANDARD
Blanc.Composition.ProrataWethVault.PairBacked.donation|$STANDARD
Blanc.Prorata.ProrataAccountingPath.priceLe_first_last|propext, Quot.sound
Blanc.Composition.ProrataWethVault.vault_message_preserves_conserved|$STANDARD
Blanc.Composition.ProrataWethVault.vault_nonflow_message_preserves_conserved|$STANDARD
Blanc.Composition.ProrataWethVault.ConfiguredRoot.conserved|$STANDARD
Blanc.Composition.ProrataWethVault.ConfiguredRoot.backed|$STANDARD
Blanc.Composition.ProrataWethVault.ConfiguredMessages.preserves_conserved|$STANDARD
Blanc.Composition.ProrataWethVault.ConfiguredRoot.chain_conserved|$STANDARD
Blanc.Exec.Deriv.SourceCursor.branchFlagToward|$STANDARD
Blanc.Exec.Deriv.SourceCursor.Toward.selectBranchZero|$STANDARD
Blanc.Func.localExecFree_iff|propext, Quot.sound
Blanc.Prog.componentExecFree_iff|propext, Quot.sound
Blanc.Prog.reachableExecFree_iff|propext, Quot.sound
Blanc.Exec.Deriv.SourceCursor.Toward.linearDispatchWith_selectedBody|$STANDARD
Blanc.Exec.Deriv.SourceCursor.noExec_of_reachableExecFree|$STANDARD
Blanc.Exec.noExecOccurrence_of_no_sameFrame_execAt|$STANDARD
Blanc.Exec.noRetainedWriteTo_of_no_sameFrame_execAt|$STANDARD
Blanc.Exec.noExecOccurrence_of_exactMain_reachableExecFree|$STANDARD
Blanc.Exec.noRetainedWriteTo_of_exactMain_reachableExecFree|$STANDARD
Blanc.ReachableExecFreeControl.routeControlProgram_not_reachableExecFree|propext, Quot.sound
Blanc.LidoTriggerableWithdrawalsGateway.pinnedPauseTarget_circuitBreaker_noninterference|$STANDARD
Blanc.BeaconDeposit.div_mul_eq_sub_mod|propext, Quot.sound
Blanc.BeaconDeposit.pred_div_eq|propext, Quot.sound
Blanc.BeaconDeposit.pred_mod_of_pos|propext, Quot.sound
Blanc.BeaconDeposit.pred_mod_eq|propext, Quot.sound
Blanc.BeaconDeposit.pred_div_pow_eq|propext, Quot.sound
Blanc.BeaconDeposit.mod_two_pow_eq_zero_iff|$STANDARD
Blanc.BeaconDeposit.rootAt_nil|propext
Blanc.BeaconDeposit.rootAt_short|propext
Blanc.BeaconDeposit.rootAtE_eq|propext
Blanc.BeaconDeposit.rootAt_append|propext, Quot.sound
Blanc.BeaconDeposit.empty_inv|$STANDARD
Blanc.BeaconDeposit.pending_step_even|$STANDARD
Blanc.BeaconDeposit.pending_step_odd|$STANDARD
Blanc.BeaconDeposit.rootAt_pending_even|$STANDARD
Blanc.BeaconDeposit.rootAt_pending_odd|$STANDARD
Blanc.BeaconDeposit.climb_spec|$STANDARD
Blanc.BeaconDeposit.root_correct|$STANDARD
Blanc.BeaconDeposit.empty_root|$STANDARD
Blanc.BeaconDeposit.div_two_div_pow|propext
Blanc.BeaconDeposit.div_pow_div_two|propext
Blanc.BeaconDeposit.walk_eq_none_iff|propext, Quot.sound
Blanc.BeaconDeposit.walk_isSome_iff|$STANDARD
Blanc.BeaconDeposit.walk_none_at_cap|$STANDARD
Blanc.BeaconDeposit.insert_isSome_iff|$STANDARD
Blanc.BeaconDeposit.take_drop_append|propext, Quot.sound
Blanc.BeaconDeposit.mod_pow_ge_of_bit|$STANDARD
Blanc.BeaconDeposit.mod_pow_ge_of_two_bits|$STANDARD
Blanc.BeaconDeposit.bit_zero_of_mod_zero|$STANDARD
Blanc.BeaconDeposit.completedBlock_pred|$STANDARD
Blanc.BeaconDeposit.walk_insert_spec|$STANDARD
Blanc.BeaconDeposit.insert_spec|$STANDARD
Blanc.BeaconDeposit.deposit_ne_assert_false|$STANDARD
Blanc.BeaconDeposit.deposit_ok_spec|$STANDARD
Blanc.BeaconDeposit.deposit_inv|$STANDARD
Blanc.BeaconDeposit.le64_length|
Blanc.BeaconDeposit.zeros_length|propext
Blanc.BeaconDeposit.le64_zero|
Blanc.BeaconDeposit.hashPair_input_length|propext
Blanc.BeaconDeposit.mixIn_input_length|propext
Blanc.BeaconDeposit.pubkeyRoot_input_length|propext
Blanc.BeaconDeposit.signatureRoot_input_lengths|propext, Quot.sound
Blanc.BeaconDeposit.depositDataNode_input_lengths|propext
Blanc.BeaconDeposit.code_compile|$STANDARD
Blanc.BeaconDeposit.code_eip170|$STANDARD
Blanc.BeaconDeposit.constructorInitPrefix_compile|$STANDARD
Blanc.BeaconDeposit.creationCode_eip3860|$STANDARD
Blanc.BeaconDeposit.deposit_success_settled_effects|$STANDARD
Blanc.BeaconDeposit.deposit_success_retainedStorageEffectTriples|$STANDARD
Blanc.BeaconDeposit.deposit_pubkeyLength_error_runCompiledTo|$STANDARD
Blanc.BeaconDeposit.deposit_withdrawalCredentialsLength_error_runCompiledTo|$STANDARD
Blanc.BeaconDeposit.deposit_signatureLength_error_runCompiledTo|$STANDARD
Blanc.BeaconDeposit.deposit_valueTooLow_error_runCompiledTo|$STANDARD
Blanc.BeaconDeposit.deposit_valueNotGweiMultiple_error_runCompiledTo|$STANDARD
Blanc.BeaconDeposit.deposit_valueTooHigh_error_runCompiledTo|$STANDARD
Blanc.BeaconDeposit.deposit_depositDataRootMismatch_error_runCompiledTo|$STANDARD
Blanc.BeaconDeposit.deposit_merkleTreeFull_error_runCompiledTo|$STANDARD
Blanc.BeaconDeposit.deposit_error_runCompiledTo|$STANDARD
Blanc.BeaconDeposit.deposit_malformed_noRawSstore|$STANDARD
Blanc.BeaconDeposit.noMatchSelector_runCompiledTo|$STANDARD
Blanc.BeaconDeposit.unmatched_selector_noRawSstore|$STANDARD
Blanc.BeaconDeposit.supportsInterface_runCompiled|$STANDARD
Blanc.BeaconDeposit.supportsInterface_nonzero_value_runCompiledTo|$STANDARD
Blanc.BeaconDeposit.supportsInterface_runCompiled_noRawSstore|$STANDARD
Blanc.BeaconDeposit.supportsInterface_nonzero_value_runCompiledTo_noRawSstore|$STANDARD
Blanc.BeaconDeposit.supportsInterface_short_calldata_runCompiledTo_noRawSstore|$STANDARD
Blanc.BeaconDeposit.getDepositRoot_zero_runCompiled|$STANDARD
Blanc.BeaconDeposit.getDepositRoot_nonzero_value_runCompiledTo|$STANDARD
Blanc.BeaconDeposit.getDepositRoot_zero_runCompiled_noRawSstore|$STANDARD
Blanc.BeaconDeposit.getDepositRoot_nonzero_value_runCompiledTo_noRawSstore|$STANDARD
Blanc.BeaconDeposit.getDepositCount_warm_runCompiled|$STANDARD
Blanc.BeaconDeposit.getDepositCount_cold_runCompiled|$STANDARD
Blanc.BeaconDeposit.getDepositCount_nonzero_value_runCompiledTo|$STANDARD
Blanc.BeaconDeposit.getDepositCount_warm_runCompiled_noRawSstore|$STANDARD
Blanc.BeaconDeposit.getDepositCount_cold_runCompiled_noRawSstore|$STANDARD
Blanc.BeaconDeposit.getDepositCount_nonzero_value_runCompiledTo_noRawSstore|$STANDARD
Blanc.BeaconDeposit.Exec.NinstOccurrence.beaconRuntime_sstore_pc_of_rawFrameRoot|$STANDARD
Blanc.BeaconDeposit.Exec.Deriv.beaconConstructor_sstore_coordinate|$STANDARD
Blanc.BeaconDeposit.constructor_success_retainedStorageEffectTriples|$STANDARD
Blanc.BeaconDeposit.ArtifactInv.root_eq_mixedRootOf|$STANDARD
Blanc.BeaconDeposit.ArtifactInv.count_eq_history_length|$STANDARD
Blanc.BeaconDeposit.constructorFinalStorage_artifactInv|$STANDARD
Blanc.BeaconDeposit.deposit_success_artifactInv|$STANDARD
Blanc.BeaconDeposit.canonicalDeploymentStep_establishes_root|$STANDARD
Blanc.BeaconDeposit.DeploymentRoot.constructorOccurrence|$STANDARD
Blanc.BeaconDeposit.historySpec_sound|$STANDARD
Blanc.BeaconDeposit.historySpec_preserves|$STANDARD
Blanc.BeaconDeposit.pragueOnly_history_extends|$STANDARD
Blanc.BeaconDeposit.DeploymentRoot.future_history_extends|$STANDARD
Blanc.BeaconDeposit.DeploymentRoot.future_count_root|$STANDARD
Blanc.compact_pause_word_eq_projection|$STANDARD
Blanc.LidoCircuitBreaker.PinnedTargetStubWalk.stubPause_sentinel_execution|$STANDARD
Blanc.Func.RunCompiledTo.zero_branch_of_ok_of_right_not_ok|$STANDARD
Blanc.Func.RunCompiledTo.zero_branch_of_ok_call_revert|$STANDARD
Blanc.Func.RunCompiledTo.zero_branch_of_ok_of_right_not_ok_of_prefix|$STANDARD
Blanc.Func.RunCompiledTo.zero_branch_of_ok_call_revert_of_prefix|$STANDARD
Blanc.acceptedBoolWord_iff_of_output|$STANDARD
Blanc.acceptedBoolExecution_ok_iff|$STANDARD
Blanc.boolQueryExecutionFailure_ok_iff|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.Trigger.rebaseLocalCalls_prependStoresRev|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.Trigger.rebaseLocalCalls_revertData|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.runtime_guard_zero_of_prog_run_ok|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.runtime_rebasedTriggerMalformedAbi_get|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.triggerFullWithdrawals_ok_reaches_afterValidation|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.triggerFullWithdrawals_selected_paused_not_ok|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.pinnedPauseTarget_pauseFor_effect|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.pinnedPauseTarget_isPaused_truthful|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.pinnedPauseTarget_protectedSurface_reverts|$STANDARD
Blanc.LidoTriggerableWithdrawalsGateway.pinnedPauseTarget|$STANDARD
Blanc.LidoCircuitBreaker.directBoundaryExecutions_of_afterSet_ok|$STANDARD
Blanc.Composition.LidoCircuitBreakerTwg.pauseForCalldata_eq|$STANDARD
Blanc.Composition.LidoCircuitBreakerTwg.isPausedCalldata_eq|$STANDARD
Blanc.Composition.LidoCircuitBreakerTwg.gateway_lidoPinnedPauseTarget|$STANDARD
Blanc.Composition.LidoCircuitBreakerTwg.gatewayCode_compile|$STANDARD
Blanc.Composition.LidoCircuitBreakerTwg.gatewayBoundaryExecutions_of_afterSet_ok|$STANDARD
Blanc.Composition.LidoCircuitBreakerTwg.publicPause_gatewayPinnedTarget|$STANDARD
Blanc.Composition.LidoCircuitBreakerTwg.gatewayPauseWorld_publicPausePremises|$STANDARD
Blanc.Composition.LidoCircuitBreakerTwg.gatewayPauseWorld_closedPremises|$STANDARD"
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
PRINTED="$(grep -oE '^#print axioms[[:space:]]+[A-Za-z0-9_.?]+' \
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
