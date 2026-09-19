# PRORATA WETH vault — theorem-to-claim map

Which theorem carries which sentence of the frozen claim
(`~/plans/reports/prorata-erc4626-port-sf.md` §12), which sentences are
carried only by finite evidence, and which are **not carried**.

## Audit status of the names below

Every name below is audited: it appears in `scripts/AxiomCheck.lean` and is
pinned in `scripts/check.sh` at the axiom set its proof achieves (`$STANDARD`,
or for some `Nat` lemmas a strict subset of it), so
`scripts/check.sh --no-build` fails if its axiom set moves. The map names nothing outside that set: the 89
vault names pinned before 2026-09-19, plus the rows approved on 2026-09-19
(decision `vault-axiom-audit-rows-20260919`), which are marked †. This map is
merged only together with those † rows, never ahead of them. An axiom pin fixes
a theorem's axioms, not its statement; nothing here relies on a statement pin.

Names are given unqualified. Those in `Blanc/ProrataWethVault*.lean` live in
`Blanc.ProrataWethVault`; those in `Blanc/Composition/ProrataWethVault*.lean`
live in `Blanc.Composition.ProrataWethVault`; the generic
`Prog.runCompiledTo_of_exec_revert` lives in `Blanc` (`Blanc/RevertCause.lean`).

## Scope of every statement

These apply to every row below and to any sentence quoted from this map.

- **Exact compiled contracts only.** Every theorem is about the compiled Blanc
  vault program and the exact inherited Blanc WETH runtime, installed directly
  at configured distinct accounts (`PairRoot`). None of them is about WETH9, the
  OpenZeppelin reference, or any deployed code, and no CREATE transaction is
  covered.
- **Partial correctness.** A compiled-effect theorem describes every
  *successful* run: it takes the run as a hypothesis. It does not say that a
  call succeeds.
- **The D9 premise.** The chain-level headlines take
  `NoVaultVisitKeyCollision (history.pairVisits vault) vault`. Over the WETH
  allowance pairs that the history's frames visit, no pair whose owner is the
  vault shares a hashed WETH allowance key with a different written pair. It is
  a finite, trace-local noncollision premise on Keccak outputs, approved at SF
  §13 (D9). It is not a global injectivity theorem, and it is never discharged.
- **Raw universe.** `history.pairVisits` ranges over raw frames, including
  frames that committed and were later rolled back by an enclosing revert. So
  D9 is required of rolled-back allowance frames as well. That is a stronger
  premise than a condition on settled effects, and a checker of it needs full
  call traces, not receipts.
- **P3 and P4 are existential.** Their chain-level forms conclude that *some*
  realization `steps` exists: `PairTraceRealizes root steps future` and
  `PairLedgerFaithful vault history steps`. The accounting is then stated for
  that list. They are statements about some realization faithful to the chain,
  not about the executed operations as such.
- **Membership-only faithfulness.** `PairLedgerFaithful` says that each
  realized record's allowance visit is a member of the history's visits. It
  does not fix order or multiplicity, and it is not one-to-one.
- **Induced inbound visits.** The realized ledger's `deposit`/`mint` entries
  are matched by visits induced from the vault's own frame, not by a located
  WETH `transferFrom` child frame.
- **WETH credits wrap.** The exact Blanc WETH credit is a bare addition modulo
  2^256 (SF Amendment A2, half 1). The finite evidence follows that behaviour.
  WETH's solvency invariant `State.Inv`, which `pair_history_backed` proves
  at every configured pair state under D9, excludes a wrapping credit to the
  vault row there (see deviation row 6).

## Carried by theorems

| Claim sentence | Theorem(s) |
|---|---|
| Deposit, mint, withdraw and redeem have the stated exact effects: pre-transfer quote, exact WETH child, share mint or burn, return word, logs | `deposit_compiled_effect`, `mint_compiled_effect`, `withdraw_compiled_effect`, `redeem_compiled_effect`; `deposit_compiled_effect_named`, `redeem_compiled_effect_named` |
| The views return the stated exact words: metadata, `asset`, WETH-backed `totalAssets`, supply, balances, allowances | `name_compiled_effect`†, `symbol_compiled_effect`†, `decimals_compiled_effect`†, `asset_compiled_effect`†, `totalAssets_compiled_effect`†, `totalSupply_compiled_effect`†, `balanceOf_compiled_effect`†, `allowance_compiled_effect`† |
| The converters and the four previews return the exact floor/ceil formulas | `convertToShares_compiled_effect`†, `convertToAssets_compiled_effect`†, `previewDeposit_compiled_effect`†, `previewMint_compiled_effect`†, `previewWithdraw_compiled_effect`†, `previewRedeem_compiled_effect`† |
| The `max*` views return the exact frozen formulas | `maxMint_compiled_effect`, `maxDeposit_compiled_effect`, `maxWithdraw_compiled_effect`, `maxRedeem_compiled_effect`†; at a stable state `maxMint_compiled_effect_stable`, `maxDeposit_compiled_effect_stable`, `maxWithdraw_compiled_effect_exact`; the body effects `maxMint_body_effect`, `maxDeposit_body_effect`, `maxWithdraw_body_effect`, `readTotalAssets_capacity_body_effect`; the resource discharge `Source.totalAssetsResources_of_run` |
| P1 — exact operation rounding: each flow is the exact formula, never overmints, undercharges, underburns or overpays, with a strict one-quantum residue bound | the four flow effects above, which fix deposit's mint at `convertToSharesN`, mint's charge at `previewMintN`, withdraw's burn at `previewWithdrawN` and redeem's payout at `previewRedeemN`; with `convertToSharesN_floor_le`†, `convertToSharesN_lt_floor_add_one`†, `convertToAssetsN_floor_le`†, `convertToAssetsN_lt_floor_add_one`†, `previewMintN_covers`†, `previewMintN_lt_add_denominator`†, `previewWithdrawN_covers`†, `previewWithdrawN_lt_add_assetFactor`†; and the cross-direction bounds `mint_never_overmints`, `withdraw_never_overpays` |
| P2, previews half — at the same state, each preview equals the successful actual | jointly, with no single named P2 theorem: each preview effect above and the matching flow effect return the same formula of the same pre-state `(A, S)`. The capacity half is the next row |
| P2, capacity half — capacity is honest: each `max*` is nonreverting and reachable against the vault's own constraints | Carried, as revert-cause statements about the actual execution, not as liveness. **Flows.** At a stable pair state (`PairStable`: proved at the root, `PairStable.of_root`†, and at a state the real chain reaches from it only under D9, `pair_history_stable`), with the named call-validity conditions (zero value, the static ABI head, a nonzero caller, a canonical nonzero receiver and owner, and for a delegated `withdraw`/`redeem` a collision-free allowance key and a covering allowance), if the frame's execution of the exact compiled vault code reverts on `deposit`/`mint`/`withdraw`/`redeem` of an amount at most the corresponding `max*` view's value, then its reverting walk ran a refused exact-WETH child: a `CALL`/`STATICCALL` to the configured WETH account that pushed status 0 — `deposit_exec_revert_visits_refused_weth_child`†, `mint_exec_revert_visits_refused_weth_child`†, `withdraw_exec_revert_visits_refused_weth_child`†, `redeem_exec_revert_visits_refused_weth_child`†. **Views.** With the views' own call-validity conditions (zero call value, calldata covering the one-word argument head, and a canonical address argument, `ValidAdr (Sevm.argWord sevm 0)`), under the direct WETH configuration `maxDeposit`/`maxMint`/`maxWithdraw` revert only through a refused `balanceOf` — `maxDeposit_exec_revert_visits_refused_weth_child`†, `maxMint_exec_revert_visits_refused_weth_child`†, `maxWithdraw_exec_revert_visits_refused_weth_child`† — and, under those call-validity conditions alone, `maxRedeem` never reverts — `maxRedeem_exec_never_reverts`†. **Tightness.** Every successful flow is within `max*` — `deposit_success_within_maxDeposit`†, `mint_success_within_maxMint`†, `withdraw_success_within_maxWithdraw`†, `redeem_success_within_maxRedeem`† — so at the vault's own guards `max*` is exactly the largest accepted amount (`le_maxMintN_iff`†, `le_maxDepositN_iff`†, `le_maxWithdrawN_iff`†, `convertToSharesN_maxDepositN_le_shareRoom`†, with the stable-state view identities `maxDepositViewN_eq_of_stable`†, `maxMintViewN_eq_of_stable`†, `maxWithdrawViewN_eq_of_stable`†). The exec-level forms bind the total interpreter through `Prog.runCompiledTo_of_exec_revert`†; their walk-level cores are `deposit_revert_visits_refused_weth_child`†, `mint_revert_visits_refused_weth_child`†, `withdraw_revert_visits_refused_weth_child`†, `redeem_revert_visits_refused_weth_child`†, `maxDeposit_revert_visits_refused_weth_child`†, `maxMint_revert_visits_refused_weth_child`†, `maxWithdraw_revert_visits_refused_weth_child`† and `maxRedeem_no_reverting_walk`†. **What remains possible.** (1) The refused child itself: for the inbound `transferFrom`, the caller's WETH balance or allowance (external to the vault), and for any exact-WETH child the gas, the call-depth limit or a static context; the outbound payout's liquidity is proved only arithmetically (`maxWithdrawN_le_assets`†), not by a theorem about the WETH program. (2) An exceptional halt of the vault frame — out of gas, or a write in a static context — which is not a revert and which these theorems do not cover; `vault_terminals_return_or_revert`† shows every vault terminal is `RETURN` or a `Func.revert`, so no vault guard is coded as another kind of terminal. No theorem here says that a call within `max*` succeeds: there is no liveness or gas-sufficiency claim |
| The share surface has the stated allowance, return, event and rollback behaviour, and the allowance-key guard is a proved conclusion | `approve_compiled_effect`, `transfer_compiled_effect`, `transferFrom_compiled_effect` |
| The share ledger is conserved by every vault message, and by every message that makes no external call without any premise about the asset | `vault_message_preserves_conserved` (all twenty-five targets), `vault_nonflow_message_preserves_conserved` |
| The vault reaches WETH only through three exact child forms, and a failed child rolls back | `DirectWethConfiguration.installed`†, `exactWethCallOccurrence_of_runCompiled`†, `exactWethStatcallOccurrence_of_runCompiled`†, `ExactWethChildSuccess.worldProgramRun`†, `ExactWethChildSuccess.programRun`†, `SuccessfulWethWorldProgramRun.balanceOf_effect`†, `SuccessfulWethProgramRun.balanceOf_effect`†, `SuccessfulWethProgramRun.transfer_effect`†, `SuccessfulWethProgramRun.transferFrom_effect`†, `vault_externalWethCallSites_complete`†, `readTotalAssets_exactEffect`†, `callWethTransferFrom_exactEffect`†, `callWethTransfer_exactEffect`†, `balanceOfStaging_rollback`†, `transferFromStaging_rollback`†, `transferStaging_rollback`† |
| Every exact WETH frame entered by a caller other than the vault either leaves the vault's WETH row alone, credits it from another account, debits it through a runtime-authorized allowance, or hands off to a `withdraw` callback | `wethFrame_vaultRow_classified`; `WethFrameClass.classification_sound`, `WethFrameClass.classification_complete`, `WethFrameClass.classification_total` |
| Every configured continuation of the pair root is backed, or its realized trace retains a runtime-authorized debit of positive amount (no D9) | `pair_reachable_backed_or_debit` |
| Under D9, foreign debits of the vault's WETH row are excluded, and the pair invariant and WETH's solvency hold at every configured pair state | `pair_history_backed`, `pair_history_stable` (real-chain D9, conclusions about the reached state itself); over a realized trace, `pair_reachable_backed`, `pair_reachable_stable`, `PairTraceRealizes.authorizedDebit_zero` |
| Donations are accounted rather than minted against | `wethFrame_vaultRow_classified` (a third-party credit to the vault row is its credit arm) and `pair_history_realized_dust_trace_exact`, whose equality carries credits as their own term. `donationStep` and `PairBacked.donation` are standalone model-level lemmas that no headline uses |
| P3 — exact whole-history residue, as an equality, for some realization faithful to the chain | `pair_history_realized_dust_trace_exact` (real-chain D9); `pair_realized_dust_trace_exact` over a realized trace |
| P4 — open context, no profit and victim loss, for some realization faithful to the chain | `pair_history_attacker_open_context`, `pair_history_victim_loss_bound` (real-chain D9); over a realized trace, `pair_attacker_open_context`, `pair_attacker_no_profit`, `pair_attacker_no_profit_of_no_share_gifts`, `pair_victim_loss_bound`, `pair_victim_loss_bound_of_trace` |
| The attack carrier is inhabited | `pair_attack_carrier_inhabited`, a **model-level** inhabitant (the user's inhabitant rule): a concrete `PairAttackPath` with the frozen transcript's numbers. No executed-chain history is exhibited that satisfies the P4 trace premises (review F5, open) |

**How P4 is priced.** The closed no-profit form takes a `PairAttackTrace`: every
non-victim actor is in the coalition, and the victim follows the SF-frozen
schedule (one self-paid deposit, then at most one full self-redeem). Coalition
input is attributed **by actor, not by credit source**. Every WETH credit to the
vault counts as non-victim input, whatever account it came from. So a third
party's WETH that a coalition actor moves into the vault with that party's
allowance is priced as coalition input. `pair_attacker_open_context` names
outside gifts as an explicit subsidy term. The theorems carry no
callee-honesty and no no-donation premise.

## The G6 per-message and in-flight ladder (audited, not on the headline route)

SF §7's per-occurrence ladder exists as audited theorems:
`PairStable.of_root`†, `PairStable.totalAssets`†,
`PairStable.redeemable_and_solvent`†, `vault_message_preserves_backed`†,
`vault_processMessage_preserves_stable`†, `PairInFlight.stable_of_mint`†,
`PairInFlight.stable_of_outboundSettled`†,
`PairInFlight.reverting_of_failed_child`†,
`PairInFlight.reverting_of_failed_inbound_child`†,
`PairInFlight.reverting_of_failed_outbound_child`†,
`inbound_stage_witnesses`† and `outbound_stage_witnesses`†. No headline above
consumes them. The chain-level backing route goes through replay-price
monotonicity instead. The family has three known limits:
- no in-flight witness exists for an outer-frame revert after a settled child;
- the self-receiver withdraw/redeem has no stage witness;
- the outbound settled stage carries its backed post as a field, which the
  witness theorem discharges.

## Model-level companions

These are audited, but they are statements about the PRORATA-shared accounting
model or about a sequence of vault messages, not about a configured chain. They
carry none of the chain-level sentences above.

- `dust_trace_exact`, `attacker_open_context`, `attacker_no_profit`,
  `victim_loss_bound`, `victim_loss_le`, `victim_loss_le_over_history`,
  `attack_carrier_inhabited`, `depositStep`, `redeemStep`, `donationStep`,
  `two_le_offsetN`.
- `redemption_le_assets` and `roundtrip_loss_le`. `roundtrip_loss_le` bounds a
  truncated `Nat` difference, so it does not by itself say that a round trip
  pays at most its input. P1 does not cite it. The no-profit direction
  `paid ≤ amount` is `roundtrip_no_profit`†.
- `inboundEffect_accountingStep`, `outboundEffect_accountingStep`,
  `deposit_message_accountingStep`, `redeem_message_accountingStep`,
  `nonflow_message_accountingStep`, `silent_accountingStep`,
  `silent_accountingStep_of_view`, `readOnlyEffect_accountingStep`,
  `transferEffect_accountingStep`, `approveEffect_accountingStep`,
  `transferFromEffect_accountingStep`, `SteppedMessages.toPath`,
  `SteppedMessages.victim_loss_le`, `ConfiguredRoot.conserved`,
  `ConfiguredRoot.backed`, `ConfiguredMessages.preserves_conserved`,
  `ConfiguredRoot.chain_conserved`, `vault_rely_preserves`,
  `vault_rely_preserves_conserved`.

The 2026-09-04 gaps this map used to list are closed on the chain-level route:
- the history rely is `wethFrame_vaultRow_classified` together with the
  `pair_reachable_*`/`pair_history_*` headlines;
- `mint` and `withdraw` are accounting steps of the four-quote model that P3
  and P4 use;
- foreign-debit exclusion is `pair_history_backed`/`pair_history_stable` under
  D9.

## Carried by finite evidence only

| Claim sentence | Evidence |
|---|---|
| "Finite OpenZeppelin/oracle evidence supports conformance" | Carried as finite evidence, never as a theorem: `scripts/check-prorata-weth-vault-oracle.sh` (12 property batteries over 63 boundary states; the offset-disabled control bites); `scripts/check-prorata-weth-vault-reference.sh` (the vendored OpenZeppelin v5.7.0 closure, compiler input/output and ABI surface identity-checked against the G1 hashes; its self-test's seven corruptions each fail with their own diagnostic and restore green when undone; the selected-wasm recompilation is an optional leg outside the ordered set); `scripts/check-prorata-weth-vault-differential.sh` (47 Jaune check groups over 129 declared cases, 125 implemented and 4 superseded, on the committed runtime and the constructor-patched reference, both agreeing with the oracle; sizes and gas recorded) |
| `max*` attainability as an actual successful call | The capacity row above proves that a call within `max*` takes no vault revert and that no successful flow exceeds `max*`; it does not prove that a call within `max*` succeeds. Only the oracle's tightness batteries and the differential's capacity cases evidence successful acceptance at the boundary, finitely |

## Not claimed

- No theorem is about deployed WETH9, a production vault address, the
  OpenZeppelin source, or arbitrary ERC-20 code.
- No global Keccak injectivity, and no claim that D9 holds of any particular
  chain.
- P3 and P4 are not stated for the executed operations as such (see the scope
  section above).
- No claim that `max*` accounts for a caller's external WETH balance or
  allowance, or for future concurrent state.
- No liveness or gas-sufficiency claim: a call within `max*` is proved to take
  no vault revert, not to succeed.
- No ERC-4626 certification. The standard is the source of the frozen
  statement, not a party to the proof.

## What this map is not

It does not assert that the carried rows exhaust the frozen claim. It asserts
that each carried row has the named theorems behind it and is limited by the
scope section, and that each other row has only what it names. A claim absent
from every table has not been checked either way.
