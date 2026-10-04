# Uniswap V2 Pair: new-host lane return

This is the new host's return for the allocation in
[`UNISWAP_V2_PARALLEL_HOST_HANDOFF.md`](UNISWAP_V2_PARALLEL_HOST_HANDOFF.md) (fork
`577edbac`, Jaune pin `b019bbf54eedb4f29398a80ba7b49daa664bb52a`, unchanged). It is a
work return, not an acceptance claim for the goal: the combined candidate, the full gate
catalogue, the claim map, U6, the history lifts and U11/U12 belong to the original host.

- Lane branch: `claude/uniswap-v2-newhost`, tip = the commit adding this document. Every commit descends
  from `577edbac`; no history was rewritten. Jaune, `lakefile.lean`, `lake-manifest.json`,
  `scripts/**`, the claim map, `docs/COMMON_API.md`, `Blanc.lean`, `Execution.lean` and
  `Check*.lean` are untouched on this branch.
- Shared-wiring proposal: branch `claude/uv2nh-integration-proposal` (lane tip plus
  three proposal commits `0fbcabbe`, `41a3b25c`, `c0890472`): layering rows for all 30 new modules, COMMON_API entries for the
  seven contract-neutral modules, and root imports. Take, edit or drop it at integration.
- Supporting reports: [`uniswap-v2-newhost/`](uniswap-v2-newhost/) (one per work packet,
  the immediate-entry coverage tables and the different-family model review).

## Theorem map

Every headline below is proved with explicit simplification only (`simp only` /
`simpa only`), no `sorry`, `admit`, `native_decide`, new axiom or heartbeat change, and
zero build warnings in the lane's files. Hash facts are trace-local (HASH-T) only.

### U2(a) frame refinements (handoff deliverables 1 and 2)

Shape: from the code, a covered fork, the selector, the slot representation, trace-local
HASH-T facts and a successful pc-0 run, conclude value 0, the call context, `ExactConsumes`
on the driver (`startTyped` of the entry) over the transcript derived from the actual
execution, exact Pair storage (`WriterRep`), foreign storage, exact raw logs and return
bytes. Decision J1 (master): a successful run is shown to take the success path, which
excludes every failure branch the dispatcher admits; rolled-back frames are never in a
transcript (`Exec.retainedTargetTurnsAt` keeps committed frames only), so no
raw-revert-to-model-failure correspondence is needed.

| Entry | Headline | Also |
|---|---|---|
| `sync` | `sync_bytecode_exact_consumes` (SyncGasCanonical.lean:749) | `sync_bytecode_foreign_storage` (:729); gas: `syncPc0_canonical_live` (:515), exact `post.gasLeft = G` from compiled child ENV |
| `skim` | `skim_bytecode_exact_consumes_own` (SkimCanonical.lean:205) | `skim_bytecode_exact_consumes` (:480); raw inverse `skim_raw_flag_inv` (SkimSecondWalk.lean:513) |
| `permit` | `permit_bytecode_refines_source` (PermitSource.lean:350) | canonical ECRECOVER corollary `permit_bytecode_refines_source_canonical` (:489); forward/gas `permit_source_bytecode_exact` (:420) |
| `transfer` | `transfer_bytecode_exact_consumes` (TransferSource.lean:479) | existing `transfer_source_bytecode_exact` |
| `approve` | `approve_bytecode_exact_consumes` (ApproveSource.lean:259) | existing `approve_source_bytecode_exact` |
| `transferFrom` | `transferFrom_bytecode_exact_consumes` (TransferFromSource.lean:603) | max and finite allowance branches |
| `initialize` | `initialize_bytecode_exact_consumes` (InitializeSource.lean:247) | caller = factory |
| 17 getters | `staticView_source_handler_selected` (StaticViewSource.lean:140) | any call context; the static form `staticView_source_handler_inv` (:179) now derives from it |

Reusable pieces for the original host's Burn, swap and mint frames:
`mutable_call_turns` (MutableTurns.lean:402) with `lockedPairSupply` (LockedSupply.lean)
turns a non-static token CALL into `ExactTurns` (committed nested Pair frames plus foreign
logs); `pair_lockGuarded_unlocked` (PairLockedEntries.lean:303) shows mint, burn, swap,
sync and skim succeed only unlocked; `pair_bytecode_selector_inv` (PairSelectors.lean:320)
partitions every successful run into the 27 selectors; `cursor_cut_exact`
(CursorExact.lean:198) pins the complete actual state at a later cursor.

### Model-side laws (handoff deliverable 3)

| Goal | Headline | Notes |
|---|---|---|
| U5 | `runTyped_oracle_law` (PropertiesOracleLaw.lean:658); `State.update_oracle_law` (PropertiesOracle.lean:25), `runTyped_oracle_accumulates` (:832) | every recorded update satisfies `OracleUpdate.Lawful` (Δt = (ts mod 2^32 − last) mod 2^32, increment ⌊r1·2^112/r0⌋·Δt when active), timestamps chain from the start to the final `blockTimestampLast`, accumulators are the modular fold; control `oracle_timestamp_mod_control` (:853) |
| U4 swap | `runTyped_swap_success_reserves` (PropertiesSwap.lean:561), `runTyped_swap_canonical_success` (:1042), `runTyped_swap_callback_request` (:1664) | success ⇒ the conditions over the post-callback balances, pinned by position (they become the final reserves); conditions ⇒ success on the canonical transcript; the callback request is exactly `(sender, amounts, data)` iff data is non-empty; control `swap_uint112_control` (:1151) |
| U4 mint, burn | `runTyped_mint_later` (PropertiesMintBurn.lean:310), `runTyped_burn_payout` (:924); existing `runTyped_mint_initial*`, `mintFee_spec` | later mint issues min(⌊a0·T/r0⌋, ⌊a1·T/r1⌋) over the post-fee supply; burn pays ⌊L·b_i/T⌋ per token as the transfer requests; both take the model `mintFee` acceptance on the observed feeTo answer as a premise |
| U7 | `runTyped_ledger` (PropertiesLedger.lean:548), `runTyped_ledgerOn` (:556), `ExactConsumes.ledger` (:566), `State.initialized_ledgerOn` (:76) | Σ balanceOf = totalSupply over a duplicate-free covering footprint, extended by touched keys; through nested committed children and rollback; control `footprintSum_dup_breaks_ledger` (:82) |
| U3 dependencies | existing `runTyped_product`, `runTyped_feeOff_product` (Properties.lean) | unchanged |

### U8 deployment (handoff deliverable 4)

`pair_create2_initialized` (Creation/DeployInit.lean:126): on every covered fork, the
CREATE2 step from the factory frame installs the certified runtime at
`create2NewAddress`, with slot 5 = factory, slot 12 = 1 and slot 3 = the EIP-712 domain
separator computed by the constructor walk (`domainSeparator_eip712`, Creation/Walk.lean:60;
no hash premise); every following successful `initialize` from the factory reaches
`InitializedCheckpoint` (:34), the proposed U2 checkpoint predicate. `exhibit_create2`
(:171) instantiates the exhibit pair; `initHash_eq`, `pairAddress_eq` and the two controls
`pairAddress_wrong_salt` / `pairAddress_wrong_initHash` (Creation/Facts.lean:95-115) are
kernel evaluations over all 11,636 creation bytes. Generic: `Blanc/Lift/Create2Deploy.lean`.

## Evidence

Run from the lane worktree at the tip unless stated.

- Narrow owned builds of every new and changed module and their lane consumers:
  `~/creme/scripts/creme lake-build <label> -- <modules>`, status `OK`; zero warnings from
  lane files (a forced re-elaboration of the changed files reported warnings only in
  upstream modules).
- `scripts/check-proof-module-size.sh`, `check-proof-duplication.sh`, `check-proof-debt.sh`,
  `check-proof-residue.sh`: `OK` (the one hard-cap report is the pre-existing
  `ProrataWethVaultCode.lean`).
- `scripts/check-layering.sh`: `OK` on the proposal branch (970 modules classified); red on
  the lane branch alone because the new modules need their rows (the control that the
  rows are load-bearing).
- `scripts/check-doc-counts.sh`: the same three pre-existing `GATES.md` module-count
  quotations disagree on the fork base, the lane and the proposal; they are publication
  counts and were not touched.
- Axioms: a temporary probe module importing the lane's top modules and running
  `#union_axioms_of_modules Blanc` (the walker `scripts/AxiomCheck.lean` uses) built green;
  adding an imported module with one `sorry` theorem failed at the probe with
  `reaches axioms outside #[Classical.choice, Quot.sound, propext]: #[sorryAx]`, and
  removing it restored green.
- Statement reviews: two hostile reviews by Gemini 3.8 Flash of the Claude-authored frame
  and deployment headlines (findings fixed: Sync foreign storage and output, skim foreign
  storage); a Claude Opus 5.5 different-family review of the GPT-authored model
  ([`uniswap-v2-newhost/model-review.md`](uniswap-v2-newhost/model-review.md), at
  `2ab4868c`): no model defect and no blocker; its should-fix items S1-S3 on the lane's
  own model statements are addressed by `runTyped_oracle_law`,
  `runTyped_swap_success_reserves`, `runTyped_mint_later`, `runTyped_burn_payout` and
  `runTyped_swap_callback_request`; S4-S6 and N1-N5 are recorded below or in the review.

## Remaining obligations and disclosures

- Original host (unchanged allocation): Burn, mint and swap frames, U6 reachable gas, the
  U2(b)/U5/U7 history lifts, the full catalogue, the claim map, U11/U12.
- Skim's second half is stated under the moved free pointer fitting
  (`96 ≤ p → p + 1024 < 2^256`, discharged for any transfer0 reply under 2^128 bytes by
  `skimFirstPointer_fit`); gas is an unbounded `Nat` in the model, so this is a formal edge
  a history-level gas bound removes.
- Skim's derived queues may be empty when a token address is an enabled precompile (a
  real raw case: the precompile answers and no code frame is entered); for the transfers
  the statement names that fact, for the balance queries a STATICCALL inversion exporting
  the stepped slot (counterpart of `of_run_call_val_with_depth_frame`, LadderBase.lean) is
  the missing shared fact.
- Permit's nested address-1 recovery turns are `.done`: a Pair view reached through a
  delegated address-1 account at depth 2 is not lifted (no storage effect).
- U3/U5/U7 statements here are per run (model side); history versions are the original
  host's. `OracleUpdate.Lawful` uses the reserves the frame recorded; tying them to the
  previous committed state's reserves is part of the history lift. Burn's NoShrink form is transfer-aware (`b_i ≤ final_i + payout_i`), a stated
  deviation from the goal's literal wording, which would exclude every honest burn.
- The U7 statement control here duplicates a footprint key; the goal's storage-key
  collision control belongs to the storage/history layer.
- Consolidation at integration: `SkimTransferWalk` re-derives SafeTransferWalk's private
  generic stages at an arbitrary pointer (one pointer-generic helper57 should remain, with
  first-transfer as its p = 128 instance); `PairLockedEntries` contains lock-guard walks for
  burn and swap prefixes; `skim_static_call_turns` is generic and could be hoisted.
- No Jaune change is proposed.
