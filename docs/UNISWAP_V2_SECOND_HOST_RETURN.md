# Uniswap V2 Pair: second new-host lane return

This is the second new-host lane's return for the allocation in
[`UNISWAP_V2_SECOND_HOST_HANDOFF.md`](UNISWAP_V2_SECOND_HOST_HANDOFF.md) (deliverables N1-N5). It is a
work return, not an acceptance claim for the goal. The combined candidate, the history lifts, the Burn
frame, U6 positive liveness, U9, the U10 instantiation, the full gate catalogue, the claim map and
U11/U12 belong to the original host. The first split's return,
[`UNISWAP_V2_NEWHOST_RETURN.md`](UNISWAP_V2_NEWHOST_RETURN.md), is history and vocabulary.

Every theorem name and `file:line` below was checked by `grep` against the lane tree at
`11d2e1a6` (the tree this document is committed on). Statements are transcribed from the packet
reports and the lane's docstrings; where a report's line number had moved after cleanup, the current
line is given. Line numbers move again at integration.

## Headline caveats (read these before the tables)

The full text is in [section 8](#8-remaining-obligations-and-disclosures).

- **U2's refinement control is not delivered.** Only typed-model disagreements exist (the 998 fee and the
  burn round-up mutants). The final control is blocked on the original host's Burn frame consumer and a
  concrete successful burn. Under success-only frame refinement (decision J1) the fee-998 mutant cannot
  bite, because it accepts strictly more swaps.
- **U10 is not instantiated.** The WETH9-side adapter exists, but there is no Pair-history theorem to
  instantiate it against, and its history theorem carries an unproved running ether bound `EthFits`.
- **U6 has controls only**, for token0 of sync, skim and mint, at pc-zero universal altitude with one
  concrete reverting callee code. The positive theorem is the original host's. `¬ isPrecomp tok` is a live
  premise, and no reachable-state witness is built.
- **Most controls are model or conditional altitude**, not reverting EVM executions: U3(i), U3(ii), U5 and
  the model halves of U2 and U4 are typed-model results; U7 and U4's bytecode half are universal over
  successful runs, and U7 is conditional on a storage alias.
- **Swap carries an explicit `short` premise** (every CALL reply of the run is below 2^160 bytes) that needs
  a gas-potential bound this repository derives nowhere. Mint's HASH-T key list is finite and fixed by the
  root, but noncomputable and over-inclusive.
- **N4 changed a headline bound**: skim's conditional second-half premise `96 ≤ skimFirstPointer` became
  `128 ≤` (master decision `uv2sh-n4-skim-pointer-bound`).
- **Not run here, deliberately**: the full `Blanc` build, the registered axiom union walk and the check-elab
  timing. The leaf figure is not recomputed. `check-doc-counts` reports three stale `scripts/GATES.md` count
  quotations, which are reserved and were not edited.
- **The review was by Claude Fable 5.1**, the same model family as the Opus authors, not a different family.
- **Process incident**: a stray `git stash pop` by a worker left rerere records in the shared `.git/rr-cache`.

## 1. Identity

- **Fork**: `6d6c04eb` (its parent is `8e10cca4`). The fork is published as
  `origin/codex/uniswap-v2-second-host-fork`. Every lane commit descends from it; no history was rewritten.
- **Lane branch**: `worker/uniswap-v2-second-host`. Its tip is the commit that adds this document. The
  lane content tip before this document is `11d2e1a6` (merge of `uv2sh-cleanup`).
- **Wiring proposal series**: branch `claude/uv2sh-wiring-proposal`, based on lane content tip `11d2e1a6`
  (it does not contain this document):
  - `49cc7fde` root imports, including the two orphans `ModelControls` and `UpdateOverflowWalk`;
  - `18ffec51` layering rows for the 33 new modules;
  - `7948042f` `docs/COMMON_API.md` entries for the 8 new shared modules;
  - `03070a31` merge of the lane.
  The original host merges the lane first and then the proposal.
- **Jaune pin**: unchanged at `780ad71a07787527cc074e06696d0e6a742ba104`. No Jaune change is proposed, and
  `lakefile.lean` and `lake-manifest.json` are untouched.
- **Untouched surfaces**: `Execution.lean`, `Check*.lean`, `Blanc.lean`, `scripts/**`, the claim map, the
  counts, baselines, allowlists and goldens. The hostile review found no original-host-owned file edited.
- **Authors**: the packet reports name Claude Opus 5.5 as the author of each proof packet. This document was
  written by Claude Sonnet 5.5, transcribing those reports.

## 2. Files added and changed

`git diff --stat 6d6c04eb..11d2e1a6`: 44 files changed, 8067 insertions, 1128 deletions. 33 `.lean` files
are new (all under `Blanc/`), 8 `.lean` files and 3 docs are modified. Numbers are added/deleted lines.

### N1 mint (new-host: `Mint*`, `FeeMint*`, `SqrtWalk` surfaces)

| File | Lines | Role |
|---|---|---|
| `Blanc/Lift/UniswapV2Pair/MintCanonical.lean` | +722 | pc-zero mint frame consumer, `mintTraceKeys` |
| `Blanc/Lift/UniswapV2Pair/MintCanonicalOwn.lean` | +98 | foreign-storage variant, forward component schedule |
| `Blanc/Lift/PrecompileAnswer.lean` | +266 | shared: unique precompile answer, finite root-fixed reply source |
| `Blanc/Lift/LocalStorage.lean` | +139 | shared: storage-local entry sets whose only call is STATICCALL |

### N1 swap (new `Swap*` modules)

| File | Lines | Role |
|---|---|---|
| `SwapAbi`, `SwapFront`, `SwapTransfer`, `SwapCallback` | +235, +326, +232, +427 | ABI wrapper, body prefix, both optimistic transfers, conditional callback |
| `SwapFrontTyped`, `SwapFrontTurns`, `SwapFrontCanonical` | +146, +247, +152 | typed front, mutable turns, front headline |
| `SwapCut` | +75 | the cut interface at `t_09c3_c5` between front and back |
| `SwapBalanceWalk`, `SwapCheckWalk`, `SwapUpdateWalk` | +415, +310, +275 | back-half raw walks |
| `SwapBack`, `SwapBackTurns` | +210, +215 | back-half raw inversion and typed consumption |
| `SwapCanonical` | +293 | pc-zero swap assembly (headline) |
| `SwapControls` | +74 | U4 pc-zero control (also N3) |
| `Blanc/Lift/InvWalkBranchToP.lean`, `MutableCallPost.lean`, `WordWindowMemory.lean` | +35, +58, +38 | shared helpers |

(All `Swap*` files are in `Blanc/Lift/UniswapV2Pair/`.)

### N2 permit provenance and the mutable-turn interface

| File | Lines | Role |
|---|---|---|
| `StaticViewTurns.lean` (modified) | +110 | receives the Pair static-call turn adapter |
| `PermitEntries.lean` (modified) | +160/-116 | permit walks stated for any instruction relation `P` |
| `PermitTurns.lean` | +278 | authentic recovery turns from the same pc-zero execution |
| `MutableTurns.lean` (modified) | +43/-28 | derivation-indexed `PairFrameOutcome` and `PairFrameSupply` |
| `LockedSupply.lean` (modified) | +64/-37 | authenticated `LockedAuth`, `LockedGood` over raw frames |
| `SkimCanonical.lean` (modified) | +16/-123 | relocation and interface threading |

### N3 negative controls and model mutants

| File | Lines | Role |
|---|---|---|
| `LedgerKeyControl.lean` | +111 | U7 storage-key alias control |
| `Blanc/Lift/LedgerFootprintOrder.lean` | +51 | shared: pointwise order of footprint sums |
| `OracleControls.lean` | +68 | U5 timestamp-wrap control |
| `ModelMutants.lean` | +305 | arithmetic-parameterised driver and mutants |
| `ModelControls.lean` (modified) | +147/-69 | U3(ii), U2 model mismatches; replaces the partial pricing-seam witness |
| `CalleeControls.lean` | +118 | U6 failing-callee controls |
| `Blanc/Lift/RevertingCallee.lean` | +117 | shared: a callee that fails on every input |
| `SwapControls.lean` | +74 | U4 (listed under N1 swap) |

### N4 transfer-helper consolidation

| File | Lines | Role |
|---|---|---|
| `SkimTransferWalk.lean` (modified) | +137/-687 | consumes `SafeTransferWalk`'s public pointer-generic API |
| `SkimSecondWalk.lean` (modified) | +51/-45 | `PtrMem` carriers, `128 ≤` bound |
| `SkimCanonical.lean` (modified) | see N2 | headline premise `128 ≤` |

### N5 WETH9 composition adapter

| File | Lines | Role |
|---|---|---|
| `Blanc/Composition/UniswapV2PairWeth9.lean` | +389 | WETH9 ledger model, history reading, controls |
| `Blanc/Composition/UniswapV2PairWeth9Frame.lean` | +245 | frame-level answer, storage effect, NoShrink |
| `Blanc/Composition/UniswapV2PairWeth9GasFree.lean` | +225 | WETH9-specific two-run dispatcher walk |
| `Blanc/Lift/GasErasureRun.lean` | +420 | shared: equality modulo gas across two runs of a lifted tree |

### Docs

`docs/uniswap-v2-newhost/permit.md`, `skim-canonical.md`, `skim-raw.md`: minimal factual edits (renamed and
deleted names, the `128 ≤` bound, line numbers). `docs/UNISWAP_V2_NEWHOST_RETURN.md` is historical and was
not edited; it still cites `96 ≤ p` and `skim_static_call_turns`.

## 3. U/M condition-to-theorem map

Altitude key: **EVM-universal** = a statement over every successful pc-zero run of the original bytes (a
refinement of a given run, not an existence proof of any run); **EVM-conditional** = EVM-universal under an
explicit hypothesis; **model** = a reached typed-model result (`runTyped`), not an EVM execution witness;
**concrete** = a specific EVM execution is exhibited. Status: **complete** means complete as the stated
frame/control component, never as the whole goal condition.

All file paths are in `Blanc/Lift/UniswapV2Pair/` unless prefixed with `Blanc/`.

| Condition | Theorem | file:line | Statement | Altitude | Status |
|---|---|---|---|---|---|
| U2(a) mint | `mint_bytecode_exact_consumes` (result `MintCanonicalResult`) | `MintCanonical.lean:499` (`:442`) | A successful raw pc-zero mint, under HASH-T `WriterInj/WriterApart (WriterExtend K (mintTraceKeys root))`, gives value 0, non-static, three same-run STATICCALL steps with their own code bits (including the factory `feeTo`), `ExactConsumes` of the driver over the transcript built from them, final unlock, `WriterRep`, the exact raw logs with the typed pending logs mapping onto them, and the return bytes | EVM-conditional (HASH-T) | complete (frame component); history is the original host's |
| U2(a) mint | `mint_bytecode_exact_consumes_own`, `mint_bytecode_foreign_storage` | `MintCanonicalOwn.lean:43`, `:25` | The above plus every non-Pair account keeps its storage | EVM-conditional | complete |
| U2(a) mint | `mint_bytecode_forward_consumes` | `MintCanonicalOwn.lean:68` | From the `MintPrefixForwardEnv` component schedule, an existential run (gas `env.gas + 228`) satisfying the headline | component schedule | component (reachable-state gas is the original host's) |
| U2(a) swap | `swap_bytecode_exact_consumes` | `SwapCanonical.lean:267` | A successful raw pc-zero swap (selector `0x022c0d9f`), under HASH-T over `WriterExtend K (swapTraceKeys root)` and `short`, gives `SwapCanonicalBody`: the actual transfer and callback steps in their shapes, both post-callback balance STATICCALLs at the world the callback left, `ExactConsumes` of the driver, final unlock, `WriterRep`, both balances below 2^112, exact raw logs (`Sync`, `Swap`) with the typed logs mapping onto them, empty output | EVM-conditional (HASH-T, `short`) | complete (frame component) |
| U2(a) swap | `swap_bytecode_exact_consumes_own` | `SwapCanonical.lean:184` | The above with foreign-storage silence for the lock prefix and for the post-callback tail only (see section 8) | EVM-conditional | complete |
| U2(a) swap | `swap_bytecode_front_cut_code`, `swapBack_exact_consumes_bounds` | `SwapFrontCanonical.lean:36`, `SwapBackTurns.lean:63` | Front half to the cut `SwapCut` (with Pair code unchanged); back half from the cut (with both balance bounds) | EVM-conditional | components consumed by the assembly |
| U2(a) permit | `permit_bytecode_exact_turns` | `PermitTurns.lean:226` | Every successful literal permit run gives the old guards, `PermitRecoveryAuth root out entered views`, `PermitSourceResult` at the actual bit, the authenticated `ExactConsumes`, and `Authentic` for every view | EVM-universal | complete (closes the first return's address-1 disclosure) |
| U2(a) skim | `skim_bytecode_exact_consumes_own`, `skim_bytecode_exact_consumes` | `SkimCanonical.lean:99`, `:380` | First-lane skim frame headlines, now over the consolidated helper; conditional second-half premise `128 ≤ (skimFirstPointer d.returnData).toNat` (was `96 ≤`) | EVM-conditional | complete as stated; the pointer-fit discharge is the original host's |
| U2(a) interface | `PairFrameOutcome`, `PairFrameSupply`, `LockedGood`, `LockedAuth`, `lockedPairSupply`, `mutable_call_turns` | `MutableTurns.lean:65`, `:77`; `LockedSupply.lean:43`, `:57`, `:234`; `MutableTurns.lean:417` | Derivation-keyed frame supply used by Burn, swap and history consumers (section 6) | interface | consumed by skim and swap |
| U3(ii) | `mintRoundUp_breaks_feeOff_product` | `ModelControls.lean:216` | Under `mintRoundUp`: initialize, first mint and a donation sync reach `checkpoint`; there production later mint satisfies the fee-off product (via `runTyped_feeOff_product`) and the mutant run returns `[2]` and violates it | model | complete at model altitude; a history restatement is owed if the final U3 claim is history-level |
| U3(ii) infra | `runTypedWith_production`, `driveWith_production`, `resumeWith_production`, `mintAmountUp_initial` | `ModelMutants.lean:301`, `:283`, `:262`, `:91` | `runTypedWith production = runTyped` for all inputs; the upward mutant equals production when supply is 0 | model | compatibility evidence |
| U3(i) | `noShrink_required` | `ModelControls.lean:115` | Reached `runTyped` chain (initialize, mint, donation sync, shrinking sync): `¬ SyncEntryNoShrink` and the fee-off product inequality fails. Reviewed, retained, not strengthened | model | complete at the goal's text altitude; no history or EVM counterexample |
| U2 control | `feeMutant_disagrees`, `burnRoundUp_disagrees` | `ModelControls.lean:269`, `:291` | At a reached checkpoint production rejects a swap (`UniswapV2: K`) and `feeMutant 2` (998) accepts it; after an actual LP transfer a burn returns `(1,1)` in production and `(2,2)` in `burnRoundUp` | model | **blocked on** the original host's Burn frame consumer plus a concrete successful burn |
| U4 | `swap_bytecode_uint112_control` | `SwapControls.lean:27` | Model half: balance 2^112 passes `swapCheck` and the typed swap fails. Bytecode half: every successful raw swap's two post-callback balance replies are below 2^112. Needs only the raw inversion and `short` | model + EVM-conditional (`short`) | component; no reverting pc-zero run is exhibited |
| U4 | `swap_uint112_control`; `update_overflow_exec`, `update_overflow_uint112_kernel_control` | `PropertiesSwap.lean:1151`; `UpdateOverflowWalk.lean:257`, `:390` | Fork-era model control; a concrete `Exec` that reverts with the OVERFLOW payload at the internal `_update` entry (pc `0x22e0`), storage, accounts and logs unchanged | model; concrete at an internal entry, not pc 0 | retained and reviewed |
| U5 | `oracle_law_requires_timestamp_wrap`; `OracleUpdate.LawfulNoWrap` | `OracleControls.lean:50`, `:20` | A sync at timestamp 2^32+1 and last 0: the exact Δt is 1 and the no-wrap mutant gives 2^32+1, so `Lawful ∧ ¬ LawfulNoWrap` | model | complete at model altitude; bites on the Δt conjunct only (reserves are 0) |
| U6 | `sync_no_success_of_reverting_token0`, `skim_no_success_of_reverting_token0`, `mint_no_success_of_reverting_token0` | `CalleeControls.lean:49`, `:68`, `:88` | With Pair code, a covered fork, the selector, slot 6 = `tok`, `b.getCode tok = revertingCode` and `¬ isPrecomp tok`, no successful pc-zero run exists | EVM-universal over raw runs, one concrete callee code | controls for token0 only; positive theorem is original-host work |
| U6 infra | `revertingCode`, `revertingCode_exec_error`, `processMessage_not_clean_of_reverting`, `not_staticAnswered_of_reverting` | `Blanc/Lift/RevertingCallee.lean:27`, `:47`, `:73`, `:107` | `PUSH0 PUSH0 REVERT`; every frame over it errors; no clean settlement; no `StaticAnswered` over it | EVM-universal | shared |
| U7 | `approve_storage_alias_breaks_ledger` | `LedgerKeyControl.lean:38` | A successful pc-zero approve with `approveSlot = (balance a).slot`, `a ∈ keys`, and an amount different from the raw balance of `a`: `¬ WriterFreshKeys K (approveTouched caller spender)` and `¬ RawLedgerOn keys post` | EVM-conditional (alias hypothesis) | control complete; no colliding preimage is claimed and no run is exhibited |
| U7 infra | `footprintSum_cons`, `footprintSum_le_footprintSum`, `footprintSum_lt_footprintSum` | `Blanc/Lift/LedgerFootprintOrder.lean:18`, `:24`, `:36` | Pointwise order of footprint sums; strict with one strictly grown row, no `Nodup` | generic | shared |
| U8 | `pairAddress_wrong_salt`, `pairAddress_wrong_initHash` | `Creation/Facts.lean` (first lane) | Kernel evaluations; retained, not regenerated | concrete (kernel) | retained |
| U1 | byte-mutation certificate control | Plans `evidence/uniswap-v2-pair-bytecode-v1/certificate/` | Byte 1 `0x80 → 0x81` refutes `Cert.check`, restored green; disposable-tree evidence, not repository source | concrete | retained |
| U10 | `weth9_balanceOf_answer`, `weth9_transfer_returns_true`, `weth9_transfer_effect`, `weth9_transfer_fails_of_lt` | `Blanc/Composition/UniswapV2PairWeth9Frame.lean:76`, `:148`, `:110`, `:136` | Over any successful fresh WETH9 frame: `balanceOf` answers the `balSlot` word with storage unchanged; `transfer` returns true (no gas premise); the storage effect is exactly the ledger move; a transfer above the balance never succeeds | EVM-universal over WETH9 frames | adapter inputs only |
| U10 | `weth9_frame_holder_noShrink` | `UniswapV2PairWeth9Frame.lean:197` | Successful non-`withdraw` frame under `(footSpec U).Pre`, caller ≠ p, p's tracked allowances 0: they stay 0 and p's balance word does not fall | EVM-universal | adapter input |
| U10 | `weth9_history_holder_noShrink` | `Blanc/Composition/UniswapV2PairWeth9.lean:320` | Over a configured history, p's checkpoint balance ≤ its future balance + `holderOut p (replayCalls (committedInvocations ca trace))`; allowances stay 0. Premises: `HolderCalls`, `holderTracked`, `allowZero`, HASH-T `K₀`/`fresh`, and `budget : EthFits …` | EVM-conditional | **not instantiated** (blocked on the Pair history theorem); `EthFits` unproved |
| U10 | `control_allowZero_needed`, `control_holderCall_needed`, `control_ethFits_needed` | `UniswapV2PairWeth9.lean:359`, `:370`, `:382` | Kernel counterexamples to `Ledger.step_holder` with one premise dropped | model | complete at model altitude |
| U10 infra | `SFunc.RunP.eqModGas`, `weth9_twin_wrapper` | `Blanc/Lift/GasErasureRun.lean:309`; `UniswapV2PairWeth9GasFree.lean:110` | Two successful runs of a gas-free lifted tree from states equal modulo gas end equal modulo gas; the WETH9 dispatcher walk that removes the gas premises | generic / EVM-universal | shared |
| U10 gas | `weth9_transfer_gas_exact` | `UniswapV2PairWeth9Frame.lean:172` | The transfer frame entered at `G + transferGas` with `353 ≤ G` ends at gas `G` | EVM-universal | positive component schedule for the original host |

Rows not touched by this lane: U2(b), U3 (positive), U5 (positive history), U6 (positive), U7 (history), U9,
U11, U12. They stay with the original host. The first lane's model-side laws (`runTyped_oracle_law`,
`runTyped_swap_success_reserves`, `runTyped_mint_later`, `runTyped_burn_payout`, `runTyped_ledger`) are
unchanged.

## 4. Source correspondence and observation provenance

Decision J1 (master): a successful run is shown to take the success path, which excludes every failure
branch the dispatcher admits. Rolled-back frames are never in a transcript (`retainedTargetTurnsAt` keeps
committed frames only), so no raw-revert-to-model-failure correspondence is needed. None of the headlines
below is an existence proof of an execution.

**Mint.** The headline consumes, without re-walking them, `mintBytecode_public_source_inv`
(`MintPrefixWalk`), `MintPublicTypedFeeFinished`, `MintBalanceHandlerResult`,
`FeeMintSourceObservation.resume_mint` and `mintBytecode_exact`. The three observations are STATICCALL steps
of the same root derivation: `balanceOf(pair)` to token0 (`out0`), `balanceOf(pair)` to token1 (`out1`) and
the factory `feeTo()` call (`outF`). The same reply bytes enter the transcript as `feeObservedResult`, and
each step carries its own code bit, including the factory's. Their turn queues come from
`pair_static_call_turns`: either `views = []` with an enabled precompile, or exactly the retained static
Pair turns of the committed child, whose raw frame roots lie among the root's. First mint (the
`totalSupply = 0` arm, minimum liquidity to address zero), later mint, the protocol fee mint (acceptance
derived from `FeeMintSourceObservation`) and the final unlock are all in the single headline. The typed
pending logs are tied to the exact raw log list through `mintOwnedRaw` (transfer, approval, `Sync`, `Mint`;
burn and swap events map to `none`). View authenticity is exported as selector, target and static, not as the
full `StaticViewTurn.Authentic` (available in the proof).

**Swap.** The wrapper is entered at free pointer 128; `bytes calldata` is decoded without a memory copy, so the
pointer moves only through each `_safeTransfer`. The transfers use the public
`safeTransfer_dynamicReturned_inv` at 128 and then at the moved pointer. The callback payload is built at the
moved pointer: the CALL goes to the masked recipient, the input window equals
`ExternalOperation.encode (.callback caller a0 a1 data)` including the actual data length, and the callback
runs iff `data` is non-empty. Transfer replies, the callback reply and both post-callback balance STATICCALLs
are `StepIn root` steps of the pc-zero derivation. The two balance calls are issued from the world the
callback (or the last taken transfer) left, so the observed balances are those after the transfers and
callback, not selected from another execution. The skip arms pin the state unchanged. The raw `Swap` event
carries the actual ternary input words (`swapInWord_source`). The typed log map is a new `swapOwnedRaw`
(transfer, approval, `Sync`, `Swap`).

**Permit recovery.** The `ecrecover` STATICCALL is now recovered as a step of the same pc-zero derivation
(`permit_raw_in`, via `lift_sound_in`), at the nonce-incremented world `permitNonceWorld`
(`permit_suspended_rep`). `permit_recovery_turns` applies the static-call adapter to that same occurrence.
`PermitRecoveryAuth` ties the reply `out`, the frame-entry bit `entered` and the views to the derivation: either
`views = []`, `entered = false` and `isPrecomp 1`, or `entered = true` with a committed child whose raw roots lie
among the derivation's and whose retained target turns are `views`. Pair address 1 needs no special case (the
entered child is a Pair frame and its static views are authenticated). Rollback pruning and the original raw
paths are preserved through `retainedTargetTurnsAt`.

**Skim (N4).** Nothing is re-derived. `SkimTransferWalk` now consumes `SafeTransferWalk`'s public
pointer-generic API (`safeTransfer_dynamicCall_post_inv`, `safeTransfer_dynamicCall_data`,
`safeTransfer_initialize_dynamic_inv`, `safeTransfer_dynamicPayloadMemory`); the moved-pointer carrier is
derived from the actual `safeTransfer_call128Memory` and `safeTransfer_reply292Memory` writes using
`PtrMem`, not assumed from `Wf`. The final environment, the full reply and the decoder are preserved.

**WETH9.** Every frame result consumes an actual `Exec 0 sevm pre (.ok post)` of the deployed WETH9 bytes, read
through `lift_sound_in cert_check` and `weth9_frame_effect`. The output facts carry no gas premise: the
gas-exact forward walks `weth9_balanceOf_runExact` and `weth9_transfer_runExact` are run from
`pre.withGasLeft N`, and a two-run comparison modulo gas (`SFunc.RunP.eqModGas`, `weth9_twin_wrapper`)
transfers their output to the actual frame. The history result consumes `weth9_history_committed`. No witness is synthetic
and token success is never assumed as a result.

**Transcript shapes covered.** Mint: first, later, fee and no-fee, in one headline. Swap: each of
transfer0, transfer1 and callback either skipped or taken. Permit: precompile and entered-child recovery.

## 5. Negative controls

| Control | Altitude | Bite evidence |
|---|---|---|
| U7 storage-key alias (`approve_storage_alias_breaks_ledger`) | EVM-conditional, universal over successful pc-zero approve runs under an alias hypothesis. Independent of the positive ledger/history proofs | Statement control: it concludes that conservation fails (`¬ RawLedgerOn keys post`). Uses `approve_bytecode_refines_raw` and `approvePublicPost_facts`. No mutation campaign. No colliding Keccak preimage is known or claimed |
| U5 timestamp wrap (`oracle_law_requires_timestamp_wrap`) | Model: a reached `runTyped .sync` run from the literal initialized state | `Lawful ∧ ¬ LawfulNoWrap` at timestamp 2^32+1. Bites on the Δt conjunct only. One `decide +kernel` |
| U3(i) omitted NoShrink (`noShrink_required`) | Model, kernel-checked; not strengthened | Reached shrinking-sync chain refutes the fee-off product |
| U3(ii) mint rounds up (`mintRoundUp_breaks_feeOff_product`) | Model, on a history the mutant itself reaches | The fee-off product holds in production and fails under the mutant; `runTypedWith_production` ties the parameterised driver to production |
| U2 fee 998 (`feeMutant_disagrees`) | Model | Production rejects, the mutant accepts. **Finding:** every swap the production check accepts is also accepted by the 998 mutant with the same state, so the mutant accepts strictly more. Under success-only frame refinement (J1) a reverting production run is never in a transcript, so a swap-based frame control cannot bite; only the burn-rounding route can bite for U2 |
| U2 burn rounds up (`burnRoundUp_disagrees`) | Model | Both runs succeed; the mismatch shows in returndata and stored balances. The final frame-level control needs Burn |
| U4 uint112 (`swap_bytecode_uint112_control`) | Model + EVM-universal, conditional on `short` | Model half is the existing falsifier (`swap_uint112_control`). Bytecode half is a non-existence statement for balances ≥ 2^112 in successful runs; no raw mutation campaign. The concrete reverting run is at the internal `_update` entry (`UpdateOverflowWalk`), not pc 0 |
| U6 reverting callee (`*_no_success_of_reverting_token0`) | EVM-universal over raw runs, one concrete callee code, token0 of sync/skim/mint | Loop-only evidence (`lean_multi_attempt`): clearing the token-code premise or `¬ isPrecomp tok` made the closing step fail. This is not a committed mutation record. The defeat argument for a premise-free liveness statement (it is false at a reachable state whose token0 holds `revertingCode`) is report-level, not formalised |
| U10 premises (`control_allowZero_needed`, `control_holderCall_needed`, `control_ethFits_needed`) | Model (WETH9 ledger), kernel `rfl`/`decide` | Each is a counterexample to `Ledger.step_holder` with one premise dropped |
| U1 certificate, U8 wrong salt / init hash | Concrete, retained | Not regenerated |
| Layering control | Source gate | `check-layering.sh` reports unclassified-module REGRESSIONs without the rows and OK with them |

## 6. Interface changes the original host must absorb

All are in new-host-owned files. At the fork the only consumers are `LockedSupply` and `SkimCanonical`, both
updated.

1. **N2, derivation-keyed frame interface** (`MutableTurns.lean`, `LockedSupply.lean`):
   - `PairFrameOutcome pair Rep Auth owned current invocation D sevm b post` gains the frame's derivation
     `D : Exec.Deriv`, and `Auth : Exec.Deriv → Entry → Transcript → Prop` (was `Sevm → Devm → …`); the clause
     is `Auth D entry nested`.
   - `PairFrameSupply pair Rep (Good : Exec.Deriv → Prop) Auth owned` quantifies a named
     `run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)`, takes the new premise `b.getCode pair = code`, and
     applies `Good` and the outcome to `⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩`.
   - `MutableFoldResult`, `mutable_retained_fold_inv` and `mutable_call_turns` state `Auth` over
     `Exec.Frame.rootDeriv located.frame` and `Good` for each raw root `F`.
   - `LockedGood U D`: for every raw Pair frame `F` of `D`, `pairDecodedKeys F.sevm ++ staticViewDecodedKeys F.sevm ⊆ U`.
     Discharge it from a root universe with `Exec.rawFrameRoots_trans` (see skim's `lockedGood`).
   - `LockedAuth D entry nested` reads `D.sevm`; the permit arm is
     `∃ out entered views, nested = .next (permitExternalResult out entered) (staticViewTranscript views .done) .done ∧ PermitRecoveryAuth D out entered views`.
   - `lockedPairSupply inj apart sem image pair` now takes the `CodeSem`.
   - Burn transfers and the swap callback use `mutable_call_turns supply …` with `Good`/`Auth` over derivations.
   - The per-view `Authentic` facts are proved in the standalone permit headline but are not part of
     `LockedAuth`; inside the locked supply they are implied only through `ExactConsumes`.
2. **Rename**: `skim_static_call_turns` is now `pair_static_call_turns` (`StaticViewTurns.lean:532`), statement
   unchanged. The permit walks are `permitBody_invP`, `permitEntry_invP`, `permit_selector_invP`
   (`PermitEntries.lean:211`, `:363`, `:475`) stated for any `P` that projects to `Ninst.Run`;
   `permitEntry_inv` and `permit_selector_inv` remain as their `Ninst.Run` instances. `permitBody_inv` was
   removed.
3. **N4 pointer bound**: skim's headline premise `96 ≤ skimFirstPointer` is now `128 ≤ skimFirstPointer`
   (`SkimCanonical.lean:124`, `:399`), and `skimFirstPointer_fit` is strengthened to give `128 ≤`
   (`SkimSecondWalk.lean:492`). Reason: the public dynamic API needs `128 ≤ p`. With only
   `reply.length < 2^256` and the `+1024` fit, the modular pointer wraps to exactly 100 for reply lengths in
   [2^256 − 255, 2^256 − 224], which satisfies `96 ≤ p` but not `128 ≤ p`. Excluding it needs the Jaune 2^160
   returndata bound, whose gas-potential premise has no source in this run. Master decision
   `uv2sh-n4-skim-pointer-bound`: the excluded reply lengths lie within 255 of 2^256, so the change is accepted.
   Every consumer discharges the bound through `skimFirstPointer_fit` (reply below 2^128 bytes). The change
   also reaches `skimSecondHalf_flag_inv`, `skimSecondHalf_inv` (now `{n} (mem : PtrMem p n M) (low : 128 ≤ p.toNat)`),
   `skim_raw_flag_inv` and `skim_raw_inv` (`SkimSecondWalk.lean:518`, `:554`). `PairLockedEntries` uses only
   the first-half projection of `skim_raw_inv` and is unaffected.
4. **Proposal, not applied**: a public `safeTransfer_dynamicReturned_flag_inv` in `SafeTransferWalk` (the
   `_dynamicReturned_inv` statement plus `d.stack = 1 :: (68 + (p + 164)) :: … `, obtained by keeping `stack`
   through a new `_dynamicReply_flag_inv`). With it skim could delete its local copy, CALL and decoder walk,
   about 400 lines of `SkimTransferWalk` (the decoder alone about 220). `SafeTransferWalk` is original-host
   owned. An optional variant of the dynamic API at `96 ≤ p` would restore the old bound.
5. **WETH9 adapter interface** the original host instantiates, with `ca` = WETH9, `p` = exhibit pair,
   token1 = WETH9 (USDC = token0 stays environmental):
   - `HolderCalls p (replayCalls (committedInvocations ca trace))`: the pair makes only `transfer`, plus
     deposits through the WETH9 fallback when a swap callback targets WETH9; its CALL selectors at WETH9 are
     transfer and callback, while `balanceOf` and `feeTo` are STATICCALLs.
   - `holderTracked : K₀ (.bal p)` and `allowZero` at the deployment checkpoint, HASH-T `K₀` and `fresh`.
   - `budget : EthFits (checkpoint.state.bal ca).toNat (replayCalls (committedInvocations ca trace))`
     (`UniswapV2PairWeth9.lean:265`): the model ether, run along the committed deposits and withdrawals, stays
     below 2^256 at every deposit. Unproved (section 8).
   - The identification of `holderOut p …` with the Pair's own transfer amounts in its replay.
   - Use `weth9_balanceOf_answer` for an observed `balance1`, `weth9_transfer_effect` and
     `weth9_transfer_returns_true` for a Pair `_safeTransfer` to WETH9, `weth9_transfer_fails_of_lt` for the
     failure branch, and `weth9_frame_holder_noShrink` for each non-Pair WETH9 frame between the two
     observations of a burn; supply `(footSpec U).Pre` from the WETH9 ladder. Withdraw re-entry is segmented
     through history or `Ledger.run_holder`.
6. **History consumers of mint and swap**: discharge `WriterInj/WriterApart` over `mintTraceKeys root` and
   `swapTraceKeys root := skimTraceKeys root` before obtaining any reply; a global list universe can
   concatenate them. `swap` imports `SkimCanonical` for that alias.
7. **Shared-wiring proposals**: the 33 layering rows, 8 `COMMON_API` entries and root imports are in the
   proposal series (section 1), not in the lane.

## 7. Gate verdicts

Commands were run from the packet worktrees with `~/.local/bin` first on `PATH`. Owned builds go through
`~/creme/scripts/creme lake-build <label> -- <targets>`; no bare Lake build was used.

**Narrow owned builds (packet reports).** All status `OK`:

| Packet | Result |
|---|---|
| controls (968dc8ab) | `Build completed successfully (1072 jobs).` |
| mutants (498b4528) | `Build completed successfully (965 jobs).` |
| permit (51dbff65) | status OK, all 5 targets built |
| mint (f8576d7c) | `(1164 jobs)` and `(1166 jobs)` |
| mint2 (fbd883b7) | `(1167 jobs)`, 0 warnings |
| mint3 (7ee98a36) | `Build completed successfully (1168 jobs).` 0 warnings |
| helper (7e4222e5) | `Build completed successfully (1187 jobs)` over the whole reverse import closure of the changed files |
| swap-back (f64fa036) | `Build completed successfully (1169 jobs).` |
| swap-front (8006691e) | `Build completed successfully (1194 jobs).` |
| swap-asm (81d0302e) | `Build completed successfully (1206 jobs).` |
| weth9 (f81289cc) / weth9b (40ad8803) | `(1063 jobs)` / `(1065 jobs)`, 0 warnings |
| u6ctl (bbe65fb7) | `Build completed successfully (1135 jobs).` |
| cleanup | `Build completed successfully (1253 jobs).`, 8 modules rebuilt |
| wiring narrow build | `Build completed successfully (1266 jobs).`, all 8 root targets `built` |

Master note: the integration narrow build of all lane-changed modules and their importers was green at
`33ef91d5` (1254 jobs). The packet logs above are the ones present in the session scratchpad; the
`33ef91d5` log was not re-read for this document.

**Source gates.** In every packet worktree: `check-proof-module-size.sh` OK (only the pre-existing
`ProrataWethVaultCode.lean` hard-cap breach); `check-proof-duplication.sh` OK (baseline 1/2/1, no unexcepted
rise); `check-proof-debt.sh` OK (`92 scopes inventoried; zero unexcepted new/increased findings`);
`check-proof-residue.sh` OK (`13/13 predicates checked; counts 96 -> 94; no rise`). The swap-back packet also
ran `check-trust-surface.sh`: `OK — trust surface: 12 exact allowlisted occurrence(s) across 967 module(s)`
(the new modules were not yet in the root closure). `check-proof-recipes.sh --base HEAD` (helper):
`0 unexcepted copy finding(s)`.

**On the proposal series** (wiring packet, as reported to the master; the logs for the first six gates are
not in this worktree and were not re-run here):

- `check-layering.sh`: OK (1005 modules).
- module size: OK; only the pre-existing `ProrataWethVaultCode` hard-cap breach.
- duplication: OK. debt: OK. residue: 96 -> 94 OK. trust surface: OK.
- recipes: `OK — proof-recipe gate (report-only): 8823 changed declaration(s); 0 unexcepted copy finding(s), 188 planned advisory finding(s)`.
- **`check-doc-counts.sh`: `REGRESSION — doc-counts: 3 disagreement(s) over 60 checked quotation(s), 3 transcript(s) and 7 path reference(s)`.**
  The three are reserved count quotations in `scripts/GATES.md`, not edited:
  - `:580` states 942 for the layering module count, produced 1005;
  - `:583` states 940 for the proof module-size count, produced 1003;
  - `:588` states 851 for the trust-surface closure count, produced 1002.
  The handoff records that the fork parent already had three mismatched module-count quotations and a leaf
  mismatch (1,523 actual versus 1,384 recorded); the produced values moved with the 33 new modules.

**Deliberately not run here** (user-agreed; they belong to the original host's combined-candidate run): the
full `Blanc` build, the registered axiom union walk, and check-elab timing. One attempt at the full `Blanc`
target on the wiring branch was interrupted (status `ERROR`, exit 143, target verdict `interrupted`, after
1006.6 s with 258 modules rebuilt) and yields no verdict; it was not resumed. The leaf figure is not
recomputed, and no figure here is whole-candidate axiom evidence: until the proposal's root imports are
applied, the new modules are outside the root closure and the union walk.

**Forbidden constructs.** Greps over every packet's added lines and the review's diff scan: zero
`sorry`, `admit`, `native_decide`, `axiom`; zero `set_option`, `maxHeartbeats` or `maxRecDepth` additions;
zero bare `simp`/`simpa`/`dsimp`/`simp_all`/`aesop`/`grind`; zero new `@[simp]` attributes. Two sites use
`simp (config := {decide := true}) only [...]` with an explicit lemma set
(`UniswapV2PairWeth9Frame.lean:48`, `:57`; the decide config is for literal selector disequalities). The
review (against `c37e2cd5`) counted 14 `decide +kernel` sites; a recount of the lane files at this tip finds
13 source lines with 19 occurrences (`UniswapV2PairWeth9GasFree.lean:106,170,175,204,219`;
`ModelControls.lean:242,253,276,299`; `MintCanonicalOwn.lean:22,40`; `OracleControls.lean:58`;
`SwapAbi.lean:227`). The difference from 14 is not reconciled. New `noncomputable def`s:
`precompileAnswer`, `mintFeeReplyKeys`, `mintTraceKeys`.

**Hostile review** (Claude Fable 5.1, read-only, candidate `c37e2cd5`): ACCEPT, with follow-ups. Cleanup
(`uv2sh-cleanup`, merged as `11d2e1a6`) addressed F2 (deleted `swap_bytecode_front_cut`,
`swapBack_exact_consumes`, `swapCheckFee_three`, `ethFits_of_budget` and `inflowSum`), F5 (dropped the unused
representation and HASH-T premises from the U4 control) and F7 (stale first-lane docs). Open after cleanup:
F1 (altitude gaps, carried in this document), F3 (mint HASH-T key list), F4 (`EthFits`), F6 (rr-cache), the F8
borderline `simp (config := …)` sites, and the F11 library-first notes.

## 8. Remaining obligations and disclosures

1. **U2 final control: blocked.** The goal's control is that the refinement fails against a 998 fee or a
   burn that rounds toward the user. Only typed-model disagreements exist. The final control needs the
   original host's Burn frame consumer and a concrete successful burn; that part is ours to build once it
   exists. The fee-998 route cannot bite under J1 (section 5).
2. **U10 not instantiated.** There is no Pair-history theorem yet. The adapter supplies inputs only, and its
   history theorem needs `HolderCalls`, `holderTracked`, `allowZero`, HASH-T `K₀`/`fresh` and `EthFits`.
   `EthFits` is an unproved running bound on the real chain's ether. Discharging it needs a fact exported
   from `Lift/Weth9` ("model ether ≤ real balance at each committed step", after which `EthFits` follows from
   `SumNof`), which this lane was not allowed to edit. If U10 is instantiated, this premise must appear in the
   claim map or be discharged first. The frame level excludes `withdraw`; the history theorem covers it.
3. **U6.** The positive theorem is original-host work. Our controls cover token0 of sync, skim and mint only
   (token1 would need a static-call code-preservation lemma; swap, burn and transfer callbacks have none).
   `¬ isPrecomp tok` is a genuine, fork-dependent premise, not discharged concretely. No formal reachable-state
   witness with a reverting token0 is built (`Creation/DeployInit` would supply the initialized checkpoint for
   arbitrary token addresses, but the existential execution was not constructed).
4. **Swap `short` premise.** Every swap theorem takes `short`: every actual CALL step of the root derivation
   returns fewer than 2^160 bytes. It is needed for the moved-pointer arithmetic (`p + 260 < 2^256`). Jaune's
   `call_step_returnData_length_lt_two_pow_160` proves it from the caller's gas-potential bound, which Blanc
   derives nowhere. It needs a gas or Jaune reply-length bound from the original host. It is an explicit
   hypothesis, never hidden in a definition.
5. **Skim pointer-fit discharge** stays original-host work (item 3 of section 6 explains the `128 ≤` change).
6. **Mint HASH-T key list.** `mintTraceKeys root` is a finite `List WriterKey` fixed by the root alone, with no
   cursor cut, but it is `noncomputable` (it uses `precompileAnswer`, a `Classical.choose` function whose
   uniqueness is proved by `precompileRun_ok_output_unique`) and over-inclusive: it contains the reply row of
   every successful raw frame root of the run and the precompile answer rows to `feeTo()`, not only the one
   factory reply. This is HASH-T by the letter (a larger trace-local universe is a stronger, still
   trace-local premise), but the history consumer must discharge injectivity and apartness over rows no
   execution touched. Whether the public wording tolerates that, or requires the cursor-cut route tying the
   fee reply to the single factory STATICCALL, is a decision for the master. Evaluation by `decide` of the
   list is not possible.
7. **Swap foreign storage.** `swap_bytecode_exact_consumes_own` constrains foreign storage only outside the
   transfer and callback CALLs: the lock prefix touches no foreign account, and the post-callback tail leaves
   it as the callback left it. Inside the actual CALL steps foreign storage may change, and no claim is made
   that those calls leave it unchanged (`LocalStorage` did not fit, as the swap body is not storage-local).
8. **Per-turn `targetLogEventsFrom`** provenance for swap transfer and callback turns is not exported by the
   front and not stated; only `LockedAuth` on every retained nested Pair turn is.
9. **No swap gas schedule.** The optional forward component schedule for swap (and for the back half) was not
   built. Mint has the component-schedule companion `mint_bytecode_forward_consumes`; reachable-state gas
   theorems are the original host's.
10. **Permit code bit.** The carried bit is the frame-entry bit: `true` when the recovery STATICCALL entered a
    code frame, `false` exactly in the enabled-precompile case. It is not literally `getCode 1 ≠ empty`. The
    gap is inert for the source (the recovery request has `requiresCode = false`, and `noCodeTurns` holds),
    but proving `views = []` for empty-code children needs emptiness lemmas not found in the shared library.
    Swap transfer replies use the constant `codeExists := true` (`swapTransferReply`), inert for the same reason.
11. **Superseded fork-era permit headlines.** `permit_bytecode_refines_source` (`PermitSource.lean:350`) and
    `permit_bytecode_refines_source_canonical` (`:489`) are superseded by `permit_bytecode_exact_turns`;
    `locked_permit_outcome` now consumes the latter. They have no other consumers and are listed for the
    original host's declaration-necessity review (they are fork-era, so this lane did not delete them).
    `PermitSourceResult` still carries the old unauthenticated `.done`-turn clause beside the authenticated
    conjunct, retained verbatim for compatibility.
12. **Global instance.** `ModelControls.lean:153` contains `deriving instance DecidableEq for RunStatus`, a global
    instance in a control module for an `Execution.lean` type. Delete it if the original host adds the
    instance to `Execution`.
13. **Model-altitude controls** are not EVM witnesses: U3(i), U3(ii), U5 and the model halves of U2 and U4 are
    reached typed-model runs on toy states. The U3(ii) control is per-step; a history restatement is owed if
    the final U3 claim is history-level. U5's reserves are 0, so it bites on the Δt conjunct only. A
    conditional universal theorem (U7, U4 bytecode half, U6) is not an existence proof of an execution.
14. **Orphans.** `ModelControls` and `UpdateOverflowWalk` were outside `Blanc.lean`'s root closure before the
    proposal series; the new modules stay outside the root build and union walk until the proposal's imports
    are applied.
15. **Not hoisted** (library-first notes): inline `B256` `x * 1 = x` in `swapPc0_inv`; contract-neutral
    comparison facts `swap_gt_of_gtCheck_ne`, `swap_not_gt_of_gtCheck_eq`, `swap_not_lt_of_ltCheck_eq` in
    `SwapCheckWalk`; `swapUpdate_inv` re-derives `update_inv` at a pointer `p` (a `p`-generic `update_inv`
    would remove it); `swap_rawWith_images` is a generic owned-map monotonicity; `swapTraceKeys := skimTraceKeys`
    is an alias (a neutral `pairTraceKeys` would be cleaner); `OracleControls` duplicates `answer`/`initialized`
    from `ModelControls` and asserts in a docstring an equality proved only in the unimported module; `SwapBack`
    imports `MintSource` for a heavier closure than needed.
16. **Review independence.** The hostile review was by Claude Fable 5.1, the same model family as the Claude
    Opus 5.5 authors, not a different family.
17. **rr-cache incident (process).** In the shared repository the swap-front worker ran `git stash -q; git stash
    pop -q`, which popped another session's `stash@{0}` ("prorata conversion unit before 2026-09-03 main
    rebase") into its worktree and conflicted. The worker restored the five tracked files to `HEAD`; the stash
    entry is intact and still listed, and the shared clone's `git status` is clean. The conflict state made
    rerere record resolutions in the shared `.git/rr-cache` when `e6bb1aae` was committed. The records created
    were `preimage.1` and `postimage.1` in the rr-cache directories whose names begin `ba09ada9`, `3fe3c0b5`,
    `c1d0cf9e` and `f6e2bfac`, plus the whole directory `5680807213754c9c8833be0b00a57ef5485e64d9`, all dated
    2026-10-05 between 16:00 and 16:01 (the Sep-29 `preimage` files predate them). The worker's cleanup was
    refused by the permission classifier, so those files are left for the user to remove: a later pop of that
    stash could otherwise be auto-resolved toward the worker's `HEAD`. The helper report also mentions a "stash
    comparison"; whether that used `git stash` was not established.
18. **Shared scratchpad.** Early log files of the permit packet may have collided with other packets' files of
    the same name in the shared scratchpad; one overwrite (mint's layering row) was caught and the gate rerun.
    This affects only scratch evidence, not repository content.

## 9. Local resource figures (informational)

These are not acceptance evidence and are not portable. They are not measured peaks.

- 13 proof-authoring worker packets (controls, mutants, permit, mint, mint2, mint3, weth9, weth9b, helper,
  swap-back, swap-front, swap-asm, u6ctl), plus one review, one cleanup, one wiring and this return-document
  packet.
- Wall clock for the lane about 5 hours.
- Narrow builds were admitted by the host semaphore on this host; the packet reports record no peak figure
  as a claim. Host-sensitive measurements (exact-candidate quiet elaboration, peak memory, the cost ledger)
  belong to the original host.
