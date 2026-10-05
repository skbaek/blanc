# Uniswap V2 Pair: second new-host lane return

This is the second new-host lane's return for the allocation in
[`UNISWAP_V2_SECOND_HOST_HANDOFF.md`](UNISWAP_V2_SECOND_HOST_HANDOFF.md) (deliverables N1-N5). It covers
both waves of the lane. It is a work return, not an acceptance claim for the goal. The combined candidate,
the history lifts, the Burn frame, U6 positive liveness, U9, the U10 instantiation, the full gate
catalogue, the claim map and U11/U12 belong to the original host. The first split's return,
[`UNISWAP_V2_NEWHOST_RETURN.md`](UNISWAP_V2_NEWHOST_RETURN.md), is history and vocabulary.

Every theorem name and `file:line` below was checked by `grep` against the tree this document is
committed on (lane content tip `d17961cc`). Statements are transcribed from the packet reports and the
lane's docstrings. Line numbers move again at integration.

## Headline caveats (read these before the tables)

The full text is in [section 8](#8-remaining-obligations-and-disclosures); the machine-greppable open
hypotheses are in [section 8b](#8b-open-hypotheses-cross-host-and-lane-open).

- **Key finding: pair-to-WETH9 call shapes need a gas or memory bound.** Under Jaune's unbounded gas
  (`gasLeft` is a `Nat`, with no memory-offset cap) the free-memory pointer can wrap modulo 2^256, and a
  `_safeTransfer` CALL can then send garbage calldata. The `callsites-b` packet's executable model of the
  helper's operation sequence (not a Lean counterexample) gives selector `00000000` for such a run, which
  needs gas of about 2^494. So the call-site facts of the U10 chain hold only under
  `ChainMemoryBelow R (2^160)`, which the history form `CallSiteMemoryBound` (CROSS-HOST) assumes. It is
  the same family as `SwapCallReplyShort`, `SwapForwardReplyShort` and skim's pointer-fit. Its natural
  discharge is Jaune's per-step potential export in candidate `2737c8eb`, whose adoption awaits a user pin
  decision. This lane did not move the pin.
- **Under success-only frame refinement (decision J1) the fee-998 mutant cannot bite.** It accepts strictly
  more swaps than production, so only the burn-rounding route can bite for U2. The U2 control
  `burn_refinement_control` is therefore conditional on two CROSS-HOST hypotheses
  (`BurnFrameRefinement`, `BurnWitnessExists`) that need the original host's Burn frame consumer and a
  concrete successful burn.
- **U10 is not instantiated and its headline is conditional.** `weth9_history_holder_noShrink_pairCalls`
  discharges `HolderCalls` and `Weth9SelfTargetChildren`, but still takes two LANE-OPEN obligations
  (`TransferSiteShape`, `CallbackSiteShape`, each needing a reach-to-run link and a program-wide
  free-pointer invariant in reach form), a third (`EthFits`, an unproved running ether bound), five CROSS-HOST
  hypotheses, and `apart : p ≠ ca`.
- **U6 has controls only**, now for token0 and token1 of sync and mint, token0, token1 and the callback of
  swap, and token0 of skim, at pc-zero universal altitude with one concrete reverting callee code. The
  premise-free liveness refutation `sync_liveness_refuted` is over a family defined by the exact storage
  image of deploy plus initialize; no existential deployment execution reaching its witness world is built.
  The positive U6 theorem is the original host's.
- **The swap forward schedule is closed only modulo the callee CALL-state gas words and two CROSS-HOST
  `_safeTransfer` charge functions** (exact statement in section 3 and section 8). It is a conditional
  universal construction over ENV-class callee premises, not an existential execution for arbitrary callees.
- **Most controls are model or conditional altitude**, not reverting EVM executions: U3(i), U3(ii), U5 and
  the model halves of U2 and U4 are typed-model results; U7 and U4's bytecode half are universal over
  successful runs, and U7 is conditional on a storage alias.
- **Swap carries explicit `SwapCallReplyShort`** (every CALL reply of the run is below 2^160 bytes); mint's
  HASH-T key list is finite and fixed by the root, but noncomputable and over-inclusive; skim's conditional
  second-half premise is now `128 ≤ skimFirstPointer` (was `96 ≤`, master decision
  `uv2sh-n4-skim-pointer-bound`).
- **Not run here, deliberately (user-agreed)**: the full `Blanc` build, the registered axiom union walk and
  the check-elab timing. The leaf figure is not recomputed. `check-doc-counts` reports exactly the three
  reserved `scripts/GATES.md` count quotations, which were not edited.
- **Both hostile reviews were by Claude Fable 5.1**, the same Claude family as the lane authors, not a
  different family.
- **Process incident**: a stray `git stash pop` by a worker left rerere records in the shared
  `.git/rr-cache`.

## 1. Identity

- **Fork**: `6d6c04eb` (its parent is `8e10cca4`). The fork is published as
  `origin/codex/uniswap-v2-second-host-fork`. Every lane commit descends from it; no history was rewritten.
- **Lane branch**: `worker/uniswap-v2-second-host`. Its tip is the commit that adds this document, which is
  based on lane content tip `d17961cc` (merge of `uv2sh-cleanup2`). The first wave's content tip was
  `11d2e1a6`.
- **Wiring proposal series**: branch `claude/uv2sh-wiring-proposal`, tip `28d0c25f` (merge of lane content
  tip `d17961cc`; it does not contain this document). The original host merges the lane first and then the
  proposal. The series is:
  - wave 1: `49cc7fde` root imports, including the orphans `ModelControls` and `UpdateOverflowWalk`;
    `18ffec51` layering rows for the 33 first-wave modules; `7948042f` `docs/COMMON_API.md` entries for the 8
    first-wave shared modules; `03070a31` merge of the lane;
  - wave 2: `f7bdf93d` root imports of the second-wave Pair and WETH9 call-site modules; `4fd1464b` layering
    rows for the 23 second-wave modules; `d4f90ddf` `COMMON_API` batch 2 (the four second-wave shared
    modules); `28d0c25f` merge of the lane content tip.
- **Jaune pin**: unchanged at `780ad71a07787527cc074e06696d0e6a742ba104`. No Jaune change is made, and
  `lakefile.lean` and `lake-manifest.json` are untouched. Jaune candidate `2737c8eb` is not an available
  dependency of this lane.
- **Untouched surfaces**: `Execution.lean`, `Check*.lean`, `Blanc.lean`, `scripts/**`, the claim map, the
  counts, baselines, allowlists and goldens. Both hostile reviews found no original-host-owned file edited.
- **Authors**: the packet reports name Claude Opus 5.5 as the author of the proof packets. This document
  was written by Claude Sonnet 5.5, transcribing those reports.

## 2. Files added and changed

`git diff --stat 6d6c04eb..d17961cc`: 67 files changed, 12586 insertions, 1128 deletions. 56 `.lean` files
are new (all under `Blanc/`), 8 `.lean` files and 3 docs are modified. Numbers are added/deleted lines.

All file paths are in `Blanc/Lift/UniswapV2Pair/` unless prefixed with `Blanc/`.

### N1 mint (new-host: `Mint*`, `FeeMint*`, `SqrtWalk` surfaces)

| File | Lines | Role |
|---|---|---|
| `MintCanonical.lean` | +722 | pc-zero mint frame consumer, `mintTraceKeys` |
| `MintCanonicalOwn.lean` | +98 | foreign-storage variant, forward component schedule |
| `Blanc/Lift/PrecompileAnswer.lean` | +266 | shared: unique precompile answer, finite root-fixed reply source |
| `Blanc/Lift/LocalStorage.lean` | +139 | shared: storage-local entry sets whose only call is STATICCALL |

### N1 swap (new `Swap*` modules)

| File | Lines | Role |
|---|---|---|
| `SwapAbi`, `SwapFront`, `SwapTransfer`, `SwapCallback` | +235, +326, +241, +427 | ABI wrapper, body prefix, both optimistic transfers, conditional callback |
| `SwapFrontTyped`, `SwapFrontTurns`, `SwapFrontCanonical` | +146, +264, +155 | typed front, mutable turns and per-call provenance, front headline |
| `SwapCut` | +75 | the cut interface at `t_09c3_c5` between front and back |
| `SwapBalanceWalk`, `SwapCheckWalk`, `SwapUpdateWalk` | +415, +310, +275 | back-half raw walks |
| `SwapBack`, `SwapBackTurns` | +210, +215 | back-half raw inversion and typed consumption |
| `SwapCanonical` | +296 | pc-zero swap assembly (headline) |
| `SwapCallWorld` | +161 | per-call world: child turns and storage through a CALL (wave 2) |
| `SwapForward`, `SwapForwardPrefix`, `SwapForwardTransfer`, `SwapForwardCallback`, `SwapForwardFront` | +241, +274, +375, +316, +166 | forward exact-gas schedule: assembly and front half (wave 2) |
| `SwapForwardBalance`, `SwapForwardCheck`, `SwapForwardUpdate`, `SwapForwardBack` | +217, +237, +497, +124 | forward exact-gas schedule: back half (wave 2) |
| `SwapControls` | +74 | U4 pc-zero control (also N3) |
| `Blanc/Lift/InvWalkBranchToP.lean`, `MutableCallPost.lean`, `WordWindowMemory.lean` | +35, +58, +38 | shared helpers |

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
| `RefinementControls.lean` | +142 | U2 burn-rounding refinement control (wave 2) |
| `CalleeControls.lean`, `CalleeControlsSwap.lean`, `CalleeControlsReach.lean` | +195, +238, +163 | U6 failing-callee controls and the configured-family refutation |
| `Blanc/Lift/RevertingCallee.lean` | +158 | shared: a callee that fails on every input |
| `SwapControls.lean` | +74 | U4 (listed under N1 swap) |

### N4 transfer-helper consolidation

| File | Lines | Role |
|---|---|---|
| `SkimTransferWalk.lean` (modified) | +137/-687 | consumes `SafeTransferWalk`'s public pointer-generic API |
| `SkimSecondWalk.lean` (modified) | +51/-45 | `PtrMem` carriers, `128 ≤` bound |
| `SkimCanonical.lean` (modified) | see N2 | headline premise `128 ≤` |

### N5 WETH9 composition adapter and the U10 pair-side chain

| File | Lines | Role |
|---|---|---|
| `Blanc/Composition/UniswapV2PairWeth9.lean` | +409 | WETH9 ledger model, history reading, controls |
| `Blanc/Composition/UniswapV2PairWeth9Frame.lean` | +251 | frame-level answer, storage effect, NoShrink |
| `Blanc/Composition/UniswapV2PairWeth9GasFree.lean` | +225 | WETH9-specific two-run dispatcher walk |
| `Blanc/Lift/GasErasureRun.lean` | +420 | shared: equality modulo gas across two runs of a lifted tree |
| `Blanc/Composition/UniswapV2PairWeth9Calls.lean` | +191 | `HolderCalls` from the Pair's call shape; the U10 headline (wave 2) |
| `Blanc/Composition/Weth9SettledCallers.lean` | +86 | `Weth9SelfTargetChildren` proved from the WETH9 history premises (wave 2) |
| `PairCallShape.lean`, `PairCallSiteShape.lean`, `PairCallSites.lean`, `PairCallSitesCheck.lean` | +68, +46, +66, +44 | Pair call shape from the certificate's call sites (wave 2) |
| `Blanc/Lift/CallSite.lean`, `CallSiteChildren.lean`, `CallChildren.lean`, `CallerProvenance.lean` | +45, +217, +216, +213 | shared: call-site vocabulary and children of a certified frame, caller fold (wave 2) |

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
| U2(a) swap | `swap_bytecode_exact_consumes` | `SwapCanonical.lean:271` | A successful raw pc-zero swap (selector `0x022c0d9f`), under HASH-T over `WriterExtend K (swapTraceKeys root)` and `SwapCallReplyShort`, gives `SwapCanonicalBody`: the actual transfer and callback steps in their shapes, each carrying `SwapCallProvenance`, both post-callback balance STATICCALLs at the world the callback left, `ExactConsumes` of the driver, final unlock, `WriterRep`, both balances below 2^112, exact raw logs (`Sync`, `Swap`) with the typed logs mapping onto them, empty output | EVM-conditional (HASH-T, `SwapCallReplyShort`) | complete (frame component) |
| U2(a) swap | `swap_bytecode_exact_consumes_own` | `SwapCanonical.lean:188` | The above with foreign-storage silence for the lock prefix and the post-callback tail | EVM-conditional | complete |
| U2(a) swap | `swap_bytecode_front_cut_code`, `swapBack_exact_consumes_bounds` | `SwapFrontCanonical.lean:37`, `SwapBackTurns.lean:63` | Front half to the cut `SwapCut` (with Pair code unchanged); back half from the cut (with both balance bounds) | EVM-conditional | components consumed by the assembly |
| U2(a) swap, per call | `SwapCallProvenance`, `MutableCallWorld`, `mutable_call_world` | `SwapFrontTurns.lean:46`, `SwapCallWorld.lean:25`, `:41` | For each taken transfer and the callback: an actual CALL step `pre → d` of the root derivation, and either no turns with no child or a rolled-back child, or a committed child of that step whose turns are `targetLogEventsFrom pair [] 0 childRun`. In both cases the storage after the call of every account with code at the call is the child's endpoint storage (committed) or the pre-call storage | EVM-conditional | complete; accounts without code at the call are not characterised (a child CREATE can give them storage) |
| U2/U6 swap, forward | `swap_bytecode_forward_consumes` | `SwapForward.lean:196` | From the nonpayable, size and selector guards, the ABI guards, the entry representation, the source guards and the front and back forward environments, a successful pc-zero run exists with initial gas `swapFrontTransferGas pre … back.gas + swapPrefixGas … + 445` ending at the back half's world and memory with residual `g`; under HASH-T and `SwapCallReplyShort` that run satisfies `swap_bytecode_exact_consumes_own`'s result. **Cost is closed only modulo the callee CALL-state gas words `cg0 cg1 cgC` (tied to the next segment through each ENV premise's `gas`/`returnedGas` field) and the two CROSS-HOST `_safeTransfer` charge functions `pre n p` and `post n p reply`, parameters of `SwapSafeTransferForward`.** Callee frames are ENV-class premises (`SwapTransferCallForward`, `SwapCallbackCallForward`, `SwapBalanceEnv`); `SwapBackForwardEnv` also bundles the Pair-path primitive facts (input guard, `SwapKFacts`, uint112 bounds, non-static, the three `_update` SSTORE sentries, the unlock sentry) | component schedule, ENV premises | component; conditional on `SwapSafeTransferForward`, `SwapForwardReplyShort`, `SwapCallReplyShort` |
| U2/U6 swap, forward | `swapBody_exact`, `swapBody_front_exact`, `swapBack_exact` | `SwapForward.lean:159`, `SwapForwardFront.lean:88`, `SwapForwardBack.lean:103` | Body `t_0683_c54` forward run joined from the front half (lock prefix, both optional transfers, conditional callback) to the back half (two balance queries, inputs, `K` check, `_update`, `Swap` log, unlock); the back half alone ends with residual exactly `G` | component schedule, ENV premises | components; `swapDispatch_exact` (`:18`, 166 gas), `swapAbi_exact` (`:99`, 279) and `swapPc0_exact` (`:140`) wrap them |
| U2(a) permit | `permit_bytecode_exact_turns` | `PermitTurns.lean:226` | Every successful literal permit run gives the old guards, `PermitRecoveryAuth root out entered views`, `PermitSourceResult` at the actual bit, the authenticated `ExactConsumes`, and `Authentic` for every view | EVM-universal | complete (closes the first return's address-1 disclosure) |
| U2(a) skim | `skim_bytecode_exact_consumes_own`, `skim_bytecode_exact_consumes` | `SkimCanonical.lean:99`, `:380` | First-lane skim frame headlines, now over the consolidated helper; conditional second-half premise `128 ≤ (skimFirstPointer d.returnData).toNat` (was `96 ≤`) | EVM-conditional | complete as stated; the pointer-fit discharge is the original host's |
| U2(a) interface | `PairFrameOutcome`, `PairFrameSupply`, `LockedGood`, `LockedAuth`, `lockedPairSupply`, `mutable_call_turns` | `MutableTurns.lean:65`, `:77`; `LockedSupply.lean:43`, `:57`, `:234`; `MutableTurns.lean:417` | Derivation-keyed frame supply used by Burn, swap and history consumers (section 6) | interface | consumed by skim and swap |
| U2 control | `burn_refinement_control` (support `burn_witness_disagrees`, def `BurnReturnRefines`) | `RefinementControls.lean:124` (`:59`, `:76`) | `BurnFrameRefinement Rep Good Auth → BurnWitnessExists Rep Good Auth → ¬ BurnReturnRefines burnRoundUp Rep Good Auth`. The contradiction is `encodeWords [1,1] ≠ encodeWords [2,2]` after both refinements are pinned to the same run and transcript; only the returndata consequence is used | EVM-conditional on two CROSS-HOST hypotheses; the witness prefix (first mint, donation sync, LP transfer from `initializedState 0x1000 0 0x3000 0x3001`) is typed-model | **blocked on** the original host's Burn frame consumer and burn liveness; no EVM witness exists |
| U2 control (model) | `feeMutant_disagrees`, `burnRoundUp_disagrees` | `ModelControls.lean:269`, `:291` | At a reached checkpoint production rejects a swap (`UniswapV2: K`) and `feeMutant 2` (998) accepts it; after an actual LP transfer a burn returns `(1,1)` in production and `(2,2)` in `burnRoundUp` | model | supporting only; the fee route cannot bite under J1 |
| U3(ii) | `mintRoundUp_breaks_feeOff_product` | `ModelControls.lean:216` | Under `mintRoundUp`: initialize, first mint and a donation sync reach `checkpoint`; there production later mint satisfies the fee-off product (via `runTyped_feeOff_product`) and the mutant run returns `[2]` and violates it | model | complete at model altitude; a history restatement is owed if the final U3 claim is history-level |
| U3(ii) infra | `runTypedWith_production`, `driveWith_production`, `resumeWith_production`, `mintAmountUp_initial` | `ModelMutants.lean:301`, `:283`, `:262`, `:91` | `runTypedWith production = runTyped` for all inputs; the upward mutant equals production when supply is 0 | model | compatibility evidence |
| U3(i) | `noShrink_required` | `ModelControls.lean:115` | Reached `runTyped` chain (initialize, mint, donation sync, shrinking sync): `¬ SyncEntryNoShrink` and the fee-off product inequality fails. Reviewed, retained, not strengthened | model | complete at the goal's text altitude; no history or EVM counterexample |
| U4 | `swap_bytecode_uint112_control` | `SwapControls.lean:28` | Model half: balance 2^112 passes `swapCheck` and the typed swap fails. Bytecode half: every successful raw swap's two post-callback balance replies are below 2^112. Needs only the raw inversion and `SwapCallReplyShort` | model + EVM-conditional | component; no reverting pc-zero run is exhibited |
| U4 | `swap_uint112_control`; `update_overflow_exec`, `update_overflow_uint112_kernel_control` | `PropertiesSwap.lean:1151`; `UpdateOverflowWalk.lean:257`, `:390` | Fork-era model control; a concrete `Exec` that reverts with the OVERFLOW payload at the internal `_update` entry (pc `0x22e0`), storage, accounts and logs unchanged | model; concrete at an internal entry, not pc 0 | retained and reviewed |
| U5 | `oracle_law_requires_timestamp_wrap`; `OracleUpdate.LawfulNoWrap` | `OracleControls.lean:50`, `:20` | A sync at timestamp 2^32+1 and last 0: the exact Δt is 1 and the no-wrap mutant gives 2^32+1, so `Lawful ∧ ¬ LawfulNoWrap` | model | complete at model altitude; bites on the Δt conjunct only (reserves are 0) |
| U6 | `sync_no_success_of_reverting_token0`, `skim_no_success_of_reverting_token0`, `mint_no_success_of_reverting_token0` | `CalleeControls.lean:51`, `:103`, `:123` | With Pair code, a covered fork, the selector, slot 6 = `tok`, `b.getCode tok = revertingCode` and `¬ isPrecomp tok`, no successful pc-zero run exists | EVM-universal over raw runs, one concrete callee code | controls; positive theorem is original-host work |
| U6 | `sync_no_success_of_reverting_token1`, `mint_no_success_of_reverting_token1` | `CalleeControls.lean:71`, `:156` | The same with slot 7; the code survives the token0 STATICCALL child (`revertingCode_kept`) | EVM-universal over raw runs | controls |
| U6 | `swap_no_success_of_reverting_token0`, `swap_no_success_of_reverting_token1`, `swap_no_success_of_reverting_callback` | `CalleeControlsSwap.lean:122`, `:158`, `:208` | `amount0Out ≠ 0` with reverting token0; `amount1Out ≠ 0` with reverting token1; non-empty `data` with a reverting recipient: no successful raw swap. Token1 and callback take `SwapCallReplyShort` (CROSS-HOST); token0 does not (the transfer runs at the PC0 pointer) | EVM-universal over raw runs (token1 and callback conditional) | controls |
| U6 | `sync_liveness_refuted`, `reachWorld_configured`, `initialize_reaches_configured` | `CalleeControlsReach.lean:154`, `:118`, `:68` | `¬ ∀ w pair, ConfiguredWorld w pair → SyncLive w pair`, kernel-checked. `ConfiguredWorld` is the family of worlds with the certified runtime at `pair` and storage equal to the exact deploy-plus-initialize image (`initializedStor`, `:44`); `reachWorld` is a member whose token0 holds `revertingCode`, and `0x2000` is a non-precompile on Prague, Osaka, BPO1 and BPO2 (kernel `decide` per fork list). `initialize_reaches_configured` is the U8 link: a successful pc-zero `initialize` at the constructor image ends in a `ConfiguredWorld` (universal direction only) | EVM-universal for the controls; the world is concrete, its reachability is not | control; **no existential deploy+initialize execution reaching `reachWorld` is proved**; refutes premise-free liveness for sync only |
| U6 infra | `revertingCode`, `revertingCode_exec_error`, `processMessage_not_clean_of_reverting`, `not_staticAnswered_of_reverting`, `revertingCode_kept`, `call_flag_zero_of_reverting` | `Blanc/Lift/RevertingCallee.lean:31`, `:51`, `:77`, `:111`, `:123`, `:134` | `PUSH0 PUSH0 REVERT`; every frame over it errors; no clean settlement; no `StaticAnswered` over it; successful steps keep it installed; a CALL to it leaves flag 0 | EVM-universal | shared |
| U7 | `approve_storage_alias_breaks_ledger` | `LedgerKeyControl.lean:38` | A successful pc-zero approve with `approveSlot = (balance a).slot`, `a ∈ keys`, and an amount different from the raw balance of `a`: `¬ WriterFreshKeys K (approveTouched caller spender)` and `¬ RawLedgerOn keys post` | EVM-conditional (alias hypothesis) | control complete; no colliding preimage is claimed and no run is exhibited |
| U7 infra | `footprintSum_cons`, `footprintSum_le_footprintSum`, `footprintSum_lt_footprintSum` | `Blanc/Lift/LedgerFootprintOrder.lean:18`, `:24`, `:36` | Pointwise order of footprint sums; strict with one strictly grown row, no `Nodup` | generic | shared |
| U8 | `pairAddress_wrong_salt`, `pairAddress_wrong_initHash` | `Creation/Facts.lean:108`, `:113` (first lane) | Kernel evaluations; retained, not regenerated | concrete (kernel) | retained |
| U1 | byte-mutation certificate control | Plans `evidence/uniswap-v2-pair-bytecode-v1/certificate/` | Byte 1 `0x80 → 0x81` refutes `Cert.check`, restored green; disposable-tree evidence, not repository source | concrete | retained |
| U10 | `weth9_history_holder_noShrink_pairCalls` | `Blanc/Composition/UniswapV2PairWeth9Calls.lean:166` | `weth9_history_holder_noShrink` with the pair-side `HolderCalls` replaced by the call-site chain and `Weth9SelfTargetChildren` proved from the WETH9 history premises. Premises: `apart : p ≠ ca`, `holderTracked`, `allowZero`, HASH-T `K₀`/`fresh`, `budget : EthFits …`, `TransferSiteShape`, `CallbackSiteShape`, `PairFramesRunPairCode`, `PairSendsNoRootMessage`, `CallSiteMemoryBound` | EVM-conditional | **conditional; not instantiated** (blocked on the Pair history theorem and the open hypotheses of section 8b) |
| U10 | `pairCalls_holderCalls` | `UniswapV2PairWeth9Calls.lean:122` | `HolderCalls p (replayCalls (committedInvocations ca trace))` from the site facts, `CallSiteMemoryBound`, the Pair-code and no-root facts and `Weth9SelfTargetChildren`; folds over the settled frames' parents with `settledFrames_callerTarget_of_children` (`Blanc/Lift/CallChildren.lean:192`) | EVM-conditional | consumed by the headline |
| U10 | `weth9_history_settled_children_caller`, `weth9_history_settled_runsCode` | `Blanc/Composition/Weth9SettledCallers.lean:60`, `:25` | From the `weth9_history_committed` premises, every direct child of a settled non-static frame at `ca` has caller `ca` (this discharges `Weth9SelfTargetChildren`, `UniswapV2PairWeth9Calls.lean:113`); each such frame runs WETH9 code at pc 0 on a covered fork | EVM-universal over WETH9 history | complete (static frames are handled by `Exec.childFrames_isStatic`) |
| U10 | `pair_callsTransferOrCallback`, `pair_call_site`, `cert_callSites` | `PairCallShape.lean:37`, `PairCallSites.lean:48`, `PairCallSitesCheck.lean:37` | Every successful Pair-code frame (pc 0, empty stack and memory, chain memory below 2^160) calls non-statically only with the `transfer` or `uniswapV2Call` selector. A chain node decoding CALL sits at one of three certificate sites (`t_09aa_c4`, `t_20e1_c57`, `t_20e1_c71`); `cert_callSites` is a kernel check (`decide +kernel` per entry, 102 entries) that the certificate has no other CALL node. This classification replaced the four per-entry call-shape hypotheses (`BurnCallShape`, `QuietEntriesCallShape`, `SkimCallShape`, `SwapCallShape`), which no longer exist | EVM-conditional (`TransferSiteShape`, `CallbackSiteShape`, memory bound) | classification complete; the two site facts are LANE-OPEN |
| U10 | `weth9_balanceOf_answer`, `weth9_transfer_returns_true`, `weth9_transfer_effect`, `weth9_transfer_fails_of_lt` | `Blanc/Composition/UniswapV2PairWeth9Frame.lean:76`, `:148`, `:110`, `:136` | Over any successful fresh WETH9 frame: `balanceOf` answers the `balSlot` word with storage unchanged; `transfer` returns true (no gas premise); the storage effect is exactly the ledger move; a transfer above the balance never succeeds | EVM-universal over WETH9 frames | adapter inputs |
| U10 | `weth9_frame_holder_noShrink` | `UniswapV2PairWeth9Frame.lean:203` | Successful non-`withdraw` frame under `(footSpec U).Pre`, caller ≠ p, p's tracked allowances 0: they stay 0 and p's balance word does not fall | EVM-universal | adapter input |
| U10 | `weth9_history_holder_noShrink` | `UniswapV2PairWeth9.lean:340` | Over a configured history, p's checkpoint balance ≤ its future balance + `holderOut p (replayCalls (committedInvocations ca trace))`; allowances stay 0. Premises: `HolderCalls`, `holderTracked`, `allowZero`, HASH-T `K₀`/`fresh`, `EthFits` | EVM-conditional | conditional on `EthFits` |
| U10 | `control_allowZero_needed`, `control_holderCall_needed`, `control_ethFits_needed` | `UniswapV2PairWeth9.lean:379`, `:390`, `:402` | Kernel counterexamples to `Ledger.step_holder` (`:213`) with one premise dropped | model | complete at model altitude |
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
(transfer, approval, `Sync`, `Swap`). Wave 2 adds per-call provenance: for each taken transfer and the
callback, `SwapCallProvenance` names the actual CALL step `pre → d` of the root derivation, with the world
(`MutableCallWorld`) pinned by that same step's `Xinst.Run`, so turns, storage and the call are one
execution. Transfer0 runs from `swapPrefixWorld sevm b` to `b1`, transfer1 `b1 → b2`, callback `b2 → d`.

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

**WETH9 and the Pair's calls to it.** Every WETH9 frame result consumes an actual `Exec 0 sevm pre (.ok post)`
of the deployed WETH9 bytes, read through `lift_sound_in cert_check` and `weth9_frame_effect`. The output facts
carry no gas premise: the gas-exact forward walks `weth9_balanceOf_runExact` and `weth9_transfer_runExact` are
run from `pre.withGasLeft N`, and a two-run comparison modulo gas (`SFunc.RunP.eqModGas`,
`weth9_twin_wrapper`) transfers their output to the actual frame. The history result consumes
`weth9_history_committed`. The caller of a committed WETH9 frame is traced upward through its parents: a frame
at `ca` with caller `p` is a settled root (excluded by `PairSendsNoRootMessage`), a direct child of a settled
frame at `p` (whose selector is `transfer` or `uniswapV2Call` by `pair_callsTransferOrCallback`, which
`wethHolderSafe_of_selector` decodes as a transfer or a deposit), or a same-target child of a frame at `ca`
(excluded by `Weth9SelfTargetChildren`, proved). No witness is synthetic and token success is never assumed as
a result.

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
| U2 burn rounds up (`burn_refinement_control`, model `burnRoundUp_disagrees`) | EVM-conditional on `BurnFrameRefinement` and `BurnWitnessExists` (CROSS-HOST); the witness steps are typed-model | The mutant statement is the production statement with `production` replaced by `burnRoundUp`; the contradiction rests on `encodeWords [1,1] ≠ encodeWords [2,2]` (kernel `decide`). With `burnRoundUp := production` the mutant statement would equal the first hypothesis and the theorem would be false, so the mutant carries the refutation. No EVM execution witness exists. The witness state does not reuse `burnReady` (its factory and pair addresses 0x10 and 0x11 are precompiles on Prague and later) and fixes the domain separator to 0 (independence not proved) |
| U4 uint112 (`swap_bytecode_uint112_control`) | Model + EVM-universal, conditional on `SwapCallReplyShort` | Model half is the existing falsifier (`swap_uint112_control`). Bytecode half is a non-existence statement for balances ≥ 2^112 in successful runs; no raw mutation campaign. The concrete reverting run is at the internal `_update` entry (`UpdateOverflowWalk`), not pc 0 |
| U6 reverting callee (`*_no_success_of_reverting_*`) | EVM-universal over raw runs, one concrete callee code; sync, mint, swap on both tokens and the callback, skim token0 | Loop-only evidence for the first sync token0 control (`lean_multi_attempt`): clearing the token-code premise or `¬ isPrecomp tok` made the closing step fail. The later controls consume `tokenCode`, `recipientCode` and `notPrecompile` syntactically; no mutation run was done for them. This is not a committed mutation record. The defeat argument for a premise-free liveness statement is formalised only for sync, as `sync_liveness_refuted` |
| U10 premises (`control_allowZero_needed`, `control_holderCall_needed`, `control_ethFits_needed`) | Model (WETH9 ledger), kernel `rfl`/`decide` | Each is a counterexample to `Ledger.step_holder` with one premise dropped |
| U10 call-site check (`cert_callSites`) | Kernel decision over the generated certificate | With `callbackCall` dropped from `pairCallOk`, a disposable uncommitted module (deleted afterwards) failed to build: three "`decide` proved that the proposition is false" errors and one kernel application-type mismatch, all at the `decide +kernel` line. The unmodified module builds green |
| U1 certificate, U8 wrong salt / init hash | Concrete, retained | Not regenerated |
| Layering control | Source gate | `check-layering.sh` reports unclassified-module REGRESSIONs without the rows and OK with them |

## 6. Interface changes the original host must absorb

All are in new-host-owned files unless stated. At the fork the only consumers were `LockedSupply` and
`SkimCanonical`, both updated.

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
   owned. An optional variant of the dynamic API at `96 ≤ p` would restore the old bound. A public
   moved-pointer forward theorem there (the sibling of `safeTransfer_first_exact`) would discharge
   `SwapSafeTransferForward`.
5. **Swap interface (wave 2)**: `short` is now the named `SwapCallReplyShort D sevm`
   (`SwapTransfer.lean:149`, same body). `SwapCanonicalBody` gains `SwapCallProvenance` conjuncts for each
   taken transfer and the callback (a strengthening). `pair_callsTransferOrCallback` takes
   `ChainMemoryBelow … (2^160)`. `mutable_call_world` (`SwapCallWorld.lean:41`) restates
   `mutable_call_turns` with the child tied to the CALL step, because the latter's committed disjunct does not
   tie its child to the step; proposal: make `mutable_call_turns` a corollary of `mutable_call_world` and hoist
   both to a contract-neutral module (N2-owned `MutableTurns` was not edited for this).
6. **WETH9 adapter interface** the original host instantiates, with `ca` = WETH9, `p` = exhibit pair,
   token1 = WETH9 (USDC = token0 stays environmental). The preferred entry is now
   `weth9_history_holder_noShrink_pairCalls`, whose remaining inputs are:
   - the CROSS-HOST hypotheses `PairFramesRunPairCode p trace`, `PairSendsNoRootMessage p trace` (Pair history
     replay) and `CallSiteMemoryBound p trace` (Jaune potential export), and `holderTracked : K₀ (.bal p)` and
     `allowZero` at the deployment checkpoint, with HASH-T `K₀` and `fresh`;
   - the LANE-OPEN obligations `TransferSiteShape`, `CallbackSiteShape` and
     `budget : EthFits (checkpoint.state.bal ca).toNat (replayCalls (committedInvocations ca trace))`
     (`UniswapV2PairWeth9.lean:274`), the model ether run along the committed deposits and withdrawals staying
     below 2^256 at every deposit;
   - `apart : p ≠ ca`, and the identification of `holderOut p …` with the Pair's own transfer amounts in its
     replay.
   Use `weth9_balanceOf_answer` for an observed `balance1`, `weth9_transfer_effect` and
   `weth9_transfer_returns_true` for a Pair `_safeTransfer` to WETH9, `weth9_transfer_fails_of_lt` for the
   failure branch, and `weth9_frame_holder_noShrink` for each non-Pair WETH9 frame between the two
   observations of a burn; supply `(footSpec U).Pre` from the WETH9 ladder. Withdraw re-entry is segmented
   through history or `Ledger.run_holder`.
7. **History consumers of mint and swap**: discharge `WriterInj/WriterApart` over `mintTraceKeys root` and
   `swapTraceKeys root := skimTraceKeys root` before obtaining any reply; a global list universe can
   concatenate them. `swap` imports `SkimCanonical` for that alias.
8. **Shared-wiring proposals**: the 56 layering rows, the 12 `COMMON_API` entries (8 first-wave, 4
   second-wave) and the root imports are in the proposal series (section 1), not in the lane.

## 7. Gate verdicts

Commands were run from the packet worktrees with `~/.local/bin` first on `PATH`. Owned builds go through
`~/creme/scripts/creme lake-build <label> -- <targets>`; no bare Lake build was used.

**Narrow owned builds, wave 1 (packet reports).** All status `OK`:

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

**Narrow owned builds, wave 2 (packet reports).** All status `OK`; each report records the source gates
below green at its checkpoint:

| Packet | Result |
|---|---|
| weth9c (2328fc20, docstrings only) | `Build completed successfully (1065 jobs).` |
| u2ctl (f154165e) | `Build completed successfully (1054 jobs).` |
| swap2 (767e318e / c67a26c2) | `(1207 jobs)` / `(1206 jobs)` |
| u6ctl2 (a4b24923) | `Build completed successfully (1208 jobs).` |
| u10 (0857beb1) | `(942 jobs)` and `(1179 jobs)`, 0 warnings |
| weth9d (96aafffc) | `Build completed successfully (1181 jobs).` 0 warnings |
| swapfwd-back (4f40f91c) | `Build completed successfully (1123 jobs).` |
| swapfwd-front (ade1fca3) | `Build completed successfully (1214 jobs).` |
| callsites (7f89343e) | `Build completed successfully (1069 jobs).` |
| callsites-b | `(1137 jobs)`, fresh; no code written |

The `uv2sh-cleanup2` follow-up (`aa45b5a4`, `d6a31d4e`) did not leave a build report that I read.

**Source gates.** In every packet worktree: `check-proof-module-size.sh` OK (only the pre-existing
`ProrataWethVaultCode.lean` hard-cap breach); `check-proof-duplication.sh` OK (baseline 1/2/1, no unexcepted
rise); `check-proof-debt.sh` OK (`92 scopes inventoried; zero unexcepted new/increased findings`);
`check-proof-residue.sh` OK (`13/13 predicates checked; counts 96 -> 94; no rise`). The swap-back packet also
ran `check-trust-surface.sh`: `OK — trust surface: 12 exact allowlisted occurrence(s) across 967 module(s)`.
`check-proof-recipes.sh --base HEAD` (helper): `0 unexcepted copy finding(s)`.

**On the proposal series tip `28d0c25f`** (wiring packet, as reported to the master; these logs are not in this
worktree and were not re-run here):

- `check-layering.sh`: OK (1028 modules classified).
- module size: OK; only the pre-existing `ProrataWethVaultCode` hard-cap breach.
- duplication: OK. debt: OK. residue: 96 -> 94 OK. trust surface: OK.
- narrow build of the root-imported Pair and Composition modules: `Build completed successfully (1308 jobs).`
- **`check-doc-counts.sh`: REGRESSION with only the three reserved count quotations in `scripts/GATES.md`,
  not edited:**
  - `:580` layering module count 942, produced 1028;
  - `:583` proof module-size count 940, produced 1026;
  - `:588` trust-surface closure count 851, produced 1025.
  The handoff records that the fork parent already had three mismatched module-count quotations and a leaf
  mismatch (1,523 actual versus 1,384 recorded); the produced values moved with the 56 new modules.

**Deliberately not run here** (user-agreed; they belong to the original host's combined-candidate run): the
full `Blanc` build, the registered axiom union walk, and check-elab timing. One earlier attempt at the full
`Blanc` target on the first-wave wiring branch was interrupted (status `ERROR`, exit 143, target verdict
`interrupted`, after 1006.6 s with 258 modules rebuilt) and yields no verdict; it was not resumed. The leaf
figure is not recomputed, and no figure here is whole-candidate axiom evidence: until the proposal's root
imports are applied, the new modules are outside the root closure and the union walk.

**Forbidden constructs.** Greps over every packet's added lines and the reviews' diff scans: zero `sorry`,
`admit`, `native_decide`, `axiom`; zero `set_option`, `maxHeartbeats` or `maxRecDepth` additions; zero bare
`simp`/`simpa`/`dsimp`/`simp_all`/`aesop`/`grind`; zero new `@[simp]` attributes. Two sites use
`simp (config := {decide := true}) only [...]` with an explicit lemma set
(`UniswapV2PairWeth9Frame.lean:48`, `:57`; the decide config is for literal selector disequalities). A
recount of the lane files at `d17961cc` finds 16 source lines with 25 occurrences of `decide +kernel`
(`UniswapV2PairWeth9GasFree.lean` 5, `ModelControls.lean` 4, `MintCanonicalOwn.lean` 2,
`RefinementControls.lean` 2, `OracleControls.lean` 1, `SwapAbi.lean` 1, `PairCallSitesCheck.lean` 1 lines).
(The first review counted 14; the difference is not reconciled.) New `noncomputable def`s:
`precompileAnswer`, `mintFeeReplyKeys`, `mintTraceKeys`. Two global instances were added: `deriving
instance DecidableEq for RunStatus` (`ModelControls.lean:153`) and `deriving instance DecidableEq for SFunc`
(`CallSiteChildren.lean:27`, in a SHARED module).

**Hostile reviews** (both Claude Fable 5.1, read-only, same family as the authors):

- Wave 1, candidate `c37e2cd5`: ACCEPT with follow-ups. Cleanup (`uv2sh-cleanup`, merged as `11d2e1a6`)
  addressed F2 (deleted `swap_bytecode_front_cut`, `swapBack_exact_consumes`, `swapCheckFee_three`,
  `ethFits_of_budget` and `inflowSum`), F5 and F7.
- Wave 2, candidate `32882331`: ACCEPT with carried gaps. `uv2sh-cleanup2` (merged as `d17961cc`) then deleted
  `swapBody_front_cut` (over-strong `pairKeep` premise), `swapRaw_of_check` and the superseded caller fold
  `CallerIssuers` (`aa45b5a4`), made `initialize_reaches_configured` a named headline, removed the stale
  `CROSS-HOST` marker from `HolderCalls`, named `SwapCallReplyShort` in the swap controls, and re-labelled
  `EthFits` LANE-OPEN (`d6a31d4e`). The carried findings are in section 8 (items 12-16).

## 8. Remaining obligations and disclosures

1. **U2 final control: conditional, blocked.** The goal's control is that the refinement fails against a 998
   fee or a burn that rounds toward the user. `burn_refinement_control` is proved but conditional on
   `BurnFrameRefinement` and `BurnWitnessExists` (section 8b). It needs the original host's Burn frame consumer
   (instantiate `Rep := WriterRep K`, `Good` its HASH-T and reply-bound premises, `Auth` its observation
   relation) and a concrete successful raw burn at a state `Rep`-related to the typed-model `burnReady`, whose
   prefix (mint, sync, LP transfer) has no EVM witness; the domain separator is fixed to 0, and `Auth`
   determining the transcript at the witness run is also the original host's to show. If `BurnWitnessExists` is
   never discharged the control proves nothing about the refinement. Only returndata is compared. The fee-998
   route cannot bite under J1 (section 5). Review-2 F7 carries this gap.
2. **U10 not instantiated; the headline is conditional.** There is no Pair-history theorem yet. Open inputs
   are the LANE-OPEN `TransferSiteShape`, `CallbackSiteShape` and `EthFits`, the CROSS-HOST
   `PairFramesRunPairCode`, `PairSendsNoRootMessage`, `CallSiteMemoryBound`, `holderTracked` and `allowZero`,
   and `apart : p ≠ ca`. The last (`apart`) is trivially true for the exhibit pair but was missing from the
   first report of the headline's conditions (review-2 F5). The frame level excludes `withdraw`; the history
   theorem covers it.
3. **`EthFits` is an unproved running bound on the real chain's ether.** The packet established that it cannot
   be derived from facts exported to the Composition stratum: the model ledger at each committed step can be
   linked to the real ledger at that frame's entry in Composition (about 150 lines, `Linked`), but the
   per-frame fact `trackedSum U (pre storage) + value ≤ bal ca` is not exported (the generic
   `ConfiguredHistoryTrace.entryGood_settled` carries only a storage invariant). Routes: generalise
   `entryGood_settled` so `EntryGood` also reports `(footSpec U).Pre`, or a `Lift/Weth9` export of "model ether
   ≤ real balance at each committed step". Master decision `uv2sh-weth9-ethfits-disclosed`. If U10 is
   instantiated this premise must appear in the claim map or be discharged first.
4. **The memory/gas bound** (section "Headline caveats"). `ChainMemoryBelow R (2^160)` is a premise of
   `pair_callsTransferOrCallback`, and the history form `CallSiteMemoryBound` is CROSS-HOST. Even with it,
   neither site fact follows from the bound alone: each also needs a free-pointer lower bound at the encoding
   block's entry (a pointer below `0x5c` for the callback, below 96 for the transfer, lets the head writes
   overwrite slot `0x40`, from which the CALL re-reads its input offset). That lower bound is a
   certificate-wide reachable-state invariant that no existing walk states in reach form.
5. **LANE-OPEN site shapes.** `TransferSiteShape` and `CallbackSiteShape` are this lane's own open obligations.
   The route (master decision `uv2sh-u10-stop-at-site-shapes`): a reach-to-run determinism link that carries
   the facts of a synthetic forward walk (`swapCallbackCall_inv` has them as premises `PtrMem q`,
   `128 ≤ q < 2^162`, `len ≤ 2^32`) to the actual node, plus a program-wide free-pointer invariant in reach
   form. With length 68 the actual transfer CALL is always the `t_20e1_c71` clone. The callback target fact
   (`target ≠ token0/1`, and then `≠ WETH9`, which needs a further history premise) was not attempted.
6. **U6.** The positive theorem is original-host work. Controls cover sync and mint (token0 and token1), swap
   (token0, token1, callback) and skim token0. Not done: skim token1 and skim's transfer CALL (a token that
   answers `balanceOf` but fails `transfer` is a different callee code), burn, and the amount-free swap token0
   control (with `amount0Out = 0` a reverting token0 still kills swap at the back-half STATICCALL, not
   formalised). Swap token1 and the callback carry `SwapCallReplyShort`. `¬ isPrecomp tok` remains a genuine,
   fork-dependent premise of every control; it is discharged concretely only for `reachWorld`. No existential
   deploy-plus-initialize execution reaching `reachWorld` is built, so `sync_liveness_refuted` holds for the
   family as defined (the U2/U8 checkpoint image), and a liveness theorem refutes through it only when its
   accepted-frame set is non-empty.
7. **Swap `SwapCallReplyShort` and the CROSS-HOST reply bounds.** Every swap theorem except the token0 U6
   control takes `SwapCallReplyShort` (every CALL step returns fewer than 2^160 bytes), needed for the
   moved-pointer arithmetic (`p + 260 < 2^256`); the forward twin is `SwapForwardReplyShort`. Jaune's
   `call_step_returnData_length_lt_two_pow_160` proves it from the caller's gas-potential bound, which Blanc
   derives nowhere. `swap_bytecode_forward_consumes` re-assumes `SwapCallReplyShort` on the constructed run
   although its CALL steps are already bounded by the ENV premises (a redundant premise, not wrong; review-2 F4).
8. **Swap forward schedule is a conditional construction (review-2 F4).** `swapBody_exact` and
   `swap_bytecode_forward_consumes` are closed only modulo the callee CALL-state gas words and the two
   CROSS-HOST charge functions (section 3). The callee premises (`SwapBalanceEnv`, `SwapTransferCallForward`,
   `SwapCallbackCallForward`) are genuinely callee-side, but **`SwapBackForwardEnv` bundles Pair-path facts under
   the "Env" name** (input guard `guard`, `k`, uint112 bounds `bound0/1`, `static`, the `sentries`, `unlock`);
   its docstring discloses this, and "ENV class" in module headers should not be read as covering them. The
   forward schedule does not need `SwapCut`. `swapUpdate_exact` re-derives `update_exact`'s composition at
   pointer `p` (a `p`-generic `update_exact` in the shared `UpdateWalk` would remove it).
9. **Skim pointer-fit discharge** stays original-host work (section 6, item 3). The `128 ≤` change makes the
   conditional second-half clause strictly weaker on paper.
10. **Mint HASH-T key list.** `mintTraceKeys root` is a finite `List WriterKey` fixed by the root alone, with no
    cursor cut, but it is `noncomputable` (it uses `precompileAnswer`, a `Classical.choose` function whose
    uniqueness is proved by `precompileRun_ok_output_unique`) and over-inclusive: it contains the reply row of
    every successful raw frame root of the run and the precompile answer rows to `feeTo()`, not only the one
    factory reply. This is HASH-T by the letter (a larger trace-local universe is a stronger, still
    trace-local premise), but the history consumer must discharge injectivity and apartness over rows no
    execution touched. Whether the public wording tolerates that, or requires the cursor-cut route tying the
    fee reply to the single factory STATICCALL, is a decision for the master. Evaluation by `decide` of the
    list is not possible.
11. **Swap foreign storage and turn provenance.** `swap_bytecode_exact_consumes_own` constrains foreign storage
    outside the transfer and callback CALLs (the lock prefix touches no foreign account, and the
    post-callback tail leaves it as the callback left it). Inside each CALL, `MutableCallWorld` now states the
    storage of every account with code at the call (the child's endpoint storage if committed, the pre-call
    storage otherwise); accounts without code at the call are not characterised. The no-turn case is stated raw
    (`Xinst.Run .none` or a rolled-back child), not in skim's `isPrecomp` form, because `SwapTransferCall` does
    not export the CALL's success flag. There is no per-call code-frame `extcodesize` bit for transfers
    (`swapTransferReply` uses the constant `codeExists := true`, inert because a transfer request has
    `requiresCode = false`).
12. **Permit code bit.** The carried bit is the frame-entry bit: `true` when the recovery STATICCALL entered a
    code frame, `false` exactly in the enabled-precompile case. It is not literally `getCode 1 ≠ empty`. The
    gap is inert for the source (the recovery request has `requiresCode = false`, and `noCodeTurns` holds),
    but proving `views = []` for empty-code children needs emptiness lemmas not found in the shared library.
13. **Superseded fork-era permit headlines.** `permit_bytecode_refines_source` (`PermitSource.lean:350`) and
    `permit_bytecode_refines_source_canonical` (`:489`) are superseded by `permit_bytecode_exact_turns`;
    `locked_permit_outcome` now consumes the latter. They have no other consumers and are listed for the
    original host's declaration-necessity review (they are fork-era, so this lane did not delete them).
    `PermitSourceResult` still carries the old unauthenticated `.done`-turn clause beside the authenticated
    conjunct, retained verbatim for compatibility.
14. **Global instances (review-2 F6).** `ModelControls.lean:153` contains `deriving instance DecidableEq for
    RunStatus`, a global instance in a control module for an `Execution.lean` type; delete it if the original
    host adds the instance to `Execution`. `CallSiteChildren.lean:27` contains `deriving instance DecidableEq for
    SFunc`, a global instance on a shared type in a SHARED module (benign: the kernel check compares trees at
    CALL nodes only, but every importer sees it).
15. **Model-altitude controls** are not EVM witnesses: U3(i), U3(ii), U5 and the model halves of U2 and U4 are
    reached typed-model runs on toy states. The U3(ii) control is per-step; a history restatement is owed if
    the final U3 claim is history-level. U5's reserves are 0, so it bites on the Δt conjunct only. A
    conditional universal theorem (U7, U4 bytecode half, U6) is not an existence proof of an execution.
16. **Orphans and wiring.** `ModelControls` and `UpdateOverflowWalk` were outside `Blanc.lean`'s root closure
    before the proposal series; the new modules stay outside the root build and union walk until the
    proposal's imports are applied.
17. **Not hoisted** (library-first notes): inline `B256` `x * 1 = x` in `swapPc0_inv`; contract-neutral
    comparison facts `swap_gt_of_gtCheck_ne`, `swap_not_gt_of_gtCheck_eq`, `swap_not_lt_of_ltCheck_eq` in
    `SwapCheckWalk`; `swapUpdate_inv` re-derives `update_inv` at a pointer `p`; `swap_rawWith_images` is a
    generic owned-map monotonicity; `swapTraceKeys := skimTraceKeys` is an alias (a neutral `pairTraceKeys`
    would be cleaner); `OracleControls` duplicates `answer`/`initialized` from `ModelControls`; `SwapBack`
    imports `MintSource` for a heavier closure than needed; `addressSlotWriteWord_toAdr` and `warm_getCode`
    (the latter duplicates `temporalAccountAccessBase_getCode` in the Lido pause-suffix walk) belong in a
    common module; forward-walk helpers `swapStoreCost`, the `swapfwd_rx`/`sfw_rx`/`sfc_rx` step macros and a
    shared `rx_address` are candidates.
18. **Review independence.** Both hostile reviews were by Claude Fable 5.1, the same model family as the Claude
    Opus 5.5 authors, not a different family.
19. **rr-cache incident (process).** In the shared repository the swap-front worker ran `git stash -q; git stash
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
20. **Shared scratchpad.** Early log files of the permit packet may have collided with other packets' files of
    the same name in the shared scratchpad; one overwrite (mint's layering row) was caught and the gate rerun.
    This affects only scratch evidence, not repository content.

## 8b. Open hypotheses: CROSS-HOST and LANE-OPEN

Both tables are generated from `grep -rn "CROSS-HOST HYPOTHESIS\|LANE-OPEN OBLIGATION" Blanc` at the tip, which
finds 11 `CROSS-HOST HYPOTHESIS` marker lines (nine rows below; the `holderTracked`/`allowZero` row covers three of the lines) and 3
`LANE-OPEN OBLIGATION` marker lines. Consumers are the declarations whose docstring
carries a `CROSS-HOST: conditional on …` or `LANE-OPEN: conditional on …` line. Paths are in
`Blanc/Lift/UniswapV2Pair/` unless prefixed with `Blanc/`; "marker" is the line of the marker text, "def" the
line of the declaration.

**Consolidation procedure (one line):** instantiate each hypothesis at its consumers with the discharging
theorem, delete the `def` and its marker lines, and check that the `grep` above returns nothing.

### CROSS-HOST (original host or Jaune; delete at consolidation)

| Name | marker / def | Consumers | Expected discharge |
|---|---|---|---|
| `SwapCallReplyShort D sevm` | `SwapTransfer.lean:144` / `:149` | `swapTransfers_inv` (`SwapTransfer.lean:156`), `swap_bytecode_uint112_control` (`SwapControls.lean:28`), `swap_bytecode_front_cut_code` (`SwapFrontCanonical.lean:37`), `swap_bytecode_exact_consumes_own` (`SwapCanonical.lean:188`), `swap_bytecode_exact_consumes` (`:271`), `swap_no_success_of_reverting_token1` (`CalleeControlsSwap.lean:158`), `swap_no_success_of_reverting_callback` (`:208`), `swap_bytecode_forward_consumes` (`SwapForward.lean:196`) | The caller gas-potential reply-length bound, Jaune `call_step_returnData_length_lt_two_pow_160` (from `gasMeasure + memcost < 2^256` at the CALL), via the original host or the pending Jaune dependency work (candidate `2737c8eb`, user pin decision) |
| `SwapForwardReplyShort d` | `SwapForwardTransfer.lean:209` / `:214` | `SwapFrontForwardEnv` (`SwapForwardFront.lean:57`), `swapBody_front_exact` (`:88`), `swapFwdOpt_layout` (`SwapForwardTransfer.lean:255`), `swapFwdTransfers_exact` (`:303`), `swapBody_exact` (`SwapForward.lean:159`), `swap_bytecode_forward_consumes` (`:196`) | The same Jaune bound, applied to the environment's actual `CALL` step; the forward twin of `SwapCallReplyShort`. Nothing discharges it at consolidation unless the ENV premises are replaced by actual callee runs |
| `SwapSafeTransferForward pre post` | `SwapForwardTransfer.lean:14` / `:25` | `swapFwdTransfer0_call` (`SwapForwardTransfer.lean:66`), `swapFwdTransfer1_call` (`:107`), `swapFwdOpt_layout` (`:255`), `swapFwdTransfers_exact` (`:303`), `swapBody_front_exact` (`SwapForwardFront.lean:88`), `swapBody_exact` (`SwapForward.lean:159`), `swap_bytecode_forward_consumes` (`:196`) | A public dynamic-pointer forward theorem in `SafeTransferWalk`, the moved-pointer sibling of `safeTransfer_first_exact` (which has the same shape at `p = 128`, `n = 192`, `pre = 620`); original host. The charge functions `pre n p` and `post n p reply` are parameters of the hypothesis |
| `PairFramesRunPairCode p trace` | `Blanc/Composition/UniswapV2PairWeth9Calls.lean:78` / `:84` | `pairCalls_holderCalls` (`:122`), `weth9_history_holder_noShrink_pairCalls` (`:166`) | The original host's Pair history replay: the Pair analogue of `weth9_history_committed`'s code-intact conjunct, with `Exec.rawFrameDescendants_entry`/`_fresh` and the Pair certificate's CALL/STATICCALL-only restriction |
| `PairSendsNoRootMessage p trace` | `UniswapV2PairWeth9Calls.lean:90` / `:94` | `pairCalls_holderCalls` (`:122`), `weth9_history_holder_noShrink_pairCalls` (`:166`) | The original host's Pair history replay: `TransactionTrace.sender_ne` (EIP-3607) with the Pair code installed at each transaction's begin state, and `systemAddress ≠ p` |
| `CallSiteMemoryBound p trace` | `UniswapV2PairWeth9Calls.lean:98` / `:105` | `pairCalls_holderCalls` (`:122`), `weth9_history_holder_noShrink_pairCalls` (`:166`) | Jaune's per-step potential export (`gasMeasure + memcost(memory.size)` never grows along a chain, public in candidate `2737c8eb`, private at the current pin) with entry gas below 2^256; may merge with `SwapCallReplyShort` at consolidation |
| `holderTracked`, `allowZero` (hypotheses, not defs) | `UniswapV2PairWeth9.lean:335`, `:337`; `UniswapV2PairWeth9Frame.lean:200` / theorem lines `UniswapV2PairWeth9.lean:340`, `UniswapV2PairWeth9Frame.lean:203` | `weth9_history_holder_noShrink` (`UniswapV2PairWeth9.lean:340`), `weth9_frame_holder_noShrink` (`UniswapV2PairWeth9Frame.lean:203`), `weth9_history_holder_noShrink_pairCalls` (`UniswapV2PairWeth9Calls.lean:166`) | The original host's choice of the checkpoint footprint `K₀` (the exhibit pair's balance row is tracked), and its deployment-checkpoint fact that the Pair never grants a WETH9 allowance (it never calls `approve`); at frame level, carried from the checkpoint by `weth9_history_holder_noShrink` |
| `BurnFrameRefinement Rep Good Auth` | `RefinementControls.lean:89` / `:96` | `burn_refinement_control` (`RefinementControls.lean:124`) | The original host's Burn frame consumer (every successful raw burn run `ExactConsumes` the decoded `.burn` entry on its authenticated transcript with `post.output` equal to the finished bytes), composed with `runTyped_of_exact` and `runTypedWith_production`; instantiate `Rep := WriterRep K` |
| `BurnWitnessExists Rep Good Auth` | `RefinementControls.lean:100` / `:107` | `burn_refinement_control` (`RefinementControls.lean:124`) | The original host's burn liveness: a concrete successful raw burn run at the certified runtime on a covered fork, at timestamp `1700000000`, from storage `Rep`-related to `burnReady`, whose every `Auth`-authenticated reading is `.burn holder` with transcript `ModelControls.burnTranscript` |

### LANE-OPEN (this lane's own open obligations)

| Name | marker / def | Consumers | Route |
|---|---|---|---|
| `TransferSiteShape` | `PairCallSiteShape.lean:30` / `:35` | `pair_callsTransferOrCallback` (`PairCallShape.lean:37`), `pairCalls_holderCalls` (`UniswapV2PairWeth9Calls.lean:122`), `weth9_history_holder_noShrink_pairCalls` (`:166`) | A backward walk through `_safeTransfer`'s memcpy loop and encoding block with a free-pointer lower bound at the helper's entry: a reach-to-run determinism link plus a program-wide free-pointer invariant in reach form (master decision `uv2sh-u10-stop-at-site-shapes`) |
| `CallbackSiteShape` | `PairCallSites.lean:21` / `:34` | `pair_callsTransferOrCallback` (`PairCallShape.lean:37`), `pairCalls_holderCalls` (`UniswapV2PairWeth9Calls.lean:122`), `weth9_history_holder_noShrink_pairCalls` (`:166`) | A backward walk over the straight block `t_08e8_c4` → `t_09aa_c4` with a reachable-state free-pointer fact at its entry (`0x5c ≤ p`, no wrap of `p + 0xa4 + len`); the same reach-to-run link and invariant (decision `uv2sh-u10-stop-at-site-shapes`) |
| `EthFits` | `Blanc/Composition/UniswapV2PairWeth9.lean:269` / `:274` | `Ledger.run_holder` (`UniswapV2PairWeth9.lean:281`), `weth9_history_holder_noShrink` (`:340`), `weth9_history_holder_noShrink_pairCalls` (`UniswapV2PairWeth9Calls.lean:166`) | An `EntryGood`/ladder generalisation exposing `(footSpec U).Pre` at every committed frame entry (a generalised `ConfiguredHistoryTrace.entryGood_settled`) plus the model-to-real ledger link, or a `Lift/Weth9` export (decision `uv2sh-weth9-ethfits-disclosed`) |

## 9. Local resource figures (informational)

These are not acceptance evidence and are not portable. They are not measured peaks.

- Wave 1: 13 proof-authoring worker packets (controls, mutants, permit, mint, mint2, mint3, weth9, weth9b,
  helper, swap-back, swap-front, swap-asm, u6ctl), plus one review, one cleanup and one wiring packet. Wall
  clock about 5 hours.
- Wave 2: 10 worker packets (weth9c, u2ctl, swap2, u6ctl2, u10, weth9d, swapfwd-back, swapfwd-front,
  callsites, callsites-b), plus a second review, a second cleanup and the wiring update. Their wall clock is
  not recorded in the reports I read.
- Narrow builds were admitted by the host semaphore on this host; the packet reports record no peak figure
  as a claim. Host-sensitive measurements (exact-candidate quiet elaboration, peak memory, the cost ledger)
  belong to the original host.
