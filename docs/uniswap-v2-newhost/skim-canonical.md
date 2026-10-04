# uv2nh-skim2 lane report (P6b, episode uv2nh-skim2-1)

Branch `claude/uv2nh-skim2`, worktree `~/blanc/.worktrees/uv2nh-skim2`, base `0b7e28a6`.
Commits: 814af83c (fold), bb1facc2 (selectors + lock exclusion), ac7df9c1 (locked supply),
6655d7d4 (call adapter), 60dabf8c (canonical skim), b74550c7 (raw log image). Final: b74550c7.
New files only; no existing file edited.

## Status

Delivered: `skim_bytecode_exact_consumes`, the canonical skim frame (no explicit turn-queue
or transport premise left), with an entry-parametric mutable-call turn producer and its
locked-Pair instance. Kept explicit: the transfer0 reply-pointer fit (see Remaining).

## Theorem map (U-conditions)

| Theorem | File:line | Statement | U |
|---|---|---|---|
| `skim_bytecode_exact_consumes` | SkimCanonical.lean:196 | Successful raw skim run (code, covered fork, selector 0xbc25cf77, rep, installed image, b.output=[], trace-local HASH-T over `skimTraceKeys`) ⇒ value 0, nonstatic, the actual first query/transfer0 steps (`SkimFirstSteps`), and, for a fitting transfer0 reply pointer, the second steps, `ExactConsumes (startTyped current ctx (.skim recipient))` over replies out0, transfer0 reply, out1, transfer1 reply with turn queues derived from the actual children (views via retained static frames; transfers via `targetLogEventsFrom`), final checkpoint/context, `WriterRep K'` (K' ⊆ HASH-T universe) of post Pair storage vs final state, unlocked=1, liquidityCore preserved, model logs = current ++ added, `post.logs = b.logs ++ L` with the raw image of added = L, selector/target authenticity of views, `LockedAuth` of every invoked frame, `post.output = []` | U2(a) frame |
| `mutable_retained_fold_inv` | MutableTurns.lean:169 | Entry-parametric (`PairFrameSupply`) fold over any committed run: derived `MutableTurn` list whose events = `targetLogEventsFrom`, ExactTurns continuation, Rep transport, raw-log image | U2(a) producer |
| `mutable_call_turns` | MutableTurns.lean:402 | One lifted CALL/STATICCALL step of a Pair frame ⇒ exact turn queue derived from the actual child (or empty when not entered / rolled back), Rep at the parent's post world, parent raw logs = pre ++ L with image | U2(a) producer |
| `lockedPairSupply` | LockedSupply.lean:209 | While locked, every committed Pair root frame is an exact invocation of transfer/approve/transferFrom/permit/initialize/view at the current checkpoint; rep grows only by decoded rows in the universe; lock-guarded entries cannot commit | U2(a) nested |
| `pair_bytecode_selector_inv` | PairSelectors.lean:320 | Any successful raw run carries one of the 27 published selectors (fallback reverts), any context | U2(a) J1 inverse |
| `pair_lockGuarded_unlocked` | PairLockedEntries.lean:303 | mint/burn/swap/sync/skim succeed only from slot12 = 1 (new burn/swap dispatch+decoder+lock walks; mint/sync/skim reuse) | U2(a) J1 inverse |
| `skim_static_call_turns` | SkimCanonical.lean:43 | One lifted STATICCALL step ⇒ retained static views of its actual child at the incoming frame | U2(a) producer |
| `Exec.targetLogEventsFrom_frames` | TargetLogEvents.lean:107 | Frame projection of the new log-interleaved traversal = existing `retainedTargetFramesFromAt` | generic headline |
| `Xinst.call_run_logs` | TargetLogEvents.lean:547 | CALL/STATICCALL appends exactly its committed child's logs, nothing otherwise | generic headline |

Consumed: `burn_raw_unlocked` :54, `swap_raw_unlocked` :156, `mint_raw_unlocked` :289; generic
TargetLogEvents step lemmas (storage, logs, code, child entry, membership); `childContext_writer`,
`mutable_selected_root`, `mutableTranscript_append`, `LockedRep.congr`, per-entry `locked_*_outcome`.

## Source correspondence (refined rows)

| Source | Raw | Model |
|---|---|---|
| `_safeTransfer(token0/1)` CALL | StepIn CALL at the helper (pointer 128 / moved p) | `.next (skimTransferReply out true) (mutableTranscript turns .done)`: turns = foreign LOGs and retained committed Pair frames of the actual child, in order |
| nested Pair frames while locked | any committed frame at the Pair inside the child | `.invoke caller value isStatic entry nested`; entries per `LockedAuth` (selector-decoded); lock-guarded entries excluded |
| `balanceOf` STATICCALL | StepIn STATICCALL | `staticViewTranscript views .done` from the child's retained static views |
| reserve1 after transfer0 | SLOAD 8 on transfer0's post world | `LockedRep` at that world + `skim_transfer0_reserve1` |

## Gate receipts (candidate b74550c7, PATH with ~/.local/bin first)

- `~/creme/scripts/creme lake-build uv2nh-skim2 -- Blanc.Lift.TargetLogEvents Blanc.Lift.UniswapV2Pair.MutableTurns Blanc.Lift.UniswapV2Pair.PairSelectors Blanc.Lift.UniswapV2Pair.PairLockedEntries Blanc.Lift.UniswapV2Pair.LockedSupply Blanc.Lift.UniswapV2Pair.SkimCanonical` → `Build completed successfully (1185 jobs).` status OK (all builds this session peak lean RSS ≤ ~1.7 GiB).
- `scripts/check-proof-module-size.sh` → `OK — proof module size (report-only): 964 modules; ... 1 new-module hard-cap breach(es)` (pre-existing ProrataWethVaultCode; largest new file 649 lines).
- `scripts/check-proof-duplication.sh` → `OK — proof duplication ratchet: 964 module(s), 34314 declaration(s); 1 K1 families ... 0 unexcepted rise(s)`.
- `scripts/check-proof-debt.sh` → `OK — proof-debt: 92 scopes inventoried; zero unexcepted new/increased findings`.
- `scripts/check-proof-residue.sh` → `OK — proof residue: 13/13 predicates checked; counts 96 -> 94; no rise`.
- `scripts/check-layering.sh` with the proposal below applied uncommitted → `REGRESSION — layering: 12 violation(s) across 14 contract(s), 966 module(s)`; all 12 are other packets' unclassified modules (Create2Deploy, CursorExact, Ecrecover, Creation.*, Permit*, SyncGasCanonical, WordImage); zero findings for the modules of this packet or P6.
- `grep -nwE 'sorry|admit|native_decide|axiom'` and bare-simp grep over the six new files → no output.

## Shared-wiring proposal (exact diff, applied only uncommitted)

```diff
diff --git a/docs/COMMON_API.md b/docs/COMMON_API.md
index 96f72494..b5f62244 100644
--- a/docs/COMMON_API.md
+++ b/docs/COMMON_API.md
@@ -1047,6 +1047,22 @@ childless calls advance the parent counter; interpreted children use
 subtree before the parent continuation is appended. These equations support
 a local producer over the retained frames; they do not establish its request,
 reply or contract-model correspondence.
+For a fold that must also see the actual foreign LOGs in order (the turn queue of
+a mutable external call), use `Exec.targetLogEventsFrom` in
+[`Blanc/Lift/TargetLogEvents.lean`](../Blanc/Lift/TargetLogEvents.lean): retained
+target frames interleaved with each foreign frame's successful `Exec.logAt?`.
+`Exec.targetLogEventsFrom_frames` proves its frame projection equals
+`Exec.retainedTargetFramesFromAt`, with matching `_target`, `_halt`, `_cont`,
+`_doneOk` and `_runOk` equations. The same module transports one foreign step for
+arbitrary callee code: storage of a code-bearing owner (`Evm.step_cont_getStor_foreign`,
+`Evm.step_done_getStor`, `Xinst.spawn_run_getStor`/`Evm.step_run_getStor`: the settled
+child's committed endpoint or the rollback, pointwise), logs (`Exec.cont_logs_eq`,
+`Exec.doneOk_logs_eq`, `Exec.runOk_logs_eq`, path-independent `Exec.committed_logs_at`,
+and `Xinst.call_run_logs`: a CALL/STATICCALL appends exactly its committed child's
+logs), the installed image (`CodeSem.At.parentStep`, `CodeSem.At.spawnChild`,
+`CodeSem.At.callChild`, self-calls included), child entry (`Xinst.spawn_child_world`,
+`Xinst.spawn_child_logs`, `Xinst.call_spawn_ofCall`, `Frame.ofCall_settle_clean`),
+`Exec.retainedTargetFramesFromAt_rawFrameRoot` and `Lift.StepIn.codePreserve`.
 The existing `goal-head:StateReplay` recipe selects chronology continuity;
 the joint chunk/Link/observation premises are discovered through this registry.

@@ -3521,6 +3537,9 @@ contract-neutral.
   from initialization, word writes or pointer changes; this is registry-only.
   The same module's `mergeFour_bytes` gives the fixed high-four/low-twenty-eight
   byte image of a masked word merge; see the M1 manual codec route above.
+- Free-pointer word without an allocation size: `PtrWord p M` in
+  [`Blanc/Lift/PtrWordMemory.lean`](../Blanc/Lift/PtrWordMemory.lean) keeps only
+  `Mem.Wf M` and the pointer word at offset64.
 - Gas-exact writer walks for solc-0.4-style runtimes: the scratch-memory invariant `FpMem n M` (word-aligned,
   free pointer `0x60`, kept for an arbitrary `M`; `FpMem.init`, `FpMem.write`, `FpMem.write_out`,
   `FpMem.readback`, `scratchW`), its steps (`rx_mstoreF`, `rx_mstoreOut`, `rx_mloadFp`, `rx_keccakF`,
diff --git a/scripts/check-layering.py b/scripts/check-layering.py
index 7f27b080..32d99809 100644
--- a/scripts/check-layering.py
+++ b/scripts/check-layering.py
@@ -169,6 +169,11 @@ SHARED += ["Lift.Loop", "Lift.CheckFast", "Lift.CheckAssembly", "Lift.ExactWalkO
 # Creation code (deploy-init-v1): the size-optimised packed-hash site and the CREATE bridge
 # for lifted creation code; contract-neutral.
 SHARED += ["Lift.PackedShaSize", "Lift.Deploy", "Lift.CreationOps"]
+# Size-free free-pointer word carrier for moved-pointer walks (uv2nh-skim)
+SHARED += ["Lift.PtrWordMemory"]
+# Retained target frames interleaved with actual foreign LOGs, and per-step storage/log
+# transport across arbitrary callee code (uv2nh-skim2): contract-neutral.
+SHARED += ["Lift.TargetLogEvents"]
 # Solc-0.4 scratch-memory walk kit and the value-bearing CALL to a code-free recipient
 # (weth9-liveness-v1): contract-neutral.
 SHARED += ["Lift.ExactWalkSolc", "Lift.ExactWalkCall"]
@@ -271,6 +276,16 @@ CONTRACTS = {
         "Lift.UniswapV2Pair.SyncWalk",
         "Lift.UniswapV2Pair.SyncTurns",
         "Lift.UniswapV2Pair.SyncCanonical",
+        "Lift.UniswapV2Pair.SkimWalk",
+        "Lift.UniswapV2Pair.SkimTransferWalk",
+        "Lift.UniswapV2Pair.SkimSecondWalk",
+        "Lift.UniswapV2Pair.SkimSource",
+        "Lift.UniswapV2Pair.SkimHandler",
+        "Lift.UniswapV2Pair.SkimCanonical",
+        "Lift.UniswapV2Pair.MutableTurns",
+        "Lift.UniswapV2Pair.PairSelectors",
+        "Lift.UniswapV2Pair.PairLockedEntries",
+        "Lift.UniswapV2Pair.LockedSupply",
         "Lift.UniswapV2Pair.StaticViewClassify",
         "Lift.UniswapV2Pair.StaticViewSource",
         "Lift.UniswapV2Pair.StaticViewTurns",
```
(The PtrWordMemory SHARED row and the five Skim* rows are P6's earlier proposal, repeated so
the gate classifies the skim chain; the COMMON_API PtrWord line here is abbreviated — use P6's
full entry text.)

## Remaining obligations / judgments

1. Fit: the second half is stated under `96 ≤ p ∧ p+1024 < 2^256` for p = `skimFirstPointer`
   of transfer0's reply; `skimFirstPointer_fit` discharges it for replies below 2^128 bytes. A
   gas-based discharge is not available: gas is an unbounded Nat, so no memory/returndata bound
   follows without a transaction gas-limit premise (shared with Burn).
2. Transfer flag: the existing skim walk facts do not expose the CALL success flag, so
   `mutable_call_turns` also covers the impossible branches (child not entered or rolled back):
   empty queue, storage/logs unchanged. Exposing the flag (additive strengthening of
   `skimTransferTail_inv`/`SkimFirstFacts`) would let the canonical theorem assert the entered
   child.
3. Permit nested turns: P3's permit frame uses `.next (permitExternalResult out false) .done .done`;
   a Pair view reached under a DELEGATED address-1 account at depth 2 is not lifted (storage
   unaffected). `codeExists` of the recovery observation is fixed to false.
4. Foreign storage of non-Pair accounts is not restated (transfers change token storage; the
   per-step lemmas give it pointwise if a consumer needs it).
5. Static view authenticity in the conclusion is selector+target only (the full `Authentic`
   at frame2 depends on internal c1).

## Consolidation (for the original host: Burn transfers, swap transfers and callback)

- `mutable_call_turns` + `lockedPairSupply` apply verbatim to any CALL step a locked Pair frame
  makes: Burn's two `_safeTransfer` CALLs and swap's transfers and `uniswapV2Call` callback
  (all run while locked). Give it the StepIn CALL fact from the walk, the model frame/request,
  `LockedRep` at the pre world; it returns the derived turn queue, the post-world `LockedRep`
  and the raw log image. Reserve transport follows as in skim (fixed slots of `WriterRep`).
- `skim_static_call_turns` is generic (any STATICCALL step of a Pair frame): reuse it for Burn's
  four and swap's two balance queries; recommend hoisting it beside `StaticViewTurns` under a
  neutral name.
- `pair_bytecode_selector_inv` and `pair_lockGuarded_unlocked` (incl. burn/swap dispatch,
  decoder and lock walks) are the J1 classification any nested-frame producer needs.
- Generic `Blanc/Lift/TargetLogEvents.lean` holds the contract-neutral traversal and per-step
  transport (COMMON_API entry text in the diff above).
- K1 note: `PairSelectors.pair_selector_inv` shares its fallback-branch text with
  `staticView_selector_inv` (the gate reports no rise); a later refactor could derive the
  static classifier from it.

## Follow-up (master should-fix, commit d5e1c67b)

The four queue clauses of `skim_bytecode_exact_consumes` now read:

```lean
        (views0 = [] ∨ ∃ (child : Evm) (raw : Execution)
          (childRun : Exec child.pc child.sta child.dyna raw),
          Execution.commits raw = true ∧
          (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots root.exc) ∧
          views0.map Prod.fst =
            (Exec.retainedTargetTurnsAt sevm.currentTarget [] childRun).filterMap
              Sum.getRight?) ∧
        (views1 = [] ∨ ∃ (child : Evm) (raw : Execution)
          (childRun : Exec child.pc child.sta child.dyna raw),
          Execution.commits raw = true ∧
          (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots root.exc) ∧
          views1.map Prod.fst =
            (Exec.retainedTargetTurnsAt sevm.currentTarget [] childRun).filterMap
              Sum.getRight?) ∧
        ((turns1 = [] ∧ sevm.benvStat.rules.isPrecomp
            (skimToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr) ∨
          ∃ (child : Evm) (raw : Execution)
          (childRun : Exec child.pc child.sta child.dyna raw)
          (committed : Execution.commits raw = true),
          (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots root.exc) ∧
          turns1.map MutableTurn.event =
            Exec.targetLogEventsFrom sevm.currentTarget [] 0 childRun committed) ∧
        ((turns3 = [] ∧ sevm.benvStat.rules.isPrecomp
            (skimToken1 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr) ∨
          ∃ (child : Evm) (raw : Execution)
          (childRun : Exec child.pc child.sta child.dyna raw)
          (committed : Execution.commits raw = true),
          (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots root.exc) ∧
          turns3.map MutableTurn.event =
            Exec.targetLogEventsFrom sevm.currentTarget [] 0 childRun committed) ∧
```

None of the four can be unconditional. Jaune routes a message to a precompile before it looks at
code (`executeCode.enter`), and the world may carry nonzero code at a precompile address. So a
skim whose token is, for example, 0x04 with code passes EXTCODESIZE. Identity then answers the
balance query (36 bytes, first word ≥ reserve) and the transfer (68 bytes, nonzero first word),
and no code frame is entered. The transfer clauses now name that exact raw fact. A transfer
queue is empty only when the token is an enabled precompile without a delegation designator.
Otherwise it is the derived projection of the committed actual child. The rolled-back case is
excluded by the exported CALL success flag.

The balance clauses gain `Execution.commits` (STATICCALL flag 1), but their empty branch is still
not tied to the precompile fact. The missing raw fact is a STATICCALL inversion that exports the
stepped slot, the STATICCALL analogue of the `Ninst.StepRun pc … xl` component of
`of_run_call_val_with_depth_frame` (LadderBase.lean:1702, shared). `of_run_staticcall_val_with_depth_cause`
(LadderBase.lean:2561) does not provide it. With it, `Xinst.call_none_precompile` would carry
over verbatim.

New, additive: `Xinst.call_run_flag_commits` (TargetLogEvents.lean:651), `Xinst.call_none_precompile`
(:706), `executeCode.enter_inr`, `skimTransferTail_flag_inv`, `skimTransfer_flag_inv`
(SkimTransferWalk.lean:1176), `SkimSecondFlagFacts`, `skimSecondHalf_flag_inv`, and `skim_raw_flag_inv`
(SkimSecondWalk.lean:513). Existing statements are unchanged; `skimTransferTail_inv`,
`skimTransfer_inv`, `skimSecondHalf_inv` and `skim_raw_inv` are now projections. The
packet-internal `mutable_call_turns` empty disjunct gained its raw reason (no code frame, or an
uncommitted child), and `skim_static_call_turns` gained a flag premise.

Gates at d5e1c67b:
- Narrow build of the nine affected modules: `Build completed successfully (1185 jobs)`, status OK.
- Module-size, duplication (34323 declarations, 0 unexcepted rise), debt and residue checks: OK.
- Grep for sorry/admit/native_decide/axiom and bare simp: no hits.
- No new modules, so the layering proposal is unchanged.

## Follow-up 2 (commit 009d191a)

`skim_bytecode_exact_consumes_own` (SkimCanonical.lean:205) = canonical statement plus own-code foreign-storage conjuncts (prefix segment, reserve1-read segment, tail after transfer1: `∀ a, a ≠ sevm.currentTarget → post.getStor a = d2.getStor a`); `skim_bytecode_exact_consumes` unchanged, now a projection. Gates OK, zero warnings.
