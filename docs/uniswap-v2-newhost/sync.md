# uv2nh-sync (P1) lane report — episode uv2nh-sync-1

Branch `claude/uv2nh-sync`, base 577edbac, checkpoint **c71a8215** (two new files, nothing else).

## Theorem map

| U-condition | Declaration | file:line | Statement |
|---|---|---|---|
| U2(a) sync, deliverable 1 "state/gas alignment" (also U6 material) | `syncPc0_canonical_live` | Blanc/Lift/UniswapV2Pair/SyncGasCanonical.lean:515 | From the WIP 7ae1533a premises (accepted syncPc0_exact ENV: compiled child calls call0/call1, success stacks, returnedGas0/1, widths, uint112 bounds, sentries) there is a run with `post.gasLeft = G`. Under trace-local HASH-T (now written `WriterInj … → WriterApart … → …`), there is a `SyncCanonicalResult` for that same run with `returned0.devm = d0`, `returned1.devm = d1`, `out0 = d0.returnData` and `out1 = d1.returnData`. |
| generic (consumed) | `cursor_cut_exact` | Blanc/Lift/CursorExact.lean:198 | Start from a successful actual frame at a checked cursor, with a `SFunc.CutAt` path to `tgt` and a gas-exact synthetic run of the cut tree halting in `s`. Then the actual node at `tgt` exists, with an `ExecFreeUntil` span from the start, the same sevm and outcome, a checked cursor, and `N.devm = s`. |
| generic (consumed) | `cursor_callNext_exact` | CursorExact.lean:384 | Crosses one internal call edge with its exact `PopBurnBy [d] gMid` state. |
| generic (consumed) | `Exec.Deriv.ExecFreeUntil.eq_of_execAt` | CursorExact.lean:410 | Two frame-entry-free spans from one node that end at decoded exec instructions end at the same node. |
| generic support (consumed) | `ninstRun_eq_of_runCompiled` :34, `popBurnBy_eq_of_length` :42, `burnBy_eq` :65, `ConfStep.of_dest/of_branch/of_branchTo/of_callNext` :91–110, `CursorOK.jumpdestAt_of_dest/jumpiAt_of_branch/jumpiAt_of_branchTo/jumpAt_of_callNext` :124–157, `SFunc.CutAt` :177 | CursorExact.lean | Support lemmas: functional exact frames, inversion of a stateful step by node kind, and decoded jump bytes under checked control nodes. |
| contract-local (consumed, private) | `sync_dispatch_cut` :21, `sync_first_call_cut` :277, `sync_second_call_cut` :443, the `*_cut_rx` chunks, `syncFirstCallInput` :269, `syncSecondCallInput` :431, `SyncBalanceSite.afterCallTree` :131, `syncUpdateUnlockClosedGas` :491 | SyncGasCanonical.lean | The actual cuts root → first STATICCALL and first return → second STATICCALL, each with its complete pre-state. |

### How the two WIP holes closed
The holes were firstInput and secondInput: the complete pre-states of the canonical occurrences. Both are now derived; no ENV or endpoint premise was added.
- A cut walk goes from root through the dispatcher, then `cursor_callNext_exact`, then the callee prefix, and reaches node A. Its state is derived as `syncFirstCallInput` (`= pre0`).
- `ExecFreeUntil.eq_of_execAt` with `order.firstFree` gives `A = result.first.node`.
- `cursor_next_forward` plus `ninstRun_eq_of_runCompiled` with `call0` gives the continuation state `d0`. `ParentStep.unique` with `order`'s edge identifies that continuation as `returned0`.
- The second cut walk from `returned0` reaches `pre1` (`syncSecondCallInput`), and the same identification gives `second.node` and `returned1 = d1`.

On "existing cursor conclusions hide gas": the existing `ConfStep`/`Jinst.Run` facts, together with the existing exact-gas jump lemmas, were enough. No common-library exact-lift annotation of `lift_exact` was needed. The generic piece is the new cut-tree file above, which is a proposal for the master.

## Correspondence rows (refined entry)
sync 0xfff6cae9: the canonical success frame (SyncCanonical.lean:187) is now tied to the compiled exact-gas run. The result's actual returned worlds and outputs are the ENV's d0/d1. The only new definitions are the pre-call state names `syncFirstCallInput`/`syncSecondCallInput`, which are definitional restatements of the syncPc0_exact call0/call1 inputs.

## J1 failure-branch coverage (sync): no gap found, nothing added
Every `.ok` sync run takes the success path. The existing inverses that establish this:
- `sync_raw_source_handler_inv` (SyncWalk.lean:2060) gives value = 0, 4 ≤ calldata size, isStatic = false, unlocked = 1, both code sizes ≠ 0, both STATICCALL flags = 1 (`StaticCallPost … 1`, via `SyncPrimitiveCallPair`), both reply widths ≥ 32 and < 2^256, and `State.update = .ok`. `State.update = .ok` implies both balances < 2^112 (Model.lean:148).
- `sync_canonical_source_frame_result` restates value, static and unlocked in `sourceEffects`.
- Primitive-level inverses: `sync_raw_inv` :1853 (value, size), `syncLockGuard_inv` :973 (locked), `syncFirstRequestLine_inv` :776 (static, via SSTORE), `syncCodeGuard_inv` :284 (missing code), `balanceCall_inv`/`balanceReturn_inv` (BalanceCallWalk.lean; failed or short reply), `syncCallee_inv` :1031 (uint112 bounds).
- Turn level: `sync_revert_guard_no_ok` SyncTurns:314, `sync_fallback_no_ok` :608, `sync_locked_failure_no_ok` :1527, `sync_balance_failed_call_no_ok` :2478, `sync_first_failed_call_no_ok` :2499.
- Overflow REVERT control: `update_overflow_exec` UpdateOverflowWalk.lean:257.

## Gate receipts (worktree, at c71a8215 content)
1. `~/creme/scripts/creme lake-build uv2nh-sync -- Blanc.Lift.CursorExact Blanc.Lift.UniswapV2Pair.SyncGasCanonical` → `Build completed successfully (1167 jobs).`, status OK. Log: creme/.creme/lean-build-ownership/logs/uv2nh-sync-20261004T191830.126386Z-55004.log. No lane module imports the new files, so there are no other consumers to build.
2. With `~/.local/bin` first on PATH:
   - `check-proof-module-size.sh` → `OK — proof module size (report-only): 942 modules; …1 new-module hard-cap breach(es)…`. The breach is the pre-existing ProrataWethVaultCode.lean. New files: 419 and 709 lines.
   - `check-proof-duplication.sh` → `OK — proof duplication ratchet: … 0 unexcepted rise(s)`.
   - `check-proof-debt.sh` → `OK — proof-debt: 92 scopes inventoried; zero unexcepted new/increased findings`.
   - `check-proof-residue.sh` → `OK — proof residue: 13/13 predicates checked; counts 96 -> 94; no rise`.
3. `check-layering.sh` → `OK — layering: 14 contract(s) are siblings; 944 module(s) classified …`. This ran with both proposals below applied uncommitted, then both were reverted.
   - Without the COMMON_API entry: `REGRESSION … CursorExact.lean is classified SHARED … but docs/COMMON_API.md never cites it`.
   - Without the CONTRACTS row: `REGRESSION … SyncGasCanonical is not classified`.
   - Restoring gave OK, so both controls bite.
4. `grep -nwE 'sorry|admit|native_decide|axiom'` and the bare-simp grep over both files: 0 hits (rc=1). No maxHeartbeats, maxRecDepth or @[simp] added.

## Shared-wiring proposals (exact diffs, not committed)
```diff
diff --git a/scripts/check-layering.py b/scripts/check-layering.py
index 7f27b080..38569c41 100644
--- a/scripts/check-layering.py
+++ b/scripts/check-layering.py
@@ -187,7 +187,7 @@ SHARED += ["Lift.CommittedLogs", "Lift.SegmentedReplay", "Lift.SegmentedHistory"
 SHARED += ["Lift.CalldataGuards", "Lift.StaticCall", "Lift.StaticCallGuard", "Lift.WalkSteps", "Lift.MapSlot", "Lift.Vyper", "Lift.PackedWord"]
 # The frame cursor, the reentrancy-lock exclusion kit and its bytecode checker, owner
 # discipline, and concrete-run evaluation (deployed-lido-vyper-v1): contract-neutral.
-SHARED += ["Lift.Reach", "Lift.ReachWalk", "Lift.ReachChain", "Lift.Cursor", "Lift.CursorCuts", "Lift.CallRestriction", "Lift.StaticOnlyFrames", "LockExclusion", "OwnerDiscipline", "ConcreteRun",
+SHARED += ["Lift.Reach", "Lift.ReachWalk", "Lift.ReachChain", "Lift.Cursor", "Lift.CursorCuts", "Lift.CursorExact", "Lift.CallRestriction", "Lift.StaticOnlyFrames", "LockExclusion", "OwnerDiscipline", "ConcreteRun",
            "Lift.LockCheck", "Lift.LockCheckSound", "Lift.LockCheckFlow"]
 # The constant memory map and its checker, code tries as data, and the executable-witness
 # engine with its child runs and spawn facts (deployed-lido-vyper-v1, V-): contract-neutral.
@@ -271,6 +271,7 @@ CONTRACTS = {
         "Lift.UniswapV2Pair.SyncWalk",
         "Lift.UniswapV2Pair.SyncTurns",
         "Lift.UniswapV2Pair.SyncCanonical",
+        "Lift.UniswapV2Pair.SyncGasCanonical",
         "Lift.UniswapV2Pair.StaticViewClassify",
         "Lift.UniswapV2Pair.StaticViewSource",
         "Lift.UniswapV2Pair.StaticViewTurns",
diff --git a/docs/COMMON_API.md b/docs/COMMON_API.md
index 96f72494..0a9ed83b 100644
--- a/docs/COMMON_API.md
+++ b/docs/COMMON_API.md
@@ -3228,6 +3228,24 @@ contract-neutral.
   covered fork; they do not establish child context, settlement or ordered
   history. The joint node/tree premises are discovered here because the
   existential result alone is not a reliable recipe trigger.
+- To pin the *complete* actual state (gas and world metadata included) at a
+  later cursor of a successful raw suffix, use
+  [`Blanc/Lift/CursorExact.lean`](../Blanc/Lift/CursorExact.lean). Build
+  `SFunc.CutAt fs tgt f f'` along the actual path (`next` for frame-free
+  instructions, `dest`, `zero`/`succ`, `toZero`, and `toSucc` inlining
+  `fs[k]`), then prove the gas-exact synthetic run of the cut tree with the
+  usual `rx_*` kit ending in `rx_stop`; `cursor_cut_exact` returns the actual
+  node at `tgt`, its `ExecFreeUntil` span, cursor, unchanged static
+  environment/outcome and `N.devm` equal to the synthetic halting state.
+  `cursor_callNext_exact` crosses one internal call edge with its exact pop.
+  `Exec.Deriv.ExecFreeUntil.eq_of_execAt` identifies two frame-entry-free
+  spans from one node ending at decoded frame-entering instructions (use it to
+  identify a cut with a canonical occurrence), and `ninstRun_eq_of_runCompiled`
+  pins an actual primitive step against a compiled one from the same state.
+  `popBurnBy_eq_of_length`, `burnBy_eq` and `ConfStep.of_dest`/`of_branch`/
+  `of_branchTo`/`of_callNext` are the supporting inversions. Worked use:
+  `syncPc0_canonical_live` in
+  [`Blanc/Lift/UniswapV2Pair/SyncGasCanonical.lean`](../Blanc/Lift/UniswapV2Pair/SyncGasCanonical.lean).
 - To expose the six actual STATICCALL operands, use
   `cursor_staticcall_operands` in
   [`Blanc/Lift/CursorCuts.lean`](../Blanc/Lift/CursorCuts.lean). `CursorOK` and
```

## Remaining obligations
- The master applies the two diffs above, plus the doc-count or `GATES.md` module counts if the catalogue requires them (944 classified modules). The new module also needs the full catalogue run at integration (proof-recipes, check.sh, check-elab).
- Configured-frame and history refinement, and reachable-state discharge of the ENV (U6 reachable gas), remain with the original host.
- The certify/elab gates were not run (outside the narrow-checkpoint contract).

## Follow-up (master review 1.1/1.2), commit 556e1908 on top of the lane tip 6b6dd21b (ff-merged)

| U-condition | Declaration | file:line |
|---|---|---|
| U2(a) foreign storage (review 1.1) | `sync_bytecode_foreign_storage` | SyncGasCanonical.lean:729 |
| U2(a) sync headline frame (review 1.1 + 1.2) | `sync_bytecode_exact_consumes` | SyncGasCanonical.lean:749 |
| support (private, consumed) | `syncResultWorld_getStor_foreign` | SyncGasCanonical.lean:~710 |

Statements (verbatim):
```lean
theorem sync_bytecode_foreign_storage {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    ∀ a, a ≠ sevm.currentTarget → post.getStor a = b.getStor a := by

theorem sync_bytecode_exact_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (hashTInj : WriterInj (WriterExtend K
      (syncTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (hashTApart : WriterApart (WriterExtend K
      (syncTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩))) :
    sevm.value = 0 ∧ sevm.isStatic = false ∧
    ∃ result : SyncCanonicalResult K current invocation
        ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b post,
      let ctx := writerContext sevm invocation
      let frame0 := syncSourceLockedFrame current ctx
      let frame1 := syncSourceSecondFrame current ctx
      let request0 := requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)
      let request1 := requestFor .syncBalance1 current.state.token1 (.balanceOf ctx.pair)
      ExactConsumes (startTyped current ctx .sync)
        (.next (syncExternalReply result.out0) (staticViewTranscript result.views0 .done)
          (.next (syncExternalReply result.out1) (staticViewTranscript result.views1 .done) .done))
        {status := .success [],
          frame := syncSourceUpdatedFrame (frame1.beginResume request1)
            result.sourcePost result.event result.oracle,
          remaining := .done,
          childReturns := staticViewChildReturns frame0 request0 0 result.views0 ++
            staticViewChildReturns frame1 request1 0 result.views1} ∧
      WriterRep K (post.getStor ctx.pair) {result.sourcePost with unlocked := 1} ∧
      (∀ a, a ≠ ctx.pair → post.getStor a = b.getStor a) ∧
      post.logs = b.logs ++
        [⟨ctx.pair, [updateSyncTopic],
          encodeWords [Bytes.toB256 (result.out0.take 32), Bytes.toB256 (result.out1.take 32)]⟩] ∧
      post.output = [] := by
```
How 1.1 is proved:
- The premises are exactly the producer's (`codeEq`, `fork`, `selector`, and the run that is the root of every `SyncCanonicalResult` for it). No new premise is added.
- `sync_raw_inv` and then `syncCallee_inv` supply:
  - `∀ a, d1.getStor a = (syncFirstWorld sevm b).getStor a`, which comes from both STATICCALL posts;
  - the returned world `syncResultWorld`.
- The update and unlock only `afterSload`, `afterSstore` on `currentTarget` and `addLog`, so a full-map rewrite (`afterSstore_getStor_ne`, `afterSload_getStor`, `Devm.addLog_getStor`) closes the goal.
- The result's own fields would not suffice on their own: they retain the child processes but no post-storage frame for foreign accounts. The raw run is part of the result's index, so nothing is missing.

How 1.2 is proved: `post.output = []` is `result.outputPreserved.trans freshOutput`, with `b.output = []` as a premise, mirroring `initialize_bytecode_exact_consumes`.

Follow-up gate receipts:
- `creme lake-build uv2nh-sync -- Blanc.Lift.CursorExact Blanc.Lift.UniswapV2Pair.SyncGasCanonical` → `Build completed successfully (1167 jobs).`
- module-size OK (947 modules; the 1 hard-cap breach is the pre-existing ProrataWethVaultCode); duplication OK (0 unexcepted rise); debt OK; residue OK (96 -> 94).
- Forbidden-token, bare-simp and debt greps: 0 hits.
- Layering at the lane tip without proposals: `REGRESSION 7 violations`. With my two diffs applied (unchanged from above): 5 remain, all P4 modules not classified: `Lift.Create2Deploy` and `Lift.UniswapV2Pair.Creation.{Deploy,DeployInit,Facts,Walk}`. None of them are mine. The diffs were reverted afterwards.
