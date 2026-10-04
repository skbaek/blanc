# uv2nh-skim lane report (P6, episode uv2nh-skim-1)

Branch `claude/uv2nh-skim`, worktree `~/blanc/.worktrees/uv2nh-skim`, base `6b6dd21b`.
Commits: `90310a79` (raw inverse), `5ace0b8e` (source consumption + handler), `afb34b81` (PtrWord hoist). Final: `afb34b81`.

## Status against the objective

Delivered: (1) the complete raw U2(a) inverse for skim (every `.ok` run at the Pair code with selector
0xbc25cf77 takes the success path, decision J1 inverse coverage); (2) the source-side ExactConsumes for
`startTyped .skim` over the four ordered observations; (3) a raw-to-source handler that turns the raw guard
fields into source acceptance. NOT delivered: the canonical same-witness `SkimCanonicalResult` (analogue of
`SyncCanonicalResult`). It needs the four turn-queue producers and the reserve/storage/log transport across the
two non-static transfer CALL children; these remain explicit implications/premises (see Remaining obligations).

## Theorem map (U-conditions)

| Theorem | File:line | Statement (one line) | U |
|---|---|---|---|
| `skim_raw_inv` | SkimSecondWalk.lean:463 | Every successful raw run (code, covered fork, selector) gives value=0, ABI head (len-4 ≥ 32), slot12=1, then `SkimFirstFacts` (nonstatic, token0 code, balance0 STATICCALL at 128 with exact request/full reply ≥32, r0 ≤ b0, transfer0 helper with SAME-D CALL, canonical calldata, optional-bool acceptance) and, for a fitting pointer, `SkimSecondFacts` (reserve1 read on the post-transfer0 world, token1 code, balance1 STATICCALL at the moved pointer, r1 ≤ b1, transfer1 CALL/calldata/acceptance, post = afterSstore d2 12 1) | U2(a) raw + J1 inverse |
| `skimFirstPointer_fit` | SkimSecondWalk.lean:438 | Any transfer0 reply below 2^128 bytes gives the fit (96 ≤ p, p+1024 < 2^256) | U2(a) discharge |
| `skim_source_exact_consumption` | SkimSource.lean:162 | Four exact turn queues + four successful observations ⇒ ExactConsumes (startTyped current ctx (.skim r)) to success, final frame and ordered childReturns as conclusions | U2(a) source |
| `skim_raw_source_consumption` | SkimHandler.lean:107 | Raw guard fields + slot reps + reserve1 transport ⇒ unlocked=1 and ∀ four exact turn queues, ExactConsumes on `writerContext sevm invocation` with the observed replies | U2(a) handler |
| `skim_source_liquidity` | SkimSource.lean:279 | A consumed successful skim keeps supply/reserves (via existing `drive_startTyped_skim_liquidity`) | U2(a)/U3 corollary |
| `skimTransfer_inv` | SkimTransferWalk.lean:1153 | Pointer-generic helper57 inverse at any fitting free pointer p: SAME-P CALL operands, calldata at p+164 = selector++to++amount, acceptance, returned frame | moved-pointer helper |

Consumed intermediate lemmas (not leaves): skimSelector_inv, skimWrapper_inv, skimLock_inv, skimFirstLine_inv,
skimFirstHalf_inv, SkimFirstFacts.mono (SkimWalk); skimAfterFirst_ptr, skimSecondLine_inv, skimRequestMemory_ptr/_read,
skimReplyWord, skimUnlockTail_inv, skimSecondHalf_inv (SkimSecondWalk); all SkimTransferWalk stages; skim_startTyped_suspended,
skim_resume*, skim_decodeTransfer, driveTurns_frame_shape, ExactTurns.frame_shape, skim_transfer0_reserve1 (SkimSource);
skimCache_source, skimReserve1Word_eq, skimSliceD_take, skimAccepted_source, skim_raw_source_guards (SkimHandler).

## Source correspondence (skim, Pair skim:190-195)

| Source | Bytecode (refined) | Model |
|---|---|---|
| lock modifier | t_18de_c34 slot12==1; t_194f SSTORE 12:=0 (static excluded) | `Frame.lock` (skim_startTyped_suspended) |
| cache token0/1, reserve0 | t_194f SLOAD 6,7,8; reserve0 = mask112 &&& slot8 before balance0 | `SkimLocals`; skimCache_source: cached words = token0/token1/reserve0 |
| balanceOf(token0,this) | STATICCALL pc 0x19f1 (c34), request at 128, width guard, decode | `.skimBalance0` resume |
| sub(reserve0) + _safeTransfer(token0) | sub59 then helper57 (pointer 128, continuation 0x1a2b) | `.skimTransfer0` request amount b0 - reserve0 |
| reserve1 after transfer0 | t_1a2b SLOAD 8 on the post-transfer0 world, (slot8/2^112)&mask112 | `executed1.frame` reserve1 = entry reserve1 (skim_transfer0_reserve1) |
| balanceOf(token1) | STATICCALL pc 0x19f1 (c67) at the MOVED pointer p | `.skimBalance1` |
| sub(reserve1) + _safeTransfer(token1) | sub59 then helper57 at p (continuation 0x1aca) | `.skimTransfer1` |
| unlock | t_1aca SSTORE 12:=1, jump 0x0257 STOP | `Frame.finishLocked []` (no own log/update) |

## Gate receipts (final candidate afb34b81, run from the worktree, PATH with ~/.local/bin first)

- `~/creme/scripts/creme lake-build uv2nh-skim -- Blanc.Lift.PtrWordMemory Blanc.Lift.UniswapV2Pair.SkimSecondWalk Blanc.Lift.UniswapV2Pair.SkimHandler` → `Build completed successfully (1117 jobs).` status OK. Earlier same-session builds of SkimWalk, SkimTransferWalk, SkimSource, SkimHandler all `Build completed successfully` (1112-1116 jobs), peak lean RSS <= 1.93 GiB.
- `scripts/check-proof-module-size.sh` → `OK — proof module size (report-only): 953 modules; ... 1 new-module hard-cap breach(es)` (the breach is pre-existing Blanc/ProrataWethVaultCode.lean; no Skim finding; largest new file 1208 lines).
- `scripts/check-proof-duplication.sh` → `OK — proof duplication ratchet: 953 module(s), 34116 declaration(s); 1 K1 families ... 0 unexcepted rise(s)`.
- `scripts/check-proof-debt.sh` → `OK — proof-debt: 92 scopes inventoried; zero unexcepted new/increased findings` (no heartbeat/recDepth options added).
- `scripts/check-proof-residue.sh` → `OK — proof residue: 13/13 predicates checked; counts 96 -> 94; no rise`.
- `scripts/check-layering.sh` with both proposals applied uncommitted → `REGRESSION — layering: 7 violation(s) across 14 contract(s), 955 module(s)`; all 7 are pre-existing unclassified modules from other packets (Lift.Create2Deploy, Lift.CursorExact, Creation.Deploy/DeployInit/Facts/Walk, SyncGasCanonical); zero Skim/PtrWord findings. Control: without the proposals the gate reports 13 violations including all 5 Skim modules and Lift.PtrWordMemory; with the SHARED row but no COMMON_API entry it reports the PtrWordMemory discovery violation.
- `grep -nwE 'sorry|admit|native_decide|axiom'` over Skim*.lean and PtrWordMemory.lean → no output. Bare-simp grep (`simp|simpa|simp_all|simp_arith` not followed by `only`) → no output.
- `python3 -m creme reclaim --wind-down uv2nh-skim` → `"status": "OK"`, "cleanup verified; no matching hold remained".

## Shared-wiring proposals (exact diffs; applied only uncommitted to run the gate)

### scripts/check-layering.py
```diff
diff --git a/scripts/check-layering.py b/scripts/check-layering.py
index 7f27b080..9e725bfa 100644
--- a/scripts/check-layering.py
+++ b/scripts/check-layering.py
@@ -169,6 +169,8 @@ SHARED += ["Lift.Loop", "Lift.CheckFast", "Lift.CheckAssembly", "Lift.ExactWalkO
 # Creation code (deploy-init-v1): the size-optimised packed-hash site and the CREATE bridge
 # for lifted creation code; contract-neutral.
 SHARED += ["Lift.PackedShaSize", "Lift.Deploy", "Lift.CreationOps"]
+# Size-free free-pointer word carrier for moved-pointer walks (uv2nh-skim)
+SHARED += ["Lift.PtrWordMemory"]
 # Solc-0.4 scratch-memory walk kit and the value-bearing CALL to a code-free recipient
 # (weth9-liveness-v1): contract-neutral.
 SHARED += ["Lift.ExactWalkSolc", "Lift.ExactWalkCall"]
@@ -271,6 +273,11 @@ CONTRACTS = {
         "Lift.UniswapV2Pair.SyncWalk",
         "Lift.UniswapV2Pair.SyncTurns",
         "Lift.UniswapV2Pair.SyncCanonical",
+        "Lift.UniswapV2Pair.SkimWalk",
+        "Lift.UniswapV2Pair.SkimTransferWalk",
+        "Lift.UniswapV2Pair.SkimSecondWalk",
+        "Lift.UniswapV2Pair.SkimSource",
+        "Lift.UniswapV2Pair.SkimHandler",
         "Lift.UniswapV2Pair.StaticViewClassify",
         "Lift.UniswapV2Pair.StaticViewSource",
         "Lift.UniswapV2Pair.StaticViewTurns",
```

### docs/COMMON_API.md (M-branch entry beside PtrMem)
```diff
diff --git a/docs/COMMON_API.md b/docs/COMMON_API.md
index 96f72494..be722374 100644
--- a/docs/COMMON_API.md
+++ b/docs/COMMON_API.md
@@ -3521,6 +3521,15 @@ contract-neutral.
   from initialization, word writes or pointer changes; this is registry-only.
   The same module's `mergeFour_bytes` gives the fixed high-four/low-twenty-eight
   byte image of a masked word merge; see the M1 manual codec route above.
+- Free-pointer word without an allocation size: `PtrWord p M` in
+  [`Blanc/Lift/PtrWordMemory.lean`](../Blanc/Lift/PtrWordMemory.lean) keeps only
+  `Mem.Wf M` and the pointer word at offset64. Use it instead of `PtrMem` when a
+  walk's allocation grows by an unbounded reply (for example a moved free pointer
+  after a full-returndata copy), so no size bound is owed. `PtrWord.of_ptrMem`
+  enters it; `write` (any byte list at offset96 or above), `extend`, `extends`
+  and `set` (pointer replacement) preserve it; `memRead_extend_fst` reads through
+  a read's extension. The Pair's skim walk consumes it for its second query and
+  transfer after transfer0's allocation.
 - Gas-exact writer walks for solc-0.4-style runtimes: the scratch-memory invariant `FpMem n M` (word-aligned,
   free pointer `0x60`, kept for an arbitrary `M`; `FpMem.init`, `FpMem.write`, `FpMem.write_out`,
   `FpMem.readback`, `scratchW`), its steps (`rx_mstoreF`, `rx_mstoreOut`, `rx_mloadFp`, `rx_keccakF`,
```

## Consolidation flags

- `SkimTransferWalk.lean` re-derives, pointer-generically, the semantics of SafeTransferWalk's PRIVATE stages
  (`safeTransfer_initialize_inv`, `_copyBody/_copyPass/_copyExit/_copy68_inv`, `_partialCall_inv`, `_call_inv`,
  `_afterCall_inv`/`_allocate_inv`, `_success_inv`/`_optional_inv`/`_decodeWords_inv`/`_head_inv`/`_check_inv`/`_return_inv`,
  `safeTransfer_payload128_data`, `safeTransfer_copy128_image`). Text differs (Line-based walks, image-based memory
  evaluation at arbitrary p), so the K1 gate does not flag it, but it is semantic duplication. This is exactly the
  original host's planned Burn moving-pointer helper: Burn's second transfer and final balance queries follow the same
  moved pointer. Recommended consolidation: make `skimTransfer_inv` (or a renamed `safeTransfer_inv` at pointer p)
  the single helper57 inverse, re-derive `safeTransfer_first_inv` as its p=128 instance, and delete the private stages.
  Likewise `skimSecondLine_inv`/`skimRequestMemory_*` are a moved-pointer balance request that BalanceCallWalk's
  pointer-128 `balanceRead_*` cannot express.
- `skimAfterFirst_ptr` re-proves the pointer/Wf part of private `safeTransfer_call128_ptr`/`safeTransfer_reply292_image`.
- `skimOffset` is a thin implicit-argument alias of `B256.toNat_add_eq_of_nof` (kept for rw ergonomics).

## Remaining obligations (for the canonical result)

1. Turn producers for the two balance children: retained static Pair views → `ExactTurns` with `StaticViewTurn`
   authentication, as SyncTurns does for sync's two queries (its pipeline is sync-occurrence specific; needs an
   occurrence-generic version or a skim instance for pc 0x19f1 at c34/c67).
2. Turn producers for the two NON-static transfer children: arbitrary nested Pair invocations (transfer, approve,
   transferFrom, permit, initialize succeed while locked; mint/burn/swap/skim/sync fail and are pruned) and foreign
   logs → `ExactTurns`; this is the history-lift layer (nested writer refinements in a non-root context).
3. Reserve1 transport across transfer0: raw `reserve1Read (d.getStorVal pair 8) = Nat.toB256 reserve1` (premise
   `transport` of the handler); follows from (2) because no locked-admissible entry writes slot 8.
4. Exact storage/log correspondence of the final world: `WriterRep K (post.getStor pair) {final with unlocked := 1}`
   and `post.logs = b.logs ++ child logs` in model order; follows from (2). The raw facts already give the Pair's own
   writes (slot12 0 then 1, nothing else) and no own LOG.
5. Fit discharge in the composed statement: `skim_raw_inv` states the second half under the pointer fit;
   `skimFirstPointer_fit` discharges it for replies below 2^128 bytes. A gas/memory-expansion bound producer
   (shared with Burn) would remove the residual case of gigantic replies.
6. Composition: a top theorem combining `skim_raw_inv` and `skim_raw_source_consumption` (its hypotheses are fields
   of `SkimFirstFacts`/`SkimSecondFacts`) once (1)-(4) exist; U6 forward/gas direction not attempted.
