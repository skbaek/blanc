# uv2nh-permit lane report (P3, episode uv2nh-permit-1)

Branch `claude/uv2nh-permit`, base acb5efeb. Commits: c4a5b71e (raw walk), 1ec6514b (source refinement),
bafaa428 (canonical ECRECOVER corollary). Final: **bafaa428**. Not pushed.

## Theorem map (U2(a) permit, selector 0xd505accf)

| U-condition | Theorem | Location | Statement (one line) |
|---|---|---|---|
| U2(a) inverse, raw | `permit_pc0_inv` / `permit_bytecode_refines_raw` | PermitEntries.lean:483 / :502 | A successful pc0 run (from `Exec` via `lift_sound`) has value 0, both length guards, nonstatic, `time ≤ deadline`, one actual STATICCALL to 1 (gas word, callGas, `StaticCallPost` with flag 1, bounded reply `out`, `StaticAnswered` on the exact request window) whose copied word is a nonzero `owner`, and `post = permitPublicPost sevm b d out sel G'`. |
| U2(a) frame refinement | `permit_bytecode_refines_source` | PermitSource.lean:350 | Under `WriterRep K`, `WriterFreshKeys K [nonce owner, allowance owner spender]` (trace-local HASH-T), representable calldata, `b.output = []`: value 0, 228 ≤ len, nonstatic, timely, the raw call facts, and for every code bit `PermitSourceResult`: `startTyped` suspends with the model request whose calldata equals the actual call input and target 1; `resumeSegment` at the observed reply finishes; `ExactConsumes (startTyped …) (.next reply .done .done) permitSourceDone`; `drive 3 … = permitSourceDone`; WriterRep of the post storage vs `permitSourceState` (nonce+1 then allowance); pending owned Approval at origin (invocation, segment 1, afterCall permitRecovery); updates unchanged; raw `post.output = []`, `post.logs = b.logs ++ [Approval]`, exact `.set nonceSlot (nonce+1) |>.set allowanceSlot value`, foreign storage unchanged, `gasLeft = residual`. |
| U2(a) ExactConsumes | `permit_exact_consumes` | PermitSource.lean:80 | Model-only: value 0, timely, nonstatic, recovered word nonzero = owner ⇒ ExactConsumes of the permit segment and its resume at the observed reply. |
| U2(a) forward / gas companion | `permit_source_bytecode_exact` | PermitSource.lean:420 | Typed acceptance (`startTyped … = .suspended …`, `resumeSegment … reply = .finished …`) + compiled recovery call ENV (`Ninst.RunCompiled` at the derived state, success stack, returned gas `G + approveCharge + 2165`) + both store sentries ⇒ `SProg.RunExact` and `Nonempty Exec` at gas `callGas + nonceStore + nonceLoads + 1137`, and the same `PermitSourceResult`. |
| raw forward | `permit_pc0_exact` / `permit_bytecode_live_raw` | PermitEntries.lean:807 / :832 | Same premises in raw form; liveness via `lift_exact`. |
| canonical-native | `permit_bytecode_refines_source_canonical` (+ `permit_recovery_canonical` :469) | PermitSource.lean:489 | With `getDelegatedCodeAddress (b.getCode 1) = none`: the observed reply is `ecrecoverOutput` of the model request calldata (activation by `ecrecover_active` on every covered fork); the typed resume consumes the native answer. No signer/unforgeability premise. |
| J1 exclusions | inside `permit_bytecode_refines_source` | — | value≠0 (guard), len<228 (`word_calldata_guards_iff`), EXPIRED (`t_1b15` noOk), static (nonce SSTORE), failed call (`t_1cd3` noOk, flag = 1), INVALID_SIGNATURE (`t_1d5c` noOk both arms) are all excluded for `.ok`. |

Supporting: `approve64_exact_at`/`approve64_inv_at` (ApproveCore.lean:46/:204; old `approve64_exact`/`_inv` :184/:375 are now specializations, statements unchanged); four literal lines in PermitWalk.lean (nonce 114 gas + 3 selected charges; struct 273; digest 192; request 174) each with inverse and exact; `permitSigner_inv/_exact`, `permitBody_inv/_exact` (PermitEntries.lean:59/:211/:601); `WriterRep.permit_store` (PermitSource.lean:154); `permit_startTyped_inv` / `permit_resume_inv` (:372/:402).

## Source correspondence (UniswapV2ERC20.sol permit, lines 81–94)

| Source | Bytecode / theorem |
|---|---|
| `require(deadline >= block.timestamp, 'EXPIRED')` | t_1b0c_c29 (TIMESTAMP, DUP5, LT, ISZERO, JUMPI); `timely` in `permitBody_inv` |
| `nonces[owner]++` (old value in digest) | permitNonceLine: SLOAD 3, keccak(owner‖4), SLOAD, ADD 1, SSTORE; `permitNonceWorld`, `permit_reads` |
| `keccak256(abi.encode(PERMIT_TYPEHASH, owner, spender, value, nonce, deadline))` | permitStructLine, window 160..352 = `encodeWords […]` (`permitStructImage_window`) |
| `keccak256(abi.encodePacked('\x19\x01', DOMAIN_SEPARATOR, inner))` | permitDigestLine, overlapping writes 384/386/418, window 384..450 (`permitDigestImage_window`); `permitCallDigest_source` = model `permitDigest` |
| `ecrecover(digest, v, r, s)` | permitRequestLine (0 at 450, ptr 482, words at 482..610 = `ExternalOperation.encode (.recover …)`), STATICCALL(gas,1,482,128,450,32); reply word `permitRecoveredWord out` |
| `require(recovered != 0 && recovered == owner, 'INVALID_SIGNATURE')` | t_1cdc/t_1d27/t_1d57 in `permitSigner_inv` |
| `_approve(owner, spender, value)` | t_1dc2 → `approve64_inv_at`/`_exact_at` at pointer 482 (no expansion); `WriterRep.permit_store` |
| model | Execution.lean startTyped :315–324, permitDigest :286, resumeSegment :564–567 |

## Gate receipts (worktree, `~/.local/bin` first on PATH)

- `~/creme/scripts/creme lake-build uv2nh-permit -- Blanc.Lift.UniswapV2Pair.PermitEntries Blanc.Lift.UniswapV2Pair.ApproveSource Blanc.Lift.UniswapV2Pair.InitializeSource Blanc.Lift.UniswapV2Pair.TransferSource Blanc.Lift.UniswapV2Pair.StaticViewClassify` → `Build completed successfully (1125 jobs)`, status OK (c4a5b71e content).
- `… lake-build uv2nh-permit -- Blanc.Lift.UniswapV2Pair.PermitSource Blanc.Lift.Ecrecover Blanc.Weth10Permit` → `Build completed successfully (1107 jobs)` (final content; WriterEntries/WordImage/PermitWalk built earlier, OK).
- With proposed layering rows + COMMON_API entries applied uncommitted (then reverted):
  - `scripts/check-layering.sh` → `OK — layering: 14 contract(s) … 947 module(s) classified … none stale; 213/217 shared module(s) cited …`
  - `scripts/check-proof-module-size.sh` → `OK — proof module size (report-only): 945 modules …` (the one hard-cap breach is pre-existing ProrataWethVaultCode.lean)
  - `scripts/check-proof-duplication.sh` → `OK — proof duplication ratchet: 945 module(s), 34011 declaration(s); 1 K1 families … 0 unexcepted rise(s)`
  - `scripts/check-proof-debt.sh` → `OK — proof-debt: 92 scopes inventoried; zero unexcepted new/increased findings`
  - `scripts/check-proof-residue.sh` → `OK — proof residue: 13/13 predicates checked; counts 96 -> 94; no rise`
- Without the layering rows, check-layering fails closed on the unclassified new modules (expected).
- `grep -nwE 'sorry|admit|native_decide|axiom'` and bare-simp grep over ApproveCore, PermitWalk, PermitEntries, PermitSource, WordImage, Ecrecover: 0 hits; no maxHeartbeats/maxRecDepth/@[simp].

## Shared-wiring proposals (exact diffs, NOT committed)

### scripts/check-layering.py
```diff
diff --git a/scripts/check-layering.py b/scripts/check-layering.py
index 7f27b080..43b04266 100644
--- a/scripts/check-layering.py
+++ b/scripts/check-layering.py
@@ -173,7 +173,7 @@ SHARED += ["Lift.PackedShaSize", "Lift.Deploy", "Lift.CreationOps"]
 # (weth9-liveness-v1): contract-neutral.
 SHARED += ["Lift.ExactWalkSolc", "Lift.ExactWalkCall"]
 # Parameterized free-pointer memory for lifted walks.
-SHARED += ["Lift.ExactWalkMemory", "Lift.ByteWindowMemory"]
+SHARED += ["Lift.ExactWalkMemory", "Lift.ByteWindowMemory", "Lift.WordImage", "Lift.Ecrecover"]
 # Pure-model ledger updates (vyper-3crv-bytecode-v1): contract-neutral.
 SHARED += ["LedgerUpdate"]
 # Floor share bounds for two-reserve AMMs: contract-neutral.
@@ -281,6 +281,9 @@ CONTRACTS = {
         "Lift.UniswapV2Pair.GetterStorageReservesMemory",
         "Lift.UniswapV2Pair.GetterStorageReservesWrapper",
         "Lift.UniswapV2Pair.GetterStorageReservesWalk",
+        "Lift.UniswapV2Pair.PermitWalk",
+        "Lift.UniswapV2Pair.PermitEntries",
+        "Lift.UniswapV2Pair.PermitSource",
     ],
     "beacon-deposit": ["BeaconDepositModel", "BeaconDepositCorrectness",
                        # the deployed runtime, lifted (decision beacon-lift-layering-family-20260926)
```

### docs/COMMON_API.md
```diff
diff --git a/docs/COMMON_API.md b/docs/COMMON_API.md
index 96f72494..247ffa6e 100644
--- a/docs/COMMON_API.md
+++ b/docs/COMMON_API.md
@@ -1858,6 +1858,33 @@ covers unrelated encode/decode goals, so this remains a manual registry route.
   `fixed-byte-offsets` matcher recognizes `Mem.Wf`, `Mem.Reads`, or
   `Bytes.writeAt` in a target, and does not recognize this byte-codec equality
   or a `Mem.read` equality alone. No broader trigger is registered.
+- Whole-word byte images and the low-byte mask live in
+  [`Blanc/Lift/WordImage.lean`](../Blanc/Lift/WordImage.lean).
+  `Bytes.sliceD_writeAt_word_after` keeps a window that starts past an earlier
+  word write; `Bytes.sliceD_writeAt_word_last` appends a word written exactly at
+  a window's end, so consecutive word stores (an ABI encoding, a recovery
+  request) read back as their concatenation, peeled from the right.
+  `Bytes.sliceD_writeAt_short` reads a short write (a call reply prefix of at
+  most 32 bytes) at the head of a word window followed by the old image, and
+  `B256.zero_toBytes_sliceD` reads zeros from any tail of the zero word.
+  `B256.and_ff_eq_toUInt8` and `UInt8.toB256_and_ff` identify `AND 0xff` with
+  the low byte as a `UInt8`, as a `uint8` ABI decoder masks it. Discovery is
+  manual; no trigger is registered. First consumer: the Uniswap V2 Pair permit
+  walk (`Blanc/Lift/UniswapV2Pair/PermitWalk.lean`).
+- The ECRECOVER precompile on arbitrary calldata lives in
+  [`Blanc/Lift/Ecrecover.lean`](../Blanc/Lift/Ecrecover.lean).
+  `ecrecoverOutput data` is the precompile's own success output (empty for a
+  malformed `v`, zero or out-of-range scalars, or failed recovery; otherwise the
+  recovered address as one word), defined through Jaune's `executeEcrecover`;
+  `executeEcrecover_eq` states it for any machine that can pay the fixed charge.
+  `ecrecover_output_of_processMessage_clean` turns a clean synchronous
+  non-delegated address-1 child (the `ProcessMessage` a `StaticAnswered` witness
+  exhibits) into `gasEcrecover ≤ gas` and that output, and `ecrecover_active`
+  discharges activation of address 1 on every covered fork by `CoveredFork.cases`.
+  It identifies the executed answer; it never asserts that recovery succeeds or
+  that signatures are unforgeable. Consumers: the Uniswap V2 Pair permit
+  canonical corollary; `Blanc/Weth10Permit.lean`'s two address-1 clean-child
+  theorems can become corollaries (proposed migration). Discovery is manual.
 - Fixed or padded memory windows: use `Mem.Wf` and `Mem.Reads` before adding a
   local take/drop proof.

```

### Blanc/Weth10Permit.lean (optional dedup; builds with the patch: `lake-build … Blanc.Weth10Permit` → `Build completed successfully (1024 jobs)`; dependents not rebuilt, statements unchanged)
```diff
diff --git a/Blanc/Weth10Permit.lean b/Blanc/Weth10Permit.lean
index d73d2699..6e727114 100644
--- a/Blanc/Weth10Permit.lean
+++ b/Blanc/Weth10Permit.lean
@@ -8,6 +8,7 @@
 import Blanc.Weth10Functional
 import Blanc.Ladder
 import Blanc.Weth10Errors
+import Blanc.Lift.Ecrecover

 namespace Blanc

@@ -766,52 +767,8 @@ theorem gasEcrecover_le_of_processMessage_clean
         calldata code false) xl (.ok child))
     (hclean : child.error.isSome = false)
     (hfork : CoveredFork sevm.benvStat.fork) :
-    gasEcrecover ≤ gas := by
-  by_contra hgas
-  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hpm
-  unfold FrameBody at hbody
-  rcases hbt :
-      (callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
-        calldata code false).benvAfterTransfer with e | benv <;>
-    rw [hbt] at hbody
-  · rw [hbody.2] at hset
-    unfold processMessage.settle at hset
-    cases hset
-  · have hca :
-        ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
-          calldata code false).withBenv benv).codeAddress = some 1 := rfl
-    rcases of_executeCode_someCode hca hbody with hpc | hinterp
-    · have hexec := hpc.2.2
-      rw [show executePrecomp
-          (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
-            calldata code false).withBenv benv)) 1 =
-          applyPrecompResult
-            (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
-              calldata code false).withBenv benv))
-            (executeEcrecover
-              (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
-                calldata code false).withBenv benv))) from rfl] at hexec
-      unfold executeEcrecover PrecompResult.chargeGas at hexec
-      rw [if_neg (by
-        show ¬gasEcrecover ≤
-          (initEvm ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
-            calldata code false).withBenv benv)).dyna.gasLeft
-        change ¬gasEcrecover ≤ gas
-        exact hgas)] at hexec
-      rw [handleErrorWith_withBenv_of_covered hbt
-        (by rw [callMsg_stat]; exact hfork)] at hexec
-      simp only [applyPrecompResult, executeCode.handleError] at hexec
-      rw [← hexec] at hset
-      unfold processMessage.settle at hset
-      simp only [bind, Except.bind, Option.isSome] at hset
-      injection hset with hchild
-      subst child
-      change true = false at hclean
-      contradiction
-    · exact False.elim (hinterp.1 (by
-        obtain ⟨st_mid, hsub, hbenv⟩ := of_benvAfterTransfer rfl hbt
-        subst benv
-        exact hpre))
+    gasEcrecover ≤ gas :=
+  (Blanc.Lift.ecrecover_output_of_processMessage_clean hpre hpm hclean hfork).1

 /-- A clean synchronous address-1 child returns exactly the canonical
 ECRECOVER image.  This identifies empty output with signature rejection and a
@@ -827,39 +784,12 @@ theorem output_of_processMessage_permitEcrecover_clean
     (hclean : child.error.isSome = false)
     (hfork : CoveredFork sevm.benvStat.fork) :
     child.output = permitEcrecoverOutput digest v sigR sigS := by
-  have hgas : gasEcrecover ≤ gas :=
-    gasEcrecover_le_of_processMessage_clean hpre hpm hclean hfork
-  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hpm
-  unfold FrameBody at hbody
-  rcases hbt :
-      (callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
-        (permitEcrecoverImage digest v sigR sigS) code false).benvAfterTransfer
-    with e | benv <;> rw [hbt] at hbody
-  · rw [hbody.2] at hset
-    unfold processMessage.settle at hset
-    cases hset
-  · have hca :
-        ((callMsg sevm parent gas 0 sevm.currentTarget 1 1 true true
-          (permitEcrecoverImage digest v sigR sigS) code false).withBenv
-          benv).codeAddress = some 1 := rfl
-    rcases of_executeCode_someCode hca hbody with hpc | hinterp
-    · have hexec := hpc.2.2
-      rw [executePrecomp_one_permitImage (by rfl) (by
-        change gasEcrecover ≤ gas
-        exact hgas), permitEcrecoverResult_eq] at hexec
-      rw [handleErrorWith_withBenv_of_covered hbt
-        (by rw [callMsg_stat]; exact hfork)] at hexec
-      simp only [applyPrecompResult, executeCode.handleError] at hexec
-      rw [← hexec] at hset
-      unfold processMessage.settle at hset
-      simp only [bind, Except.bind, Option.isSome] at hset
-      injection hset with hchild
-      subst child
-      rfl
-    · exact False.elim (hinterp.1 (by
-        obtain ⟨st_mid, hsub, hbenv⟩ := of_benvAfterTransfer rfl hbt
-        subst benv
-        exact hpre))
+  have native := (Blanc.Lift.ecrecover_output_of_processMessage_clean hpre hpm hclean hfork).2
+  have canonical := Blanc.Lift.executeEcrecover_eq
+    (evm := Blanc.Lift.ecrecoverEvm (permitEcrecoverImage digest v sigR sigS)) (Nat.le_refl _)
+  rw [executeEcrecover_permitImage rfl (Nat.le_refl _), permitEcrecoverResult_eq] at canonical
+  injection canonical with _ output
+  exact native.trans output.symm

 /-- An errored synchronous address-1 child has empty output.  ECRECOVER's
 signature-rejection cases are ordinary clean successes, so the only enabled
```

The duplication ratchet is green without this migration (the new Ecrecover proofs are not
byte-copies: they are stated over arbitrary calldata). No Execution.lean / Check / root-import change is needed.

## Remaining obligations

1. Forward canonical discharge of the compiled call ENV in `permit_source_bytecode_exact` (native
   address-1 run with forwarded gas ≥ 3000 via ForwardCall `runCompiled_staticcall_doneFrame`); the
   forward theorems still take `call : Ninst.RunCompiled …` plus returned gas as premises.
2. Delegated address-1 code: the observed-reply refinement uses transcript `.next reply .done .done`
   (no entered-child turns). If address 1 carries a delegation designator, the entered EVM child's
   (static) turns are not represented; the canonical corollary excludes this by `noDelegation`.
   A history producer must discharge `noDelegation` or carry the child turns.
3. Reachable/history liveness: WriterRep/footprint (with nonce and allowance keys) and fresh
   frame entry (`b.output = []`, empty stack/memory) must come from the configured-history lane.
4. Failure correspondence (raw revert ⇒ model `.failed`) not attempted (J1).
5. Root import of the new modules into `Blanc.lean` and claim-map rows are master integration.
