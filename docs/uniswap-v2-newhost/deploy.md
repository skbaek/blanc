# uv2nh-deploy lane report (packet P4, episode uv2nh-deploy-1)

Branch `claude/uv2nh-deploy`, commit d6b8b5b2 on 577edbac. Owned files only (5 new modules, 1,090 lines).
No Jaune edit, no pin/lakefile/manifest change, no shared-wiring commit, InitializeSource untouched.

## Theorem map (U8)

| Item | Name | file:line | Statement |
|---|---|---|---|
| generic | `Xinst.step_create2_spawn` | Blanc/Lift/Create2Deploy.lean:62 | admitted CREATE2 (covered fork, non-static, affordable, nonce<max, depth>0, `Create2TargetEmpty`) steps to `.spawn (Frame.ofCreate (createMsg … (create2NewAddress currentTarget salt (create2InitCode M i sz)) …)) (.create …)` |
| generic | `create2_runCompiled` | Create2Deploy.lean:135 | with `processCreateMessage childMsg = .ok child`, `child.error = none`: `Ninst.RunCompiled … (.exec .create2) (create2Post …)` (address on stack, child world) |
| generic | `create2NewAddress_eq_ofHash` | Create2Deploy.lean:34 | `create2NewAddress s salt code = create2AddressOfHash s salt (keccak code)` (rfl; digest view for controls) |
| constructor | `ctor_run` | Creation/Walk.lean:250 | gas-exact constructor walk from a fresh account: output = runtime window, error kept, storage = `ctorStor chainId self caller s` (slot12:=1, slot3:=domainSeparator, slot5:=caller), gas G left |
| domain | `domain_read` | Walk.lean:207 | the 160 bytes the second KECCAK256 reads are typeHash‖nameHash‖versionHash‖chainId‖address (proved from walked memory; no hash premise) |
| domain | `domainSeparator_eip712` | Walk.lean:60 | `domainSeparator c a = keccak(keccak(typeString)‖keccak("Uniswap V2")‖keccak("1")‖c‖a)` |
| message deploy | `pair_create` | Creation/Deploy.lean:43 | zero-value creation message, ≥2.4M gas, covered fork: `.ok post`, code = certified runtime, storage = `ctorStor (chainId) target caller empty`, no error |
| CREATE2 deploy | `pair_create2` | Deploy.lean:105 | any non-static factory frame with creation code in memory: compiled CREATE2 step pushes `create2NewAddress creator salt code`, runtime installed, storage = ctorStor over creating frame's chain id, that address, creator |
| checkpoint | `InitializedCheckpoint` (def) | Creation/DeployInit.lean:34 | `WriterRep (fun _ => False) s (initializeSourceState (State.empty factory domain) t0 t1)` |
| checkpoint | `ctorStor_rep` | DeployInit.lean:45 | ctor storage represents `State.empty factory (domainSeparator c self)` with empty footprint |
| U8 init | `pair_initialized` | DeployInit.lean:102 | successful pc-0 `initialize` run at ctor storage: caller = factory ∧ `InitializedCheckpoint` with decoded tokens (consumes `initialize_bytecode_refines_source` InitializeSource.lean:199) |
| U8 headline | `pair_create2_initialized` | DeployInit.lean:126 | every covered fork: CREATE2 step + every following successful factory `initialize` at that address reaches `InitializedCheckpoint` |
| exhibit | `exhibit_create2` | DeployInit.lean:171 | factory 0x5C69…aA6f, salt keccak(USDC‖WETH): CREATE2 pushes `pairAddress` 0xB4e1…C9Dc with runtime + ctor storage |
| kernel | `salt_eq`, `initHash_eq`, `pairAddress_eq` | Creation/Facts.lean:92/95/104 | salt = 0x8505…e760; keccak(all 11,636 bytes) = 0x96e8ac42…845f; `pairAddress = create2NewAddress factory salt code.toList` |
| control | `pairAddress_wrong_salt`, `pairAddress_wrong_initHash` | Facts.lean:108/113 | salt^1 / digest^1 give a different address |
| kernel | `runtimeWindow_eq`, `typeWindow_eq`, `typeHash_eq`/`nameHash_eq`/`versionHash_eq` | Facts.lean:65/57/44-46 | runtime window = certified runtime; trailing 82 bytes = EIP712Domain type string; hashes of literals |

Proposed U2 checkpoint predicate: `Blanc.Lift.UniswapV2Pair.InitializedCheckpoint` (DeployInit.lean:34).
Read-out: zero supply/reserves/timestamp/accumulators/kLast, unlocked=1, factory/token0/token1/domain as given,
nonzero raw words only at fixed slots, all ledger/allowance/nonce rows zero in the model. No claim that hashed
slots read zero (HASH-T on first touch, WETH9 pattern). Note: `initialize` has no once-guard; `pair_initialized`
admits any decoded tokens (no sorting/distinctness, per design).

Scope: message/opcode-level deployment, not configured-chain inclusion; factory bytes not lifted (the creating
frame is any non-static frame; the factory identity enters as `sevm.currentTarget`).

## Resource evidence (Keccak in the kernel)
- 40-byte salt probe: 1.7 s, 1.2 GiB. Full 11,636-byte keccak via `code.toList` (ByteArray-indexed): RETRACTED by
  watchdog at 10.9 GiB peak (O(n^2) array reads). Via the literal chunk list: OK, 15.9 s, 5.0 GiB peak.
- Final `Facts` module (all kernel facts): 17.5 s, 5.09 GiB peak lean RSS; kept in its own module so no LSP worker
  elaborates it. `Walk`: 21.4 s, 3.2 GiB.

## Gate receipts (worktree, commit d6b8b5b2 content)
1. `~/creme/scripts/creme lake-build uv2nh-deploy -- Blanc.Lift.UniswapV2Pair.Creation.DeployInit` → `"status": "OK"`, failed [], modules_rebuilt 4 (closure Facts→Walk→Deploy→DeployInit; Create2Deploy built earlier in the same closure), 41.9 s, peak 5092.5 MiB. Re-probe: `NOT_REQUIRED_FRESH`.
2. `scripts/check-proof-module-size.sh` → `OK — proof module size (report-only): 945 modules; … 1 new-module hard-cap breach(es)` (the breach is pre-existing Blanc/ProrataWethVaultCode.lean, not this lane).
   `scripts/check-proof-duplication.sh` → `OK — proof duplication ratchet: … 0 unexcepted rise(s)`.
   `scripts/check-proof-debt.sh` → `OK — proof-debt: 92 scopes inventoried; zero unexcepted new/increased findings`.
   `scripts/check-proof-residue.sh` → `OK — proof residue: 13/13 predicates checked; counts 96 -> 94; no rise`.
3. `scripts/check-layering.sh` with the two proposals below applied uncommitted → `OK — layering: 14 contract(s) are siblings; 947 module(s) classified …; 212/216 shared module(s) cited`. Without the COMMON_API entry it fails: `LAYERING — Blanc/Lift/Create2Deploy.lean is classified SHARED … but docs/COMMON_API.md never cites it`. Both reverted (`git checkout`).
4. `grep -nwE 'sorry|admit|native_decide|axiom'` over the 5 files → 0; bare-simp grep (simp/simpa/simp_all/simp_arith not followed by `only`) → 0; no maxHeartbeats/maxRecDepth/@[simp].
- Controls bite: disposable probe file (deleted) restating each control with the perturbation removed (`saltWord`, `initHash ^^^ 0`) → kernel rejects (`(kernel) application type mismatch … decide (… ≠ pairAddress) = true`); the controls themselves are accepted.
- `python3 -m creme reclaim --wind-down uv2nh-deploy` → `"status": "OK"`, "cleanup verified; no matching hold remained".

## Shared-wiring proposals (exact diffs, not committed)

### scripts/check-layering.py
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
```

### docs/COMMON_API.md
```diff
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

Root `Blanc.lean` import of `Blanc.Lift.UniswapV2Pair.Creation.DeployInit` (and `Blanc.Lift.Create2Deploy` if the root lists generic modules) is needed for the full target to elaborate these files; not applied.

## Reuse / hoist
Reused: `liftCreate_ok`, `of_processCreateMessage`, `XStep.run_toStep`, `chargeGas_eq_ok`, `Devm.push_eq_ok`,
`Mem.Reads.write/read`, `Bytes.sliceD_writeAt(_before/_after)`, `List.sliceD_split`, `Mem.size_write_word_aligned`,
`read_covered(_len)`, `charge_covered`, all `rx_*` steps, `initialize_bytecode_refines_source`, `b256_and_zero/or_zero`.
Hoist candidates (left `private` in Walk.lean:36/44): `rx_chainid`, `rx_address` (contract-neutral, 4 lines each;
natural home `Blanc/Lift/CreationOps.lean`, a shared file not owned here).

## Remaining obligations
- Master: apply the layering row, COMMON_API entry and root import; claim-map/U11 entries.
- Not proved: CREATE2 failure branches (collision, insufficient gas) — U8 asks for the success composition only.
- A configured-history attainment witness (ConfiguredHistoryTrace) of the deployment is a separate U2/U6 seam.
- The ~5 GiB Facts module is a new heavy row for check-elab budgets.
