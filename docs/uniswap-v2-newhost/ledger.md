# uv2nh-ledger (P2c, U7 model side) — lane report

Branch claude/uv2nh-ledger, commit 91377037 (base 0b7e28a6). Episode uv2nh-ledger-1. Owned files:
Blanc/Lift/UniswapV2Pair/PropertiesLedger.lean (593 lines, new), Blanc/Lift/LedgerFootprint.lean (153 lines,
new, contract-neutral; created under the shared contract's "generic machinery goes in new files under Blanc/Lift/").

## Theorem map (U7)

Invariant: State.LedgerOn keys st (PropertiesLedger.lean:48) = keys.Nodup ∧ FootprintCovers keys st.balanceOf
(every nonzero balanceOf row, incl. address 0 and feeTo when they hold LP) ∧ footprintSum keys balanceOf = totalSupply.
Transport form State.Ledger st (:36) = SumBacked balanceOf totalSupply (full address sum = supply).

| Condition | Name | Location | Statement |
|---|---|---|---|
| U7(1) deploy | State.empty_ledgerOn | PropertiesLedger.lean:71 | (State.empty f d).LedgerOn [] |
| U7(1) initialize | State.initialized_ledgerOn | :76 | {State.empty f d with token0,token1}.LedgerOn [] (this is initializedState, DeployInit.lean:30, unfolded; not imported to keep this module bytecode-free) |
| U7(2) segments | startTyped_ledger | :408 | current.state.Ledger → (startTyped current ctx entry).frame.Ledger (all 27 entries) |
| U7(2) segments | resumeSegment_ledger | :455 | prior.Ledger → (resumeSegment prior req cont res).frame.Ledger (fee mint to feeTo, MINIMUM_LIQUIDITY lock at 0, recipient mint, burn, updates, permit approve) |
| U7(3) driver | drive_ledger | :487 | ∀ fuel, drive and driveTurns keep Frame.Ledger (checkpoint and current), through Transcript.invoke children, foreign logs, failed-call rollback and failed-segment rollback |
| U7(3) headline | runTyped_ledger | :548 | st.Ledger → (runTyped st ctx entry transcript).frame.Ledger |
| U7(3) headline, footprint | runTyped_ledgerOn | :556 | st.LedgerOn keys → rows outside touched unchanged → final state LedgerOn (keys ++ touched).dedup |
| U7(3) relational | ExactConsumes.ledger | :566 | ExactConsumes seg tr out → seg.frame.Ledger → out.frame.Ledger (incl. ExactTurns.invoke) |
| U7 control | footprintSum_dup_breaks_ledger | :82 | st.LedgerOn keys → balanceOf key ≠ 0 → footprintSum (key :: keys) ≠ totalSupply |
| consumer API | State.Ledger.on / State.LedgerOn.extend / .ledger | :58 / :64 / :53 | any duplicate-free covering footprint reads the invariant; extension by touched keys |

Step lemmas (consumed): State.{mintLP,burnLP,transferLP,transferFromLP,approveLP,update}_preserves, mintFee_preserves,
Frame.{fail,withEvents,finishLP,finishUpdated,mintAfterFee,burnAfterFee,lock,afterSwapTransfer0/1}_ledger, startImmediate_ledger.
Generic (LedgerFootprint.lean): SumBacked :23, footprintSum :27, FootprintCovers :31, sumBelow_eq_ledgerSumOn_filter :35,
Adr.max_toNat :97 (kernel decide), sum_eq_ledgerSumOn :101, footprintSum_eq_sum :119, FootprintCovers.extend :128,
footprintSum_dup_ne_sum :141 (generic control).

How the original host consumes it: the history lift holds LedgerOn keys at its checkpoint, takes touched = the balanceOf keys
its HASH-T trace writes (the same keys a SlotFootprint/WriterRep footprint extension adds), discharges "rows outside touched
unchanged" from its frame facts, and applies runTyped_ledgerOn / ExactConsumes.ledger + State.LedgerOn.extend.
No SlotFootprint import needed: the model-side invariant is over Adr keys; the slot-level injectivity stays the lift's HASH-T premise.

Reused: Blanc.sum, sum_ledgerCredit, sum_ledgerDebit, sum_ledgerDebit_credit, SumNof (LedgerUpdate/LadderBase),
ledgerSumOn (LedgerConservation), State.mintLP_ledger, State.update_ledger, mintLP_supply, burnLP_supply,
update_supply_reserves (Properties.lean). Hoisted: the footprint/sum bridge into LedgerFootprint.lean.
No source correspondence rows: no entry was refined (pure model). Properties.lean, Execution.lean untouched.

## Gate receipts (worktree, commit 91377037)

1. ~/creme/scripts/creme lake-build uv2nh-ledger -- Blanc.Lift.LedgerFootprint Blanc.Lift.UniswapV2Pair.PropertiesLedger
   → "Build completed successfully (966 jobs)", status OK, 0 warnings. No lane consumers import these modules.
2. scripts/check-proof-module-size.sh → "OK — proof module size (report-only) ... 1 new-module hard-cap breach(es)"
   (the breach is pre-existing Blanc/ProrataWethVaultCode.lean, not this packet);
   check-proof-duplication.sh → "OK — proof duplication ratchet ... 0 unexcepted rise(s)";
   check-proof-debt.sh → "OK — proof-debt: 92 scopes inventoried; zero unexcepted new/increased findings";
   check-proof-residue.sh → "OK — proof residue: 13/13 predicates checked; counts 96 -> 94; no rise".
3. scripts/check-layering.sh with the proposal below applied uncommitted → "REGRESSION — layering: 18 violation(s)";
   all 18 are pre-existing unclassified lane modules from other packets (Create2Deploy, CursorExact, Ecrecover,
   PtrWordMemory, Creation.{Deploy,DeployInit,Facts,Walk}, Permit{Entries,Source,Walk}, Skim{Handler,SecondWalk,Source,
   TransferWalk,Walk}, SyncGasCanonical, WordImage); zero violations name this packet's modules (without the
   COMMON_API entry the count was 19, the 19th being LedgerFootprint's missing citation). Reverted after.
4. grep -nwE 'sorry|admit|native_decide|axiom' and a bare simp/simpa/simp_all grep over both files → zero hits
   (no simp of any kind is used; no new maxHeartbeats/maxRecDepth).

## Shared-wiring proposals (exact diff, not committed)

```diff
diff --git a/docs/COMMON_API.md b/docs/COMMON_API.md
index 96f72494..b27e6710 100644
--- a/docs/COMMON_API.md
+++ b/docs/COMMON_API.md
@@ -1529,6 +1529,18 @@ laws live in [`Blanc/LadderBase.lean`](../Blanc/LadderBase.lean):
   supply those guard facts nor establish an execution path or history. The
   `finite-coalition-ledger` recipe reaches this branch from a target containing
   `ledgerSumOn`.
+- For a pure ledger read over a *finite key footprint* (a history observes only
+  the rows it touches), import
+  [`Blanc/Lift/LedgerFootprint.lean`](../Blanc/Lift/LedgerFootprint.lean).
+  `footprintSum keys balances` sums the rows a key list names and
+  `FootprintCovers keys balances` says the list names every nonzero row;
+  `footprintSum_eq_sum` equates a duplicate-free covering footprint's sum with
+  the full address `sum` (via `sum_eq_ledgerSumOn` for any covering
+  coalition), so a conservation law proved over `sum` (packaged as
+  `SumBacked balances supply`) is read over any covering footprint.
+  `FootprintCovers.extend` extends a footprint by the keys a step touches, and
+  `footprintSum_dup_ne_sum` is the statement control: a repeated nonzero key
+  breaks the equation.

 ### S6. I need a basic EVM-word identity

diff --git a/scripts/check-layering.py b/scripts/check-layering.py
index 7f27b080..6a1c98f8 100644
--- a/scripts/check-layering.py
+++ b/scripts/check-layering.py
@@ -178,6 +178,8 @@ SHARED += ["Lift.ExactWalkMemory", "Lift.ByteWindowMemory"]
 SHARED += ["LedgerUpdate"]
 # Floor share bounds for two-reserve AMMs: contract-neutral.
 SHARED += ["Lift.AMMArithmetic", "Lift.BabylonianSqrt"]
+# Token-ledger sums read over a finite covering key footprint: contract-neutral.
+SHARED += ["Lift.LedgerFootprint"]
 # Ordinary interpreter output provenance for actual-call returndata bounds.
 SHARED += ["Lift.ReturnDataBound", "Lift.PrecompileOutputBound"]
 # Exact chunks and local simulation over existing configured state chronology.
@@ -220,6 +222,7 @@ CONTRACTS = {
         "Lift.UniswapV2Pair.Model",
         "Lift.UniswapV2Pair.Execution",
         "Lift.UniswapV2Pair.Properties",
+        "Lift.UniswapV2Pair.PropertiesLedger",
         "Lift.UniswapV2Pair.ModelControls",
         "Lift.UniswapV2Pair.SqrtWalk",
         "Lift.UniswapV2Pair.GetterMemory",
```

## Remaining obligations
- Original host: the history-level lift (touched keys from the HASH-T trace, slot injectivity) consuming
  runTyped_ledgerOn / ExactConsumes.ledger.
- Master: apply the layering/COMMON_API rows above; optional: a Blanc.lean root import if the lane wires new modules there.
