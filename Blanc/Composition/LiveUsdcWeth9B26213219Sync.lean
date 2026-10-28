import Blanc.Composition.LiveUsdcWeth9B26213219AllowanceReplay
import Blanc.Composition.UniswapV2PairUsdcWeth9SyncLiveF

/-!
# Sync at the live Pair from the original deployment histories

Finite observations and the original linked histories produce the checkpoint.
The future trace retains the established governance, freshness and call/gas
conditions. The Pair's proxy-admin exclusion follows from the finite admin read.
No final checkpoint or USDC quiet-allowance premise is supplied. Historical
receipt absence and finite observations remain explicit, unadopted inputs.
-/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.UniswapV2Pair
  Blanc.Composition.UniswapV2PairUsdcWeth9
  Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.Weth9Token Blanc.Composition.UsdcLive

/-- Future governance preserves the finite admin read's exclusion. -/
theorem ObservedAt.future_pair_not_admin {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K : Usdc.Key → Prop}
    (reads : ObservedAt checkpoint.state)
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : Usdc.UsdcHistF usdc K trace) :
    pair ≠ Usdc.adminOf future.state usdc := by
  rw [(Usdc.usdc_history_end_installedF trace hist).2]
  exact reads.pair_not_admin

/-- The live-address sync row consumes original deployment history, not a
supplied joint checkpoint. All gas/call premises of the established support-free
sync theorem are preserved; proxy-admin exclusion is derived from the reads. -/
theorem sync_from_linked_receipts {checkpoint future : BlockChain}
    (reads : ObservedAt checkpoint.state) (wd : WethDeploymentTo checkpoint)
    (pd : PairDeploymentTo checkpoint) (link : DeploymentHistoryLink wd pd)
    (holderFresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots wd.keys (.bal pair))
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (logs : ∀ (spender : Adr) (data : Bytes),
      Log.mk weth [Weth9.approvalTopic, pair.toB256, spender.toB256] data ∉
        link.beforePairReceiptLogs)
    (trace : ConfiguredHistoryTrace mainnetChainConfig checkpoint future)
    (pairFresh : WriterFreshKeys pd.keys (pairHistoryTouchedKeys pair trace))
    (usdcFresh : Usdc.KeysFresh (FiniteCheckpoint.rowKeys usdcRows)
      (Usdc.historyTouchedKeys usdc trace))
    (wethFresh : Weth9.KeysFresh wd.keys (Weth9.historyTouchedKeys weth trace))
    (governance : Usdc.UsdcGovernance usdc trace)
    {sevm : Sevm} {pre d0 d1 : Devm} {callGas0 callGas1 G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9) (static : sevm.isStatic = false)
    (depth : 2 ≤ sevm.depth)
    (sentry : gCallStipend <
      (callGas0 + 5 + 22 + temporalAccountAccessCost (syncFirstWorld sevm pre)
        (syncFirstToken sevm pre).toAdr) + sloadCost sevm (syncLockedWorld sevm pre) 6 + 119 +
      sstoreCost sevm (afterSload sevm pre 12) 12 0)
    (_read1 : (d1, callGas1) = syncWethRead1 sevm (syncUsdcRead0Skel sevm pre) G)
    (_read0 : (d0, callGas0) = syncUsdcRead0 sevm pre callGas1)
    (fits0 : callGas0 < 2 ^ 256) (fits1 : callGas1 < 2 ^ 256)
    (room0 : usdcBalNeed sevm (syncFirstWorld sevm pre) syncTail getterInitMemory 128
        (syncFirstToken sevm pre) ≤
      except64th (syncRead0Need sevm callGas1 (syncUsdcRead0Skel sevm pre) +
        usdcBalUsed sevm (syncFirstWorld sevm pre) syncTail getterInitMemory 128
          (syncFirstToken sevm pre)))
    (room1 : balUsed sevm (afterSload sevm d0 7) (syncTail1 d0)
        (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData) 128
          (syncToken1 sevm d0) ≤
      except64th (syncRead1Need sevm d0 G (wethBalanceSkel sevm (afterSload sevm d0 7)
          (syncTail1 d0) (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData)
          128 (syncToken1 sevm d0)) +
        balUsed sevm (afterSload sevm d0 7) (syncTail1 d0)
          (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData) 128
          (syncToken1 sevm d0))) :
    SyncLiveOutcome pair trace pd.keys pd.model sevm pre d0 d1 callGas0 G := by
  have joint := checkpoint_at_deployment_model reads wd pd link holderFresh excluded logs
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := reads.factory_facts pd.rep
  have notAdmin : pair ≠ Usdc.adminOf pre.state usdc := by
    rw [state]
    exact reads.future_pair_not_admin trace
      ⟨joint.usdcInstalled, governance, joint.usdcFoot, usdcFresh⟩
  exact pair_usdc_weth9_history_sync_live_finite trace joint pairFresh usdcFresh wethFresh
    governance factoryInstalled factoryNotSystem target state codeEq fork output representable
    value size selector static depth notAdmin sentry _read1 _read0 fits0 fits1 room0 room1

end Blanc.Composition.LiveUsdcWeth9B26213219
