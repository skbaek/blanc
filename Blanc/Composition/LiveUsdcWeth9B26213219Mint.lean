import Blanc.Composition.LiveUsdcWeth9B26213219Sync
import Blanc.Composition.UniswapV2PairUsdcWeth9MintLiveF

/-!
# Live Pair mint from the original linked histories

The historical checkpoint, factory facts and proxy-admin exclusion are derived
from the same original history and finite reads as the live sync connection.
All existing mint call, freshness, transfer-acceptance and outcome conditions
remain explicit. Observations and receipt absence are not adopted here.
-/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairUsdcWeth9
  Blanc.Composition.UniswapV2PairWeth9Joint Blanc.Composition.UsdcToken
  Blanc.Composition.Weth9Token Blanc.Composition.UsdcLive

/-- The live-address mint theorem, with its checkpoint and admin facts derived
from original deployment histories. It retains every operation-specific premise
of the existing support-free theorem, and adds no USDC quiet/P1 premise. -/
theorem mint_from_linked_receipts {checkpoint future : BlockChain}
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
    {sevm : Sevm} {pre : Devm} {G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842) (depth : 2 ≤ sevm.depth)
    (callee : MintCalleeRest sevm pre [0x6a627842] getterInitMemory
      (Sevm.dataWord sevm 4).toAdr.toB256 0x039b (G + 43))
    (_read1 : (callee.d1, callee.callGas1) = mintWethRead1 sevm
      (mintUsdcRead0Skel sevm (mintCacheWorld sevm pre) [0x6a627842] getterInitMemory
        (mintR1 sevm pre) (mintR0 sevm pre) (Sevm.dataWord sevm 4).toAdr.toB256 0x039b)
      [0x6a627842] getterInitMemory (mintR1 sevm pre) (mintR0 sevm pre)
      (Sevm.dataWord sevm 4).toAdr.toB256 0x039b callee.factoryGas)
    (_read0 : (callee.d0, callee.callGas0) = mintUsdcRead0 sevm (mintCacheWorld sevm pre)
      [0x6a627842] getterInitMemory (mintR1 sevm pre) (mintR0 sevm pre)
      (Sevm.dataWord sevm 4).toAdr.toB256 0x039b callee.callGas1)
    (fits0 : callee.callGas0 < 2 ^ 256) (fits1 : callee.callGas1 < 2 ^ 256)
    (room0 : usdcBalNeed sevm (afterSload sevm (mintCacheWorld sevm pre) 6)
        (mintTail0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
          (Sevm.dataWord sevm 4).toAdr.toB256 0x039b) getterInitMemory 128
        (mintToken0 sevm (mintCacheWorld sevm pre)) ≤
      except64th (mintRead0Need sevm callee.callGas1
          (mintUsdcRead0Skel sevm (mintCacheWorld sevm pre) [0x6a627842] getterInitMemory
            (mintR1 sevm pre) (mintR0 sevm pre) (Sevm.dataWord sevm 4).toAdr.toB256 0x039b) +
        usdcBalUsed sevm (afterSload sevm (mintCacheWorld sevm pre) 6)
          (mintTail0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
            (Sevm.dataWord sevm 4).toAdr.toB256 0x039b) getterInitMemory 128
          (mintToken0 sevm (mintCacheWorld sevm pre))))
    (room1 : balUsed sevm (afterSload sevm callee.d0 7)
        (mintTail1 callee.d0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
          (Sevm.dataWord sevm 4).toAdr.toB256 0x039b)
        (balanceReplyMemory getterInitMemory sevm.currentTarget callee.d0.returnData) 128
        (syncToken1 sevm callee.d0) ≤
      except64th (mintRead1Need sevm callee.factoryGas (wethBalanceSkel sevm
          (afterSload sevm callee.d0 7)
          (mintTail1 callee.d0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
            (Sevm.dataWord sevm 4).toAdr.toB256 0x039b)
          (balanceReplyMemory getterInitMemory sevm.currentTarget callee.d0.returnData) 128
          (syncToken1 sevm callee.d0)) +
        balUsed sevm (afterSload sevm callee.d0 7)
          (mintTail1 callee.d0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
            (Sevm.dataWord sevm 4).toAdr.toB256 0x039b)
          (balanceReplyMemory getterInitMemory sevm.currentTarget callee.d0.returnData) 128
          (syncToken1 sevm callee.d0)))
    (rowsFresh : WriterFreshKeys (pairHistoryUniverse pair trace pd.keys)
      (lpMintTouched (0 : B256).toAdr ++ lpMintTouched (Sevm.dataWord sevm 4).toAdr ++
        lpMintTouched callee.feeTo)) :
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace pd.keys pd.model finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 → transcript.ownTail.firstWord = callee.balance1 →
        transcript.ownTail.ownTail.firstWord.toAdr = callee.feeTo →
        (runTyped finish (writerContext sevm []) (.mint (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ (liquidity : B256)
          (run : Exec 0 sevm (St pre [] Mem.empty (callee.gas + 228))
            (.ok (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G))),
          (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G).gasLeft = G ∧
          (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G).output =
            liquidity.toBytes ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace pd.keys)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩) →
            PairAdmittedOutcome
              (WriterExtend (pairHistoryUniverse pair trace pd.keys)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩
              (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G)) := by
  have joint := checkpoint_at_deployment_model reads wd pd link holderFresh excluded logs
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := reads.factory_facts pd.rep
  have notAdmin : pair ≠ Usdc.adminOf pre.state usdc := by
    rw [state]
    exact reads.future_pair_not_admin trace
      ⟨joint.usdcInstalled, governance, joint.usdcFoot, usdcFresh⟩
  exact pair_usdc_weth9_history_mint_live_finite trace joint pairFresh usdcFresh wethFresh
    governance factoryInstalled factoryNotSystem target state codeEq fork output representable
    value size guard selector depth notAdmin callee _read1 _read0 fits0 fits1 room0 room1 rowsFresh

end Blanc.Composition.LiveUsdcWeth9B26213219
