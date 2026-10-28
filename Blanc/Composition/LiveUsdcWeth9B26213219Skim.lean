import Blanc.Composition.LiveUsdcWeth9B26213219Sync
import Blanc.Composition.UniswapV2PairUsdcWeth9SkimLiveF

/-!
# Live Pair skim from the original linked histories

The historical checkpoint, factory facts and proxy-admin exclusion are derived
from the same original history and finite reads as the live sync connection.
All existing skim call, freshness, transfer-acceptance and outcome conditions
remain explicit. Observations and receipt absence are not adopted here.
-/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairUsdcWeth9
  Blanc.Composition.UniswapV2PairWeth9Joint Blanc.Composition.UsdcToken
  Blanc.Composition.Weth9Token Blanc.Composition.UsdcLive

/-- The live-address skim theorem, with its checkpoint and admin facts derived
from original deployment histories. It retains every operation-specific premise
of the existing support-free theorem, and adds no USDC quiet/P1 premise. -/
theorem skim_from_linked_receipts {checkpoint future : BlockChain}
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
    {sevm : Sevm} {pre : Devm} {g : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (abi : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (static : sevm.isStatic = false) (depth : 2 ≤ sevm.depth)
    (callee : SkimCalleeUW sevm pre g) (usdcSentries : callee.UsdcSentries)
    (wethSentries : callee.WethSentries)
    (recipientFresh : Usdc.KeysFresh (Usdc.historyKeyUniverse usdc trace (FiniteCheckpoint.rowKeys usdcRows))
      [.bal (Sevm.dataWord sevm 4).toAdr])
    (usdcLive : UsdcTransferOk
      (Usdc.ledger (SlotFootprint.extendBy (Usdc.historyKeyUniverse usdc trace (FiniteCheckpoint.rowKeys usdcRows))
        [.bal (Sevm.dataWord sevm 4).toAdr]) (pre.state.getStor usdc))
      pair (Sevm.dataWord sevm 4).toAdr (callee.balance0 - skimReserve0 sevm pre).toNat) :
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace pd.keys pd.model finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 →
        transcript.ownTail.ownTail.firstWord = callee.balance1 →
        (runTyped finish (writerContext sevm []) (.skim (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty callee.gas) (.ok callee.post),
          callee.post.gasLeft = g ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace pd.keys)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩) →
            PairAdmittedOutcome
              (WriterExtend (pairHistoryUniverse pair trace pd.keys)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩ callee.post) := by
  have joint := checkpoint_at_deployment_model reads wd pd link holderFresh excluded logs
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := reads.factory_facts pd.rep
  have notAdmin : pair ≠ Usdc.adminOf pre.state usdc := by
    rw [state]
    exact reads.future_pair_not_admin trace
      ⟨joint.usdcInstalled, governance, joint.usdcFoot, usdcFresh⟩
  exact pair_usdc_weth9_history_skim_live_finite trace joint pairFresh usdcFresh wethFresh
    governance factoryInstalled factoryNotSystem target state codeEq fork output representable
    value size abi selector static depth notAdmin callee usdcSentries wethSentries recipientFresh usdcLive

end Blanc.Composition.LiveUsdcWeth9B26213219
