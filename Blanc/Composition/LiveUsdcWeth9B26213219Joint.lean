import Blanc.Composition.LiveUsdcWeth9B26213219P1
import Blanc.Composition.UniswapV2PairUsdcWeth9JointF

/-!
# Concrete live Pair joint invariant from original histories

The bound finite observations and deployment histories construct the checkpoint.
The original USDC constructor-to-D-to-B inputs derive touched-row P1 for the
same future trace. All historical evidence, finite-check truth and future
governance/freshness conditions remain explicit; no observation is adopted.
-/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken Blanc.Composition.PairTwoToken Blanc.Composition.Weth9Token
  Blanc.Composition.UniswapV2PairUsdcWeth9

/-- The complete source conclusion on the original future trace, with checkpoint
and USDC quietness derived rather than supplied. -/
theorem joint_from_original_history
    {checkpoint future : BlockChain}
    (anchor : ObservedCheckpoint checkpoint)
    (wd : WethDeploymentTo checkpoint) (pd : PairDeploymentTo checkpoint)
    (link : DeploymentHistoryLink wd pd)
    (holderFresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots wd.keys (.bal pair))
    (wethSenderExcluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (avoid : ∀ root ∈ link.beforePairFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ pair)
    (initialPair : wd.cut.afterBenv.state.getCode pair = ByteArray.empty)
    (continuation : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    (usdcHistory : OriginalUsdcHistory (anchor.futureTrace continuation))
    (pairFresh : WriterFreshKeys pd.keys
      (pairHistoryTouchedKeys pair (anchor.futureTrace continuation)))
    (usdcFresh : Usdc.KeysFresh (FiniteCheckpoint.rowKeys usdcRows)
      (Usdc.historyTouchedKeys usdc (anchor.futureTrace continuation)))
    (wethFresh : Weth9.KeysFresh wd.keys
      (Weth9.historyTouchedKeys weth (anchor.futureTrace continuation)))
    (governance : Usdc.UsdcGovernance usdc (anchor.futureTrace continuation)) :
    let trace := anchor.futureTrace continuation
    (∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      trace.settledFrames = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = pair ∧ A.sevm.isStatic = false)) →
      ¬ Usdc.UsdcShadowed usdc trace before f →
      ∃ (st : UniswapV2Pair.State) (K : WriterKey → Prop),
        WriterRep K (f.pre.state.getStor pair) st ∧ st.unlocked = 1 ∧ st.token0 = usdc ∧
          st.token1 = weth ∧
          st.reserve0.val ≤
            (Usdc.ledger (Usdc.historyKeyUniverse usdc trace (FiniteCheckpoint.rowKeys usdcRows)) (f.pre.state.getStor usdc)).bal pair ∧
          (∀ g, (Usdc.ledger (Usdc.historyKeyUniverse usdc trace (FiniteCheckpoint.rowKeys usdcRows))
            (f.pre.state.getStor usdc)).allow pair g = 0) ∧
          st.reserve1.val ≤
            ((Weth9.ledger (Weth9.historyKeyUniverse weth trace wd.keys) (f.pre.state.getStor weth)).bal
              pair).toNat ∧
          ∀ g, (Weth9.ledger (Weth9.historyKeyUniverse weth trace wd.keys)
            (f.pre.state.getStor weth)).allow pair g = 0) ∧
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace pd.keys pd.model finish K' ∧
        finish.reserve0.val ≤ Usdc.balanceBits ((future.state.getStor usdc).get (Usdc.balSlot pair)) ∧
        (∀ g, Usdc.historyKeyUniverse usdc trace (FiniteCheckpoint.rowKeys usdcRows) (.allow pair g) →
          (future.state.getStor usdc).get (Usdc.allowSlot pair g) = 0) ∧
        finish.reserve1.val ≤ ((future.state.getStor weth).get (Weth9.balSlot pair)).toNat ∧
        ∀ g, Weth9.historyKeyUniverse weth trace wd.keys (.allow pair g) →
          (future.state.getStor weth).get (Weth9.allowSlot pair g) = 0 := by
  let trace := anchor.futureTrace continuation
  have joint := checkpoint_at_bound_deployment_model anchor wd pd link holderFresh
    wethSenderExcluded avoid initialPair
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := anchor.reads.factory_facts pd.rep
  exact pair_usdc_weth9_joint_finite trace joint pairFresh usdcFresh wethFresh
    governance usdcHistory.quiet factoryInstalled factoryNotSystem

/-- Receipt-premise variant: the same conclusion and remaining hypotheses,
using absence of Pair-owned WETH approvals in the original pre-deployment receipts.
The receipt premise is explicit and no external observation is adopted. -/
theorem joint_from_original_receipts
    {checkpoint future : BlockChain}
    (anchor : ObservedCheckpoint checkpoint)
    (wd : WethDeploymentTo checkpoint) (pd : PairDeploymentTo checkpoint)
    (link : DeploymentHistoryLink wd pd)
    (holderFresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots wd.keys (.bal pair))
    (wethSenderExcluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (logs : ∀ (spender : Adr) (data : Bytes),
      Log.mk weth [Weth9.approvalTopic, pair.toB256, spender.toB256] data ∉
        link.beforePairReceiptLogs)
    (continuation : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    (usdcHistory : OriginalUsdcHistory (anchor.futureTrace continuation))
    (pairFresh : WriterFreshKeys pd.keys
      (pairHistoryTouchedKeys pair (anchor.futureTrace continuation)))
    (usdcFresh : Usdc.KeysFresh (FiniteCheckpoint.rowKeys usdcRows)
      (Usdc.historyTouchedKeys usdc (anchor.futureTrace continuation)))
    (wethFresh : Weth9.KeysFresh wd.keys
      (Weth9.historyTouchedKeys weth (anchor.futureTrace continuation)))
    (governance : Usdc.UsdcGovernance usdc (anchor.futureTrace continuation)) :
    let trace := anchor.futureTrace continuation
    (∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      trace.settledFrames = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = pair ∧ A.sevm.isStatic = false)) →
      ¬ Usdc.UsdcShadowed usdc trace before f →
      ∃ (st : UniswapV2Pair.State) (K : WriterKey → Prop),
        WriterRep K (f.pre.state.getStor pair) st ∧ st.unlocked = 1 ∧ st.token0 = usdc ∧
          st.token1 = weth ∧
          st.reserve0.val ≤
            (Usdc.ledger (Usdc.historyKeyUniverse usdc trace (FiniteCheckpoint.rowKeys usdcRows)) (f.pre.state.getStor usdc)).bal pair ∧
          (∀ g, (Usdc.ledger (Usdc.historyKeyUniverse usdc trace (FiniteCheckpoint.rowKeys usdcRows))
            (f.pre.state.getStor usdc)).allow pair g = 0) ∧
          st.reserve1.val ≤
            ((Weth9.ledger (Weth9.historyKeyUniverse weth trace wd.keys) (f.pre.state.getStor weth)).bal
              pair).toNat ∧
          ∀ g, (Weth9.ledger (Weth9.historyKeyUniverse weth trace wd.keys)
            (f.pre.state.getStor weth)).allow pair g = 0) ∧
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace pd.keys pd.model finish K' ∧
        finish.reserve0.val ≤ Usdc.balanceBits ((future.state.getStor usdc).get (Usdc.balSlot pair)) ∧
        (∀ g, Usdc.historyKeyUniverse usdc trace (FiniteCheckpoint.rowKeys usdcRows) (.allow pair g) →
          (future.state.getStor usdc).get (Usdc.allowSlot pair g) = 0) ∧
        finish.reserve1.val ≤ ((future.state.getStor weth).get (Weth9.balSlot pair)).toNat ∧
        ∀ g, Weth9.historyKeyUniverse weth trace wd.keys (.allow pair g) →
          (future.state.getStor weth).get (Weth9.allowSlot pair g) = 0 := by
  let trace := anchor.futureTrace continuation
  have joint := checkpoint_at_bound_deployment_model_of_receipts anchor wd pd link holderFresh
    wethSenderExcluded logs
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := anchor.reads.factory_facts pd.rep
  exact pair_usdc_weth9_joint_finite trace joint pairFresh usdcFresh wethFresh
    governance usdcHistory.quiet factoryInstalled factoryNotSystem

end Blanc.Composition.LiveUsdcWeth9B26213219
