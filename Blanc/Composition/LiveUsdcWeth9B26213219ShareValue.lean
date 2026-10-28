import Blanc.Composition.LiveUsdcWeth9B26213219P1
import Blanc.Composition.UniswapV2PairUsdcWeth9ShareValueF

/-!
# Concrete live Pair share-value products from original histories

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
theorem feeOn_product_from_original_history
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
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
        PairObservedReplayWith PairAdmittedConsumes pd.model steps finish ∧
        runSourceInvocations pd.model (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        ∀ before inv after, (before, inv, after) ∈ sourceReplaySteps pd.model (steps.map PairStep.source) →
          0 < before.totalSupply.toNat →
          before.reserve0.val * before.reserve1.val * after.totalSupply.toNat ^ 2 ≤
            after.reserve0.val * after.reserve1.val *
              (before.totalSupply.toNat + entryFeeAmount before inv.entry inv.transcript) ^ 2 := by
  let trace := anchor.futureTrace continuation
  have joint := checkpoint_at_bound_deployment_model anchor wd pd link holderFresh
    wethSenderExcluded avoid initialPair
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := anchor.reads.factory_facts pd.rep
  exact pair_usdc_weth9_history_feeOn_product_finite trace joint pairFresh usdcFresh wethFresh
    governance usdcHistory.quiet factoryInstalled factoryNotSystem

/-- The complete source conclusion on the original future trace, with checkpoint
and USDC quietness derived rather than supplied. -/
theorem feeOff_product_from_original_history
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
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
        PairObservedReplayWith PairAdmittedConsumes pd.model steps finish ∧
        runSourceInvocations pd.model (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        (sourceReplayFeeOff pd.model (steps.map PairStep.source) →
          ∀ before after, (before, after) ∈ sourceReplayEdges pd.model (steps.map PairStep.source) →
            0 < before.totalSupply.toNat →
            before.reserve0.val * before.reserve1.val * after.totalSupply.toNat ^ 2 ≤
              after.reserve0.val * after.reserve1.val * before.totalSupply.toNat ^ 2) := by
  let trace := anchor.futureTrace continuation
  have joint := checkpoint_at_bound_deployment_model anchor wd pd link holderFresh
    wethSenderExcluded avoid initialPair
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := anchor.reads.factory_facts pd.rep
  exact pair_usdc_weth9_history_feeOff_product_finite trace joint pairFresh usdcFresh wethFresh
    governance usdcHistory.quiet factoryInstalled factoryNotSystem

/-- Receipt-premise variant: the same conclusion and remaining hypotheses,
using absence of Pair-owned WETH approvals in the original pre-deployment receipts.
The receipt premise is explicit and no external observation is adopted. -/
theorem feeOn_product_from_original_receipts
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
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
        PairObservedReplayWith PairAdmittedConsumes pd.model steps finish ∧
        runSourceInvocations pd.model (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        ∀ before inv after, (before, inv, after) ∈ sourceReplaySteps pd.model (steps.map PairStep.source) →
          0 < before.totalSupply.toNat →
          before.reserve0.val * before.reserve1.val * after.totalSupply.toNat ^ 2 ≤
            after.reserve0.val * after.reserve1.val *
              (before.totalSupply.toNat + entryFeeAmount before inv.entry inv.transcript) ^ 2 := by
  let trace := anchor.futureTrace continuation
  have joint := checkpoint_at_bound_deployment_model_of_receipts anchor wd pd link holderFresh
    wethSenderExcluded logs
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := anchor.reads.factory_facts pd.rep
  exact pair_usdc_weth9_history_feeOn_product_finite trace joint pairFresh usdcFresh wethFresh
    governance usdcHistory.quiet factoryInstalled factoryNotSystem

/-- Receipt-premise variant: the same conclusion and remaining hypotheses,
using absence of Pair-owned WETH approvals in the original pre-deployment receipts.
The receipt premise is explicit and no external observation is adopted. -/
theorem feeOff_product_from_original_receipts
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
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
        PairObservedReplayWith PairAdmittedConsumes pd.model steps finish ∧
        runSourceInvocations pd.model (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        (sourceReplayFeeOff pd.model (steps.map PairStep.source) →
          ∀ before after, (before, after) ∈ sourceReplayEdges pd.model (steps.map PairStep.source) →
            0 < before.totalSupply.toNat →
            before.reserve0.val * before.reserve1.val * after.totalSupply.toNat ^ 2 ≤
              after.reserve0.val * after.reserve1.val * before.totalSupply.toNat ^ 2) := by
  let trace := anchor.futureTrace continuation
  have joint := checkpoint_at_bound_deployment_model_of_receipts anchor wd pd link holderFresh
    wethSenderExcluded logs
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := anchor.reads.factory_facts pd.rep
  exact pair_usdc_weth9_history_feeOff_product_finite trace joint pairFresh usdcFresh wethFresh
    governance usdcHistory.quiet factoryInstalled factoryNotSystem

end Blanc.Composition.LiveUsdcWeth9B26213219
