import Blanc.Composition.PairTwoTokenShareValue
import Blanc.Composition.UniswapV2PairUsdcWeth9Joint
import Blanc.Composition.UniswapV2PairUsdcWeth9ShareValueF

/-!
# C6(b) for the USDC/WETH9 Pair (Appendix A §10, U8b)

`pair_usdc_weth9_history_feeOn_product` / `…feeOff_product`: the generic two-core share-value rows
(`pair_two_token_feeOn_product` / `pair_two_token_feeOff_product`) at the exhibit, with every generic
premise discharged exactly as `pair_usdc_weth9_joint` discharges C6(a)'s.  The fee-on row keeps no
token antecedent; the fee-off row keeps only the factory's fee-off answer `sourceReplayFeeOff`.
Premises: the two-token joint checkpoint, the three HASH-T premises, USDC's governance premise F2
and the two factory premises (the never-signer fact comes from the checkpoint,
`usdc_neverSigner_pair`).  No hypothesis mentions either token's answers.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken Blanc.Composition.PairTwoToken Blanc.Composition.Weth9Token

/-- **C6(b), fee on, the exhibit**: share value with no token antecedent. -/
theorem pair_usdc_weth9_history_feeOn_product {pair usdc weth : Adr}
    {cfg : ChainConfig} {checkpoint future : BlockChain} {KU : Usdc.Key → Prop}
    {KW : Weth9.Key → Prop} {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint2 pair usdc weth KU KW KP st₀ checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (usdcFresh : Usdc.KeysFresh KU (Usdc.historyTouchedKeys usdc trace))
    (wethFresh : Weth9.KeysFresh KW (Weth9.historyTouchedKeys weth trace))
    (governance : Usdc.UsdcGovernance usdc trace)
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress) :
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
        PairObservedReplayWith PairAdmittedConsumes st₀ steps finish ∧
        runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        ∀ before inv after, (before, inv, after) ∈ sourceReplaySteps st₀ (steps.map PairStep.source) →
          0 < before.totalSupply.toNat →
          before.reserve0.val * before.reserve1.val * after.totalSupply.toNat ^ 2 ≤
            after.reserve0.val * after.reserve1.val *
              (before.totalSupply.toNat + entryFeeAmount before inv.entry inv.transcript) ^ 2 := by
  exact pair_usdc_weth9_history_feeOn_product_finite trace joint.toF pairFresh usdcFresh
    wethFresh governance (joint.allowQuiet usdcFresh) factoryInstalled
    factoryNotSystem

/-- **C6(b), fee off, the exhibit**: only the factory's fee-off answer stays. -/
theorem pair_usdc_weth9_history_feeOff_product {pair usdc weth : Adr}
    {cfg : ChainConfig} {checkpoint future : BlockChain} {KU : Usdc.Key → Prop}
    {KW : Weth9.Key → Prop} {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint2 pair usdc weth KU KW KP st₀ checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (usdcFresh : Usdc.KeysFresh KU (Usdc.historyTouchedKeys usdc trace))
    (wethFresh : Weth9.KeysFresh KW (Weth9.historyTouchedKeys weth trace))
    (governance : Usdc.UsdcGovernance usdc trace)
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress) :
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
        PairObservedReplayWith PairAdmittedConsumes st₀ steps finish ∧
        runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        (sourceReplayFeeOff st₀ (steps.map PairStep.source) →
          ∀ before after, (before, after) ∈ sourceReplayEdges st₀ (steps.map PairStep.source) →
            0 < before.totalSupply.toNat →
            before.reserve0.val * before.reserve1.val * after.totalSupply.toNat ^ 2 ≤
              after.reserve0.val * after.reserve1.val * before.totalSupply.toNat ^ 2) := by
  exact pair_usdc_weth9_history_feeOff_product_finite trace joint.toF pairFresh usdcFresh
    wethFresh governance (joint.allowQuiet usdcFresh) factoryInstalled
    factoryNotSystem

end Blanc.Composition.UniswapV2PairUsdcWeth9
