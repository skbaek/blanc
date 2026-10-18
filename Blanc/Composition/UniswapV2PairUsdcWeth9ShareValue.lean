import Blanc.Composition.PairTwoTokenShareValue
import Blanc.Composition.UniswapV2PairUsdcWeth9Joint

/-!
# C6(b) for the USDC/WETH9 Pair (Appendix A §10, U8b)

`pair_usdc_weth9_history_feeOn_product` / `…feeOff_product`: the generic two-core share-value rows
(`pair_two_token_feeOn_product` / `pair_two_token_feeOff_product`) at the exhibit, with every generic
premise discharged exactly as `pair_usdc_weth9_joint` discharges C6(a)'s.  The fee-on row keeps no
token antecedent; the fee-off row keeps only the factory's fee-off answer `sourceReplayFeeOff`.
Premises: the two-token joint checkpoint, the three HASH-T premises, USDC's governance premise F2,
the never-signer premise for the Pair and the two factory premises.  No hypothesis mentions either
token's answers.
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
    (neverSigner : Blanc.Lift.Token.NeverSigner usdc (Usdc.usdcBookS usdc) trace pair)
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
  obtain ⟨hist0, answerable0, start0, laws0⟩ :=
    JointCheckpoint2.toUsdcCore trace joint governance neverSigner usdcFresh
  obtain ⟨hist1, answerable1, start1⟩ := JointCheckpoint.toCore trace joint.weth9 wethFresh
  exact pair_two_token_feeOn_product (usdcCore usdc KU) (weth9Core weth KW).weak
    (usdcBook_erc20Abi usdc) weth9Book_erc20Abi (usdcSelfCaller usdc KU)
    (weth9SelfCaller weth KW).weak trace laws0 (weth9Book_laws.holderLaws weth trace pair)
    joint.weth9.pairCode joint.weth9.pairRep pairFresh hist0 hist1 joint.token0 joint.weth9.token
    joint.weth9.unlocked joint.apart joint.weth9.apart answerable0 answerable1
    joint.weth9.distinct joint.weth9.notSystem
    (UniswapV2FactoryQuiet.pair_history_factoryQuiet trace joint.weth9.pairCode factoryInstalled
      joint.weth9.pairNonzero factoryNotSystem)
    (usdc_tokenEntered trace joint hist0) (weth9_tokenEntered trace joint.weth9) start0 start1

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
    (neverSigner : Blanc.Lift.Token.NeverSigner usdc (Usdc.usdcBookS usdc) trace pair)
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
  obtain ⟨hist0, answerable0, start0, laws0⟩ :=
    JointCheckpoint2.toUsdcCore trace joint governance neverSigner usdcFresh
  obtain ⟨hist1, answerable1, start1⟩ := JointCheckpoint.toCore trace joint.weth9 wethFresh
  exact pair_two_token_feeOff_product (usdcCore usdc KU) (weth9Core weth KW).weak
    (usdcBook_erc20Abi usdc) weth9Book_erc20Abi (usdcSelfCaller usdc KU)
    (weth9SelfCaller weth KW).weak trace laws0 (weth9Book_laws.holderLaws weth trace pair)
    joint.weth9.pairCode joint.weth9.pairRep pairFresh hist0 hist1 joint.token0 joint.weth9.token
    joint.weth9.unlocked joint.apart joint.weth9.apart answerable0 answerable1
    joint.weth9.distinct joint.weth9.notSystem
    (UniswapV2FactoryQuiet.pair_history_factoryQuiet trace joint.weth9.pairCode factoryInstalled
      joint.weth9.pairNonzero factoryNotSystem)
    (usdc_tokenEntered trace joint hist0) (weth9_tokenEntered trace joint.weth9) start0 start1

end Blanc.Composition.UniswapV2PairUsdcWeth9
