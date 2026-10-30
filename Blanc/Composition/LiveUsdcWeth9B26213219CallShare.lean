import Blanc.Composition.LiveUsdcWeth9B26213219P1
import Blanc.Composition.UniswapV2PairUsdcWeth9JointF
import Blanc.Composition.PairTwoTokenCallShare

/-!
# Live USDC/WETH9 Pair: share value at every outer Pair call

`pair_usdc_weth9_call_product_finite` instantiates `pair_two_token_call_product` at the USDC/WETH9
Pair over the support-free checkpoint (the arguments of `pair_usdc_weth9_history_feeOn_product_finite`);
`live_pair_call_product` roots it in the WETH9 and Pair deployments (`WethDeploymentTo`,
`PairDeploymentTo`) with the premises of `feeOn_product_from_original_history`.  Every outer Pair
call with positive incoming supply word keeps `r0 · r1 · T'² ≤ r0' · r1' · (T + F)²` over the stored
words at its entry and exit, `F` the fee mint over the entry words at the call's `feeTo` answer.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken Blanc.Composition.PairTwoToken Blanc.Composition.Weth9Token

/-- **Share value at every outer call of the USDC/WETH9 Pair, support-free checkpoint.** -/
theorem pair_usdc_weth9_call_product_finite {pair usdc weth : Adr}
    {cfg : ChainConfig} {checkpoint future : BlockChain} {KU : Usdc.Key → Prop}
    {KW : Weth9.Key → Prop} {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint2F pair usdc weth KU KW KP st₀ checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (usdcFresh : Usdc.KeysFresh KU (Usdc.historyTouchedKeys usdc trace))
    (wethFresh : Weth9.KeysFresh KW (Weth9.historyTouchedKeys weth trace))
    (governance : Usdc.UsdcGovernance usdc trace)
    (quiet : PairUsdcAllowQuiet pair usdc trace)
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress) :
    ∀ f, OuterPairCall pair trace f →
      ∃ s : PairStep, s.frame = f ∧ s.AuthenticWith PairEntryAuth pair ∧
        (0 < (supplyWord (preS pair f)).toNat →
          (reserve0Word (preS pair f)).toNat * (reserve1Word (preS pair f)).toNat *
              (supplyWord (postS pair f)).toNat ^ 2 ≤
            (reserve0Word (postS pair f)).toNat * (reserve1Word (postS pair f)).toNat *
              ((supplyWord (preS pair f)).toNat +
                entryFeeWords (preS pair f) s.entry s.transcript) ^ 2) := by
  obtain ⟨hist0, answerable0, start0, laws0⟩ :=
    JointCheckpoint2F.toUsdcCoreF trace joint governance quiet usdcFresh
  obtain ⟨hist1, answerable1, start1⟩ := JointCheckpoint.toCore trace joint.weth9 wethFresh
  exact pair_two_token_call_product (usdcCoreF usdc KU) (weth9Core weth KW).weak
    (usdcBook_erc20Abi usdc) weth9Book_erc20Abi (usdcSelfCallerF usdc KU)
    (weth9SelfCaller weth KW).weak trace laws0 (weth9Book_laws.holderLaws weth trace pair)
    joint.weth9.pairCode joint.weth9.pairRep pairFresh hist0 hist1 joint.token0 joint.weth9.token
    joint.weth9.unlocked joint.apart joint.weth9.apart answerable0 answerable1
    joint.weth9.distinct joint.weth9.notSystem
    (UniswapV2FactoryQuiet.pair_history_factoryQuiet trace joint.weth9.pairCode factoryInstalled
      joint.weth9.pairNonzero factoryNotSystem)
    (usdc_tokenEntered trace joint hist0) (weth9_tokenEntered trace joint.weth9) start0 start1

end Blanc.Composition.UniswapV2PairUsdcWeth9

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken Blanc.Composition.PairTwoToken Blanc.Composition.Weth9Token
  Blanc.Composition.UniswapV2PairUsdcWeth9

/-- **Share value at every outer call of the live USDC/WETH9 Pair**, from the WETH9 and Pair
deployments (the premises of `feeOn_product_from_original_history`). -/
theorem live_pair_call_product
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
    ∀ f, OuterPairCall pair (anchor.futureTrace continuation) f →
      ∃ s : PairStep, s.frame = f ∧ s.AuthenticWith PairEntryAuth pair ∧
        (0 < (supplyWord (preS pair f)).toNat →
          (reserve0Word (preS pair f)).toNat * (reserve1Word (preS pair f)).toNat *
              (supplyWord (postS pair f)).toNat ^ 2 ≤
            (reserve0Word (postS pair f)).toNat * (reserve1Word (postS pair f)).toNat *
              ((supplyWord (preS pair f)).toNat +
                entryFeeWords (preS pair f) s.entry s.transcript) ^ 2) := by
  have joint := checkpoint_at_bound_deployment_model anchor wd pd link holderFresh
    wethSenderExcluded avoid initialPair
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := anchor.reads.factory_facts pd.rep
  exact pair_usdc_weth9_call_product_finite (anchor.futureTrace continuation) joint pairFresh
    usdcFresh wethFresh governance usdcHistory.quiet factoryInstalled factoryNotSystem

end Blanc.Composition.LiveUsdcWeth9B26213219
