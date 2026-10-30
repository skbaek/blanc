import Blanc.Composition.LiveUsdcWeth9B26213219P1
import Blanc.Composition.UniswapV2PairUsdcWeth9JointF
import Blanc.Composition.PairTwoTokenCallShare

/-!
# Live USDC/WETH9 Pair: share value at every outer Pair call

`pair_usdc_weth9_call_product_finite` instantiates `pair_two_token_call_product` at the USDC/WETH9
Pair over the support-free checkpoint (the arguments of `pair_usdc_weth9_history_feeOn_product_finite`,
plus the factory being no precompile).  `live_pair_share_value` roots it in the WETH9 and Pair
deployments (`WethDeploymentTo`, `PairDeploymentTo`) and the observed block, concluding `LiveShareValue`: every outer Pair call keeps
`ShareValueKept` over the stored words at its entry and committed exit, with the fee `callFeeWords`
its `mint`/`burn` mints at the factory's actual `feeTo()` answer (`feeToAnswer`, read from the frame
the call's factory query entered).  `live_pair_share_value_feeOff` is the fee-off reading under
`FeeOffAlong`.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken Blanc.Composition.PairTwoToken Blanc.Composition.Weth9Token

/-- The stored factory is entered as code at every node of a non-static Pair frame: its runtime is
installed (so undelegated) and it is no precompile of a covered fork. -/
theorem factory_entered {pair factory : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (pairInstalled : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (factoryInstalled :
      some (checkpoint.state.getCode factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotPrecompile : ∀ s : BenvStat, CoveredFork s.fork → ¬ s.rules.isPrecomp factory) :
    ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair → G.sevm.isStatic = false →
      ∀ {node : Exec.Deriv}, Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv G) node →
        getDelegatedCodeAddress (node.devm.getCode factory) = none ∧
          ¬ node.sevm.benvStat.rules.isPrecomp factory := by
  intro G member _ _ node chain
  have nonempty : UniswapV2Factory.code.toList ≠ [] := UniswapV2Factory.factorySem.ne_nil rfl
  have entryCode : (Blanc.Exec.Frame.rootDeriv G).devm.getCode factory = UniswapV2Factory.code :=
    bytes_eq_of_image (trace.settled_codeImage UniswapV2Factory.factorySem factory factoryInstalled
      G member)
  have atNode := Blanc.Exec.Deriv.ParentPrefix.codePreserve chain factory
    (by rw [entryCode]; exact nonempty)
  obtain ⟨-, -, fork, -⟩ := trace.settled_ownCode (pairSem.ne_nil rfl) (pairSem.not_delegation rfl)
    (pair_ownSpawns pair) (bytes_eq_of_image pairInstalled) G member
  refine ⟨?_, ?_⟩
  · rw [atNode, entryCode]
    unfold getDelegatedCodeAddress
    simp only [UniswapV2Factory.factorySem.not_delegation rfl, ↓reduceIte]
  · rw [Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain]
    exact factoryNotPrecompile _ fork

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
    (factoryNotSystem : st₀.factory ≠ systemAddress)
    (factoryNotPrecompile : ∀ s : BenvStat, CoveredFork s.fork → ¬ s.rules.isPrecomp st₀.factory) :
    ∀ f, OuterPairCall pair trace f →
      ShareValueKept (preS pair f) (postS pair f) (callFeeWords pair f) := by
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
    (factory_entered trace joint.weth9.pairCode factoryInstalled factoryNotPrecompile)

end Blanc.Composition.UniswapV2PairUsdcWeth9

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken Blanc.Composition.PairTwoToken Blanc.Composition.Weth9Token
  Blanc.Composition.UniswapV2PairUsdcWeth9

/-- **Share value at every outer call of the live Pair** (the stored words at each outer call's
entry and committed exit; `F` the fee `mint`/`burn` mints at the factory's actual `feeTo()`
answer, zero otherwise). -/
def LiveShareValue {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace mainnetChainConfig checkpoint future) : Prop :=
  ∀ f, OuterPairCall pair trace f →
    ShareValueKept (preS pair f) (postS pair f) (callFeeWords pair f)

/-- The factory answered `feeTo() = 0` at every outer call of the live Pair. -/
def FeeOffAlong {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace mainnetChainConfig checkpoint future) : Prop :=
  ∀ f, OuterPairCall pair trace f → feeToAnswer f = 0

/-- The live factory address is no precompile of a covered fork. -/
theorem factory_notPrecompile : ∀ s : BenvStat, CoveredFork s.fork →
    ¬ s.rules.isPrecomp finiteModel.factory := fun s covered =>
  covered.cases (motive := fun f => ¬ (Fork.ruleSet f).isPrecomp finiteModel.factory)
    (by decide) (by decide) (by decide) (by decide)

/-- **Share value at every outer call of the live USDC/WETH9 Pair**, from the WETH9 and Pair
deployments and the observed block: every outer Pair call with
positive incoming supply word keeps `r0 · r1 · T'² ≤ r0' · r1' · (T + F)²` over the stored words
at its entry and committed exit, `F` the protocol fee its `mint`/`burn` mints at the factory's
actual `feeTo()` answer. -/
theorem live_pair_share_value
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
    LiveShareValue (anchor.futureTrace continuation) := by
  have joint := checkpoint_at_bound_deployment_model anchor wd pd link holderFresh
    wethSenderExcluded avoid initialPair
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := anchor.reads.factory_facts pd.rep
  have same := pd.rep.fixed.2.2.1.symm.trans anchor.reads.pairWords.fixedMatches.2.2.1
  exact pair_usdc_weth9_call_product_finite (anchor.futureTrace continuation) joint pairFresh
    usdcFresh wethFresh governance usdcHistory.quiet factoryInstalled factoryNotSystem
    (by rw [same]; exact factory_notPrecompile)

/-- **Fee-off share value at every outer call of the live USDC/WETH9 Pair**: where the factory
answered `feeTo() = 0` at every outer call, no call mints a fee, and every outer Pair call with
positive incoming supply word keeps `r0 · r1 · T'² ≤ r0' · r1' · T²` over its stored words. -/
theorem live_pair_share_value_feeOff
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
    (governance : Usdc.UsdcGovernance usdc (anchor.futureTrace continuation))
    (feeOff : FeeOffAlong (anchor.futureTrace continuation)) :
    ∀ f, OuterPairCall pair (anchor.futureTrace continuation) f →
      ShareValueKept (preS pair f) (postS pair f) 0 := by
  intro f outer
  have kept := live_pair_share_value anchor wd pd link holderFresh wethSenderExcluded avoid
    initialPair continuation usdcHistory pairFresh usdcFresh wethFresh governance f outer
  have zero : callFeeWords pair f = 0 := by
    unfold callFeeWords feeMintWords
    rw [feeOff f outer]
    split <;> simp only [true_or, ↓reduceIte]
  rwa [zero] at kept

end Blanc.Composition.LiveUsdcWeth9B26213219
