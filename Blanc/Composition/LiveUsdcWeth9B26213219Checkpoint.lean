import Blanc.Composition.LiveUsdcWeth9B26213219Words
import Blanc.Composition.LiveUsdcWeth9B26213219Code
import Blanc.Lift.UniswapV2Factory.CallShape

/-!
# Concrete finite checkpoint assembly at B26213219

`ObservedAt` names only the supplied code and finite word reads. The kernel
checks their finite conditions; historical representation and backing remain
on the same arbitrary world. No world or storage map is enumerated, and no
observed state root is authenticated by these theorems. Fetched observations
remain unadmitted. L3's future touched-row allowance result is still separate.
-/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair
  Blanc.Composition.UniswapV2PairUsdcWeth9
  Blanc.Composition.UniswapV2PairWeth9Joint LiveUsdcWeth9B26213219Data

/-- Finite observations at the fixed block, without any support assertion. -/
structure ObservedAt (w : Jaune.State) : Prop where
  pairRuntime : (w.getCode pair).data.toList = pairCode
  wethRuntime : (w.getCode weth).data.toList = weth9Code
  proxyRuntime : (w.getCode usdc).data.toList = usdcProxyCode
  implRuntime : (w.getCode Usdc.usdcImpl).data.toList = usdcImplementationCode
  libRuntime : (w.getCode Usdc.usdcLib).data.toList = usdcLibraryCode
  factoryRuntime : (w.getCode finiteModel.factory).data.toList = factoryCode
  implementation : (w.getStor usdc).get Usdc.implSlot = usdcImplementationWord
  initialized : (w.getStor usdc).get 8 = usdcInitializedWord
  version : (w.getStor usdc).get 18 = usdcVersionWord
  admin : (w.getStor usdc).get usdcAdminWordSlot = usdcAdminWord
  usdcBalance : (w.getStor usdc).get usdcPairBalanceWordSlot = usdcPairBalanceWord
  wethBalance : (w.getStor weth).get wethPairBalanceWordSlot = wethPairBalanceWord
  pairWords : PairWordsAt (w.getStor pair)

/-- The existing finite admin read excludes the Pair as proxy administrator. -/
theorem ObservedAt.pair_not_admin {w : Jaune.State} (reads : ObservedAt w) :
    pair ≠ Usdc.adminOf w usdc := by
  have slot : Usdc.adminSlot = usdcAdminWordSlot := by decide +kernel
  rw [Usdc.adminOf, slot, reads.admin]
  decide +kernel

/-- All bounded WETH9/Pair conditions follow from the supplied finite reads. -/
theorem ObservedAt.weth_checked {w : Jaune.State} (reads : ObservedAt w) :
    checkWeth9PairFinite pair weth finiteModel w = true := by
  simp only [checkWeth9PairFinite, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨reads.pairRuntime.trans pair_code,
    reads.wethRuntime.trans weth_code⟩, token1_eq⟩, unlocked_eq⟩, ?_⟩,
    address_separation.1⟩, ?_⟩, address_separation.2.2.2.1⟩,
    address_separation.2.2.2.2.1⟩, addresses_not_precompiles.2.2⟩
  · rw [weth_balance_slot, reads.wethBalance]
    exact weth_reserve
  · rw [token0_eq, token1_eq]
    exact address_separation.2.2.1

/-- All bounded USDC conditions, including the singleton balance row, are checked. -/
theorem ObservedAt.usdc_checked {w : Jaune.State} (reads : ObservedAt w) :
    Usdc.checkUsdcF usdc usdcRows w = true := by
  simp only [Usdc.checkUsdcF, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨reads.proxyRuntime.trans usdc_proxy_code,
    reads.implRuntime.trans usdc_implementation_code⟩,
    reads.libRuntime.trans usdc_library_code⟩,
    reads.implementation.trans usdc_implementation⟩,
    address_separation.2.2.2.2.2.1⟩, address_separation.2.2.2.2.2.2⟩,
    usdc_rows_checked.1⟩, usdc_rows_checked.2.1⟩, usdc_rows_checked.2.2⟩,
    reads.initialized ▸ usdc_initialized⟩, reads.version ▸ usdc_version⟩

/-- Concrete finite truth; no checker acceptance premise is supplied. -/
theorem ObservedAt.checked {w : Jaune.State} (reads : ObservedAt w) :
    checkJointHybrid pair usdc weth usdcRows finiteModel w = true := by
  simp only [checkJointHybrid, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨reads.weth_checked, reads.usdc_checked⟩, token0_eq⟩,
    usdc_holder_checked reads.usdcBalance⟩, address_separation.2.1⟩,
    addresses_not_precompiles.2.1⟩, addresses_not_precompiles.1⟩

/-- The concrete finite proof assembles with actual same-world history.
The conclusion retains the historical model and both abstract key predicates. -/
theorem checkpoint_of_history {w : Jaune.State} {st : UniswapV2Pair.State}
    {KW : Weth9.Key → Prop} {KP : WriterKey → Prop}
    (reads : ObservedAt w) (pairRep : WriterRep KP (w.getStor pair) st)
    (wethFoot : Weth9.FootInv KW (w.getStor weth) (w.bal weth))
    (sumNof : SumNof w.bal) (tracked : KW (.bal pair))
    (noAllowance : ∀ g, KW (.allow pair g) →
      (w.getStor weth).get (Weth9.allowSlot pair g) = 0) :
    JointCheckpoint2F pair usdc weth (FiniteCheckpoint.rowKeys usdcRows) KW KP st w := by
  apply checkJointHybrid_sound pairRep wethFoot sumNof tracked noAllowance
  rw [reads.pairWords.check_model pairRep.fixed]
  exact reads.checked

/-- Factory identity follows at the original historical model's factory address. -/
theorem factory_checked_of_history {w : Jaune.State} {st : UniswapV2Pair.State}
    {KP : WriterKey → Prop} (reads : ObservedAt w)
    (pairRep : WriterRep KP (w.getStor pair) st) : checkFactory st.factory w = true := by
  have hfactory : st.factory = finiteModel.factory :=
    pairRep.fixed.2.2.1.symm.trans reads.pairWords.fixedMatches.2.2.1
  rw [checkFactory, decide_eq_true_eq, hfactory]
  exact reads.factoryRuntime.trans factory_code

/-- The future composition's factory premises follow from the same finite
reads and historical Pair model; neither is an extra observation. -/
theorem ObservedAt.factory_facts {w : Jaune.State} {st : UniswapV2Pair.State}
    {KP : WriterKey → Prop} (reads : ObservedAt w)
    (pairRep : WriterRep KP (w.getStor pair) st) :
    some (w.getCode st.factory).toList = UniswapV2Factory.factorySem.image ∧
      st.factory ≠ systemAddress := by
  refine ⟨checkFactory_sound (factory_checked_of_history reads pairRep), ?_⟩
  have same : st.factory = finiteModel.factory :=
    pairRep.fixed.2.2.1.symm.trans reads.pairWords.fixedMatches.2.2.1
  rw [same]
  decide +kernel

end Blanc.Composition.LiveUsdcWeth9B26213219
