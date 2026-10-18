import Blanc.Composition.PairTwoToken
import Blanc.Composition.UniswapV2PairUsdcWeth9CheckpointF
import Blanc.Composition.UniswapV2PairWeth9Joint
import Blanc.Composition.UsdcTokenF
import Blanc.MachineDataFacts

/-!
# C6(a) for the USDC/WETH9 Pair over the support-free checkpoint

Twin of `UniswapV2PairUsdcWeth9Joint.lean`: `pair_usdc_weth9_joint_finite` is
`pair_usdc_weth9_joint` with `joint : JointCheckpoint2F …` and the added quiet premise
`PairUsdcAllowQuiet` right after `governance`.  The USDC side's `hist`, `answerable`,
joint relation and holder laws come from `JointCheckpoint2F.toUsdcCoreF`; everything
else is discharged exactly as the original discharges it.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken Blanc.Composition.PairTwoToken Blanc.Composition.Weth9Token

/-- At every node of every settled frame, USDC's installed proxy runtime is no delegation
designator and USDC is not a precompile of the frame's rules (from the support-free
checkpoint). -/
theorem usdc_tokenEntered {pair usdc weth : Adr} {KU : Usdc.Key → Prop} {KW : Weth9.Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint2F pair usdc weth KU KW KP st₀ checkpoint.state)
    (hist : Usdc.UsdcHistF usdc KU trace) :
    ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair → G.sevm.isStatic = false →
      ∀ {node : Exec.Deriv}, Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv G) node →
        getDelegatedCodeAddress (node.devm.getCode usdc) = none ∧
          ¬ node.sevm.benvStat.rules.isPrecomp usdc := by
  intro G member _ _ node chain
  have nonempty : Usdc.Proxy.code.toList ≠ [] := Usdc.proxySem.ne_nil rfl
  have entryCode : (Blanc.Exec.Frame.rootDeriv G).devm.getCode usdc = Usdc.Proxy.code :=
    bytes_eq_of_image (trace.settled_codeImage Usdc.proxySem usdc joint.usdcInstalled.proxy G member)
  have atNode := Blanc.Exec.Deriv.ParentPrefix.codePreserve chain usdc
    (by rw [entryCode]; exact nonempty)
  refine ⟨by rw [atNode, entryCode]; exact Usdc.proxy_undelegated, ?_⟩
  rw [Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain]
  exact joint.usdcNotPrecompile _ (Usdc.usdc_settled_factsF trace hist G member).fork

/-- **C6(a), the exhibit composition, support-free**: `pair_usdc_weth9_joint` from the
support-free joint checkpoint, with the quiet allowance premise in place of support. -/
theorem pair_usdc_weth9_joint_finite {pair usdc weth : Adr}
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
    (∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      trace.settledFrames = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = pair ∧ A.sevm.isStatic = false)) →
      ¬ Usdc.UsdcShadowed usdc trace before f →
      ∃ (st : UniswapV2Pair.State) (K : WriterKey → Prop),
        WriterRep K (f.pre.state.getStor pair) st ∧ st.unlocked = 1 ∧ st.token0 = usdc ∧
          st.token1 = weth ∧
          st.reserve0.val ≤
            (Usdc.ledger (Usdc.historyKeyUniverse usdc trace KU) (f.pre.state.getStor usdc)).bal pair ∧
          (∀ g, (Usdc.ledger (Usdc.historyKeyUniverse usdc trace KU)
            (f.pre.state.getStor usdc)).allow pair g = 0) ∧
          st.reserve1.val ≤
            ((Weth9.ledger (Weth9.historyKeyUniverse weth trace KW) (f.pre.state.getStor weth)).bal
              pair).toNat ∧
          ∀ g, (Weth9.ledger (Weth9.historyKeyUniverse weth trace KW)
            (f.pre.state.getStor weth)).allow pair g = 0) ∧
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace KP st₀ finish K' ∧
        finish.reserve0.val ≤ Usdc.balanceBits ((future.state.getStor usdc).get (Usdc.balSlot pair)) ∧
        (∀ g, Usdc.historyKeyUniverse usdc trace KU (.allow pair g) →
          (future.state.getStor usdc).get (Usdc.allowSlot pair g) = 0) ∧
        finish.reserve1.val ≤ ((future.state.getStor weth).get (Weth9.balSlot pair)).toNat ∧
        ∀ g, Weth9.historyKeyUniverse weth trace KW (.allow pair g) →
          (future.state.getStor weth).get (Weth9.allowSlot pair g) = 0 := by
  obtain ⟨hist0, answerable0, start0, laws0⟩ :=
    JointCheckpoint2F.toUsdcCoreF trace joint governance quiet usdcFresh
  obtain ⟨hist1, answerable1, start1⟩ := JointCheckpoint.toCore trace joint.weth9 wethFresh
  obtain ⟨positions, finish, K₁, -, -, -, -, -, rep, ⟨res0, zero0⟩, ⟨res1, zero1⟩, -⟩ :=
    pair_two_token_joint (usdcCoreF usdc KU) (weth9Core weth KW).weak (usdcBook_erc20Abi usdc)
      weth9Book_erc20Abi (usdcSelfCallerF usdc KU) (weth9SelfCaller weth KW).weak trace laws0
      (weth9Book_laws.holderLaws weth trace pair) joint.weth9.pairCode joint.weth9.pairRep
      pairFresh hist0 hist1 joint.token0 joint.weth9.token joint.weth9.unlocked joint.apart
      joint.weth9.apart answerable0 answerable1 joint.weth9.distinct joint.weth9.notSystem
      (UniswapV2FactoryQuiet.pair_history_factoryQuiet trace joint.weth9.pairCode factoryInstalled
        joint.weth9.pairNonzero factoryNotSystem)
      (usdc_tokenEntered trace joint hist0) (weth9_tokenEntered trace joint.weth9) start0 start1
  obtain ⟨-, finish', K', replayed⟩ :=
    pair_history_replayed trace joint.weth9.pairCode joint.weth9.pairRep pairFresh
  obtain ⟨-, -, -, -, -, -, -, rep'⟩ := id replayed
  obtain ⟨r0, r1⟩ := WriterFixedMatches.reserves_eq rep'.fixed rep.fixed
  refine ⟨fun before f after split noOpaque lit => ?_, finish', K', replayed, ?_, ?_, ?_, ?_⟩
  · obtain ⟨st, K, rep, opened, token0, token1, ⟨reserveAt0, zeroAt0⟩, ⟨reserveAt1, zeroAt1⟩⟩ :=
      positions before f after split noOpaque lit id
    exact ⟨st, K, rep, opened, token0, token1, reserveAt0, zeroAt0, reserveAt1,
      fun g => B256.eq_zero_of_toNat (zeroAt1 g)⟩
  · change finish.reserve0.val ≤
      (Usdc.ledger (Usdc.historyKeyUniverse usdc trace KU) (future.state.getStor usdc)).bal pair
      at res0
    rwa [Usdc.ledger_bal (Or.inl joint.tracked), ← r0] at res0
  · intro g row
    have zeroG : (Usdc.ledger (Usdc.historyKeyUniverse usdc trace KU)
      (future.state.getStor usdc)).allow pair g = 0 := zero0 g
    rw [Usdc.ledger_allow row] at zeroG
    exact B256.eq_zero_of_toNat zeroG
  · change finish.reserve1.val ≤ (Weth9.tracked (Weth9.historyKeyUniverse weth trace KW)
      (future.state.getStor weth) pair).toNat at res1
    rwa [Weth9.tracked_self (Or.inl joint.weth9.tracked), ← r1] at res1
  · intro g row
    have zeroG := B256.eq_zero_of_toNat (zero1 g)
    change Weth9.trackedAllow (Weth9.historyKeyUniverse weth trace KW) (future.state.getStor weth)
      pair g = 0 at zeroG
    rwa [Weth9.trackedAllow_self row] at zeroG

end Blanc.Composition.UniswapV2PairUsdcWeth9
