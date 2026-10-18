import Blanc.Composition.PairTwoToken
import Blanc.Composition.UniswapV2PairUsdcWeth9Checkpoint
import Blanc.Composition.UniswapV2PairWeth9Joint

/-!
# C6(a) for the USDC/WETH9 Pair (Appendix A §10, U8b)

The generic two-core headline `pair_two_token_joint` instantiated at the exhibit: `C0 := usdcCore`
(USDC at `token0`), `C1 := (weth9Core weth KW).weak` (WETH9 at `token1`).  The USDC side's `hist`,
`answerable`, joint relation and holder laws come from `JointCheckpoint2.toUsdcCore` (under the
governance and never-signer premises); the WETH9 side's from the predecessor's
`JointCheckpoint.toCore` and `weth9Book_laws`; `factoryQuiet` from the factory lift; `tokenEntered`
for USDC from the proxy's code image persisting at every settled frame (`settled_codeImage`) and
along each frame's same-frame prefix (`ParentPrefix.codePreserve`), the proxy's runtime being no
delegation designator and USDC no precompile (`JointCheckpoint2.usdcNotPrecompile`); for WETH9 from
`weth9_tokenEntered`.

The generic `JointAtW` conclusions are read back as the concrete ledger forms at every position and
as the stored balance words and zero allowance rows at the end.  No hypothesis mentions either
token's answers.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken Blanc.Composition.PairTwoToken Blanc.Composition.Weth9Token

/-- At every node of every settled frame, USDC's installed proxy runtime is no delegation
designator and USDC is not a precompile of the frame's rules. -/
theorem usdc_tokenEntered {pair usdc weth : Adr} {KU : Usdc.Key → Prop} {KW : Weth9.Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint2 pair usdc weth KU KW KP st₀ checkpoint.state)
    (hist : Usdc.UsdcHist usdc KU trace) :
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
  exact joint.usdcNotPrecompile _ (Usdc.usdc_settled_facts trace hist G member).fork

/-- A WETH9 word whose value is zero is the zero word. -/
theorem word_eq_zero {x : B256} (h : x.toNat = 0) : x = 0 :=
  B256.toNat_inj x 0 (by rw [h]; decide)

/-- Two model states the Pair's storage represents agree on both reserves (the reserves are read
from the fixed word at slot `8`). -/
theorem reserves_eq_of_fixed {s : Stor} {st st' : UniswapV2Pair.State}
    (h : WriterFixedMatches s st) (h' : WriterFixedMatches s st') :
    st.reserve0.val = st'.reserve0.val ∧ st.reserve1.val = st'.reserve1.val := by
  have lt : ∀ r : Fin (2 ^ 112), r.val < 2 ^ 256 :=
    fun r => Nat.lt_trans r.isLt (Nat.pow_lt_pow_right (by decide) (by decide))
  refine ⟨?_, ?_⟩
  · have e := h.2.2.2.2.2.1.symm.trans h'.2.2.2.2.2.1
    rw [← B256.toNat_toB256_of_lt (lt st.reserve0), e, B256.toNat_toB256_of_lt (lt st'.reserve0)]
  · have e := h.2.2.2.2.2.2.1.symm.trans h'.2.2.2.2.2.2.1
    rw [← B256.toNat_toB256_of_lt (lt st.reserve1), e, B256.toNat_toB256_of_lt (lt st'.reserve1)]

/-- **C6(a), the exhibit composition**: every V2 pair whose `token0` is USDC and `token1` is WETH9,
from the two-token joint checkpoint, with HASH-T for the Pair, USDC and WETH9, USDC's governance
premise F2, the never-signer premise for the Pair and the factory premises.  At every settled frame
outside the Pair's non-static frames and outside USDC's writer frames, both joint relations hold; at
the end, over the Pair's full replay, both reserves are covered by the stored balance words and
every tracked allowance row of the Pair is zero.  No hypothesis mentions either token's answers. -/
theorem pair_usdc_weth9_joint {pair usdc weth : Adr}
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
    JointCheckpoint2.toUsdcCore trace joint governance neverSigner usdcFresh
  obtain ⟨hist1, answerable1, start1⟩ := JointCheckpoint.toCore trace joint.weth9 wethFresh
  obtain ⟨positions, finish, K₁, -, -, -, -, -, rep, ⟨res0, zero0⟩, ⟨res1, zero1⟩, -⟩ :=
    pair_two_token_joint (usdcCore usdc KU) (weth9Core weth KW).weak (usdcBook_erc20Abi usdc)
      weth9Book_erc20Abi (usdcSelfCaller usdc KU) (weth9SelfCaller weth KW).weak trace laws0
      (weth9Book_laws.holderLaws weth trace pair) joint.weth9.pairCode joint.weth9.pairRep
      pairFresh hist0 hist1 joint.token0 joint.weth9.token joint.weth9.unlocked joint.apart
      joint.weth9.apart answerable0 answerable1 joint.weth9.distinct joint.weth9.notSystem
      (UniswapV2FactoryQuiet.pair_history_factoryQuiet trace joint.weth9.pairCode factoryInstalled
        joint.weth9.pairNonzero factoryNotSystem)
      (usdc_tokenEntered trace joint hist0) (weth9_tokenEntered trace joint.weth9) start0 start1
  obtain ⟨-, finish', K', replayed⟩ :=
    pair_history_replayed trace joint.weth9.pairCode joint.weth9.pairRep pairFresh
  obtain ⟨-, -, -, -, -, -, -, rep'⟩ := id replayed
  obtain ⟨r0, r1⟩ := reserves_eq_of_fixed rep'.fixed rep.fixed
  refine ⟨fun before f after split noOpaque lit => ?_, finish', K', replayed, ?_, ?_, ?_, ?_⟩
  · obtain ⟨st, K, rep, opened, token0, token1, ⟨reserveAt0, zeroAt0⟩, ⟨reserveAt1, zeroAt1⟩⟩ :=
      positions before f after split noOpaque lit id
    exact ⟨st, K, rep, opened, token0, token1, reserveAt0, zeroAt0, reserveAt1,
      fun g => word_eq_zero (zeroAt1 g)⟩
  · change finish.reserve0.val ≤
      (Usdc.ledger (Usdc.historyKeyUniverse usdc trace KU) (future.state.getStor usdc)).bal pair
      at res0
    rwa [Usdc.ledger_bal (Or.inl joint.tracked), ← r0] at res0
  · intro g row
    have zeroG : (Usdc.ledger (Usdc.historyKeyUniverse usdc trace KU)
      (future.state.getStor usdc)).allow pair g = 0 := zero0 g
    rw [Usdc.ledger_allow row] at zeroG
    exact word_eq_zero zeroG
  · change finish.reserve1.val ≤ (Weth9.tracked (Weth9.historyKeyUniverse weth trace KW)
      (future.state.getStor weth) pair).toNat at res1
    rwa [Weth9.tracked_self (Or.inl joint.weth9.tracked), ← r1] at res1
  · intro g row
    have zeroG := word_eq_zero (zero1 g)
    change Weth9.trackedAllow (Weth9.historyKeyUniverse weth trace KW) (future.state.getStor weth)
      pair g = 0 at zeroG
    rwa [Weth9.trackedAllow_self row] at zeroG

end Blanc.Composition.UniswapV2PairUsdcWeth9
