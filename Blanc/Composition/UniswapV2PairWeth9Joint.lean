import Blanc.Composition.PairTokenJoint
import Blanc.Composition.UniswapV2PairWeth9CheckpointCore
import Blanc.Composition.UniswapV2FactoryQuiet
import Blanc.ExecutionSettledOwnCode
import Blanc.LockExclusion
import Blanc.Lift.Weth9.Check
import Blanc.Lift.Weth9.LiveTx
import Blanc.Lift.Weth9.LiveWriters

/-!
# C3 for WETH9 (Appendix A §8 as amended)

The generic C3 headline `pair_token_joint` instantiated at the WETH9 core: `C := weth9Core`,
`laws := weth9Book_laws`, `self := weth9SelfCaller`; `hist`, `answerable` and the joint relation at
the checkpoint from `JointCheckpoint.toCore`; `distinct`, `notSystem` from `JointCheckpoint`;
`factoryQuiet` (H1) from the factory lift (`pair_history_factoryQuiet`, amendments A4/A14);
`tokenEntered` from WETH9's installed code persisting at every settled frame
(`settled_ownCode`) and along each frame's same-frame prefix (`ParentPrefix.codePreserve`), and
WETH9 not a precompile (`JointCheckpoint.wethNotPrecompile`).

The ERC-20 ABI facet (as amended by A15: representable calldata only) holds for WETH9's book
(`weth9Book_erc20Abi`): WETH9's dispatcher reads both standard selectors exactly so.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.Token
  Blanc.Lift.UniswapV2Pair Blanc.Composition.Weth9Token Blanc.Composition.PairTokenJoint

/-! ## The ERC-20 ABI facet for WETH9 -/

/-- **WETH9's book reads the standard selectors as the standard operations** (A15 form). -/
theorem weth9Book_erc20Abi : Erc20Abi weth9Book where
  transfer a long fits selector := by
    have short := not_shortCall (Nat.le_trans (by decide) long) fits
    rw [show weth9Book.op = weth9Op from rfl]
    unfold weth9Op decodeCall
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => absurd (selector.symm.trans h.2)
        (by decide)), ite_eq_right_of_eq_false _ _ (eq_false short), selector,
      ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
      ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  balanceOf a long fits selector := by
    have short := not_shortCall (Nat.le_trans (by decide) long) fits
    rw [show weth9Book.op = weth9Op from rfl]
    unfold weth9Op
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨short, selector⟩)]

/-! ## WETH9's code at every node of a settled frame -/

/-- WETH9's runtime spawns only by `CALL`, `STATICCALL` (and never `CREATE*` but `CREATE2`). -/
theorem weth9_ownSpawns (ca : Adr) : OwnSpawns ca Weth9.code := fun hpc hcode _ fork chain hat =>
  let ⟨_, _, ok⟩ := cursor_of_parentPrefix Weth9.cert_check hpc hcode fork chain
  ok.exec_spawn hat

/-- At every node of every settled frame, WETH9's installed code is no delegation designator and
WETH9 is not a precompile of the frame's rules. -/
theorem weth9_tokenEntered {pair weth : Adr} {K₀ : Key → Prop} {KP : WriterKey → Prop}
    {st₀ : UniswapV2Pair.State} {side : TokenSide} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint pair weth K₀ KP st₀ side checkpoint.state) :
    ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair → G.sevm.isStatic = false →
      ∀ {node : Exec.Deriv}, Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv G) node →
        getDelegatedCodeAddress (node.devm.getCode weth) = none ∧
          ¬ node.sevm.benvStat.rules.isPrecomp weth := by
  intro G member _ _ node chain
  have nonempty : Weth9.code.toList ≠ [] := weth9Sem.ne_nil rfl
  obtain ⟨atEntry, -, fork, -⟩ := trace.settled_ownCode nonempty (weth9Sem.not_delegation rfl)
    (weth9_ownSpawns weth) (code_eq_of_image joint.wethCode) G member
  have entryCode : (Blanc.Exec.Frame.rootDeriv G).devm.getCode weth = Weth9.code := atEntry
  have atNode := Blanc.Exec.Deriv.ParentPrefix.codePreserve chain weth (by rw [entryCode]; exact nonempty)
  refine ⟨by rw [atNode, entryCode]; exact Weth9.getDelegatedCodeAddress_code, ?_⟩
  rw [Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain]
  exact joint.wethNotPrecompile _ fork

/-! ## C3 for WETH9 -/

/-- C3 for WETH9 over any ERC-20 ABI facet of its book (the body of `pair_weth9_joint`). -/
theorem pair_weth9_joint_of_abi (abi : Erc20Abi weth9Book) {pair weth : Adr} (side : TokenSide)
    {cfg : ChainConfig} {checkpoint future : BlockChain} {K₀ : Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint pair weth K₀ KP st₀ side checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (wethFresh : KeysFresh K₀ (historyTouchedKeys weth trace))
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress) :
    (∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      trace.settledFrames = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = pair ∧ A.sevm.isStatic = false)) →
      ∃ (st : UniswapV2Pair.State) (K : WriterKey → Prop),
        WriterRep K (f.pre.state.getStor pair) st ∧ st.unlocked = 1 ∧ st.tokenOn side = weth ∧
          st.reserveOn side ≤
            ((ledger (historyKeyUniverse weth trace K₀) (f.pre.state.getStor weth)).bal pair).toNat ∧
          ∀ g, (ledger (historyKeyUniverse weth trace K₀) (f.pre.state.getStor weth)).allow pair g = 0) ∧
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace KP st₀ finish K' ∧
        finish.reserveOn side ≤ ((future.state.getStor weth).get (balSlot pair)).toNat ∧
        ∀ g, historyKeyUniverse weth trace K₀ (.allow pair g) →
          (future.state.getStor weth).get (allowSlot pair g) = 0 := by
  obtain ⟨hist, answerable, start⟩ := JointCheckpoint.toCore trace joint wethFresh
  have factoryQuiet := UniswapV2FactoryQuiet.pair_history_factoryQuiet trace joint.pairCode
    factoryInstalled joint.pairNonzero factoryNotSystem
  obtain ⟨positions, finish, K', replayed, reserve, zero⟩ := pair_token_joint (weth9Core weth K₀)
    weth9Book_laws abi (weth9SelfCaller weth K₀) side trace joint.pairCode joint.pairRep pairFresh
    hist joint.token joint.unlocked joint.apart answerable joint.distinct joint.notSystem
    factoryQuiet (weth9_tokenEntered trace joint) start
  have word : ∀ x : B256, x.toNat = 0 → x = 0 := fun x h => B256.toNat_inj x 0 (by rw [h]; decide)
  refine ⟨fun before f after split noOpaque => ?_, finish, K', replayed, ?_, ?_⟩
  · obtain ⟨st, K, rep, opened, tokenOn, reserveAt, zeroAt⟩ :=
      positions before f after split noOpaque
    exact ⟨st, K, rep, opened, tokenOn, reserveAt, fun g => word _ (zeroAt g)⟩
  · have trackedPair : historyKeyUniverse weth trace K₀ (.bal pair) := Or.inl joint.tracked
    change finish.reserveOn side ≤
      (tracked (historyKeyUniverse weth trace K₀) (future.state.getStor weth) pair).toNat at reserve
    rwa [tracked_self trackedPair] at reserve
  · intro g row
    have zeroG := word _ (zero g)
    change trackedAllow (historyKeyUniverse weth trace K₀) (future.state.getStor weth) pair g = 0
      at zeroG
    rwa [trackedAllow_self row] at zeroG
/-- **C3 for WETH9** (Appendix A §8 as amended by A4/A10/A11/A14): from the joint checkpoint, both
HASH-T premises and the factory premises, at every settled frame outside the Pair's own frames the
Pair is unlocked with WETH9 on `side`, its reserve is at most WETH9's booked balance of the Pair and
the Pair has granted no booked allowance; at the history's end, over the Pair's full replay, the
reserve is at most the Pair's stored WETH9 balance word and every tracked allowance row is zero. -/
theorem pair_weth9_joint {pair weth : Adr} (side : TokenSide)
    {cfg : ChainConfig} {checkpoint future : BlockChain} {K₀ : Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint pair weth K₀ KP st₀ side checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (wethFresh : KeysFresh K₀ (historyTouchedKeys weth trace))
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress) :
    (∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      trace.settledFrames = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = pair ∧ A.sevm.isStatic = false)) →
      ∃ (st : UniswapV2Pair.State) (K : WriterKey → Prop),
        WriterRep K (f.pre.state.getStor pair) st ∧ st.unlocked = 1 ∧ st.tokenOn side = weth ∧
          st.reserveOn side ≤
            ((ledger (historyKeyUniverse weth trace K₀) (f.pre.state.getStor weth)).bal pair).toNat ∧
          ∀ g, (ledger (historyKeyUniverse weth trace K₀) (f.pre.state.getStor weth)).allow pair g = 0) ∧
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace KP st₀ finish K' ∧
        finish.reserveOn side ≤ ((future.state.getStor weth).get (balSlot pair)).toNat ∧
        ∀ g, historyKeyUniverse weth trace K₀ (.allow pair g) →
          (future.state.getStor weth).get (allowSlot pair g) = 0 :=
  pair_weth9_joint_of_abi weth9Book_erc20Abi side trace joint pairFresh wethFresh factoryInstalled
    factoryNotSystem

end Blanc.Composition.UniswapV2PairWeth9Joint
