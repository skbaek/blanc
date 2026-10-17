import Blanc.Composition.PairTokenJoint

/-!
# C6(a)/(b) generic: two token cores on one Pair

`pair_two_token_joint` (Appendix A §10): a Pair whose `token0` is `T0` and `token1` is `T1`, each a
writer-shadowed core (`CoreW`) with holder laws for the Pair.  The generic walk
(`pair_token_walk`) runs once per core over the **same** Pair steps: at a position, the replay of the
steps before it (`pair_history_stateAt_auth`); at the end, the history's full replay
(`pair_history_replayed`).  One Pair witness thus carries both joint relations, and the two
per-side halves of the walk combine through `sourceReplayNoShrink_iff_sides` into the whole
`sourceReplayNoShrink`, with no token antecedent.

`sourceReplayFeeOff` is the factory's fee-off answer along a replay, the one antecedent the fee-off
share-value row (`PairTwoTokenShareValue.lean`) keeps.
-/

namespace Blanc.Composition.PairTwoToken

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint

/-- Every step of a replay is fee-off (the factory's `feeTo` answers zero): the one antecedent the
fee-off share-value row keeps (a factory fact, no token answer). -/
def sourceReplayFeeOff : UniswapV2Pair.State → List SourceInvocation → Prop
  | _, [] => True
  | st, inv :: rest => EntryFeeOff inv.entry inv.transcript ∧
      sourceReplayFeeOff (inv.run st).frame.current.state rest

/-- **C6(a)/(b) generic, two cores.**  For a Pair whose `token0` is `T0` and `token1` is `T1`, each
an instance of the writer-shadowed core with holder laws for the Pair: at every settled frame
outside the Pair's non-static frames and unshadowed in both cores, the Pair is unlocked with both
joint relations; both hold at the end; and every outer Pair step satisfies the full `EntryNoShrink`
(no token antecedent). -/
theorem pair_two_token_joint {pair T0 T1 : Adr} {B0 B1 : Book} (C0 : CoreW T0 B0) (C1 : CoreW T1 B1)
    (abi0 : Erc20Abi B0) (abi1 : Erc20Abi B1) (self0 : SelfCallerW C0) (self1 : SelfCallerW C1)
    {cfg : ChainConfig} {checkpoint future : BlockChain} {K₀ : WriterKey → Prop}
    {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (laws0 : HolderLaws T0 B0 trace pair) (laws1 : HolderLaws T1 B1 trace pair)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (hist0 : C0.Hist trace) (hist1 : C1.Hist trace)
    (token0 : st₀.token0 = T0) (token1 : st₀.token1 = T1) (unlocked : st₀.unlocked = 1)
    (apart0 : pair ≠ T0) (apart1 : pair ≠ T1)
    (answerable0 : C0.Answerable trace pair) (answerable1 : C1.Answerable trace pair)
    (distinct : st₀.token0 ≠ st₀.token1) (notSystem : pair ≠ systemAddress)
    (factoryQuiet : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → G.sevm.caller ≠ st₀.factory)
    (tokenEntered0 : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → ∀ {node : Exec.Deriv},
        Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv G) node →
          getDelegatedCodeAddress (node.devm.getCode T0) = none ∧
            ¬ node.sevm.benvStat.rules.isPrecomp T0)
    (tokenEntered1 : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → ∀ {node : Exec.Deriv},
        Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv G) node →
          getDelegatedCodeAddress (node.devm.getCode T1) = none ∧
            ¬ node.sevm.benvStat.rules.isPrecomp T1)
    (start0 : JointAtW C0 trace pair .zero st₀ checkpoint.state)
    (start1 : JointAtW C1 trace pair .one st₀ checkpoint.state) :
    (∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      trace.settledFrames = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = pair ∧ A.sevm.isStatic = false)) →
      ¬ C0.Shadowed trace f → ¬ C1.Shadowed trace f →
      ∃ (st : UniswapV2Pair.State) (K : WriterKey → Prop),
        WriterRep K (f.pre.state.getStor pair) st ∧ st.unlocked = 1 ∧ st.token0 = T0 ∧
          st.token1 = T1 ∧ JointAtW C0 trace pair .zero st f.pre.state ∧
          JointAtW C1 trace pair .one st f.pre.state) ∧
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop) (steps : List PairStep),
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      PairObservedReplayWith PairAdmittedConsumes st₀ steps finish ∧
      runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
      WriterRep K' (future.state.getStor pair) finish ∧
      JointAtW C0 trace pair .zero finish future.state ∧
      JointAtW C1 trace pair .one finish future.state ∧
      sourceReplayNoShrink st₀ (steps.map PairStep.source) := by
  have walk0 := pair_token_walk C0 abi0 self0 .zero trace laws0 installed initial fresh hist0 token0
    unlocked apart0 answerable0 distinct notSystem factoryQuiet tokenEntered0
  have walk1 := pair_token_walk C1 abi1 self1 .one trace laws1 installed initial fresh hist1 token1
    unlocked apart1 answerable1 distinct notSystem factoryQuiet tokenEntered1
  refine ⟨fun before f after split noOpaque lit0 lit1 => ?_, ?_⟩
  · -- one Pair witness (the replay of the steps before `f`) for both sides
    obtain ⟨steps, st, K, observed, auth, replay, rep⟩ :=
      pair_history_stateAt_auth trace installed initial fresh before f after split noOpaque
    have closed := before_pairClosed trace split noOpaque
    obtain ⟨l0, run0, reserve0, zero0, tokens, opened, -⟩ := walk0 steps replay auth observed
      (pre := []) (post := f :: after) split (PairClosed.nil pair) closed ⟨rfl, rfl, rfl⟩
      unlocked rfl start0.1 start0.2
    obtain ⟨l1, run1, reserve1, zero1, -⟩ := walk1 steps replay auth observed
      (pre := []) (post := f :: after) split (PairClosed.nil pair) closed ⟨rfl, rfl, rfl⟩
      unlocked rfl start1.1 start1.2
    rw [List.nil_append, C0.replayAt trace hist0 before f after split lit0] at run0
    rw [List.nil_append, C1.replayAt trace hist1 before f after split lit1] at run1
    cases run0
    cases run1
    exact ⟨st, K, rep, opened, tokens.1.trans token0, tokens.2.1.trans token1,
      ⟨reserve0, zero0⟩, ⟨reserve1, zero1⟩⟩
  · -- the history's full replay, walked once per core
    obtain ⟨-, finish, K', steps, observed, auth, replay, realized, -, -, rep⟩ :=
      pair_history_replayed trace installed initial fresh
    have whole : trace.settledFrames = [] ++ trace.settledFrames ++ [] := by
      rw [List.nil_append, List.append_nil]
    obtain ⟨l0, run0, reserve0, zero0, -, -, side0⟩ := walk0 steps replay auth observed
      (pre := []) (post := []) whole (PairClosed.nil pair) (settledFrames_pairClosed trace)
      ⟨rfl, rfl, rfl⟩ unlocked rfl start0.1 start0.2
    obtain ⟨l1, run1, reserve1, zero1, -, -, side1⟩ := walk1 steps replay auth observed
      (pre := []) (post := []) whole (PairClosed.nil pair) (settledFrames_pairClosed trace)
      ⟨rfl, rfl, rfl⟩ unlocked rfl start1.1 start1.2
    rw [List.nil_append, C0.replayEnd trace hist0] at run0
    rw [List.nil_append, C1.replayEnd trace hist1] at run1
    cases run0
    cases run1
    exact ⟨finish, K', steps, observed, auth, replay, realized, rep, ⟨reserve0, zero0⟩,
      ⟨reserve1, zero1⟩, sourceReplayNoShrink_iff_sides.mpr ⟨side0, side1⟩⟩

end Blanc.Composition.PairTwoToken
