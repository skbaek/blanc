import Blanc.Composition.PairTwoToken

/-!
# C6(b) generic: share value with no token antecedent

`pair_two_token_feeOn_product` / `pair_two_token_feeOff_product` (Appendix A §10): the share-value
rows of `pair_history_feeOn_product` / `…feeOff…` over a Pair whose two tokens are writer-shadowed
cores with holder laws for the Pair.  Both token halves of `EntryNoShrink` are theorems
(`pair_two_token_joint`); the fee-on row keeps no antecedent, the fee-off row keeps only the
factory's fee-off answer `sourceReplayFeeOff`.
-/

namespace Blanc.Composition.PairTwoToken

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint

/-- The fee-off answer and the whole backing condition along a replay are its answer conditions. -/
private theorem sourceReplayAnswers_of_feeOff {st : UniswapV2Pair.State} {invs : List SourceInvocation}
    (feeOff : sourceReplayFeeOff st invs) (noShrink : sourceReplayNoShrink st invs) :
    sourceReplayAnswers st invs := by
  induction invs generalizing st with
  | nil => trivial
  | cons inv rest ih => exact ⟨feeOff.1, noShrink.1, ih feeOff.2 noShrink.2⟩

/-- **C6(b) generic, fee on: share value with no token antecedent.**  Hypotheses of
`pair_two_token_joint`. -/
theorem pair_two_token_feeOn_product {pair T0 T1 : Adr} {B0 B1 : Book} (C0 : CoreW T0 B0)
    (C1 : CoreW T1 B1) (abi0 : Erc20Abi B0) (abi1 : Erc20Abi B1) (self0 : SelfCallerW C0)
    (self1 : SelfCallerW C1) {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
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
  obtain ⟨-, finish, K', steps, observed, auth, replay, realized, rep, -, -, noShrink⟩ :=
    pair_two_token_joint C0 C1 abi0 abi1 self0 self1 trace laws0 laws1 installed initial fresh
      hist0 hist1 token0 token1 unlocked apart0 apart1 answerable0 answerable1 distinct notSystem
      factoryQuiet tokenEntered0 tokenEntered1 start0 start1
  have source := replay.sourceReplay fun _ _ _ _ consumed => consumed.positional.forget
  exact ⟨steps, observed, auth, finish, K', replay, realized, rep, source.feeOn_product noShrink⟩


/-- **C6(b) generic, fee off**: the only antecedent is the factory's fee-off answer. -/
theorem pair_two_token_feeOff_product {pair T0 T1 : Adr} {B0 B1 : Book} (C0 : CoreW T0 B0)
    (C1 : CoreW T1 B1) (abi0 : Erc20Abi B0) (abi1 : Erc20Abi B1) (self0 : SelfCallerW C0)
    (self1 : SelfCallerW C1) {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
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
  obtain ⟨-, finish, K', steps, observed, auth, replay, realized, rep, -, -, noShrink⟩ :=
    pair_two_token_joint C0 C1 abi0 abi1 self0 self1 trace laws0 laws1 installed initial fresh
      hist0 hist1 token0 token1 unlocked apart0 apart1 answerable0 answerable1 distinct notSystem
      factoryQuiet tokenEntered0 tokenEntered1 start0 start1
  have source := replay.sourceReplay fun _ _ _ _ consumed => consumed.positional.forget
  exact ⟨steps, observed, auth, finish, K', replay, realized, rep,
    fun feeOff => source.feeOff_product (sourceReplayAnswers_of_feeOff feeOff noShrink)⟩

end Blanc.Composition.PairTwoToken
