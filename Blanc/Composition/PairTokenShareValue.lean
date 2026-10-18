import Blanc.Composition.PairTokenJoint

/-!
# C4(a): share value with one token's half discharged (generic token side)

`pair_token_feeOff_product` / `pair_token_feeOn_product` (Appendix A §8, with the C3 hypotheses of
A8/A11): the share-value rows of `pair_history_feeOff_product_with` / `…feeOn…` over the Pair's
history, where the per-side answer premise on `side` is a theorem rather than a hypothesis.  Only
the other side's half (`sourceReplayAnswersSide side.other` / `sourceReplayNoShrinkSide side.other`)
stays a premise.

The `_w` rows state them over the writer-shadowed core (`CoreW`, `HolderLaws`, `SelfCallerW`,
Route R); the `Core` rows are those at `C.weak`, `laws.holderLaws`, `self.weak`.

Proof: C3's `pair_token_noShrinkSide_w` supplies the `side` half over the history's own steps;
`sourceReplayAnswers_of_sides` / `sourceReplayNoShrink_iff_sides` combine the halves; the source
replay's product laws (`SourceReplay.feeOff_product` / `SourceReplay.feeOn_product`) close it.
-/

namespace Blanc.Composition.PairTokenShareValue

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint

/-- **C4(a), fee off, generic token side, over the writer-shadowed core** (Route R).  The
share-value row of `pair_history_feeOff_product`
with the `side` half of the per-side premise removed: only the other side's half (and the
fee-recipient answer) stays. -/
theorem pair_token_feeOff_product_w {pair T : Adr} {B : Book} (C : CoreW T B)
    (abi : Erc20Abi B) (self : SelfCallerW C) (side : TokenSide) {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (laws : HolderLaws T B trace pair)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (hist : C.Hist trace) (token : st₀.tokenOn side = T) (unlocked : st₀.unlocked = 1)
    (apart : pair ≠ T) (answerable : C.Answerable trace pair)
    (distinct : st₀.token0 ≠ st₀.token1) (notSystem : pair ≠ systemAddress)
    (factoryQuiet : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → G.sevm.caller ≠ st₀.factory)
    (tokenEntered : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → ∀ {node : Exec.Deriv},
        Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv G) node →
          getDelegatedCodeAddress (node.devm.getCode T) = none ∧
            ¬ node.sevm.benvStat.rules.isPrecomp T)
    (start : JointAtW C trace pair side st₀ checkpoint.state) :
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
        PairObservedReplayWith PairAdmittedConsumes st₀ steps finish ∧
        runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        (sourceReplayAnswersSide side.other st₀ (steps.map PairStep.source) →
          ∀ before after, (before, after) ∈ sourceReplayEdges st₀ (steps.map PairStep.source) →
            0 < before.totalSupply.toNat →
            before.reserve0.val * before.reserve1.val * after.totalSupply.toNat ^ 2 ≤
              after.reserve0.val * after.reserve1.val * before.totalSupply.toNat ^ 2) := by
  obtain ⟨finish, K', steps, observed, auth, replay, realized, rep, mine⟩ :=
    pair_token_noShrinkSide_w C abi self side trace laws installed initial fresh hist token
      unlocked apart answerable distinct notSystem factoryQuiet tokenEntered start
  have source := replay.sourceReplay fun _ _ _ _ consumed => consumed.positional.forget
  exact ⟨steps, observed, auth, finish, K', replay, realized, rep,
    fun other => source.feeOff_product (sourceReplayAnswers_of_sides side mine other)⟩

/-- **C4(a), fee on, generic token side, over the writer-shadowed core** (Route R). -/
theorem pair_token_feeOn_product_w {pair T : Adr} {B : Book} (C : CoreW T B)
    (abi : Erc20Abi B) (self : SelfCallerW C) (side : TokenSide) {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (laws : HolderLaws T B trace pair)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (hist : C.Hist trace) (token : st₀.tokenOn side = T) (unlocked : st₀.unlocked = 1)
    (apart : pair ≠ T) (answerable : C.Answerable trace pair)
    (distinct : st₀.token0 ≠ st₀.token1) (notSystem : pair ≠ systemAddress)
    (factoryQuiet : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → G.sevm.caller ≠ st₀.factory)
    (tokenEntered : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → ∀ {node : Exec.Deriv},
        Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv G) node →
          getDelegatedCodeAddress (node.devm.getCode T) = none ∧
            ¬ node.sevm.benvStat.rules.isPrecomp T)
    (start : JointAtW C trace pair side st₀ checkpoint.state) :
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
        PairObservedReplayWith PairAdmittedConsumes st₀ steps finish ∧
        runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        (sourceReplayNoShrinkSide side.other st₀ (steps.map PairStep.source) →
          ∀ before inv after, (before, inv, after) ∈ sourceReplaySteps st₀ (steps.map PairStep.source) →
            0 < before.totalSupply.toNat →
            before.reserve0.val * before.reserve1.val * after.totalSupply.toNat ^ 2 ≤
              after.reserve0.val * after.reserve1.val *
                (before.totalSupply.toNat + entryFeeAmount before inv.entry inv.transcript) ^ 2) := by
  obtain ⟨finish, K', steps, observed, auth, replay, realized, rep, mine⟩ :=
    pair_token_noShrinkSide_w C abi self side trace laws installed initial fresh hist token
      unlocked apart answerable distinct notSystem factoryQuiet tokenEntered start
  have source := replay.sourceReplay fun _ _ _ _ consumed => consumed.positional.forget
  refine ⟨steps, observed, auth, finish, K', replay, realized, rep, fun other => ?_⟩
  refine source.feeOn_product (sourceReplayNoShrink_iff_sides.mpr ?_)
  cases side
  · exact ⟨mine, other⟩
  · exact ⟨other, mine⟩

/-- **C4(a), fee off, generic token side.**  The share-value row of `pair_history_feeOff_product`
with the `side` half of the per-side premise removed: only the other side's half (and the
fee-recipient answer) stays. -/
theorem pair_token_feeOff_product {pair T : Adr} {B : Book} (C : Core T B) (laws : BookLaws B)
    (abi : Erc20Abi B) (self : SelfCaller C) (side : TokenSide) {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (hist : C.Hist trace) (token : st₀.tokenOn side = T) (unlocked : st₀.unlocked = 1)
    (apart : pair ≠ T) (answerable : C.Answerable trace pair)
    (distinct : st₀.token0 ≠ st₀.token1) (notSystem : pair ≠ systemAddress)
    (factoryQuiet : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → G.sevm.caller ≠ st₀.factory)
    (tokenEntered : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → ∀ {node : Exec.Deriv},
        Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv G) node →
          getDelegatedCodeAddress (node.devm.getCode T) = none ∧
            ¬ node.sevm.benvStat.rules.isPrecomp T)
    (start : JointAt C trace pair side st₀ checkpoint.state) :
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
        PairObservedReplayWith PairAdmittedConsumes st₀ steps finish ∧
        runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        (sourceReplayAnswersSide side.other st₀ (steps.map PairStep.source) →
          ∀ before after, (before, after) ∈ sourceReplayEdges st₀ (steps.map PairStep.source) →
            0 < before.totalSupply.toNat →
            before.reserve0.val * before.reserve1.val * after.totalSupply.toNat ^ 2 ≤
              after.reserve0.val * after.reserve1.val * before.totalSupply.toNat ^ 2) :=
  pair_token_feeOff_product_w C.weak abi self.weak side trace (laws.holderLaws T trace pair)
    installed initial fresh hist token unlocked apart answerable distinct notSystem factoryQuiet
    tokenEntered start

/-- **C4(a), fee on, generic token side.** -/
theorem pair_token_feeOn_product {pair T : Adr} {B : Book} (C : Core T B) (laws : BookLaws B)
    (abi : Erc20Abi B) (self : SelfCaller C) (side : TokenSide) {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (hist : C.Hist trace) (token : st₀.tokenOn side = T) (unlocked : st₀.unlocked = 1)
    (apart : pair ≠ T) (answerable : C.Answerable trace pair)
    (distinct : st₀.token0 ≠ st₀.token1) (notSystem : pair ≠ systemAddress)
    (factoryQuiet : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → G.sevm.caller ≠ st₀.factory)
    (tokenEntered : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → ∀ {node : Exec.Deriv},
        Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv G) node →
          getDelegatedCodeAddress (node.devm.getCode T) = none ∧
            ¬ node.sevm.benvStat.rules.isPrecomp T)
    (start : JointAt C trace pair side st₀ checkpoint.state) :
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
        PairObservedReplayWith PairAdmittedConsumes st₀ steps finish ∧
        runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        (sourceReplayNoShrinkSide side.other st₀ (steps.map PairStep.source) →
          ∀ before inv after, (before, inv, after) ∈ sourceReplaySteps st₀ (steps.map PairStep.source) →
            0 < before.totalSupply.toNat →
            before.reserve0.val * before.reserve1.val * after.totalSupply.toNat ^ 2 ≤
              after.reserve0.val * after.reserve1.val *
                (before.totalSupply.toNat + entryFeeAmount before inv.entry inv.transcript) ^ 2) :=
  pair_token_feeOn_product_w C.weak abi self.weak side trace (laws.holderLaws T trace pair)
    installed initial fresh hist token unlocked apart answerable distinct notSystem factoryQuiet
    tokenEntered start

end Blanc.Composition.PairTokenShareValue
