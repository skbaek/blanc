import Blanc.Composition.PairTokenJoint
import Blanc.Lift.Token.Signed

/-!
# C4: the generic C3 headlines for the signature variant

`pair_token_joint_signed` / `pair_token_noShrinkSide_signed`: the writer-shadowed C3 headlines
(`pair_token_joint_w`, `pair_token_noShrinkSide_w`) for a token whose book admits the holder's own
signature as a third authorizer (`BookLawsS`), under the trace-local facet that the Pair never
signs a booked entry (`NeverSigner`).  The holder-indexed laws come from bridge 2
(`BookLawsS.holderLaws`).  Contract-neutral.
-/

namespace Blanc.Composition.PairTokenSigned

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint

/-- **C4 generic C3 for the signature variant** (`Blanc/Composition/PairTokenSigned.lean`):
`pair_token_joint_w` from `BookLawsS` and `NeverSigner` for the Pair. -/
theorem pair_token_joint_signed {pair T : Adr} {S : BookS} (C : CoreW T S.toBook)
    (lawsS : BookLawsS S) (abi : Erc20Abi S.toBook) (self : SelfCallerW C) (side : TokenSide)
    {cfg : ChainConfig} {checkpoint future : BlockChain} {K₀ : WriterKey → Prop}
    {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (never : NeverSigner T S trace pair)
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
    (∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      trace.settledFrames = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = pair ∧ A.sevm.isStatic = false)) →
      ¬ C.Shadowed trace f →
      ∃ (st : UniswapV2Pair.State) (K : WriterKey → Prop),
        WriterRep K (f.pre.state.getStor pair) st ∧ st.unlocked = 1 ∧ st.tokenOn side = T ∧
          JointAtW C trace pair side st f.pre.state) ∧
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
        JointAtW C trace pair side finish future.state :=
  pair_token_joint_w C abi self side trace (lawsS.holderLaws T never) installed initial fresh hist
    token unlocked apart answerable distinct notSystem factoryQuiet tokenEntered start

/-- **C4 generic NoShrink side for the signature variant.** -/
theorem pair_token_noShrinkSide_signed {pair T : Adr} {S : BookS} (C : CoreW T S.toBook)
    (lawsS : BookLawsS S) (abi : Erc20Abi S.toBook) (self : SelfCallerW C) (side : TokenSide)
    {cfg : ChainConfig} {checkpoint future : BlockChain} {K₀ : WriterKey → Prop}
    {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (never : NeverSigner T S trace pair)
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
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop) (steps : List PairStep),
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      PairObservedReplayWith PairAdmittedConsumes st₀ steps finish ∧
      runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
      WriterRep K' (future.state.getStor pair) finish ∧
      sourceReplayNoShrinkSide side st₀ (steps.map PairStep.source) :=
  pair_token_noShrinkSide_w C abi self side trace (lawsS.holderLaws T never) installed initial
    fresh hist token unlocked apart answerable distinct notSystem factoryQuiet tokenEntered start

end Blanc.Composition.PairTokenSigned
