import Blanc.Composition.PairTokenJointWalk

/-!
# C3: the joint invariant of the Pair and a token core (headlines)

`pair_token_joint` (Appendix A §6b as amended by A3/A8, with A11's `tokenEntered`): over any
configured history from a checkpoint where the Pair's code is installed over a model state whose
token on `side` is `T` and the joint relation holds, at the entry of every settled frame outside the
Pair's own non-static frames the Pair's storage represents an unlocked model state with that token
and the joint relation holds there; it holds at the history's end with the Pair's full replay.

`pair_token_noShrinkSide`: every outer Pair step of the history satisfies the token half of
`EntryNoShrink` on `side` (`sourceReplayNoShrinkSide`).

Both are the positional walk (`pair_token_walk`) over the Pair's observed replay: at a position, the
replay of the steps before it (`pair_history_stateAt_auth`) over the Pair-closed prefix
(`before_pairClosed`); at the end, the history's full replay (`pair_history_replayed`).

`tokenEntered` (A11, trace-local): at every node of every settled non-static Pair frame, `T`'s code
is not an EIP-7702 designator and `T` is not a precompile of that frame's rules.  It gives the
per-call field of `pair_token_step_model` through each observed call's same-frame prefix.
-/

namespace Blanc.Composition.PairTokenJoint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair

/-- **C3, the joint invariant (headline).**  Over any configured history from a checkpoint where the
Pair's code is installed over a model state whose token on `side` is `T`, and where the joint
relation holds: at the entry of every settled frame outside the Pair's own frames (the committed
points where the Pair is unlocked), the Pair's storage represents an unlocked model state with that
token, and the joint relation holds there; it holds at the history's end.  Stated against the C2
core only: no token storage layout appears.  Reentrant callbacks during `swap` are inside the
Pair's frames and are consumed by the Pair's positional replay. -/
theorem pair_token_joint {pair T : Adr} {B : Book} (C : Core T B) (laws : BookLaws B)
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
    (∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      trace.settledFrames = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = pair ∧ A.sevm.isStatic = false)) →
      ∃ (st : UniswapV2Pair.State) (K : WriterKey → Prop),
        WriterRep K (f.pre.state.getStor pair) st ∧ st.unlocked = 1 ∧ st.tokenOn side = T ∧
          JointAt C trace pair side st f.pre.state) ∧
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
        JointAt C trace pair side finish future.state := by
  have walk := pair_token_walk C laws abi self side trace installed initial fresh hist token
    unlocked apart answerable distinct notSystem factoryQuiet tokenEntered
  have tokenOf : ∀ {st : UniswapV2Pair.State}, TokensFix st₀.token0 st₀.token1 st₀.factory st →
      st.tokenOn side = T := by
    intro st tokens
    rw [← token]
    cases side
    · exact tokens.1
    · exact tokens.2.1
  refine ⟨fun before f after split noOpaque => ?_, ?_⟩
  · obtain ⟨steps, st, K, observed, auth, replay, rep⟩ :=
      pair_history_stateAt_auth trace installed initial fresh before f after split noOpaque
    obtain ⟨l', run', reserve, zero, tokens, opened, -⟩ := walk steps replay auth observed
      (pre := []) (post := f :: after) split (PairClosed.nil pair)
      (before_pairClosed trace split noOpaque) ⟨rfl, rfl, rfl⟩ unlocked rfl start.1 start.2
    have atF := C.replayAt trace hist before f after split
    rw [List.nil_append, atF] at run'
    cases run'
    exact ⟨st, K, rep, opened, tokenOf tokens, reserve, zero⟩
  · obtain ⟨-, finish, K', replayed⟩ := pair_history_replayed trace installed initial fresh
    obtain ⟨steps, observed, auth, replay, -⟩ := id replayed
    obtain ⟨l', run', reserve, zero, -⟩ := walk steps replay auth observed (pre := [])
      (post := []) (by rw [List.nil_append, List.append_nil]) (PairClosed.nil pair)
      (settledFrames_pairClosed trace) ⟨rfl, rfl, rfl⟩ unlocked rfl start.1 start.2
    rw [List.nil_append, C.replayEnd trace hist] at run'
    cases run'
    exact ⟨finish, K', replayed, reserve, zero⟩

/-- **C3 inside a step (what C4 consumes).**  At every outer Pair step, each token-side
`balanceOf(pair)` answer the step's transcript carries is at least the step's incoming reserve on
that side, and a `burn` step's final answer is at least its initial answer less its own payout:
the token half of `EntryNoShrink`, as a theorem. -/
theorem pair_token_noShrinkSide {pair T : Adr} {B : Book} (C : Core T B) (laws : BookLaws B)
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
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop) (steps : List PairStep),
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      PairObservedReplayWith PairAdmittedConsumes st₀ steps finish ∧
      runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
      WriterRep K' (future.state.getStor pair) finish ∧
      sourceReplayNoShrinkSide side st₀ (steps.map PairStep.source) := by
  obtain ⟨-, finish, K', steps, observed, auth, replay, realized, -, -, rep⟩ :=
    pair_history_replayed trace installed initial fresh
  obtain ⟨-, -, -, -, -, -, noShrink⟩ := pair_token_walk C laws abi self side trace installed
    initial fresh hist token unlocked apart answerable distinct notSystem factoryQuiet tokenEntered
    steps replay auth observed (pre := []) (post := [])
    (by rw [List.nil_append, List.append_nil]) (PairClosed.nil pair)
    (settledFrames_pairClosed trace) ⟨rfl, rfl, rfl⟩ unlocked rfl start.1 start.2
  exact ⟨finish, K', steps, observed, auth, replay, realized, rep, noShrink⟩

end Blanc.Composition.PairTokenJoint
