import Blanc.Lift.OutermostFrames
import Blanc.ExecutionTargetPrefix
import Blanc.Composition.PairTokenStepModel
import Blanc.Composition.PairTokenCallers
import Blanc.ExecutionTraceSettledForest

/-!
# The positional walk of C3

A list-level induction over settled positions (design §2.2).  A settled prefix is *Pair-closed*
when every non-static Pair frame in it has its whole block of descendants in it (`Blanc.ExecutionTrace.TargetClosed`).
Along an observed Pair replay whose steps observe exactly a Pair-closed run of settled frames:

* between two outer Pair steps lies a *gap* with no non-static Pair frame; the Pair calls no token
  entry there (`gap_no_pair_entries`: a pair-called entry has a positional parent that is a
  non-static Pair frame, `settledFrames_parent`, whose block would end inside the gap), so the
  booked balance of the Pair does not fall (`pair_token_segment`);
* each outer step is one contiguous subtree (`settledFrames_contig`) consumed by
  `pair_token_step_model`; a step frame is non-static and not at the token, so it is not shadowed
  (`CoreW.shadow_kind`).

The walk is stated over the writer-shadowed core `CoreW` and the holder-indexed laws
`HolderLaws` (Route R).

`pair_token_walk` carries the joint relation, the fixed tokens and the open lock through the walk
and collects the steps' `EntryNoShrinkSide`.
-/

namespace Blanc.Composition.PairTokenJoint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair

/-! ## Gaps -/

/-- **The Pair calls no token entry inside a gap after a Pair-closed prefix.** -/
theorem gap_no_pair_entries {pair T : Adr} {B : Book} (C : CoreW T B) (self : SelfCallerW C)
    {cfg : ChainConfig} {checkpoint future : BlockChain} {K₀ : WriterKey → Prop}
    {st₀ : UniswapV2Pair.State} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (hist : C.Hist trace) (apart : pair ≠ T) (notSystem : pair ≠ systemAddress)
    {pre gap post : List Exec.Frame} (split : trace.settledFrames = pre ++ gap ++ post)
    (closed : Blanc.ExecutionTrace.TargetClosed pair pre) (quiet : gap.flatMap (Blanc.Exec.Frame.obsAt pair) = []) :
    ∀ F ∈ gap, IsEntry T F → F.sevm.isStatic = false → F.sevm.caller = pair → False := by
  intro F member entry mutable caller
  obtain ⟨g₁, g₂, rfl⟩ := List.mem_iff_append.mp member
  have at' : trace.settledFrames = (pre ++ g₁) ++ F :: (g₂ ++ post) := by
    rw [split]
    simp only [List.append_assoc, List.cons_append]
  rcases trace.settledFrames_parent at' with root | ⟨b₁, G, b₂, hb, child, ⟨relation, static⟩,
    shorter⟩
  · exact pair_history_settledRoots_caller_ne trace installed initial fresh notSystem F root caller
  · have settledG : G ∈ trace.settledFrames := by
      rw [at', hb]
      exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
    cases mutableG : G.sevm.isStatic
    · have atPair : G.sevm.currentTarget = pair := by
        rcases relation with callerEq | targetEq
        · exact callerEq.symm.trans caller
        · have selfCaller := self.child_caller trace hist G settledG
            (targetEq.symm.trans entry.1) mutableG F child entry
          exact absurd (caller.symm.trans selfCaller) apart
      rcases List.split_append_cons hb with ⟨m, inPre, rfl⟩ | ⟨n, -, inGap⟩
      · have short := closed b₁ G m inPre atPair mutableG
        rw [List.length_append] at shorter
        omega
      · have inG₁ : G ∈ g₁ := by
          rw [inGap]
          exact List.mem_append_right _ List.mem_cons_self
        have obs := Blanc.ExecutionTrace.mem_flatMap_obsAt (pair := pair) (fs := g₁ ++ F :: g₂)
          (List.mem_append_left _ inG₁) atPair mutableG
        rw [quiet] at obs
        cases obs
    · rw [static mutableG] at mutable
      cases mutable

/-- **The booked balance of the Pair does not fall across a gap** after a Pair-closed prefix. -/
theorem pair_token_gap {pair T : Adr} {B : Book} (C : CoreW T B)
    (abi : Erc20Abi B) (self : SelfCallerW C) (side : TokenSide) {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (laws : HolderLaws T B trace pair)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (hist : C.Hist trace) (token : st₀.tokenOn side = T) (unlocked : st₀.unlocked = 1)
    (apart : pair ≠ T) (notSystem : pair ≠ systemAddress)
    (factoryQuiet : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → G.sevm.caller ≠ st₀.factory)
    {pre gap post : List Exec.Frame} (split : trace.settledFrames = pre ++ gap ++ post)
    (closed : Blanc.ExecutionTrace.TargetClosed pair pre) (quiet : gap.flatMap (Blanc.Exec.Frame.obsAt pair) = [])
    {l l' : B.Ledger} (atPre : B.run (C.ledgerOf trace checkpoint.state) (entryAsks T pre) = some l)
    (step : B.run l (entryAsks T gap) = some l') (zero : ∀ g, B.allow l pair g = 0) :
    B.bal l pair ≤ B.bal l' pair ∧ ∀ g, B.allow l' pair g = 0 := by
  obtain ⟨moved, zero'⟩ := pair_token_segment C abi self side trace laws installed initial fresh
    hist token unlocked apart notSystem factoryQuiet split atPre step zero
  rw [entryAsks_filter_caller_nil (gap_no_pair_entries C self trace installed initial fresh hist
    apart notSystem split closed quiet), List.map_nil, List.sum_nil, Nat.add_zero] at moved
  exact ⟨moved, zero'⟩

/-! ## The walk -/

/-- **The positional walk.**  Along an observed Pair replay whose steps observe exactly the settled
run `fs` after a Pair-closed prefix `pre` (with `pre ++ fs` Pair-closed), the joint relation, the
fixed tokens and the open lock carry from the ledger after `pre` to the ledger after `pre ++ fs`,
and every step satisfies its side's `EntryNoShrinkSide`. -/
theorem pair_token_walk {pair T : Adr} {B : Book} (C : CoreW T B)
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
            ¬ node.sevm.benvStat.rules.isPrecomp T) :
    ∀ (steps : List PairStep) {st st' : UniswapV2Pair.State} {pre fs post : List Exec.Frame}
      {l : B.Ledger},
      PairObservedReplayWith PairAdmittedConsumes st steps st' →
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) →
      steps.flatMap (fun s => Blanc.Exec.Frame.subtreeAt pair s.frame) = fs.flatMap (Blanc.Exec.Frame.obsAt pair) →
      trace.settledFrames = pre ++ fs ++ post →
      Blanc.ExecutionTrace.TargetClosed pair pre → Blanc.ExecutionTrace.TargetClosed pair (pre ++ fs) →
      TokensFix st₀.token0 st₀.token1 st₀.factory st → st.unlocked = 1 →
      B.run (C.ledgerOf trace checkpoint.state) (entryAsks T pre) = some l →
      st.reserveOn side ≤ B.bal l pair → (∀ g, B.allow l pair g = 0) →
      ∃ l', B.run (C.ledgerOf trace checkpoint.state) (entryAsks T (pre ++ fs)) = some l' ∧
        st'.reserveOn side ≤ B.bal l' pair ∧ (∀ g, B.allow l' pair g = 0) ∧
        TokensFix st₀.token0 st₀.token1 st₀.factory st' ∧ st'.unlocked = 1 ∧
        sourceReplayNoShrinkSide side st (steps.map PairStep.source) := by
  intro steps
  induction steps with
  | nil =>
      intro st st' pre fs post l replay _ observed split closedPre _ tokens opened atPre
        reserve zero
      cases replay
      have whole := C.replayEnd trace hist
      rw [split, entryAsks_append, entryAsks_append] at whole
      obtain ⟨l', run'⟩ := Book.run_some_of_append whole
      have step : B.run l (entryAsks T fs) = some l' := by
        rw [Book.run_append, atPre, Option.bind_some] at run'
        exact run'
      obtain ⟨grows, zero'⟩ := pair_token_gap C abi self side trace laws installed initial fresh
        hist token unlocked apart notSystem factoryQuiet split closedPre observed.symm atPre step
        zero
      refine ⟨l', ?_, Nat.le_trans reserve grows, zero', tokens, opened, trivial⟩
      rw [entryAsks_append, Book.run_append, atPre, Option.bind_some]
      exact step
  | cons s rest ih =>
      intro st st' pre fs post l replay auth observed split closedPre closedAll tokens opened atPre
        reserve zero
      cases replay with
      | @cons _ _ _ _ out consumed successful tail =>
      obtain ⟨-, -, atPair, mutable, -⟩ := auth s List.mem_cons_self
      rw [List.flatMap_cons, Blanc.Exec.Frame.subtreeAt_of_target atPair mutable, List.cons_append] at observed
      obtain ⟨gap, rest', rfl, quiet, -, -, restObs⟩ := Blanc.ExecutionTrace.obsAt_first observed.symm
      -- the step's subtree is contiguous and inside `fs`
      have closedAt := closedAll (pre ++ gap) s.frame rest' (by
        simp only [List.append_assoc]) atPair mutable
      have globalSplit : trace.settledFrames = (pre ++ gap) ++ s.frame :: (rest' ++ post) := by
        rw [split]
        simp only [List.append_assoc, List.cons_append]
      obtain ⟨r, contig⟩ := trace.settledFrames_contig globalSplit
      have descPrefix : Exec.descendantFrames s.frame.run <+: rest' :=
        List.prefix_of_prefix_length_le ⟨r, contig.symm⟩ (List.prefix_append rest' post) closedAt
      obtain ⟨rest'', rfl⟩ := descPrefix
      rw [List.flatMap_append, List.append_cancel_left_eq] at restObs
      -- across the gap
      have settledS : s.frame ∈ trace.settledFrames := by
        rw [globalSplit]
        exact List.mem_append_right _ List.mem_cons_self
      have litS : ¬ C.Shadowed trace (pre ++ gap) s.frame := fun shadowed => by
        rcases C.shadow_kind trace hist (pre ++ gap) s.frame _ globalSplit shadowed with
          static | ⟨atT, -⟩
        · rw [mutable] at static
          cases static
        · exact apart (atPair.symm.trans atT)
      have entryLedger := C.replayAt trace hist (pre ++ gap) s.frame _ globalSplit litS
      have gapStep : B.run l (entryAsks T gap) = some (C.ledgerOf trace s.frame.pre.state) := by
        rw [entryAsks_append, Book.run_append, atPre, Option.bind_some] at entryLedger
        exact entryLedger
      obtain ⟨grows, zeroGap⟩ := pair_token_gap C abi self side trace laws installed initial fresh
        hist token unlocked apart notSystem factoryQuiet (pre := pre) (gap := gap)
        (post := s.frame :: (Exec.descendantFrames s.frame.run ++ rest'' ++ post)) globalSplit closedPre
        quiet atPre gapStep zero
      -- across the step
      have stepSplit : trace.settledFrames =
          (pre ++ gap) ++ Exec.committedFrames s.frame.run ++ (rest'' ++ post) := by
        rw [globalSplit, Exec.Frame.committedFrames_self]
        simp only [List.append_assoc, List.cons_append]
      have stepToken : st.tokenOn side = T := by
        rw [← token]
        cases side
        · exact tokens.1
        · exact tokens.2.1
      obtain ⟨noShrink, l', run', reserve', zero'⟩ := pair_token_step_model C abi self side
        trace laws hist apart answerable stepSplit atPair litS
        (current := { state := st, logs := [], updates := [] }) consumed stepToken
        (by rw [tokens.1, tokens.2.1]; exact distinct) opened
        (by rw [tokens.2.2]; exact factoryQuiet)
        (fun observed _ => tokenEntered s.frame settledS atPair mutable observed.call.sameFrame)
        ⟨Nat.le_trans reserve grows, zeroGap⟩ successful
      have quietStep : FactoryQuiet st₀.factory pair (Exec.committedFrames s.frame.run) :=
        fun D member => factoryQuiet D
          (stepSplit ▸ List.mem_append_left _ (List.mem_append_right _ member))
      obtain ⟨outFix, outOpen, -, -⟩ := PairStep.consumedFix consumed atPair quietStep tokens opened
      have closedNext : Blanc.ExecutionTrace.TargetClosed pair ((pre ++ gap) ++ Exec.committedFrames s.frame.run) :=
        (closedPre.append (Blanc.ExecutionTrace.TargetClosed.gap quiet)).append (Blanc.ExecutionTrace.TargetClosed.committed pair s.frame)
      obtain ⟨l'', run'', reserve'', zero'', tokens'', opened'', noShrinkRest⟩ :=
        ih tail (fun s' member => auth s' (List.mem_cons_of_mem _ member)) restObs
          (pre := (pre ++ gap) ++ Exec.committedFrames s.frame.run) (post := post)
          (by rw [stepSplit]; simp only [List.append_assoc]) closedNext
          (by rw [Exec.Frame.committedFrames_self]
              simpa only [List.append_assoc, List.cons_append] using closedAll)
          outFix.1 (outOpen rfl _ successful) run' reserve' zero'
      refine ⟨l'', ?_, reserve'', zero'', tokens'', opened'', noShrink, ?_⟩
      · rw [Exec.Frame.committedFrames_self] at run''
        simpa only [List.append_assoc, List.cons_append] using run''
      · have runEq : s.source.run st = out := (runTyped_of_exact consumed.positional.forget).1
        change sourceReplayNoShrinkSide side (s.source.run st).frame.current.state
          (rest.map PairStep.source)
        rw [runEq]
        exact noShrinkRest

end Blanc.Composition.PairTokenJoint
