import Blanc.Composition.PairTokenStepModel
import Blanc.Composition.PairTokenCallers
import Blanc.ExecutionTraceSettledForest

/-!
# The positional walk of C3

A list-level induction over settled positions (design §2.2).  A settled prefix is *Pair-closed*
when every non-static Pair frame in it has its whole block of descendants in it (`PairClosed`).
Along an observed Pair replay whose steps observe exactly a Pair-closed run of settled frames:

* between two outer Pair steps lies a *gap* with no non-static Pair frame; the Pair calls no token
  entry there (`gap_no_pair_entries`: a pair-called entry has a positional parent that is a
  non-static Pair frame, `settledFrames_parent`, whose block would end inside the gap), so the
  booked balance of the Pair does not fall (`pair_token_segment`);
* each outer step is one contiguous subtree (`settledFrames_contig`) consumed by
  `pair_token_step_model`.

`pair_token_walk` carries the joint relation, the fixed tokens and the open lock through the walk
and collects the steps' `EntryNoShrinkSide`.
-/

namespace Blanc.Composition.PairTokenJoint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair

/-! ## Pair-closed prefixes -/

/-- Every non-static Pair frame of `pre` has its whole block of descendants inside `pre`. -/
def PairClosed (pair : Adr) (pre : List Exec.Frame) : Prop :=
  ∀ (b₁ : List Exec.Frame) (G : Exec.Frame) (b₂ : List Exec.Frame), pre = b₁ ++ G :: b₂ →
    G.sevm.currentTarget = pair → G.sevm.isStatic = false →
      (Exec.descendantFrames G.run).length ≤ b₂.length

theorem PairClosed.nil (pair : Adr) : PairClosed pair [] := by
  intro b₁ G b₂ split
  cases b₁ <;> cases split

/-- A Pair-closed prefix extended by a part that is Pair-closed in itself. -/
theorem PairClosed.append {pair : Adr} {X Y : List Exec.Frame} (closed : PairClosed pair X)
    (inY : PairClosed pair Y) : PairClosed pair (X ++ Y) := by
  intro b₁ G b₂ split atPair mutable
  rcases List.split_append_cons split with ⟨m, inX, rfl⟩ | ⟨n, -, inY'⟩
  · have short := closed b₁ G m inX atPair mutable
    rw [List.length_append]
    omega
  · exact inY n G b₂ inY' atPair mutable

/-- A frame observed by the Pair lies in the observation of every list holding it. -/
theorem mem_pairObs {pair : Adr} {fs : List Exec.Frame} {G : Exec.Frame} (member : G ∈ fs)
    (atPair : G.sevm.currentTarget = pair) (mutable : G.sevm.isStatic = false) :
    G ∈ fs.flatMap (pairFrameObs pair) := by
  refine List.mem_flatMap.mpr ⟨G, member, ?_⟩
  rw [pairFrameObs, ite_eq_left_of_eq_true _ _ (eq_true ⟨atPair, mutable⟩)]
  exact List.mem_singleton_self G

/-- A gap (a list with no non-static Pair frame) is Pair-closed. -/
theorem PairClosed.gap {pair : Adr} {gap : List Exec.Frame}
    (quiet : gap.flatMap (pairFrameObs pair) = []) : PairClosed pair gap := by
  intro b₁ G b₂ split atPair mutable
  have inGap : G ∈ gap := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  have member := mem_pairObs (pair := pair) inGap atPair mutable
  rw [quiet] at member
  cases member

/-- A frame's committed subtree is Pair-closed. -/
theorem PairClosed.committed (pair : Adr) (F : Exec.Frame) :
    PairClosed pair (Exec.committedFrames F.run) := by
  intro b₁ G b₂ split _ _
  rw [Exec.Frame.committedFrames_self] at split
  cases b₁ with
  | nil =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj split
      exact Nat.le_refl _
  | cons x b₁' =>
      obtain ⟨-, inDesc⟩ := List.cons.inj split
      obtain ⟨r, rfl⟩ := Exec.descendantFrames_contig F.run inDesc
      rw [List.length_append]
      omega

/-- The whole settled list is Pair-closed. -/
theorem settledFrames_pairClosed {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    PairClosed pair trace.settledFrames := by
  intro b₁ G b₂ split _ _
  obtain ⟨r, rfl⟩ := trace.settledFrames_contig split
  rw [List.length_append]
  omega

/-- The settled frames before an unlocked position are Pair-closed: a non-static Pair frame whose
block reached the position would enclose it. -/
theorem before_pairClosed {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) {before : List Exec.Frame}
    {f : Exec.Frame} {after : List Exec.Frame} (split : trace.settledFrames = before ++ f :: after)
    (noOpaque : ∀ A ∈ before, A.Encloses f →
      ¬ (A.sevm.currentTarget = pair ∧ A.sevm.isStatic = false)) :
    PairClosed pair before := by
  intro b₁ G b₂ inBefore atPair mutable
  rw [inBefore, List.append_assoc, List.cons_append] at split
  obtain ⟨r, rest⟩ := trace.settledFrames_contig split
  have inB : G ∈ before := by
    rw [inBefore]
    exact List.mem_append_right _ List.mem_cons_self
  refine Nat.le_of_not_lt fun longer => noOpaque G inB ?_ ⟨atPair, mutable⟩
  rcases List.append_eq_append_iff.mp rest with ⟨a', descEq, tailEq⟩ | ⟨c', b₂Eq, -⟩
  · cases a' with
    | nil =>
        rw [List.append_nil] at descEq
        rw [descEq] at longer
        exact absurd longer (Nat.lt_irrefl _)
    | cons y a'' =>
        obtain ⟨rfl, -⟩ := List.cons.inj tailEq
        change f ∈ Exec.descendantFrames G.run
        rw [descEq]
        exact List.mem_append_right _ List.mem_cons_self
  · rw [b₂Eq, List.length_append] at longer
    omega

/-! ## Gaps -/

/-- **The Pair calls no token entry inside a gap after a Pair-closed prefix.** -/
theorem gap_no_pair_entries {pair T : Adr} {B : Book} (C : Core T B) (self : SelfCaller C)
    {cfg : ChainConfig} {checkpoint future : BlockChain} {K₀ : WriterKey → Prop}
    {st₀ : UniswapV2Pair.State} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (hist : C.Hist trace) (apart : pair ≠ T) (notSystem : pair ≠ systemAddress)
    {pre gap post : List Exec.Frame} (split : trace.settledFrames = pre ++ gap ++ post)
    (closed : PairClosed pair pre) (quiet : gap.flatMap (pairFrameObs pair) = []) :
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
        have obs := mem_pairObs (pair := pair) (fs := g₁ ++ F :: g₂)
          (List.mem_append_left _ inG₁) atPair mutableG
        rw [quiet] at obs
        cases obs
    · rw [static mutableG] at mutable
      cases mutable

/-- The first observed frame of a list splits it into a gap, that frame and the rest. -/
theorem pairFrameObs_first {pair : Adr} :
    ∀ {fs : List Exec.Frame} {F₀ : Exec.Frame} {xs : List Exec.Frame},
      fs.flatMap (pairFrameObs pair) = F₀ :: xs →
      ∃ gap rest, fs = gap ++ F₀ :: rest ∧ gap.flatMap (pairFrameObs pair) = [] ∧
        F₀.sevm.currentTarget = pair ∧ F₀.sevm.isStatic = false ∧
        xs = rest.flatMap (pairFrameObs pair)
  | [], _, _, h => by cases h
  | y :: ys, F₀, xs, h => by
      rw [List.flatMap_cons] at h
      by_cases hy : y.sevm.currentTarget = pair ∧ y.sevm.isStatic = false
      · rw [pairFrameObs, ite_eq_left_of_eq_true _ _ (eq_true hy), List.singleton_append] at h
        obtain ⟨rfl, rfl⟩ := List.cons.inj h
        exact ⟨[], ys, rfl, rfl, hy.1, hy.2, rfl⟩
      · rw [pairFrameObs, ite_eq_right_of_eq_false _ _ (eq_false hy), List.nil_append] at h
        obtain ⟨gap, rest, rfl, quiet, atPair, mutable, rfl⟩ := pairFrameObs_first h
        refine ⟨y :: gap, rest, rfl, ?_, atPair, mutable, rfl⟩
        rw [List.flatMap_cons, pairFrameObs, ite_eq_right_of_eq_false _ _ (eq_false hy), List.nil_append]
        exact quiet

/-- A non-static Pair frame's subtree observation begins with the frame itself. -/
theorem pairSubtreeFrames_self {pair : Adr} {F : Exec.Frame} (atPair : F.sevm.currentTarget = pair)
    (mutable : F.sevm.isStatic = false) :
    pairSubtreeFrames pair F = F :: (Exec.descendantFrames F.run).flatMap (pairFrameObs pair) := by
  rw [pairSubtreeFrames, Exec.Frame.committedFrames_self, List.flatMap_cons, pairFrameObs,
    ite_eq_left_of_eq_true _ _ (eq_true ⟨atPair, mutable⟩), List.singleton_append]

/-- **The booked balance of the Pair does not fall across a gap** after a Pair-closed prefix. -/
theorem pair_token_gap {pair T : Adr} {B : Book} (C : Core T B) (laws : BookLaws B)
    (abi : Erc20Abi B) (self : SelfCaller C) (side : TokenSide) {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (hist : C.Hist trace) (token : st₀.tokenOn side = T) (unlocked : st₀.unlocked = 1)
    (apart : pair ≠ T) (notSystem : pair ≠ systemAddress)
    (factoryQuiet : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → G.sevm.caller ≠ st₀.factory)
    {pre gap post : List Exec.Frame} (split : trace.settledFrames = pre ++ gap ++ post)
    (closed : PairClosed pair pre) (quiet : gap.flatMap (pairFrameObs pair) = [])
    {l l' : B.Ledger} (atPre : B.run (C.ledgerOf trace checkpoint.state) (entryAsks T pre) = some l)
    (step : B.run l (entryAsks T gap) = some l') (zero : ∀ g, B.allow l pair g = 0) :
    B.bal l pair ≤ B.bal l' pair ∧ ∀ g, B.allow l' pair g = 0 := by
  obtain ⟨moved, zero'⟩ := pair_token_segment C laws abi self side trace installed initial fresh
    hist token unlocked apart notSystem factoryQuiet split atPre step zero
  rw [entryAsks_filter_caller_nil (gap_no_pair_entries C self trace installed initial fresh hist
    apart notSystem split closed quiet), List.map_nil, List.sum_nil, Nat.add_zero] at moved
  exact ⟨moved, zero'⟩

/-! ## The walk -/

/-- **The positional walk.**  Along an observed Pair replay whose steps observe exactly the settled
run `fs` after a Pair-closed prefix `pre` (with `pre ++ fs` Pair-closed), the joint relation, the
fixed tokens and the open lock carry from the ledger after `pre` to the ledger after `pre ++ fs`,
and every step satisfies its side's `EntryNoShrinkSide`. -/
theorem pair_token_walk {pair T : Adr} {B : Book} (C : Core T B) (laws : BookLaws B)
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
            ¬ node.sevm.benvStat.rules.isPrecomp T) :
    ∀ (steps : List PairStep) {st st' : UniswapV2Pair.State} {pre fs post : List Exec.Frame}
      {l : B.Ledger},
      PairObservedReplayWith PairAdmittedConsumes st steps st' →
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) →
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = fs.flatMap (pairFrameObs pair) →
      trace.settledFrames = pre ++ fs ++ post →
      PairClosed pair pre → PairClosed pair (pre ++ fs) →
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
      obtain ⟨grows, zero'⟩ := pair_token_gap C laws abi self side trace installed initial fresh
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
      rw [List.flatMap_cons, pairSubtreeFrames_self atPair mutable, List.cons_append] at observed
      obtain ⟨gap, rest', rfl, quiet, -, -, restObs⟩ := pairFrameObs_first observed.symm
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
      have entryLedger := C.replayAt trace hist (pre ++ gap) s.frame _ globalSplit
      have gapStep : B.run l (entryAsks T gap) = some (C.ledgerOf trace s.frame.pre.state) := by
        rw [entryAsks_append, Book.run_append, atPre, Option.bind_some] at entryLedger
        exact entryLedger
      obtain ⟨grows, zeroGap⟩ := pair_token_gap C laws abi self side trace installed initial fresh
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
      have settledS : s.frame ∈ trace.settledFrames := by
        rw [globalSplit]
        exact List.mem_append_right _ List.mem_cons_self
      obtain ⟨noShrink, l', run', reserve', zero'⟩ := pair_token_step_model C laws abi self side
        trace hist apart answerable stepSplit atPair 
        (current := { state := st, logs := [], updates := [] }) consumed stepToken
        (by rw [tokens.1, tokens.2.1]; exact distinct) opened
        (by rw [tokens.2.2]; exact factoryQuiet)
        (fun observed _ => tokenEntered s.frame settledS atPair mutable observed.call.sameFrame)
        ⟨Nat.le_trans reserve grows, zeroGap⟩ successful
      have quietStep : FactoryQuiet st₀.factory pair (Exec.committedFrames s.frame.run) :=
        fun D member => factoryQuiet D
          (stepSplit ▸ List.mem_append_left _ (List.mem_append_right _ member))
      obtain ⟨outFix, outOpen, -, -⟩ := PairStep.consumedFix consumed atPair quietStep tokens opened
      have closedNext : PairClosed pair ((pre ++ gap) ++ Exec.committedFrames s.frame.run) :=
        (closedPre.append (PairClosed.gap quiet)).append (PairClosed.committed pair s.frame)
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
