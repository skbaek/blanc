import Blanc.Lift.UniswapV2Pair.PairHistoryShape

/-!
# A locked Pair has only static children, below any derivation

Over an arbitrary committed derivation (here: the other token's transfer child of the Pair's swap,
burn or skim), entered with the Pair storage representing a **locked** model state and the Pair runtime
installed: every committed non-static frame at the Pair has only static direct children
(`run_lockedBelow`).  The proof reads the Pair's whole-frame accounting (`pairCarrierWith`, the
arguments of `pairLadderWith`) through `Exec.coreAccounting` on the derivation itself, unfolds the replay
from the locked state, and consumes each observed step in the nested mode of
`PositionalConsumes.segInv` (`PairObservedReplayWith.lockedBelow`).

The nested mode needs the factory quiet over the derivation (the Pair's `initialize` is not
lock-guarded); `UniswapV2PairWeth9XLegFactory.frame_factoryQuiet` supplies it from code.
-/

namespace Blanc.Composition.UniswapV2PairWeth9XLeg

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.ExecutionAccountingReplay

/-- **One consumed step from a locked state** (nested mode): every direct child of the step's frame is
static, every non-static Pair frame below it has only static children, and the step leaves the Pair
locked with the same tokens and factory. -/
theorem PairStep.lockedFix {t0 t1 f pair : Adr} {s : PairStep} {current : Checkpoint}
    {out : RunResult}
    (consumed : PairAdmittedConsumes (Blanc.Exec.Frame.rootDeriv s.frame)
      (startTyped current s.source.context s.source.entry) s.transcript out)
    (target : s.frame.sevm.currentTarget = pair)
    (quiet : FactoryQuiet f pair (Exec.committedFrames s.frame.run))
    (tokens : TokensFix t0 t1 f current.state) (locked : current.state.unlocked ≠ 1) :
    LockedBelow pair (Exec.committedFrames s.frame.run) ∧
      TokensFix t0 t1 f out.frame.current.state ∧ out.frame.current.state.unlocked ≠ 1 := by
  have inv := startTyped_segInv_nested (current := current) (ctx := s.source.context)
    (entry := s.source.entry) tokens locked (fun static =>
      quiet s.frame (Exec.Frame.mem_committedFrames.mpr (Or.inl rfl)) target static)
  obtain ⟨outFix, -, children, lockedDesc⟩ := consumed.positional.segInv inv (by
    intro D member atRoot mutable
    exact quiet D (Exec.Frame.mem_committedFrames.mpr (Or.inr member)) (atRoot.trans target)
      mutable)
  refine ⟨?_, outFix.1, (outFix.2.2.1 rfl).1⟩
  intro D member atPair mutableD c child
  rcases Exec.Frame.mem_committedFrames.mp member with rfl | deeper
  · cases staticC : c.sevm.isStatic
    · exact absurd (children c child staticC).1 (by decide)
    · rfl
  · exact lockedDesc D deeper (atPair.trans target.symm) mutableD c child

/-- **An observed Pair replay from a locked state** keeps the lock, and each of its steps has only
static children below its non-static Pair frames. -/
theorem PairObservedReplayWith.lockedBelow {t0 t1 f pair : Adr} {st st' : UniswapV2Pair.State}
    {steps : List PairStep}
    (replay : PairObservedReplayWith PairAdmittedConsumes st steps st')
    (auth : ∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair)
    (quiet : ∀ s ∈ steps, FactoryQuiet f pair (Exec.committedFrames s.frame.run))
    (tokens : TokensFix t0 t1 f st) (locked : st.unlocked ≠ 1) :
    ∀ s ∈ steps, LockedBelow pair (Exec.committedFrames s.frame.run) := by
  induction replay with
  | nil st => exact fun _ member => by cases member
  | @cons st finish s rest out consumed successful tail ih =>
    obtain ⟨here, outTokens, outLocked⟩ := PairStep.lockedFix consumed
      (auth s List.mem_cons_self).2.2.1 (quiet s List.mem_cons_self) tokens locked
    intro s' member
    rcases List.mem_cons.mp member with rfl | later
    · exact here
    · exact ih (fun s'' m => auth s'' (List.mem_cons_of_mem _ m))
        (fun s'' m => quiet s'' (List.mem_cons_of_mem _ m)) outTokens outLocked s' later

/-- **A locked Pair below a derivation.**  Over a committed derivation on a covered fork, entered with
the Pair runtime installed (`pairSem.At`), admitted by `pairEntry U` over a separated universe, under
the ether-supply bound, with the Pair storage representing (over rows of `U`) a locked model state, and
with no committed non-static Pair frame called by that state's factory: every committed non-static
frame at the Pair has only static direct children. -/
theorem run_lockedBelow {pair : Adr} {U : WriterKey → Prop} (inj : WriterInj U)
    (apart : WriterApart U) {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (fork : CoveredFork sevm.benvStat.fork) (installed : pairSem.At pair pc sevm pre)
    (admitted : Exec.FrameAdmitted pair (pairEntry U) run) (bound : sum pre.state.bal < 2 ^ 256)
    {st : UniswapV2Pair.State} {K : WriterKey → Prop} (sub : ∀ k, K k → U k)
    (rep : WriterRep K (pre.state.getStor pair) st) (locked : st.unlocked ≠ 1)
    (quiet : FactoryQuiet st.factory pair (Exec.committedFrames run)) :
    LockedBelow pair (Exec.committedFrames run) := by
  have supply := pairAdmittedSupply inj apart pairSem pairSem_image
  have core := Exec.coreAccounting pair pairSem (pairEntry U)
    (pairCarrierWith PairAdmittedConsumes PairEntryAuth pair U)
    (pairObservationWith PairAdmittedConsumes PairEntryAuth pair U)
    PairReplayWith.append (fun _ _ => ()) (fun _ _ _ => rfl) (fun _ h => pairFrameObs_foreign h)
    (fun hrun target deeper => Exec.CoreAccounting.wholeFrameTarget (fun _ _ => rfl)
      (fun h => funext h) (fun _ h => pairFrameObs_static h) (pair_spawnKinds pair)
      (pair_wholeFrameReplayWith pair supply) hrun target deeper)
  obtain ⟨-, replayOf⟩ := core pc sevm pre out run installed run committed fork installed admitted
  obtain ⟨frames, replay, observed⟩ := replayOf bound
  change PairReplayWith PairAdmittedConsumes PairEntryAuth pair U (pre.state.getStor pair).get frames
    ((Execution.committedPost out committed).state.getStor pair).get at replay
  change frames.flatMap (pairSubtreeFrames pair) =
    (Exec.committedFrames run).flatMap (pairFrameObs pair) at observed
  obtain ⟨steps, framesEq, auth, finish, K', source, -, -, -⟩ := replay st K sub ⟨_, rfl, rep⟩
  rw [← framesEq, List.flatMap_map] at observed
  have inRun := mem_of_pairSubtree observed (settled := Exec.committedFrames run)
    (fun F member => member)
  have below := PairObservedReplayWith.lockedBelow source auth
    (fun s member => factoryQuiet_of_subtree (inRun s member) quiet) ⟨rfl, rfl, rfl⟩ locked
  intro D member atPair mutableD
  have inObs : D ∈ (Exec.committedFrames run).flatMap (pairFrameObs pair) := by
    refine List.mem_flatMap.mpr ⟨D, member, ?_⟩
    rw [pairFrameObs, ite_eq_left_of_eq_true _ _ (eq_true ⟨atPair, mutableD⟩)]
    exact List.mem_singleton_self D
  rw [← observed] at inObs
  obtain ⟨s, stepMem, inSubtree⟩ := List.mem_flatMap.mp inObs
  obtain ⟨F, frameMem, obs⟩ := List.mem_flatMap.mp inSubtree
  have sameF : D = F := by
    unfold pairFrameObs at obs
    split at obs
    · exact List.mem_singleton.mp obs
    · cases obs
  subst sameF
  exact below s stepMem D frameMem atPair mutableD

end Blanc.Composition.UniswapV2PairWeth9XLeg
