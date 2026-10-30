import Blanc.Lift.UniswapV2Pair.PairPositionalCalls
import Blanc.Lift.UniswapV2Pair.PropertiesMinLiquidity
import Blanc.Lift.TargetLogEvents

/-!
# Nonzero callers of the source replay, from raw frames

The minimum-liquidity law needs `SourceInvocation.CallersNonzero`: no step and no re-entered Pair
child consumed inside a step's transcript has caller zero.  Every caller a positional transcript
records is the caller of an actual raw frame entered below the consumed root at the root's own
address (`SourceSlotQueue.rawFrameRoot`), so the model premise follows from a premise over raw
frames: `RawCallersNonzero root` says every raw frame below `root` at `root`'s address has a
nonzero caller (`PositionalConsumes.callersNonzero`).
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- Every raw frame root of `root`'s execution entered at `root`'s own address has a nonzero
caller. -/
def RawCallersNonzero (root : Exec.Deriv) : Prop :=
  ∀ E ∈ Exec.rawFrameRoots root.exc,
    E.sevm.currentTarget = root.sevm.currentTarget → E.sevm.caller ≠ 0

/-- A frame selected into an observed call's queue is a raw frame root below the calling root,
at the queue's address. -/
theorem SourceSlotQueue.rawFrameRoot {root : Exec.Deriv} {x : Xinst}
    {call : CallOccurrenceStep root x} {pair : Adr} {index : Nat}
    {paths : List Exec.LocatedFrame} (queue : SourceSlotQueue call pair index paths)
    {located : Exec.LocatedFrame} (member : located ∈ paths) :
    Exec.Frame.rootDeriv located.frame ∈ Exec.rawFrameRoots root.exc ∧
      located.frame.sevm.currentTarget = pair := by
  rcases queue with ⟨-, rfl⟩ |
    ⟨evm, raw, callee, resume, pc, child, next, spawn, enter, resumed, -, excEq, rfl⟩
  · cases member
  by_cases settles : Jaune.Frame.settlementCommits callee raw = true
  · rw [ite_eq_left settles, Exec.retainedTargetTurnsAt_filterMap_eq _ _ _
      (Jaune.Frame.raw_commits_of_settlementCommits settles)] at member
    obtain ⟨rawRoot, target⟩ := Exec.retainedTargetFramesFromAt_rawFrameRoot pair child _ member
    refine ⟨?_, target⟩
    have below : Exec.Frame.rootDeriv located.frame ∈
        Exec.rawFrameDescendants call.occurrence.node.exc := by
      rw [excEq]
      simp only [Exec.rawFrameRoots, List.mem_cons] at rawRoot
      simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append]
      rcases rawRoot with same | deeper
      · exact Or.inl same
      · exact Or.inr (Or.inl deeper)
    simp only [Exec.rawFrameRoots, List.mem_cons]
    exact Or.inr (Exec.mem_rawFrameDescendants_of_parentPrefix call.sameFrame below)
  · rw [ite_eq_right settles] at member
    cases member

/-- A raw frame below `root` at `root`'s address has a nonzero caller and inherits the premise. -/
theorem RawCallersNonzero.below {root : Exec.Deriv} (callers : RawCallersNonzero root)
    {frame : Exec.Frame} (member : Exec.Frame.rootDeriv frame ∈ Exec.rawFrameRoots root.exc)
    (target : frame.sevm.currentTarget = root.sevm.currentTarget) :
    frame.sevm.caller ≠ 0 ∧ RawCallersNonzero (Exec.Frame.rootDeriv frame) :=
  ⟨callers _ member target, fun E inner same =>
    callers E (Exec.rawFrameRoots_trans member inner) (same.trans target)⟩

private theorem staticViewTranscript_callers {views : List StaticViewTurn}
    (callers : ∀ picked ∈ views, picked.1.frame.sevm.caller ≠ 0) :
    (staticViewTranscript views .done).CallersNonzero := by
  induction views with
  | nil => trivial
  | cons picked rest ih =>
    exact ⟨callers picked List.mem_cons_self, trivial,
      ih (fun other member => callers other (List.mem_cons_of_mem _ member))⟩

/-- **Positional transcripts record only raw callers.**  If every raw frame below the consumed
root at its address has a nonzero caller, the consumed transcript has no zero caller. -/
theorem PositionalConsumes.callersNonzero {root start : Exec.Deriv} {index : Nat}
    {segment : SegmentResult} {transcript : Transcript} {out : RunResult}
    (consumed : PositionalConsumes root start index segment transcript out)
    (callers : RawCallersNonzero root) : transcript.CallersNonzero := by
  refine PositionalConsumes.rec
    (motive_1 := fun root _ _ _ transcript _ _ =>
      RawCallersNonzero root → transcript.CallersNonzero)
    (motive_2 := fun _ _ _ events transcript _ _ =>
      (∀ located, Sum.inr located ∈ events →
        located.frame.sevm.caller ≠ 0 ∧ RawCallersNonzero (Exec.Frame.rootDeriv located.frame)) →
      transcript.CallersNonzero) ?_ ?_ ?_ ?_ ?_ ?_ ?_ consumed callers
  · intros; trivial
  · intros; trivial
  · intro root start index frame request continuation reply turns tail executed out
      observed gap present noCodeTurns during rest ih callers
    refine ⟨?_, ih callers⟩
    cases during with
    | staticViews views mapped authentic consumed =>
      apply staticViewTranscript_callers
      intro picked member
      have path : picked.1 ∈ observed.paths := by
        rw [← mapped]
        exact List.mem_map_of_mem member
      obtain ⟨raw, target⟩ := observed.queue.rawFrameRoot path
      exact (callers.below raw (target.trans observed.pair_eq)).1
  · intro root start index frame request continuation reply turns tail executed out events
      observed gap queue present noCodeTurns during rest ihDuring ihRest callers
    refine ⟨ihDuring fun located member => ?_, ihRest callers⟩
    have path : located ∈ events.filterMap Sum.getRight? :=
      List.mem_filterMap.mpr ⟨_, member, rfl⟩
    obtain ⟨raw, target⟩ := queue.queue.rawFrameRoot path
    exact callers.below raw (target.trans observed.pair_eq)
  · intros; trivial
  · intro frame request turn log events tail out mutable rest ih located
    exact ih fun other member => located other (List.mem_cons_of_mem _ member)
  · intro frame request turn located entry events transcript tail child out selected output rest
      ihSelected ihRest hyp
    obtain ⟨nonzero, below⟩ := hyp located List.mem_cons_self
    exact ⟨nonzero, ihSelected below,
      ihRest fun other member => hyp other (List.mem_cons_of_mem _ member)⟩

/-- **Steps of a replay with raw nonzero callers satisfy the model premise.** -/
theorem PairObservedReplayWith.callersNonzero {st finish : State} {steps : List PairStep}
    (replay : PairObservedReplayWith PairAdmittedConsumesH st steps finish)
    (callers : ∀ s ∈ steps, RawCallersNonzero (Exec.Frame.rootDeriv s.frame))
    (senders : ∀ s ∈ steps, s.frame.sevm.caller ≠ 0) :
    ∀ s ∈ steps, s.source.CallersNonzero := by
  induction replay with
  | nil => intro s member; cases member
  | cons consumed _ _ ih =>
    intro s member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨senders _ List.mem_cons_self,
        consumed.1.callersNonzero (callers _ List.mem_cons_self)⟩
    · exact ih (fun s m => callers s (List.mem_cons_of_mem _ m))
        (fun s m => senders s (List.mem_cons_of_mem _ m)) s later

end Blanc.Lift.UniswapV2Pair
