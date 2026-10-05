import Blanc.ExecutionModelAccounting
import Blanc.ExecutionAccountingAdmission
import Blanc.ExecDeterminism

/-!
# A target handler for contracts whose frame theorem covers its whole subtree

`Blanc/ExecutionModelAccounting.lean` replays a successful non-static target frame as its own steps
followed by the steps of the children it settles (`SpawnReplay`): the frame's own carrier effect must be
complete at its first external instruction.  A contract whose frame theorem already consumes everything
that happens below the frame — including re-entered frames of the same contract, run inside the frame's
own model transcript — needs no such split: its frame theorem gives one replay from the frame's entry
boundary to its post boundary whose observation is exactly the frame's committed subtree.

This module is that handler, for an arbitrary account-local carrier whose boundary reads the target's
storage only through its words:

* `Exec.CoreAccounting.WholeFrameReplay` — the contract's obligation: every successful non-static target
  frame replays, as a whole, with the observation of all of its committed frames;
* `Exec.CoreAccounting.staticObservedNil` (`Blanc/ExecutionModelAccounting.lean`) — below a static frame
  no committed frame is observed (the ladder's lower-depth hypothesis, at any code);
* `Exec.CoreAccounting.wholeFrameTarget` — the obligation and the static case give the target handler of
  `Exec.coreAccounting`;
* `ExecutionAccountingReplay.wholeFrameLadder` — the handler, the frame preservation theorem and the
  generic ladder give an `AccountingLadderAdmitted`, hence `configuredHistory`;
* `Exec.derivEntry` — an entry condition (the shape `Exec.FrameAdmitted` attaches to frame roots) that
  states a property of the frame's own derivation, such as the storage rows selected by a callee's
  answer; by determinism (`Exec.result_unique`, `Exec.unique`) it holds at a root once the property holds
  of that root's actual derivation (`Exec.derivEntry_of_deriv`).

The lower-depth hypothesis is used only for static frames: a non-static target frame's children are
covered by the contract's own frame theorem, never replayed a second time.
-/

namespace Blanc

open Jaune
open ExecutionAccountingReplay

/-- An entry condition stating `P` of every pc-`0` derivation from the given frame start.  Execution is
deterministic, so this is `P` of the frame's one actual derivation. -/
def Exec.derivEntry (P : Exec.Deriv → Prop) (sevm : Sevm) (pre : Devm) : Prop :=
  ∀ (out : Execution) (run : Exec 0 sevm pre out), P ⟨0, sevm, pre, out, run⟩

/-- `P` of an actual pc-`0` derivation is the derivation entry condition at its start. -/
theorem Exec.derivEntry_of_run {P : Exec.Deriv → Prop} {sevm : Sevm} {pre : Devm}
    {out : Execution} (exc : Exec 0 sevm pre out) (h : P ⟨0, sevm, pre, out, exc⟩) :
    Exec.derivEntry P sevm pre := by
  intro out' run
  cases Exec.result_unique exc run
  rw [Exec.unique run exc]
  exact h

/-- The same, for a derivation bundled with its start at pc `0`. -/
theorem Exec.derivEntry_of_deriv {P : Exec.Deriv → Prop} {D : Exec.Deriv} (pc : D.pc = 0)
    (h : P D) : Exec.derivEntry P D.sevm D.devm := by
  cases D with
  | mk dpc sevm pre exn exc =>
    dsimp only at pc
    subst pc
    exact Exec.derivEntry_of_run exc h

namespace Exec.CoreAccounting

variable {ca : Adr} {sem : CodeSem} {entry : Sevm → Devm → Prop} {C : ReplayCarrier ca}
  {V : ReplayObservation C}

/-- **The contract's whole-frame obligation.**  Every committed non-static target frame replays, from
its entry boundary to its post boundary, with exactly the observation of its committed frames (itself and
every committed frame below it, at any address).  The contract's frame theorem supplies it when it already
consumes the frame's whole subtree, re-entered frames of the contract included. -/
def WholeFrameReplay (ca : Adr) (sem : CodeSem) (entry : Sevm → Devm → Prop) (C : ReplayCarrier ca)
    (V : ReplayObservation C) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post)),
    Execution.commits (.ok post) = true →
    sem.Run sevm pre post → sevm.currentTarget = ca → CoveredFork sevm.benvStat.fork →
    sem.At ca 0 sevm pre → Exec.FrameAdmitted ca entry run → sum pre.state.bal < 2 ^ 256 →
    sevm.isStatic = false →
    ∃ steps : List C.Step, C.Replay (C.frameEntry sevm pre.state) steps (C.ofState post.state) ∧
      V.obs steps = (Exec.committedFrames run).flatMap V.frameObs

/-- **The whole-frame target handler.**  A successful target frame satisfies `CoreAccounting` for a
carrier whose boundary reads the target's storage only through its words (`ofStateGet`; the entry
boundary is the ordinary one), given the contract's `WholeFrameReplay`, that a static frame observes
nothing of itself, and that its frames spawn only by `CALL`/`STATICCALL`.  Static frames keep the
target's storage and, by the lower-depth hypothesis, observe nothing below them. -/
theorem wholeFrameTarget
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    (kinds : SpawnKinds ca sem) (whole : WholeFrameReplay ca sem entry C V)
    {sevm : Sevm} {pre post : Devm} (hrun : sem.Run sevm pre post)
    (target : sevm.currentTarget = ca)
    (deeper : ForallDeeperAtSem sevm.depth ca sem
      (fun pc s d e _ => Exec.CoreAccounting ca sem entry C V pc s d e)) :
    Exec.CoreAccounting ca sem entry C V 0 sevm pre (.ok post) := by
  intro run committed fork installed admitted
  by_cases hs : sevm.isStatic = true
  · have self : (Exec.committedFrames run).flatMap V.frameObs =
        V.frameObs (Exec.Frame.ofRun run committed) ++
          (Exec.descendantFrames run).flatMap V.frameObs := by
      rw [Exec.committedFrames, dite_eq_left committed, List.flatMap_cons]
    have hdf := staticObservedNil kinds run hrun target fork installed admitted deeper run
      (.refl _) hs
    have hself : V.frameObs (Exec.Frame.ofRun run committed) = [] := obsStatic _ hs
    have hobs : (Exec.committedFrames run).flatMap V.frameObs = [] := by
      rw [self, hdf, hself]
      rfl
    refine ⟨fun _ => hobs, fun _ => ⟨[], ?_, ?_⟩⟩
    · have hview := Exec.storageView_committedPost_eq_of_static run hs committed fork
      have heq : C.ofState (Execution.committedPost (.ok post) committed).state =
          C.ofState pre.state := ofStateGet fun k => congrFun (congrFun hview ca) k
      rw [heq, entryOfState]
      exact C.nil _
    · rw [hobs]
      exact V.obs_nil
  · have hs' : sevm.isStatic = false := by simpa only [Bool.not_eq_true] using hs
    exact ⟨fun h => absurd h hs, fun bound =>
      whole run committed hrun target fork installed admitted bound hs'⟩

end Exec.CoreAccounting


namespace ExecutionAccountingReplay

/-- **The accounting ladder of a whole-frame replay.**  The contract's frame preservation theorem
(`preserves`) and its `WholeFrameReplay`, for a carrier whose boundary reads the target's storage through
its words, give the observed accounting ladder of the deployed code; foreign frames, messages,
transactions, blocks and rollback are the generic ladder's. -/
def wholeFrameLadder {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop}
    (C : ReplayCarrier ca) (V : ReplayObservation C)
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    (tag : Nat → Option Nat → C.Tag) (frameTag : Sevm → Devm → C.Tag)
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    (obsForeign : ∀ f : Exec.Frame, f.sevm.currentTarget ≠ ca → V.frameObs f = [])
    (kinds : SpawnKinds ca c.sem) (whole : Exec.CoreAccounting.WholeFrameReplay ca c.sem entry C V)
    (preserves : c.PreservesAdmitted ca entry) : AccountingLadderAdmitted c ca entry where
  carrier := C
  append := append
  tag := tag
  preserves := preserves
  view := V
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ fork
      bound
    obtain ⟨installed, entryBound⟩ :=
      Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    have core := Exec.coreAccounting ca c.sem entry C V append frameTag
      (fun sevm state _ => entryOfState sevm state) obsForeign
      (fun hrun target deeper =>
        Exec.CoreAccounting.wholeFrameTarget entryOfState ofStateGet obsStatic kinds whole hrun
          target deeper)
    exact (core pc sevm pre out run installed run committed fork installed admitted).2 entryBound

end ExecutionAccountingReplay

end Blanc
