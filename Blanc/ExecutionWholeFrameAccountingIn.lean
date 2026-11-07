import Blanc.Lift.RetainedTargetCompleteness
import Blanc.ExecutionWholeFrameAccounting
import Blanc.ExecutionAccountingCoreIn
import Blanc.ExecutionAccountingMidHistoryIn

/-!
# The whole-frame handler over a selected fork domain

`Blanc/ExecutionWholeFrameAccounting.lean` over a domain `F` without state gas, for a carrier whose
frames observe nothing when static. The modern handler proves a static frame's emptiness through the
lower-depth hypothesis and `SpawnKinds`; here every committed frame of a static run is static
(`Exec.committedFrames_isStatic`), so `obsStatic` alone closes it, whatever the frame spawns.

* `Exec.CoreAccounting.WholeFrameReplayIn` — the contract's obligation;
* `Exec.CoreAccounting.wholeFrameTargetIn` — the target handler of `Exec.coreAccountingIn`;
* `ExecutionAccountingReplay.wholeFrameLadderIn` — the ladder, hence `midHistoryIn`.

Nothing here mentions a contract.
-/

namespace Blanc

open Jaune
open ExecutionAccountingReplay

/-- Every committed frame of a static run is static. -/
theorem Exec.committedFrames_isStatic {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hs : sevm.isStatic = true) :
    ∀ D ∈ Exec.committedFrames run, D.sevm.isStatic = true := by
  intro D member
  unfold Exec.committedFrames at member
  split at member
  · rcases List.mem_cons.mp member with rfl | hd
    · exact hs
    · exact Blanc.Exec.descendantFrames_isStatic run hs D hd
  · exact absurd member (List.not_mem_nil)

namespace Exec.CoreAccounting

variable {ca : Adr} {sem : CodeSem} {entry : Sevm → Devm → Prop} {C : ReplayCarrier ca}
  {V : ReplayObservation C}

/-- `WholeFrameReplay` over the fork domain `F`. -/
def WholeFrameReplayIn (F : Fork → Prop) (ca : Adr) (sem : CodeSem) (entry : Sevm → Devm → Prop)
    (C : ReplayCarrier ca) (V : ReplayObservation C) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post)),
    Execution.commits (.ok post) = true →
    sem.Run sevm pre post → sevm.currentTarget = ca → F sevm.benvStat.fork →
    sem.At ca 0 sevm pre → Exec.FrameAdmitted ca entry run → sum pre.state.bal < 2 ^ 256 →
    sevm.isStatic = false →
    ∃ steps : List C.Step, C.Replay (C.frameEntry sevm pre.state) steps (C.ofState post.state) ∧
      V.obs steps = (Exec.committedFrames run).flatMap V.frameObs

/-- **The whole-frame target handler over `F`.** -/
theorem wholeFrameTargetIn {F : Fork → Prop}
    (hsgF : ∀ {f : Fork}, F f → (Fork.ruleSet f).stateGas = none)
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    (whole : WholeFrameReplayIn F ca sem entry C V)
    {sevm : Sevm} {pre post : Devm} (hrun : sem.Run sevm pre post)
    (target : sevm.currentTarget = ca) :
    Exec.CoreAccountingIn F ca sem entry C V 0 sevm pre (.ok post) := by
  intro run committed fork installed admitted
  have rootNonempty : (pre.getCode ca).toList ≠ [] := fun empty =>
    sem.ne_nil (installed.1.symm.trans (congrArg some empty)) rfl
  by_cases hs : sevm.isStatic = true
  · have hobs : (Exec.committedFrames run).flatMap V.frameObs = [] :=
      List.flatMap_eq_nil_iff.mpr fun D member => obsStatic D (Exec.committedFrames_isStatic run hs D member)
    refine ⟨fun _ => hobs, fun _ => ⟨[], ?_, ?_⟩⟩
    · have hview := Exec.getStor_committedPost_eq_of_static_protected_noStateGas run hs committed
        (hsgF fork) ca (State.Protected.of_code_ne_nil rootNonempty)
      have heq : C.ofState (Execution.committedPost (.ok post) committed).state =
          C.ofState pre.state := ofStateGet fun k => congrArg (fun stor => stor.get k) hview
      rw [heq, entryOfState]
      exact C.nil _
    · rw [hobs]
      exact V.obs_nil
  · have hs' : sevm.isStatic = false := by simpa only [Bool.not_eq_true] using hs
    exact ⟨fun h => absurd h hs, fun bound =>
      whole run committed hrun target fork installed admitted bound hs'⟩

end Exec.CoreAccounting

namespace ExecutionAccountingReplay

/-- **The accounting ladder of a whole-frame replay over `F`.** -/
def wholeFrameLadderIn {F : Fork → Prop}
    (hsgF : ∀ {f : Fork}, F f → (Fork.ruleSet f).stateGas = none)
    {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop}
    (C : ReplayCarrier ca) (V : ReplayObservation C)
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    (tag : Nat → Option Nat → C.Tag) (frameTag : Sevm → Devm → C.Tag)
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    (obsForeign : ∀ f : Exec.Frame, f.sevm.currentTarget ≠ ca → V.frameObs f = [])
    (whole : Exec.CoreAccounting.WholeFrameReplayIn F ca c.sem entry C V)
    (preserves : c.PreservesAdmittedIn F ca entry) : AccountingLadderAdmittedIn F c ca entry where
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
    have core := Exec.coreAccountingIn F ca c.sem entry C V append frameTag
      (fun sevm state _ => entryOfState sevm state) obsForeign hsgF
      (fun hrun target _ =>
        Exec.CoreAccounting.wholeFrameTargetIn hsgF entryOfState ofStateGet obsStatic whole hrun
          target)
    exact (core pc sevm pre out run installed run committed fork installed admitted).2 entryBound

end ExecutionAccountingReplay

end Blanc
