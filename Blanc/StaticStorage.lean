import Blanc.ExecutionOccurrence

/-!
# Persistent-storage silence of static execution

`STATICCALL` may enter arbitrary interpreted code, including further calls.
The EVM static flag nevertheless propagates to every reached child frame, and
an `SSTORE` instruction cannot complete successfully in such a frame.  This
module packages that execution-level fact as the `Ninst.Inv` instance needed
by source proofs of read-only contracts.
-/

namespace Blanc

open Jaune

/-- The extensional persistent-storage observation used by contract
invariants.  `Stor` is a tree representation whose raw equality can distinguish
redundant zero entries; EVM storage semantics observes only `Stor.get`. -/
def Devm.storageView (state : Devm) : Adr → B256 → B256 :=
  fun owner key => (Devm.getStor state owner).get key

instance : PopBurn.Inv Devm.storageView := ⟨by
  intro words before after run
  funext owner
  funext key
  exact congrArg (fun storage : Stor => storage.get key)
    (Devm.PopBurn.getStor run owner).symm
⟩

instance : Burn.Inv Devm.storageView := ⟨by
  intro before after run
  funext owner
  funext key
  exact congrArg (fun storage : Stor => storage.get key)
    (Devm.Burn.getStor run owner).symm
⟩

instance storageView_linstHinv {terminal : Linst}
    [base : Linst.Hinv Devm.getStor Devm.getStor terminal] :
    Linst.Hinv Devm.storageView Devm.storageView terminal := ⟨by
  intro sevm before after run
  have equal := base.inv run
  funext owner
  funext key
  exact congrArg (fun storage : Stor => storage.get key)
    (congrFun equal owner)
⟩

instance storageView_ninstHinv {instruction : Ninst}
    [base : Ninst.Hinv Devm.getStor instruction] :
    Ninst.Hinv Devm.storageView instruction := ⟨by
  intro sevm before after run
  have equal := base.inv run
  funext owner
  funext key
  exact congrArg (fun storage : Stor => storage.get key)
    (congrFun equal owner)
⟩

/-- Every raw driver node below a static frame is itself static. -/
theorem Exec.rawNodes_isStatic_of_static
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hstatic : sevm.isStatic = true) :
    ∀ node ∈ Exec.rawNodes run, node.sevm.isStatic = true := by
  induction run with
  | halt _ =>
      intro node member
      simp only [Exec.rawNodes, List.mem_singleton] at member
      subst node
      exact hstatic
  | cont _ _ ih =>
      intro node member
      simp only [Exec.rawNodes, List.mem_cons] at member
      rcases member with rfl | member
      · exact hstatic
      · exact ih hstatic node member
  | doneErr _ _ _ =>
      intro node member
      simp only [Exec.rawNodes, List.mem_singleton] at member
      subst node
      exact hstatic
  | doneOk _ _ _ _ ih =>
      intro node member
      simp only [Exec.rawNodes, List.mem_cons] at member
      rcases member with rfl | member
      · exact hstatic
      · exact ih hstatic node member
  | runErr step enter child _ ih =>
      intro node member
      simp only [Exec.rawNodes, List.mem_cons] at member
      rcases member with rfl | member
      · exact hstatic
      · exact ih (Evm.step_run_isStatic step enter hstatic) node member
  | runOk step enter child _ next childIH nextIH =>
      intro node member
      simp only [Exec.rawNodes, List.mem_cons, List.mem_append] at member
      rcases member with rfl | member
      · exact hstatic
      · rcases member with member | member
        · exact childIH (Evm.step_run_isStatic step enter hstatic) node member
        · exact nextIH hstatic node member

/-- A static execution contains no successful persistent-storage write, so
its settlement-retained write chronology is empty.  Failed attempted writes
may still occur in the raw tree; they are correctly irrelevant here. -/
theorem Exec.retainedStorageWrites_eq_nil_of_static
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hstatic : sevm.isStatic = true) :
    Exec.retainedStorageWrites run = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro event member
  rcases Exec.exists_successfulSstore_of_mem_retainedStorageWrites
      (root := (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv))
      (event := event) member with ⟨write, _retained, _event⟩
  have nodeStatic : write.occurrence.node.sevm.isStatic = true :=
    Exec.rawNodes_isStatic_of_static run hstatic
      write.occurrence.node write.occurrence.reached
  have storeRun : Ninst.Run write.occurrence.node.sevm
      write.occurrence.node.devm (.reg .sstore) write.stepPost := by
    refine ⟨write.occurrence.slot, write.occurrence.filled,
      write.occurrence.node.pc, ?_⟩
    simpa only [write.instruction_eq, write.stepSuccess] using
      write.occurrence.stepRun
  have nonstatic := of_run_sstore_not_static storeRun
  rw [nodeStatic] at nonstatic
  exact Bool.noConfusion nonstatic

/-- A committing static execution has exactly its entry persistent-storage
observation at every owner and key. -/
theorem Exec.storageView_committedPost_eq_of_static
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hstatic : sevm.isStatic = true)
    (committed : Execution.commits out = true) :
    Devm.storageView (Execution.committedPost out committed) =
      Devm.storageView pre := by
  have replay := Exec.storageReplay_committedPost run committed
  rw [Exec.retainedStorageWrites_eq_nil_of_static run hstatic] at replay
  funext owner
  funext key
  simpa [Devm.storageView, Exec.StorageWrite.replayCell] using replay owner key

/-- Every successful `STATICCALL` preserves persistent storage, including the
case where it enters arbitrary interpreted code. -/
theorem Ninst.statcall_inv_getStor :
    Ninst.Inv Devm.storageView Ninst.statcall := by
  intro sevm pre post run
  rcases run with ⟨slot, filled, pc, stepRun⟩
  have xrun : Xinst.Run sevm pre .statcall slot (.ok post) := by
    simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep,
      Xinst.Run] using stepRun
  cases slot with
  | none =>
      have equal := (Xinst.none_getStor_eq xrun).symm
      funext owner
      funext key
      exact congrArg (fun storage : Stor => storage.get key)
        (congrFun equal owner)
  | some child =>
      rcases child with ⟨cevm, out⟩
      rcases filled with ⟨childRun⟩
      rcases XStep.Run.some_inv xrun with
        ⟨frame, resume, spawn, enter, resumed⟩
      have childStatic : cevm.sta.isStatic = true :=
        (Frame.enter_run_isStatic enter).trans
          (Xinst.step_statcall_spawn_isStatic spawn)
      have frameRun : RunFrame frame (.some ⟨cevm, out⟩)
          (frame.settle out) := by
        unfold RunFrame
        rw [enter]
        exact ⟨out, rfl, rfl⟩
      have replay : Exec.StorageReplay pre post [] := by
        simpa using Xinst.storageReplay_some_of_body spawn frameRun resumed.symm
          (writes := []) (fun committed owner key => by
            have equal := Exec.storageView_committedPost_eq_of_static
              childRun childStatic committed
            simpa [Devm.storageView, Exec.StorageWrite.replayCell] using
              congrFun (congrFun equal owner) key)
      funext owner
      funext key
      simpa [Devm.storageView, Exec.StorageWrite.replayCell] using
        (replay owner key).symm

instance : Ninst.Hinv Devm.storageView Ninst.statcall :=
  ⟨Ninst.statcall_inv_getStor⟩

end Blanc
