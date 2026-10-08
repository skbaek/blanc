import Blanc.Lift.CursorOccurrence
import Blanc.Lift.ReachChain

namespace Blanc.Lift
open Jaune

/-- The original occurrence's exact slot retains the child-root predicate. -/
theorem CallOccurrenceStep.slotFilledWith {root : Exec.Deriv} {x : Xinst}
    (call : CallOccurrenceStep root x) : call.occurrence.slot.FilledWith (InRoots root) := by
  obtain ⟨_, primitive⟩ := Cursor.parentStep_ninstIn call.edge call.occurrence.decoded
  have located : Ninst.RunWith (InRoots root) call.occurrence.node.sevm
      call.occurrence.node.devm call.occurrence.instruction call.returned.devm :=
    primitive.mono (fun _ _ _ _ _ child r member => List.mem_cons_of_mem root
      (rawFrameDescendants_sub_of_prefix call.sameFrame r (child r member)))
  obtain ⟨slot, predicate, pc, step⟩ := located
  have filled : slot.Filled := by
    cases slot with
    | none => trivial
    | some pair => obtain ⟨evm, raw⟩ := pair; obtain ⟨run, _⟩ := predicate; exact ⟨run⟩
  have same := (occurrence_stepRun_unique call.occurrence filled
    (Ninst.stepRun_pc_irrel (by rw [call.instruction]; rfl) step)).1
  exact same.symm ▸ predicate

/-- Compatibility projection keeps the original occurrence slot. -/
theorem CallOccurrenceStep.toStepIn {root : Exec.Deriv} {x : Xinst}
    (call : CallOccurrenceStep root x) :
    StepIn root call.occurrence.node.sevm call.occurrence.node.devm
      (.exec x) call.returned.devm := by
  refine ⟨call.occurrence.slot, call.slotFilledWith, call.occurrence.node.pc, ?_⟩
  simpa only [call.instruction, call.result] using call.occurrence.stepRun

end Blanc.Lift
