import Blanc.Lift.CursorCuts
import Blanc.ExecutionOccurrence
import Blanc.ExecDeterminism

/-! Actual call occurrences and their checked original-bytecode continuations. -/

namespace Blanc.Lift

open Jaune

/-- One actual same-frame external instruction and its returned parent state.
The occurrence retains the recursive slot used by the original execution. -/
structure CallOccurrenceStep (root : Exec.Deriv) (x : Xinst) where
  occurrence : Exec.NinstOccurrence root
  returned : Exec.Deriv
  instruction : occurrence.instruction = .exec x
  sameFrame : Exec.Deriv.ParentPrefix root occurrence.node
  edge : Exec.Deriv.ParentStep returned occurrence.node
  result : occurrence.stepResult = .ok returned.devm

/-- Move the same actual call to an earlier same-frame root. All computational
fields, including the filled recursive slot and complete step result, are kept. -/
def CallOccurrenceStep.reRoot {root tail : Exec.Deriv} {x : Xinst}
    (reached : Exec.Deriv.ParentPrefix root tail) (step : CallOccurrenceStep tail x) :
    CallOccurrenceStep root x where
  occurrence :=
    { node := step.occurrence.node
      instruction := step.occurrence.instruction
      slot := step.occurrence.slot
      stepResult := step.occurrence.stepResult
      reached := by
        obtain ⟨before, decomposition⟩ :=
          Exec.Deriv.ParentPrefix.rawNodes_decomposition reached
        rw [decomposition]
        exact List.mem_append_right before step.occurrence.reached
      decoded := step.occurrence.decoded
      filled := step.occurrence.filled
      stepRun := step.occurrence.stepRun }
  returned := step.returned
  instruction := step.instruction
  sameFrame := reached.trans step.sameFrame
  edge := step.edge
  result := step.result

/-- Re-rooting changes only the root-indexed reachability evidence. -/
theorem CallOccurrenceStep.reRoot_identity {root tail : Exec.Deriv} {x : Xinst}
    (reached : Exec.Deriv.ParentPrefix root tail) (step : CallOccurrenceStep tail x) :
    (step.reRoot reached).occurrence.node = step.occurrence.node ∧
    (step.reRoot reached).occurrence.instruction = step.occurrence.instruction ∧
    (step.reRoot reached).occurrence.slot = step.occurrence.slot ∧
    (step.reRoot reached).occurrence.stepResult = step.occurrence.stepResult ∧
    (step.reRoot reached).returned = step.returned := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Comparing a primitive witness at an occurrence fixes both its recursive
slot and its complete step result. -/
theorem occurrence_stepRun_unique {root : Exec.Deriv}
    (occurrence : Exec.NinstOccurrence root) {slot : Xlot} {result : Execution}
    (filled : slot.Filled)
    (step : Ninst.StepRun occurrence.node.pc occurrence.node.sevm
      occurrence.node.devm occurrence.instruction slot result) :
    occurrence.slot = slot ∧ occurrence.stepResult = result := by
  exact Blanc.Step.Run.unique_of_filled occurrence.filled filled occurrence.stepRun step

/-- Same-frame occurrences survive when the enclosing root commits. Raw
success alone does not assert this settlement property. -/
theorem CallOccurrenceStep.retained {root : Exec.Deriv} {x : Xinst}
    (step : CallOccurrenceStep root x) (committed : Execution.commits root.exn = true) :
    step.occurrence.Retained := by
  apply (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix
    root.exc step.occurrence.node).mpr
  exact ⟨Exec.Frame.ofRun root.exc committed,
    by simp only [Exec.committedFrames, committed, ↓reduceDIte, List.mem_cons, true_or],
    step.sameFrame⟩

end Blanc.Lift
