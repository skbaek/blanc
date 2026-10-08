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

/-- Cross a checked external next node at its actual same-frame occurrence.
Neither the returned machine state nor a child slot is supplied as a premise. -/
theorem cursor_next_call_occurrence_forward {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {root F : Exec.Deriv} {κ : Cursor}
    (reached : Exec.Deriv.ParentPrefix root F) (ok : CursorOK code c F κ)
    {x : Xinst} {f : SFunc} (tree : κ.f = .next (.exec x) f)
    {post : Devm} (success : F.exn = .ok post)
    (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ (step : CallOccurrenceStep root x) (κ' : Cursor),
      step.occurrence.node = F ∧
      step.returned.pc = F.pc + (.exec x : Ninst).size ∧
      Ninst.RunWith (Cursor.DescOf F) F.sevm F.devm (.exec x) step.returned.devm ∧
      SStep c κ κ' ∧
      ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
        (κ.conf F.devm) (κ'.conf step.returned.devm) ∧
      CursorOK code c step.returned κ' := by
  have decoded := ok.ninstAt_of_next tree
  obtain ⟨before, decomposition⟩ :=
    Exec.Deriv.ParentPrefix.rawNodes_decomposition reached
  have member : F ∈ Exec.rawNodes root.exc := by
    rw [decomposition]
    exact List.mem_append_right before (Exec.mem_rawNodes_self F.exc)
  obtain ⟨occurrence, sameNode, instruction⟩ :=
    Exec.exists_ninstOccurrence_of_mem_rawNodes member decoded
  obtain ⟨returned, κ', edge, pc, primitive, synthetic, stateful, placed⟩ :=
    cursor_next_forward checked ok tree success fork
  have result : occurrence.stepResult = .ok returned.devm := by
    obtain ⟨slot, filled, stepPc, step⟩ := primitive.toRun
    have actual : Ninst.StepRun occurrence.node.pc occurrence.node.sevm
        occurrence.node.devm occurrence.instruction slot (.ok returned.devm) := by
      rw [sameNode, instruction]
      exact Ninst.stepRun_pc_irrel rfl step
    exact (occurrence_stepRun_unique occurrence filled actual).2
  let step : CallOccurrenceStep root x :=
    { occurrence := occurrence
      returned := returned
      instruction := instruction
      sameFrame := by rw [sameNode]; exact reached
      edge := by rw [sameNode]; exact edge
      result := result }
  exact ⟨step, κ', sameNode, pc, primitive, synthetic, stateful, placed⟩

end Blanc.Lift
