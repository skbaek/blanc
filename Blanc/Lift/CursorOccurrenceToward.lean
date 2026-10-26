import Blanc.Lift.CursorOccurrence

/-!
# Actual call returns before a later same-frame SSTORE

The supplied parent edge, or the same-frame prefix to a later SSTORE,
provides the actual return. The enclosing execution may subsequently fail.
The occurrence keeps the original recursive slot and complete step result.
-/

namespace Blanc.Lift

open Jaune

/-- Cross an actual same-frame parent edge at a checked external instruction.
No successful final outcome is needed: the edge supplies the actual return. -/
theorem cursor_call_occurrence_of_parentStep_noStateGas
    {code : ByteArray} {c : Cert} (checked : Cert.check code c = true)
    {root F N : Exec.Deriv} {κ : Cursor}
    (reached : Exec.Deriv.ParentPrefix root F) (ok : CursorOK code c F κ)
    {x : Xinst} {f : SFunc} (tree : κ.f = .next (.exec x) f)
    (edge : Exec.Deriv.ParentStep N F)
    (hsg : F.sevm.benvStat.rules.stateGas = none) :
    ∃ (call : CallOccurrenceStep root x) (κ' : Cursor),
      call.occurrence.node = F ∧ call.returned = N ∧
      N.pc = F.pc + (.exec x : Ninst).size ∧
      Ninst.RunWith (Cursor.DescOf F) F.sevm F.devm (.exec x) N.devm ∧
      SStep c κ κ' ∧
      ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
        (κ.conf F.devm) (κ'.conf N.devm) ∧
      CursorOK code c N κ' := by
  have decoded := ok.ninstAt_of_next tree
  obtain ⟨before, decomposition⟩ :=
    Blanc.Exec.Deriv.ParentPrefix.rawNodes_decomposition reached
  have member : F ∈ Exec.rawNodes root.exc := by
    rw [decomposition]
    exact List.mem_append_right before (Exec.mem_rawNodes_self F.exc)
  obtain ⟨occurrence, sameNode, instruction⟩ :=
    Exec.exists_ninstOccurrence_of_mem_rawNodes member decoded
  obtain ⟨pc, primitive⟩ := Cursor.parentStep_ninstIn edge decoded
  obtain ⟨slot, filled, stepPc, stepRun⟩ := primitive.toRun
  have actual : Ninst.StepRun occurrence.node.pc occurrence.node.sevm
      occurrence.node.devm occurrence.instruction slot (.ok N.devm) := by
    rw [sameNode, instruction]
    exact Ninst.stepRun_pc_irrel rfl stepRun
  let call : CallOccurrenceStep root x :=
    { occurrence := occurrence
      returned := N
      instruction := instruction
      sameFrame := sameNode.symm ▸ reached
      edge := sameNode.symm ▸ edge
      result := (occurrence_stepRun_unique occurrence filled actual).2 }
  obtain ⟨κ', synthetic, stateful, placed⟩ :=
    cursor_stepS_noStateGas checked ok edge hsg
  exact ⟨call, κ', sameNode, rfl, pc, primitive, synthetic, stateful, placed⟩

/-- A checked call before a same-frame SSTORE has actually returned into the
parent continuation, even if the enclosing frame eventually reverts. This
asserts neither a set success flag nor a committing child settlement. -/
theorem cursor_call_occurrence_toward_sstore_noStateGas
    {code : ByteArray} {c : Cert} (checked : Cert.check code c = true)
    {root F target : Exec.Deriv} {κ : Cursor}
    (reached : Exec.Deriv.ParentPrefix root F) (ok : CursorOK code c F κ)
    {x : Xinst} {f : SFunc} (tree : κ.f = .next (.exec x) f)
    (toward : Exec.Deriv.ParentPrefix F target)
    (store : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (hsg : F.sevm.benvStat.rules.stateGas = none) :
    ∃ (call : CallOccurrenceStep root x) (κ' : Cursor),
      call.occurrence.node = F ∧
      Exec.Deriv.ParentPrefix call.returned target ∧
      call.returned.pc = F.pc + (.exec x : Ninst).size ∧
      Ninst.RunWith (Cursor.DescOf F) F.sevm F.devm
        (.exec x) call.returned.devm ∧
      SStep c κ κ' ∧
      ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
        (κ.conf F.devm) (κ'.conf call.returned.devm) ∧
      CursorOK code c call.returned κ' := by
  cases toward with
  | refl =>
      have decoded := ok.ninstAt_of_next tree
      have impossible : (.exec x : Ninst) = .reg .sstore :=
        Inst.next.inj (Option.some.inj (decoded.symm.trans store))
      cases impossible
  | @step F next target edge rest =>
      obtain ⟨call, κ', node, returned, pc, primitive, synthetic, stateful, placed⟩ :=
        cursor_call_occurrence_of_parentStep_noStateGas checked reached ok tree edge hsg
      refine ⟨call, κ', node, ?_, ?_, ?_, synthetic, ?_, ?_⟩
      · rw [returned]
        exact rest
      · rw [returned]
        exact pc
      · rw [returned]
        exact primitive
      · rw [returned]
        exact stateful
      · rw [returned]
        exact placed

end Blanc.Lift
