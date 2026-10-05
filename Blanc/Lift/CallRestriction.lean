import Blanc.Lift.Cursor

namespace Blanc.Lift

open Jaune

/-- Check a restriction on external instruction families throughout a
synthetic tree. Internal certificate calls retain their separate references. -/
def SFunc.execsSatisfy (allowed : Xinst → Bool) : SFunc → Bool
  | .next (.exec x) f => allowed x && f.execsSatisfy allowed
  | .next _ f | .dest f | .branchTo f _ | .callNext _ f | .pcAt _ f =>
      f.execsSatisfy allowed
  | .branch f g => f.execsSatisfy allowed && g.execsSatisfy allowed
  | _ => true

/-- Restriction at the active cursor and every suspended internal return. -/
def Cursor.ExecsSatisfy (allowed : Xinst → Bool) (cursor : Cursor) : Prop :=
  cursor.f.execsSatisfy allowed = true ∧
    ∀ k ∈ cursor.K, k.f.execsSatisfy allowed = true

theorem SStep.execsSatisfy {c : Cert} {allowed : Xinst → Bool}
    (checked : ∀ f ∈ c.prog, f.execsSatisfy allowed = true)
    {before after : Cursor} (step : SStep c before after)
    (holds : before.ExecsSatisfy allowed) : after.ExecsSatisfy allowed := by
  cases step with
  | @next n f pc a a' m K hn =>
      cases n <;> simp_all only [Cursor.ExecsSatisfy, SFunc.execsSatisfy, implies_true, and_self, Bool.and_eq_true]
  | dest | toZero | pcAt => exact holds
  | zero =>
      simp only [Cursor.ExecsSatisfy, SFunc.execsSatisfy, Bool.and_eq_true] at holds
      exact ⟨holds.1.1, holds.2⟩
  | succ =>
      simp only [Cursor.ExecsSatisfy, SFunc.execsSatisfy, Bool.and_eq_true] at holds
      exact ⟨holds.1.2, holds.2⟩
  | toSucc _ lookup | jump _ lookup =>
      exact ⟨checked _ (List.mem_of_getElem? lookup), holds.2⟩
  | call cont _ lookup eqf =>
      refine ⟨checked _ (List.mem_of_getElem? lookup), ?_⟩
      intro k member
      rcases List.mem_cons.mp member with rfl | member
      · rw [eqf]
        exact holds.1
      · exact holds.2 k member
  | ret =>
      exact ⟨holds.2 _ (by simp only [List.mem_cons, true_or]), fun k member => holds.2 k (by simp only [List.mem_cons, member,
        or_true])⟩

theorem Cursor.start_execsSatisfy {c : Cert} {allowed : Xinst → Bool}
    (checked : ∀ f ∈ c.prog, f.execsSatisfy allowed = true) :
    (Cursor.start c).ExecsSatisfy allowed := by
  cases c with
  | nil => exact ⟨rfl, by simp only [start, List.not_mem_nil, IsEmpty.forall_iff, implies_true]⟩
  | cons entry rest =>
      exact ⟨checked entry.2 (by simp only [Cert.prog, List.map_cons, List.mem_cons, List.mem_map,
        Prod.exists, exists_eq_right, true_or]), by simp only [start, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true]⟩

theorem Cursor.execsSatisfy_of_reachable {c : Cert} {allowed : Xinst → Bool}
    (checked : ∀ f ∈ c.prog, f.execsSatisfy allowed = true)
    {cursor : Cursor}
    (reachable : Relation.ReflTransGen (SStep c) (Cursor.start c) cursor) :
    cursor.ExecsSatisfy allowed := by
  induction reachable with
  | refl => exact Cursor.start_execsSatisfy checked
  | tail _ step ih => exact step.execsSatisfy checked ih

/-- At every certified same-frame location, an executed external instruction
satisfies the syntactic restriction retained by the exact cursor. -/
theorem CursorOK.execsSatisfy {code : ByteArray} {c : Cert} {node : Exec.Deriv}
    {cursor : Cursor} (ok : CursorOK code c node cursor)
    {allowed : Xinst → Bool} (holds : cursor.ExecsSatisfy allowed)
    {x : Xinst} (hat : Ninst.At node.sevm.code node.pc (.exec x)) :
    allowed x = true := by
  obtain ⟨hcode, hpc, hcheck, -, -⟩ := ok
  obtain ⟨f, pc, a, m, K⟩ := cursor
  dsimp only at hpc hcheck holds
  rw [hcode, hpc] at hat
  have hjump : ∀ j : Jinst, byteAt code pc = some j.toUInt8 → False := fun j hb => by
    have hj := byteAt_jinst_at hb
    unfold Jinst.At at hj
    unfold Ninst.At at hat
    rw [hat] at hj
    cases hj
  cases f with
  | next i g =>
    simp only [checkNode, Bool.and_eq_true] at hcheck
    obtain ⟨⟨hbytes, -⟩, -⟩ := hcheck
    have hi := Ninst.at_of_slice (bytesAt_slice (ninst_bytes_ne_nil i) hbytes)
    unfold Ninst.At at hi hat
    rw [hat] at hi
    cases hi
    simp only [Cursor.ExecsSatisfy, SFunc.execsSatisfy, Bool.and_eq_true] at holds
    exact holds.1.1
  | last l =>
    have hl := byteAt_linst_at (show byteAt code pc = some l.toUInt8 by
      simpa only [checkNode, beq_iff_eq] using hcheck)
    unfold Linst.At at hl
    unfold Ninst.At at hat
    rw [hat] at hl
    cases hl
  | undefined =>
    have hnone : code.getInst pc = none := by
      simpa only [checkNode, Option.isNone_iff_eq_none] using hcheck
    unfold Ninst.At at hat
    rw [hat] at hnone
    cases hnone
  | dest g => exact (hjump _ (by simp only [checkNode, Bool.and_eq_true, beq_iff_eq] at hcheck; exact hcheck.1)).elim
  | branch g h =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hcheck; exact hcheck.1.1)).elim
    · cases hcheck
  | branchTo g k =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hcheck; exact hcheck.1.1.1.1)).elim
    · cases hcheck
  | jump k =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp only [Bool.and_eq_true, beq_iff_eq] at hcheck; exact hcheck.1.1.1)).elim
    · cases hcheck
  | callNext k g =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcheck; exact hcheck.1.1.1)).elim
    · cases hcheck
  | ret =>
    simp only [checkNode] at hcheck
    split at hcheck
    · exact (hjump _ (by simp only [Bool.and_eq_true, beq_iff_eq] at hcheck; exact hcheck.1)).elim
    · cases hcheck
  | pcAt p g =>
    simp only [checkNode, Bool.and_eq_true] at hcheck
    have hi := Ninst.at_of_slice (bytesAt_slice (ninst_bytes_ne_nil (.reg .pc)) hcheck.1.1)
    unfold Ninst.At at hi hat
    rw [hat] at hi
    cases hi

end Blanc.Lift
