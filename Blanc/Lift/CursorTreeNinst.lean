import Blanc.Lift.Cursor

/-!
# The checked tree at a decoded instruction

`CursorOK.tree_of_ninst`: a cursor-placed node decoding any instruction other than `PC` sits at
that instruction's checked `next` node (`CursorOK.tree_of_exec` is the external-instruction
case); `CursorOK.tree_of_sstore` is the `SSTORE` instance. Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- A cursor-placed node decoding an instruction other than `PC` sits at that instruction's
`next` node, independently of its execution outcome. -/
theorem CursorOK.tree_of_ninst {code : ByteArray} {c : Cert} {n : Exec.Deriv}
    {κ : Cursor} (ok : CursorOK code c n κ) {i : Ninst} (notPc : i ≠ .reg .pc)
    (hat : Ninst.At n.sevm.code n.pc i) :
    ∃ g, κ.f = .next i g ∧ checkNode code c.entries κ.m κ.pc κ.a κ.f = true := by
  obtain ⟨hcode, hpc, hcheck, -, -⟩ := ok
  obtain ⟨f, pc, a, m, K⟩ := κ
  dsimp only at hpc hcheck ⊢
  rw [hcode, hpc] at hat
  have hjump : ∀ j : Jinst, byteAt code pc = some j.toUInt8 → False := fun j hb => by
    have hj := byteAt_jinst_at hb
    unfold Jinst.At at hj
    unfold Ninst.At at hat
    rw [hat] at hj
    cases hj
  cases f with
  | next i' g =>
    have hcheck' := hcheck
    simp only [checkNode, Bool.and_eq_true] at hcheck
    obtain ⟨⟨hbytes, _⟩, _⟩ := hcheck
    have hi := Ninst.at_of_slice (bytesAt_slice (ninst_bytes_ne_nil i') hbytes)
    unfold Ninst.At at hi hat
    rw [hat] at hi
    simp only [Option.some.injEq, Inst.next.injEq] at hi
    subst hi
    exact ⟨g, rfl, hcheck'⟩
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
    simp only [Option.some.injEq, Inst.next.injEq] at hi
    exact (notPc hi).elim

/-- A cursor-placed node decoding `SSTORE` sits at a checked `SSTORE` next node. -/
theorem CursorOK.tree_of_sstore {code : ByteArray} {c : Cert} {n : Exec.Deriv}
    {κ : Cursor} (ok : CursorOK code c n κ)
    (hat : Ninst.At n.sevm.code n.pc (.reg .sstore)) :
    ∃ g, κ.f = .next (.reg .sstore) g ∧
      checkNode code c.entries κ.m κ.pc κ.a κ.f = true :=
  ok.tree_of_ninst (by decide) hat

end Blanc.Lift
