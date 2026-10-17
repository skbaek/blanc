import Blanc.Lift.Usdc.RefineTransferNodes
import Blanc.Lift.Usdc.Families
import Blanc.Lift.Usdc.RefineShape

/-!
# Reading the family's calls back from `decodeCall`

A decoded call of the transfer and allowance family fixes the frame's selector and names its
arguments by calldata word.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc

/-- A decoded message has no value and its selector's row reads the call. -/
theorem decodeCall_row {e : Sevm} {c : Call} (h : decodeCall e = some c) :
    e.value = 0 ∧ ∃ r ∈ rows, r.sel = Sevm.selector e ∧ r.read e = c := by
  unfold decodeCall at h
  by_cases h0 : e.value ≠ 0 ∨ e.data.length < 4
  · rw [ite_eq_left h0] at h
    cases h
  · rw [ite_eq_right h0] at h
    have v0 : e.value = 0 := by
      by_contra hv
      exact h0 (Or.inl hv)
    split at h
    · cases h
    · rename_i r hr
      by_cases hl : 4 + 32 * r.headWords ≤ e.data.length
      · rw [ite_eq_left hl] at h
        cases h
        have hp := List.find?_some hr
        exact ⟨v0, r, List.mem_of_find?_eq_some hr, of_decide_eq_true hp, rfl⟩
      · rw [ite_eq_right hl] at h
        cases h

theorem decode_transfer {e : Sevm} {dst v : _} (h : decodeCall e = some (.transfer dst v)) :
    Sevm.selector e = 0xa9059cbb ∧ dst = (Sevm.dataWord e 4).toAdr ∧ v = (Sevm.dataWord e 36).toNat := by
  obtain ⟨-, r, hm, hs, hr⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | (cases hr; done) | (cases hr; exact ⟨hs.symm, rfl, rfl⟩)

theorem decode_transferFrom {e : Sevm} {src dst v : _} (h : decodeCall e = some (.transferFrom src dst v)) :
    Sevm.selector e = 0x23b872dd ∧ src = (Sevm.dataWord e 4).toAdr ∧ dst = (Sevm.dataWord e 36).toAdr ∧ v = (Sevm.dataWord e 68).toNat := by
  obtain ⟨-, r, hm, hs, hr⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | (cases hr; done) | (cases hr; exact ⟨hs.symm, rfl, rfl, rfl⟩)

theorem decode_approve {e : Sevm} {s v : _} (h : decodeCall e = some (.approve s v)) :
    Sevm.selector e = 0x095ea7b3 ∧ s = (Sevm.dataWord e 4).toAdr ∧ v = (Sevm.dataWord e 36).toNat := by
  obtain ⟨-, r, hm, hs, hr⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | (cases hr; done) | (cases hr; exact ⟨hs.symm, rfl, rfl⟩)

theorem decode_increaseAllowance {e : Sevm} {s v : _} (h : decodeCall e = some (.increaseAllowance s v)) :
    Sevm.selector e = 0x39509351 ∧ s = (Sevm.dataWord e 4).toAdr ∧ v = (Sevm.dataWord e 36).toNat := by
  obtain ⟨-, r, hm, hs, hr⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | (cases hr; done) | (cases hr; exact ⟨hs.symm, rfl, rfl⟩)

theorem decode_decreaseAllowance {e : Sevm} {s v : _} (h : decodeCall e = some (.decreaseAllowance s v)) :
    Sevm.selector e = 0xa457c2d7 ∧ s = (Sevm.dataWord e 4).toAdr ∧ v = (Sevm.dataWord e 36).toNat := by
  obtain ⟨-, r, hm, hs, hr⟩ := decodeCall_row h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | (cases hr; done) | (cases hr; exact ⟨hs.symm, rfl, rfl⟩)

end Blanc.Lift.Usdc
