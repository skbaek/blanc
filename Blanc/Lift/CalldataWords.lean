import Blanc.CommonProofs.Walk

/-!
Words and length of arbitrary selector-plus-two-word calldata. The selector
length fact is the existing shared Blanc.abiSelectorBytes_length.
-/

namespace Blanc.Lift

open Jaune Blanc

/-- A two-word call's argument words. -/
theorem dataWord_twoWords {e : Sevm} {sel w a : B256}
    (h : e.data = abiSelectorBytes sel ++ w.toBytes ++ a.toBytes) :
    Sevm.dataWord e 4 = w ∧ Sevm.dataWord e 36 = a ∧ e.data.length = 68 := by
  have l4 := abiSelectorBytes_length sel
  refine ⟨?_, ?_, ?_⟩
  · unfold Sevm.dataWord
    rw [h, show (4 : B256).toNat = 4 from rfl, List.sliceD, List.append_assoc,
      List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append,
      List.takeD_eq_take 0 (by simp only [List.length_append, B256.length_toBytes]; omega),
      List.take_left' (B256.length_toBytes w), B256.toB256_toBytes]
  · unfold Sevm.dataWord
    rw [h, show (36 : B256).toNat = 36 from rfl, List.sliceD,
      List.drop_append_of_le_length (by simp only [List.length_append, B256.length_toBytes]; omega),
      List.drop_of_length_le (by simp only [List.length_append, B256.length_toBytes]; omega),
      List.nil_append, List.takeD_eq_take 0 (by simp only [B256.length_toBytes]; omega),
      List.take_of_length_le (by simp only [B256.length_toBytes]; omega), B256.toB256_toBytes]
  · rw [h]
    simp only [List.length_append, B256.length_toBytes, l4]

end Blanc.Lift
