import Blanc.CommonProofs

/-!
# Calldata words of a fixed-shape call

The argument words at the calldata offsets of a call with one or three words, as `Sevm.dataWord`
reads them. The Curve3Pool callee answers (`Composition`) and the pool's coin/3Crv premises share
them.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc

/-- The word at calldata offset `4` of a one-argument call. -/
theorem cc_dataWord_oneWord {e : Sevm} {sel w : B256}
    (h : e.data = abiSelectorBytes sel ++ w.toBytes) : Sevm.dataWord e 4 = w := by
  have l4 := Blanc.abiSelectorBytes_length sel
  have hw := B256.length_toBytes w
  unfold Sevm.dataWord
  rw [h, show (4 : B256).toNat = 4 from rfl, List.sliceD,
    List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append,
    List.takeD_eq_take 0 (by omega), List.take_of_length_le (by omega), B256.toB256_toBytes]

/-- A three-word call's argument words. -/
theorem cc_dataWord_threeWords {e : Sevm} {sel w a x : B256}
    (h : e.data = abiSelectorBytes sel ++ w.toBytes ++ a.toBytes ++ x.toBytes) :
    Sevm.dataWord e 4 = w ∧ Sevm.dataWord e 36 = a ∧ Sevm.dataWord e 68 = x := by
  have l4 := Blanc.abiSelectorBytes_length sel
  have hw := B256.length_toBytes w
  have ha := B256.length_toBytes a
  have hx := B256.length_toBytes x
  refine ⟨?_, ?_, ?_⟩
  · unfold Sevm.dataWord
    rw [h, show (4 : B256).toNat = 4 from rfl, List.sliceD, List.append_assoc, List.append_assoc,
      List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append,
      List.takeD_eq_take 0 (by simp only [List.length_append]; omega),
      List.take_left' hw, B256.toB256_toBytes]
  · unfold Sevm.dataWord
    rw [h, show (36 : B256).toNat = 36 from rfl, List.sliceD, List.append_assoc,
      List.drop_append_of_le_length (by simp only [List.length_append]; omega),
      List.drop_of_length_le (by simp only [List.length_append]; omega), List.nil_append,
      List.takeD_eq_take 0 (by simp only [List.length_append]; omega), List.take_left' ha,
      B256.toB256_toBytes]
  · unfold Sevm.dataWord
    rw [h, show (68 : B256).toNat = 68 from rfl, List.sliceD,
      List.drop_append_of_le_length (by simp only [List.length_append]; omega),
      List.drop_of_length_le (by simp only [List.length_append]; omega), List.nil_append,
      List.takeD_eq_take 0 (by omega), List.take_of_length_le (by omega), B256.toB256_toBytes]

end Blanc.Lift.Curve3Pool
