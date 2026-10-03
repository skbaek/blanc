import Blanc.MemoryLayout
import Blanc.Lift.CopyLoop
import Blanc.Lift.MemMap

/-! Selected gas of ordered primitive writes, with actual allocation at each step. -/

namespace Blanc.MemoryStage

open Jaune

/-- Ordered primitive writes preserve word-aligned allocation. -/
theorem applyMemory_aligned (stage : MemoryStage) (memory : Mem)
    (aligned : memory.size % 32 = 0) :
    (stage.applyMemory memory).size % 32 = 0 := by
  induction stage generalizing memory with
  | nil => exact aligned
  | cons write rest ih =>
    rw [applyMemory_cons]
    apply ih
    rw [Mem.size_write_of_size rfl aligned rfl]
    exact memExtSize_mod_32 aligned

/-- Every nonempty access within an aligned bound keeps allocation within it. -/
theorem memExtsSize_le {windows : List (Nat × Nat)} {initial bound : Nat}
    (aligned : bound % 32 = 0) (start : initial ≤ bound)
    (covered : ∀ w ∈ windows, w.1 + w.2 ≤ bound) :
    memExtsSize initial windows ≤ bound := by
  induction windows generalizing initial with
  | nil => exact start
  | cons w rest ih =>
    apply ih
    · unfold memExtSize
      split
      · exact start
      · have first := Lift.ceilDiv32_mono start
        have next := Lift.ceilDiv32_mono (covered w (List.mem_cons_self))
        unfold ceilDiv at first next ⊢
        rw [ite_eq_left aligned] at first next
        have product := Nat.div_mul_le_self bound 32
        omega
    · intro w hw
      exact covered w (List.mem_cons_of_mem _ hw)

/-- An actual nonempty access forces allocation to cover its rounded end. -/
theorem memExtsSize_ge_window {windows : List (Nat × Nat)} {w : Nat × Nat}
    (member : w ∈ windows) (positive : 0 < w.2) (initial : Nat) :
    ceil32 (w.1 + w.2) ≤ memExtsSize initial windows := by
  induction windows generalizing initial with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst first
      have grows := Lift.memExtsSize_ge (memExtSize initial w.1 w.2) rest
      have lower : ceil32 (w.1 + w.2) ≤ memExtSize initial w.1 w.2 := by
        rw [ceil32_eq_mul]
        unfold memExtSize ceilDiv
        rw [ite_eq_right (by omega : w.2 ≠ 0)]
        split <;> split <;> omega
      exact Nat.le_trans lower grows
    · exact ih later _

/-- The selected base charge and expansion at each write in execution order. -/
def selectedGas (stage : MemoryStage) (memory : Mem) : Nat :=
  match stage with
  | [] => 0
  | write :: rest =>
    gVerylow + (calculateMemoryGasCost (memExtSize memory.size write.1 write.2.length) -
      calculateMemoryGasCost memory.size) +
      selectedGas rest (memory.write write.1 write.2)

/-- Sequential expansion charges telescope; empty writes retain their base charge. -/
theorem selectedGas_eq (stage : MemoryStage) (memory : Mem)
    (aligned : memory.size % 32 = 0) :
    selectedGas stage memory = gVerylow * stage.length +
      (calculateMemoryGasCost (stage.applyMemory memory).size -
        calculateMemoryGasCost memory.size) := by
  induction stage generalizing memory with
  | nil => simp only [selectedGas, List.length_nil, Nat.mul_zero,
      applyMemory_nil, Nat.sub_self, Nat.add_zero]
  | cons write rest ih =>
    have size : (memory.write write.1 write.2).size =
        memExtSize memory.size write.1 write.2.length :=
      Mem.size_write_of_size rfl aligned rfl
    have aligned' : (memory.write write.1 write.2).size % 32 = 0 := by
      rw [size]
      exact memExtSize_mod_32 aligned
    have first := Lift.calculateMemoryGasCost_mono
      (Lift.memExtSize_ge memory.size write.1 write.2.length)
    have later := Lift.calculateMemoryGasCost_mono
      (Lift.memExtsSize_ge (memory.write write.1 write.2).size (footprint rest))
    rw [← applyMemory_size rest _ aligned'] at later
    rw [← size] at first
    simp only [selectedGas, List.length_cons, applyMemory_cons]
    rw [ih _ aligned', ← size]
    rw [Nat.mul_add, Nat.mul_one]
    omega

end Blanc.MemoryStage
