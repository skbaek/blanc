import Blanc.Lift.Usdc.Constants

/-! Fixed V1 initializer header hashes and their implementation-slot bounds. -/

namespace Blanc.Lift.Usdc.InitV1ConcreteBounds

open Jaune Blanc

/-- Keccak of the name header's exact one-word encoding. -/
def slot4Hash : B256 :=
  0x8a35acfbc15ff81a39ae7d344fd709f28e8600b4aa8c65c6b64bfe7fe36bd19b

/-- Keccak of the symbol header's exact one-word encoding. -/
def slot5Hash : B256 :=
  0x036b6384b5eca791c62761152d0c79bb0604c104a5fb6f4eb0703f3154bb3db0

/-- Keccak of the currency header's exact one-word encoding. -/
def slot7Hash : B256 :=
  0xa66cc928b5edb82af9bd49922954155ab7b0942694bea4ce44661d9a8736c688

theorem slot4_hash : (4 : B256).toBytes.keccak = slot4Hash := by
  apply eq_of_beq
  decide +kernel

theorem slot5_hash : (5 : B256).toBytes.keccak = slot5Hash := by
  apply eq_of_beq
  decide +kernel

theorem slot7_hash : (7 : B256).toBytes.keccak = slot7Hash := by
  apply eq_of_beq
  decide +kernel

/-- Each actual V1 initializer header and its bounded payload region avoid the
implementation slot. The margin covers arbitrary stored old-header lengths. -/
theorem bounds {slot : B256} (member : slot ∈ [4, 5, 7]) :
    slot ≠ implSlot ∧ slot.toBytes.keccak.toNat + 2 ^ 251 < 2 ^ 256 ∧
      (implSlot.toNat < slot.toBytes.keccak.toNat ∨
        slot.toBytes.keccak.toNat + 2 ^ 251 ≤ implSlot.toNat) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp only [slot4_hash, slot5_hash, slot7_hash] <;> decide +kernel

end Blanc.Lift.Usdc.InitV1ConcreteBounds
