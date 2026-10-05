import Blanc.Lift.Deploy
import Blanc.Lift.Vyper
import Blanc.BytesWrite
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Creation.Input

/-! Symbolic constructor memory and post-state of the 0x847e creation input, with no concrete
array unfolding. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Creation

open Jaune Blanc.Lift

/-- The registered runtime's bytes. -/
abbrev runtime : List UInt8 := Blanc.Lift.VyperNonreentrantDeployed.Fixed.code.data.toList

theorem runtime_length : runtime.length = 18320 := by decide +kernel

theorem runtime_ne_nil : runtime ≠ [] := by
  intro h
  have := runtime_length
  rw [h] at this
  exact absurd this (by decide)

theorem runtime_head : runtime.head? = some 0x60 := by decide +kernel

/-- **The copy window is the registered runtime**: `creation[27, 27 + 18320)` is `Fixed.code`. -/
theorem runtime_window : creationCode.sliceD 27 18320 0 = runtime := by
  rw [ByteArray.sliceD_eq, creationCode, ByteArray.toList_eq_toList_data, List.toList_toArray]
  have hp : constructorPrefix.length = 27 := rfl
  rw [← hp, ← runtime_length]
  exact Bytes.sliceD_append_middle constructorPrefix runtime constructorSuffix

def constructorMemory : Mem := Mem.empty.write 0 runtime

/-- The state the constructor returns from: slot 1 set to 1, the runtime in memory. -/
def constructorPost (sevm : Sevm) (b : Devm) (G : Nat) : Devm :=
  returnPost (St (afterSstore sevm b 1 1) [0, 18320] constructorMemory G) 0 18320 []

theorem constructorMemory_size : constructorMemory.size = 18336 := by
  rw [constructorMemory, Mem.size_write_of_size rfl (by decide) runtime_length]
  rfl

theorem constructorMemory_read : (constructorMemory.read 0 18320).1 = runtime := by
  rw [← runtime_length]
  exact Mem.read_write_zero Mem.empty runtime_ne_nil

/-- The constructor's exact charge: 4118 for its twelve non-`SSTORE` instructions (the
`CODECOPY` of 573 words with its memory expansion is 4082) plus the selected `SSTORE`. -/
def constructorGas (sevm : Sevm) (b : Devm) : Nat := 4118 + sstoreCost sevm b 1 1

theorem constructor_codecopy_charge (b : Devm) (G : Nat) :
    gVerylow + gasCopy * ceilDiv (18320 : B256).toNat 32 +
      (St b [0, 27, 18320] Mem.empty (G + 4082)).extCost [⟨0, 18320⟩] = 4082 := by
  rw [St.extCost_eq rfl]
  rfl

theorem constructor_return_charge (b : Devm) (G : Nat) :
    (St b [0, 18320] constructorMemory G).extCost [⟨0, 18320⟩] = 0 := by
  rw [St.extCost_eq constructorMemory_size]
  rfl

theorem constructorPost_facts (sevm : Sevm) (b : Devm) (G : Nat) :
    (constructorPost sevm b G).output = runtime ∧
    (constructorPost sevm b G).error = b.error ∧
    (constructorPost sevm b G).state = (afterSstore sevm b 1 1).state ∧
    (constructorPost sevm b G).getStor sevm.currentTarget =
      (b.getStor sevm.currentTarget).set 1 1 ∧
    (constructorPost sevm b G).gasLeft = G := by
  have h := returnPost_facts (St (afterSstore sevm b 1 1) [0, 18320] constructorMemory G) 0 18320 []
  refine ⟨?_, ?_, rfl, ?_, h.2.2.2⟩
  · unfold constructorPost
    rw [h.1]
    have e0 : (0 : B256).toNat = 0 := rfl
    have e1 : (18320 : B256).toNat = 18320 := rfl
    rw [St.memory, e0, e1]
    exact constructorMemory_read
  · exact h.2.1.trans (Blanc.afterSstore_error sevm b 1 1)
  · exact (h.2.2.1 sevm.currentTarget).trans (Blanc.afterSstore_getStor_self sevm b 1 1)

theorem constructorGas_le (sevm : Sevm) (b : Devm) : constructorGas sevm b ≤ 26218 :=
  Nat.add_le_add_left (le_trans (sstoreCost_le sevm b 1 1)
    (show gasColdSload + gasStorageSet ≤ 22100 by decide)) 4118

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Creation
