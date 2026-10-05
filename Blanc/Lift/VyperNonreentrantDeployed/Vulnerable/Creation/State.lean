import Blanc.Lift.Deploy
import Blanc.Lift.Vyper
import Blanc.BytesWrite
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Creation.Input

/-! Symbolic constructor memory and post-state of the 0x6326 creation input, with no concrete
array unfolding. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Creation

open Jaune Blanc.Lift

/-- The registered runtime's bytes. -/
abbrev runtime : List UInt8 := Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code.data.toList

theorem runtime_length : runtime.length = 17535 := by decide +kernel

theorem runtime_ne_nil : runtime ≠ [] :=
  List.ne_nil_of_length_pos (by rw [runtime_length]; decide)

theorem runtime_head : runtime.head? = some 0x60 := by decide +kernel

/-- **The copy window is the registered runtime**: `creation[10, 10 + 17535)` is
`Vulnerable.code`. -/
theorem runtime_window : creationCode.sliceD 10 17535 0 = runtime := by
  rw [ByteArray.sliceD_eq, creationCode, ByteArray.toList_eq_toList_data, List.toList_toArray]
  have hp : constructorPrefix.length = 10 := rfl
  rw [← hp, ← runtime_length]
  exact Bytes.sliceD_append_middle constructorPrefix runtime constructorSuffix

def constructorMemory : Mem := Mem.empty.write 0 runtime

/-- The state the constructor returns from: slot 10 (`fee`) set to 31337, the runtime in
memory. -/
def constructorPost (sevm : Sevm) (b : Devm) (G : Nat) : Devm :=
  returnPost (St (afterSstore sevm b 10 31337) [0, 17535] constructorMemory G) 0 17535 []

theorem constructorMemory_size : constructorMemory.size = 17536 := by
  rw [constructorMemory, Mem.size_write_of_size rfl (by decide) runtime_length]
  rfl

theorem constructorMemory_read : (constructorMemory.read 0 17535).1 = runtime := by
  rw [← runtime_length]
  exact Mem.read_write_zero Mem.empty runtime_ne_nil

/-- The constructor's exact charge: 3922 for its sixteen non-`SSTORE` instructions (the
`CODECOPY` of 548 words with its memory expansion is 3877) plus the selected `SSTORE`. -/
def constructorGas (sevm : Sevm) (b : Devm) : Nat := 3922 + sstoreCost sevm b 10 31337

theorem constructor_codecopy_charge (b : Devm) (G : Nat) :
    gVerylow + gasCopy * ceilDiv (17535 : B256).toNat 32 +
      (St b [0, 10, 17535] Mem.empty (G + 3877)).extCost [⟨0, 17535⟩] = 3877 := by
  rw [St.extCost_eq rfl]
  rfl

theorem constructor_return_charge (b : Devm) (G : Nat) :
    (St b [0, 17535] constructorMemory G).extCost [⟨0, 17535⟩] = 0 := by
  rw [St.extCost_eq constructorMemory_size]
  rfl

theorem constructorPost_facts (sevm : Sevm) (b : Devm) (G : Nat) :
    (constructorPost sevm b G).output = runtime ∧
    (constructorPost sevm b G).error = b.error ∧
    (constructorPost sevm b G).state = (afterSstore sevm b 10 31337).state ∧
    (constructorPost sevm b G).gasLeft = G := by
  have h := returnPost_facts
    (St (afterSstore sevm b 10 31337) [0, 17535] constructorMemory G) 0 17535 []
  refine ⟨?_, h.2.1.trans (Blanc.afterSstore_error sevm b 10 31337), rfl, h.2.2.2⟩
  unfold constructorPost
  rw [h.1]
  have e0 : (0 : B256).toNat = 0 := rfl
  have e1 : (17535 : B256).toNat = 17535 := rfl
  rw [St.memory, e0, e1]
  exact constructorMemory_read

theorem constructorGas_le (sevm : Sevm) (b : Devm) : constructorGas sevm b ≤ 26022 :=
  Nat.add_le_add_left (le_trans (sstoreCost_le sevm b 10 31337)
    (show gasColdSload + gasStorageSet ≤ 22100 by decide)) 3922

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Creation
