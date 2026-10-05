import Blanc.Lift.Deploy
import Blanc.Lift.Vyper
import Blanc.ForwardCall
import Blanc.BytesWrite
import Blanc.Lift.WithdrawalRequest.Creation.Input
import Blanc.Lift.WithdrawalRequest.CodeFacts

/-! Symbolic constructor memory and post-state, with no concrete array unfolding. -/

namespace Blanc.Lift.WithdrawalRequest.Creation

open Jaune Blanc.Lift

def constructorMemory : Mem := Mem.empty.write 0 Blanc.withdrawalRequestCode.toList

def constructorPost (sevm : Sevm) (b : Devm) (G : Nat) : Devm :=
  returnPost (St (afterSstore sevm b 0 B256.max) [0, 504] constructorMemory G) 0 504 []

theorem runtime_length : Blanc.withdrawalRequestCode.toList.length = 504 := by
  rw [ByteArray.toList_eq_toList_data, Array.length_toList]
  exact withdrawalRequestCode_size

theorem runtime_window : creationCode.sliceD 45 504 0 = Blanc.withdrawalRequestCode.toList := by
  rw [ByteArray.sliceD_eq, creationCode, ByteArray.toList_eq_toList_data, List.toList_toArray]
  have hp : constructorPrefix.length = 45 := by rfl
  rw [← hp, ← runtime_length]
  simpa only [List.append_nil] using
    Bytes.sliceD_append_middle constructorPrefix Blanc.withdrawalRequestCode.toList []

theorem constructorMemory_size : constructorMemory.size = 512 := by
  rw [constructorMemory, Mem.size_write_of_size rfl (by decide) runtime_length]
  rfl

theorem constructorMemory_read : (constructorMemory.read 0 504).1 = Blanc.withdrawalRequestCode.toList := by
  rw [← runtime_length]
  exact Mem.read_write_zero Mem.empty withdrawalRequestCode_sem_facts.2

def constructorGas (sevm : Sevm) (b : Devm) : Nat := 117 + sstoreCost sevm b 0 B256.max

theorem constructor_codecopy_charge (b : Devm) (G : Nat) :
    gVerylow + gasCopy * ceilDiv (504 : B256).toNat 32 +
      (St b [0, 45, 504, 504] Mem.empty (G + 99)).extCost [⟨0, 504⟩] = 99 := by
  rw [St.extCost_eq rfl]
  rfl

theorem constructor_return_charge (b : Devm) (G : Nat) :
    (St b [0, 504] constructorMemory G).extCost [⟨0, 504⟩] = 0 := by
  rw [St.extCost_eq constructorMemory_size]
  rfl

theorem constructorPost_facts (sevm : Sevm) (b : Devm) (G : Nat) :
    (constructorPost sevm b G).output = Blanc.withdrawalRequestCode.toList ∧
    (constructorPost sevm b G).error = b.error ∧
    (constructorPost sevm b G).getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set 0 B256.max ∧
    (constructorPost sevm b G).gasLeft = G := by
  have h := returnPost_facts (St (afterSstore sevm b 0 B256.max) [0, 504] constructorMemory G) 0 504 []
  refine ⟨?_, ?_, ?_, h.2.2.2⟩
  · exact h.1.trans constructorMemory_read
  · exact h.2.1.trans (Blanc.afterSstore_error sevm b 0 B256.max)
  · exact (h.2.2.1 sevm.currentTarget).trans (Blanc.afterSstore_getStor_self sevm b 0 B256.max)

theorem constructorGas_le (sevm : Sevm) (b : Devm) : constructorGas sevm b ≤ 22217 := by
  exact Nat.add_le_add_left (sstoreCost_le sevm b 0 B256.max) 117

end Blanc.Lift.WithdrawalRequest.Creation
