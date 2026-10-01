import Blanc.SystemContracts

/-! Width and ordinary-code facts for the single canonical runtime. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

theorem withdrawalRequestCode_size : Blanc.withdrawalRequestCode.size = 504 := by
  unfold Blanc.withdrawalRequestCode
  change (List.toArray _).size = 504
  rw [List.size_toArray]
  repeat' rw [List.length_cons]
  rfl

theorem withdrawalRequestCode_sem_facts :
    ¬ isValidDelegation Blanc.withdrawalRequestCode ∧ Blanc.withdrawalRequestCode.toList ≠ [] := by
  have member : (withdrawalRequestPredeployAddress, Blanc.withdrawalRequestCode) ∈
      Blanc.systemContracts := by
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  exact (Blanc.systemContracts_facts _ member).2

theorem withdrawalRequestCode_nondelegated :
    getDelegatedCodeAddress Blanc.withdrawalRequestCode = none := by
  have ordinary := withdrawalRequestCode_sem_facts.1
  simp only [getDelegatedCodeAddress, ordinary, ite_false]

theorem withdrawalRequestCode_nonempty : Blanc.withdrawalRequestCode.isEmpty = false := by
  simp only [ByteArray.isEmpty, withdrawalRequestCode_size]
  rfl

end Blanc.Lift.WithdrawalRequest
