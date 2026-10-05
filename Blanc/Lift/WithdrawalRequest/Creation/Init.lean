import Blanc.Lift.WithdrawalRequest.Layout

/-! Constructor storage is the inhibitor and an empty model queue. -/

namespace Blanc.Lift.WithdrawalRequest.Creation

open Jaune Blanc.WithdrawalRequest

theorem initial_storage :
    RepresentsStorage (Stor.empty.set 0 B256.max).get initial := by
  refine ⟨initial_coherent, ⟨by decide, by decide, by decide, by decide, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact False.elim (Nat.not_lt_zero i hi)
  · rw [Stor.get_set_self]
    rfl
  · rw [Stor.get_set_ne _ (by decide)]
    rfl
  · rw [Stor.get_set_ne _ (by decide)]
    rfl
  · rw [Stor.get_set_ne _ (by decide)]
    rfl
  · intro i hi
    exact False.elim (Nat.not_lt_zero i hi)

end Blanc.Lift.WithdrawalRequest.Creation
