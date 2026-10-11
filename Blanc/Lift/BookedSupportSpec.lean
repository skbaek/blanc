import Blanc.Lift.BookedSpec
import Blanc.StorageOnlySpec

/-!
# A booked-sum solvency contract with a storage-only conjunct

`ContractSpecSem.ofBookedSum` states booked-sum solvency for any total `σ : Stor → Nat`.  A ledger whose
total is only meaningful over a *footprint* of tracked keys also needs a storage-only fact about the
whole word map — every nonzero word sits at a fixed or tracked slot (`SlotFootprint.Support`).
`ofBookedSumWith sem σ Q` is the spec whose invariant is `Q s ∧ σ s + v ≤ b`.  Every obligation is
the corresponding one of `ofBookedSum` plus the fact that ether movements preserve storage at the protected contract owner (`getStor_subBal_addBal`, `getStor_addBal`), so `Q` is carried by a rewrite.
-/

namespace Blanc

open Jaune

namespace ContractSpecSem

/-- Booked-sum solvency over `σ`, together with a storage-only property `Q`. -/
def ofBookedSumWith (sem : CodeSem) (σ : Stor → Nat) (Q : Stor → Prop) : ContractSpecSem :=
  { ofBookedSum sem σ with
    Inv := fun s v b => Q s ∧ BookedInv σ s v b
    inv_forget := fun h => ⟨h.1, (ofBookedSum sem σ).inv_forget h.2⟩
    inv_mono := fun h hle => ⟨h.1, (ofBookedSum sem σ).inv_mono h.2 hle⟩
    inv_recv := fun h heq => ⟨h.1, (ofBookedSum sem σ).inv_recv h.2 heq⟩
    inv_transfer := by
      intro st st' caller callee ca wad v sub ne side protection h
      refine ⟨?_, (ofBookedSum sem σ).inv_transfer sub ne side protection h.2⟩
      rw [getStor_subBal_addBal sub protection]
      exact h.1
    inv_recv_transfer := by
      intro st st' caller ca wad sub ne side protection h
      refine ⟨?_, (ofBookedSum sem σ).inv_recv_transfer sub ne side protection h.2⟩
      rw [getStor_subBal_addBal sub protection]
      exact h.1
    inv_addBal := by
      intro w ca a val v bound side protection h
      refine ⟨?_, (ofBookedSum sem σ).inv_addBal bound side protection h.2⟩
      change Q (((w.setBal a (w.bal a + val)).get ca).stor)
      rw [State.setBal_get_stor_of_protected protection]
      exact h.1 }

end ContractSpecSem

end Blanc
