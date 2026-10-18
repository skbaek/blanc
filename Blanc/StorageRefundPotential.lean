import Blanc.StorageRefund
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The refund potential: `SSTORE` never lowers it

Jaune's EIP-2200 refund counter (`sstoreNewRefundCounter`) can go down: re-filling a slot whose
transaction-original value is nonzero and which an earlier write in the transaction cleared takes
the clear refund back.  It never goes down for nothing: every such take-back undoes a clear.
`refundPotential` makes that exact.  Over a finite key set `K` covering every slot of `a` with a
nonzero original value, the potential of a machine is its refund counter less the clear refund for
each slot of `a` that is currently cleared (original nonzero, current zero).

* `refundPotential_afterSstore`: an `SSTORE` by a frame running at `a`, of any key and value,
  never lowers the potential;
* `refundCounter_nonneg_of_potential`: a nonnegative potential bounds the counter below by zero.

So an invariant "potential `≥ 0`" survives every `SSTORE` of the frame — what a world invariant
closed under the frame's own steps needs to deliver a nonnegative refund at the frame's end.
-/

namespace Blanc

open Jaune

/-- The slots of `a` among `K` that are currently cleared: original value nonzero (as an `SSTORE`
sentry reads it), current value zero. -/
def clearedCount (sevm : Sevm) (b : Devm) (a : Adr) (K : Finset B256) : Nat :=
  ∑ k ∈ K, if b.getOrigStorVal sevm a k ≠ 0 ∧ b.getStorVal a k = 0 then 1 else 0

/-- **The refund potential** of `b` at `a` over `K`. -/
def refundPotential (sevm : Sevm) (b : Devm) (a : Adr) (K : Finset B256) : Int :=
  b.refundCounter - (sevm.benvStat.rules.gas.storageClearRefund : Int) * clearedCount sevm b a K

theorem refundCounter_nonneg_of_potential {sevm : Sevm} {b : Devm} {a : Adr} {K : Finset B256}
    (h : 0 ≤ refundPotential sevm b a K) : 0 ≤ b.refundCounter := by
  unfold refundPotential at h
  have h1 : (0 : Int) ≤ (sevm.benvStat.rules.gas.storageClearRefund : Int) :=
    Int.natCast_nonneg _
  have h2 : (0 : Int) ≤ (clearedCount sevm b a K : Int) := Int.natCast_nonneg _
  have h3 := Int.mul_nonneg h1 h2
  omega

/-- The cleared count reads only the created-account set and the storage of `a`. -/
theorem clearedCount_congr {sevm : Sevm} {b b' : Devm} {a : Adr} {K : Finset B256}
    (hc : b'.createdAccounts = b.createdAccounts) (hs : Devm.getStor b' a = Devm.getStor b a) :
    clearedCount sevm b' a K = clearedCount sevm b a K := by
  unfold clearedCount
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [getOrigStorVal_congr_created a k hc]
  have hv : b'.getStorVal a k = b.getStorVal a k := by
    change (Devm.getStor b' a).get k = (Devm.getStor b a).get k
    rw [hs]
  rw [hv]

/-- A machine whose refund counter moved by `x`, over the same created accounts and storage of
`a`, moved its potential by `x`. -/
theorem refundPotential_add {sevm : Sevm} {b b' : Devm} {a : Adr} {K : Finset B256} {x : Int}
    (hr : b'.refundCounter = b.refundCounter + x) (hc : b'.createdAccounts = b.createdAccounts)
    (hs : Devm.getStor b' a = Devm.getStor b a) :
    refundPotential sevm b' a K = refundPotential sevm b a K + x := by
  unfold refundPotential
  rw [hr, clearedCount_congr hc hs]
  generalize (sevm.benvStat.rules.gas.storageClearRefund : Int) *
    (clearedCount sevm b a K : Int) = m
  omega

/-- The potential reads only the refund counter, the created-account set and the storage of `a`. -/
theorem refundPotential_congr {sevm : Sevm} {b b' : Devm} {a : Adr} {K : Finset B256}
    (hr : b'.refundCounter = b.refundCounter) (hc : b'.createdAccounts = b.createdAccounts)
    (hs : Devm.getStor b' a = Devm.getStor b a) :
    refundPotential sevm b' a K = refundPotential sevm b a K := by
  rw [refundPotential_add (x := 0) (by rw [hr, Int.add_zero]) hc hs, Int.add_zero]

/-- No slot is cleared while every slot of `K` holds its original value. -/
theorem clearedCount_eq_zero {sevm : Sevm} {b : Devm} {a : Adr} {K : Finset B256}
    (h : ∀ x ∈ K, b.getOrigStorVal sevm a x = b.getStorVal a x) :
    clearedCount sevm b a K = 0 :=
  Finset.sum_eq_zero fun x hx =>
    ite_eq_right_iff.mpr fun hc => absurd (by rw [h x hx]; exact hc.2) hc.1

/-- The refund counter's step, against the cleared indicator it moves. -/
theorem sstoreNewRefundCounter_potential (gas : GasSchedule) (v o c : B256) (rc : Int) :
    rc - (gas.storageClearRefund : Int) * (if o ≠ 0 ∧ c = 0 then 1 else 0 : Nat) ≤
      sstoreNewRefundCounter gas v o c rc -
        (gas.storageClearRefund : Int) * (if o ≠ 0 ∧ v = 0 then 1 else 0 : Nat) := by
  have hR : (0 : Int) ≤ (gas.storageClearRefund : Int) := Int.natCast_nonneg _
  unfold sstoreNewRefundCounter
  by_cases hcv : c = v
  · subst hcv
    simp only [ne_eq, not_true_eq_false, ↓reduceIte, le_refl]
  · simp only [ne_eq, hcv, not_false_eq_true, ↓reduceIte]
    by_cases ho : o = 0
    · simp only [ho, not_true_eq_false, false_and, ↓reduceIte, Nat.cast_zero, Int.mul_zero,
        Int.sub_zero, gasStorageSet, gasWarmAccess]
      split_ifs <;> omega
    · by_cases hc0 : c = 0
      · have hv0 : v ≠ 0 := fun h => hcv (hc0.trans h.symm)
        simp only [ho, hc0, hv0, not_false_eq_true, not_true_eq_false, and_true, and_false,
          ↓reduceIte, Nat.cast_one, Nat.cast_zero, Int.mul_one, Int.mul_zero,
          Int.sub_zero, gasWarmAccess, gasStorageUpdate, gasColdSload]
        split_ifs <;> omega
      · by_cases hv0 : v = 0
        · simp only [ho, hc0, hv0, not_false_eq_true, and_self, ↓reduceIte,
            Nat.cast_one, Nat.cast_zero, Int.mul_one, Int.mul_zero, Int.sub_zero, and_false]
          omega
        · simp only [ho, hc0, hv0, not_false_eq_true, and_false, ↓reduceIte, Nat.cast_zero,
            Int.mul_zero, Int.sub_zero, gasWarmAccess, gasStorageUpdate, gasColdSload]
          split_ifs <;> omega

/-- **An `SSTORE` by a frame at `a` never lowers the potential of `a`**, whatever the key and value,
when `K` covers every slot of `a` whose original value is nonzero. -/
theorem refundPotential_afterSstore {sevm : Sevm} {b : Devm} {K : Finset B256} {k v : B256}
    (hK : ∀ x, x ∉ K → b.getOrigStorVal sevm sevm.currentTarget x = 0) :
    refundPotential sevm b sevm.currentTarget K ≤
      refundPotential sevm (afterSstore sevm b k v) sevm.currentTarget K := by
  have hcr : (afterSstore sevm b k v).createdAccounts = b.createdAccounts :=
    afterSstore_createdAccounts sevm b k v
  have horig : ∀ x, (afterSstore sevm b k v).getOrigStorVal sevm sevm.currentTarget x =
      b.getOrigStorVal sevm sevm.currentTarget x := fun x => getOrigStorVal_congr_created _ x hcr
  have hcur : ∀ x, (afterSstore sevm b k v).getStorVal sevm.currentTarget x =
      if x = k then v else b.getStorVal sevm.currentTarget x := by
    intro x
    change (Devm.getStor (afterSstore sevm b k v) sevm.currentTarget).get x = _
    rw [afterSstore_getStor_self]
    by_cases hx : x = k
    · subst hx
      rw [Stor.get_set_self, ite_eq_left rfl]
    · rw [Stor.get_set_ne _ (Ne.symm hx), ite_eq_right hx]
      rfl
  have hrc := afterSstore_refundCounter sevm b k v
  unfold refundPotential clearedCount
  rw [hrc]
  simp only [horig, hcur]
  by_cases hk : k ∈ K
  · rw [← Finset.add_sum_erase K _ hk, ← Finset.add_sum_erase K _ hk]
    have hrest : (∑ x ∈ K.erase k, if b.getOrigStorVal sevm sevm.currentTarget x ≠ 0 ∧
          (if x = k then v else b.getStorVal sevm.currentTarget x) = 0 then 1 else 0) =
        ∑ x ∈ K.erase k, if b.getOrigStorVal sevm sevm.currentTarget x ≠ 0 ∧
          b.getStorVal sevm.currentTarget x = 0 then 1 else 0 :=
      Finset.sum_congr rfl fun x hx => by rw [ite_eq_right (Finset.ne_of_mem_erase hx)]
    rw [hrest, ite_eq_left rfl]
    have key := sstoreNewRefundCounter_potential sevm.benvStat.rules.gas v
      (b.getOrigStorVal sevm sevm.currentTarget k) (b.getStorVal sevm.currentTarget k)
      b.refundCounter
    generalize (∑ x ∈ K.erase k, if b.getOrigStorVal sevm sevm.currentTarget x ≠ 0 ∧
      b.getStorVal sevm.currentTarget x = 0 then 1 else 0) = n
    rw [Nat.cast_add, Nat.cast_add, Int.mul_add, Int.mul_add]
    omega
  · have hrest : (∑ x ∈ K, if b.getOrigStorVal sevm sevm.currentTarget x ≠ 0 ∧
          (if x = k then v else b.getStorVal sevm.currentTarget x) = 0 then 1 else 0) =
        ∑ x ∈ K, if b.getOrigStorVal sevm sevm.currentTarget x ≠ 0 ∧
          b.getStorVal sevm.currentTarget x = 0 then 1 else 0 :=
      Finset.sum_congr rfl fun x hx => by
        rw [ite_eq_right (show ¬ x = k from fun h => hk (by rw [← h]; exact hx))]
    rw [hrest]
    have key := sstoreNewRefundCounter_potential sevm.benvStat.rules.gas v
      (b.getOrigStorVal sevm sevm.currentTarget k) (b.getStorVal sevm.currentTarget k)
      b.refundCounter
    have h0 := hK k hk
    simp only [h0, ne_eq, not_true_eq_false, false_and, ↓reduceIte, Nat.cast_zero, Int.mul_zero,
      Int.sub_zero] at key
    rw [h0]
    omega

end Blanc
