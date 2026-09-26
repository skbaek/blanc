-- LedgerUpdate.lean : single-row functional updates of an address-keyed ledger.

import Blanc.LedgerConservation

/-!
# Functional single-row ledger updates

A pure token model keeps its balances as a function `Adr → B256` and books a
movement as a `Function.update` of one row.  `ledgerDebit` and `ledgerCredit`
name the two wrapping one-row updates; the lemmas here connect them to the
`Decrease` / `Increase` / `Transfer` relations of `Blanc/LadderBase.lean` and
read off the exact movement of `sum`.  Checked arithmetic is the caller's
guard: a debit is exact under `v ≤ f k`, a credit under `B256.Nof (f k) v`.

Nothing here names a contract.
-/

namespace Blanc

open Jaune

/-- Subtract `v` from row `k` (wrapping; exact under `v ≤ f k`). -/
def ledgerDebit (f : Adr → B256) (k : Adr) (v : B256) : Adr → B256 :=
  Function.update f k (f k - v)

/-- Add `v` to row `k` (wrapping; exact under `B256.Nof (f k) v`). -/
def ledgerCredit (f : Adr → B256) (k : Adr) (v : B256) : Adr → B256 :=
  Function.update f k (f k + v)

@[simp] theorem ledgerDebit_self (f : Adr → B256) (k : Adr) (v : B256) :
    ledgerDebit f k v k = f k - v := by
  simp [ledgerDebit]

theorem ledgerDebit_ne {f : Adr → B256} {k a : Adr} (v : B256) (h : a ≠ k) :
    ledgerDebit f k v a = f a := by
  simp [ledgerDebit, Function.update_of_ne h]

@[simp] theorem ledgerCredit_self (f : Adr → B256) (k : Adr) (v : B256) :
    ledgerCredit f k v k = f k + v := by
  simp [ledgerCredit]

theorem ledgerCredit_ne {f : Adr → B256} {k a : Adr} (v : B256) (h : a ≠ k) :
    ledgerCredit f k v a = f a := by
  simp [ledgerCredit, Function.update_of_ne h]

theorem ledgerDebit_decrease (f : Adr → B256) (k : Adr) (v : B256) :
    Decrease k v f (ledgerDebit f k v) := by
  intro a
  refine ⟨?_, fun h => (ledgerDebit_ne v (Ne.symm h)).symm⟩
  rintro rfl
  exact (ledgerDebit_self f k v).symm

theorem ledgerCredit_increase (f : Adr → B256) (k : Adr) (v : B256) :
    Increase k v f (ledgerCredit f k v) := by
  intro a
  refine ⟨?_, fun h => (ledgerCredit_ne v (Ne.symm h)).symm⟩
  rintro rfl
  exact (ledgerCredit_self f k v).symm

/-- A covered debit lowers `sum` by exactly the amount. -/
theorem sum_ledgerDebit {f : Adr → B256} {k : Adr} {v : B256} (h : v ≤ f k) :
    sum (ledgerDebit f k v) = sum f - v.toNat :=
  (sum_sub_assoc (ledgerDebit_decrease f k v) h).symm

/-- A non-wrapping credit raises `sum` by exactly the amount. -/
theorem sum_ledgerCredit {f : Adr → B256} {k : Adr} {v : B256}
    (h : B256.Nof (f k) v) :
    sum (ledgerCredit f k v) = sum f + v.toNat :=
  (sum_add_assoc (ledgerCredit_increase f k v) h).symm

/-- A covered debit at `src` followed by a credit at `dst` (the sequential
reading, so `src = dst` is included) is a `Transfer`. -/
theorem ledgerDebit_credit_transfer {f : Adr → B256} {src dst : Adr} {v : B256}
    (h : v ≤ f src) :
    Transfer f src v dst (ledgerCredit (ledgerDebit f src v) dst v) :=
  ⟨h, _, ledgerDebit_decrease f src v, ledgerCredit_increase _ dst v⟩

/-- Debit-then-credit preserves `sum` when the pre-ledger's sum is a word. -/
theorem sum_ledgerDebit_credit {f : Adr → B256} {src dst : Adr} {v : B256}
    (nof : SumNof f) (h : v ≤ f src) :
    sum (ledgerCredit (ledgerDebit f src v) dst v) = sum f :=
  (transfer_preserves_sum nof (ledgerDebit_credit_transfer h)).symm

/-- After a covered debit at `src`, crediting the same amount at any row cannot
wrap when the pre-ledger's sum is a word. -/
theorem ledgerDebit_credit_nof {f : Adr → B256} {src dst : Adr} {v : B256}
    (nof : SumNof f) (h : v ≤ f src) :
    B256.Nof (ledgerDebit f src v dst) v := by
  have hv : v.toNat ≤ (f src).toNat := B256.toNat_le_toNat h
  unfold B256.Nof
  unfold SumNof at nof
  by_cases same : dst = src
  · subst same
    rw [ledgerDebit_self, B256.toNat_sub_eq_of_le _ _ h]
    have := B256.toNat_lt (f dst)
    omega
  · rw [ledgerDebit_ne v same]
    have := add_le_sum_of_ne f same
    omega

end Blanc
