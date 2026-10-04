import Blanc.LedgerConservation

/-!
# A token ledger read over a finite key footprint

A pure token model keeps its balances as a function `Adr → B256`; a history only ever observes the
finitely many rows it touches.  `footprintSum keys balances` is the sum of the rows a key list names,
each occurrence counted, and `FootprintCovers keys balances` says the list names every nonzero row.
For a duplicate-free covering list the footprint sum is the full address sum `sum`
(`footprintSum_eq_sum`), so a conservation law proved over `sum` is read over any finite footprint
that covers the support, and in particular over a footprint extended by the keys a step touches.
`footprintSum_dup_ne_sum` is the statement control: one repeated nonzero key breaks the equation.

Nothing here names a contract.
-/

namespace Blanc

open Jaune

/-- The full address sum of `balances` is exactly the word `supply`.  A structure, so that
elaboration never unfolds `sum` while comparing two ledgers. -/
structure SumBacked (balances : Adr → B256) (supply : B256) : Prop where
  eq : sum balances = supply.toNat

/-- The sum of the rows `keys` names, each occurrence counted. -/
def footprintSum (keys : List Adr) (balances : Adr → B256) : Nat :=
  (keys.map fun key => (balances key).toNat).sum

/-- `keys` names every row holding a nonzero balance. -/
def FootprintCovers (keys : List Adr) (balances : Adr → B256) : Prop :=
  ∀ account, balances account ≠ 0 → account ∈ keys

/-- Below an address bound, the prefix sum is the coalition sum over the members below it. -/
theorem sumBelow_eq_ledgerSumOn_filter {balances : Adr → B256} {coalition : Finset Adr}
    (covers : ∀ account, balances account ≠ 0 → account ∈ coalition) :
    ∀ n, n ≤ 2 ^ 160 →
      sumBelow balances n = ledgerSumOn (coalition.filter fun account => account.toNat < n) balances
  | 0, _ => by
    have empty : (coalition.filter fun account : Adr => account.toNat < 0) = ∅ :=
      Finset.filter_false_of_mem fun account _ => Nat.not_lt_zero account.toNat
    rw [empty]
    rfl
  | n + 1, bound => by
    have below : n < 2 ^ 160 := bound
    have previous := sumBelow_eq_ledgerSumOn_filter covers n (Nat.le_of_lt below)
    have toNatEq : ∀ account : Adr, account.toNat = n ↔ account = n.toAdr := by
      intro account
      constructor
      · intro same
        rw [← toAdr_toNat account, same]
      · intro same
        rw [same, Nat.toNat_toAdr, Nat.lo_eq_of_lt below]
    rw [sumBelow_succ, previous]
    by_cases member : n.toAdr ∈ coalition
    · have split : (coalition.filter fun account : Adr => account.toNat < n + 1) =
          insert n.toAdr (coalition.filter fun account : Adr => account.toNat < n) := by
        apply Finset.ext
        intro account
        rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_filter, ← toNatEq account]
        constructor
        · rintro ⟨inside, lt⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp lt with lt | eq
          · exact Or.inr ⟨inside, lt⟩
          · exact Or.inl eq
        · rintro (eq | ⟨inside, lt⟩)
          · exact ⟨(toNatEq account).mp eq ▸ member, Nat.lt_succ_of_le (Nat.le_of_eq eq)⟩
          · exact ⟨inside, Nat.lt_succ_of_lt lt⟩
      have fresh : n.toAdr ∉ (coalition.filter fun account : Adr => account.toNat < n) := by
        intro inside
        have lt := (Finset.mem_filter.mp inside).2
        rw [(toNatEq n.toAdr).mpr rfl] at lt
        exact Nat.lt_irrefl n lt
      rw [split]
      unfold ledgerSumOn
      rw [Finset.sum_insert fresh, Nat.add_comm]
    · have zero : balances n.toAdr = 0 := by
        apply Classical.byContradiction
        intro nonzero
        exact member (covers _ nonzero)
      have same : (coalition.filter fun account : Adr => account.toNat < n + 1) =
          (coalition.filter fun account : Adr => account.toNat < n) := by
        apply Finset.ext
        intro account
        rw [Finset.mem_filter, Finset.mem_filter]
        constructor
        · rintro ⟨inside, lt⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp lt with lt | eq
          · exact ⟨inside, lt⟩
          · exact absurd ((toNatEq account).mp eq ▸ inside) member
        · rintro ⟨inside, lt⟩
          exact ⟨inside, Nat.lt_succ_of_lt lt⟩
      rw [same, zero]
      rfl

/-- The greatest address is `2 ^ 160 - 1`. -/
theorem Adr.max_toNat : Adr.max.toNat = 2 ^ 160 - 1 := by
  decide

/-- A coalition covering every nonzero row carries the full address sum. -/
theorem sum_eq_ledgerSumOn {balances : Adr → B256} {coalition : Finset Adr}
    (covers : ∀ account, balances account ≠ 0 → account ∈ coalition) :
    sum balances = ledgerSumOn coalition balances := by
  have bound : Adr.max.toNat.succ ≤ 2 ^ 160 := by
    rw [Adr.max_toNat]
    exact Nat.le_refl _
  unfold sum
  rw [sumBelow_eq_ledgerSumOn_filter covers _ bound]
  have whole : (coalition.filter fun account : Adr => account.toNat < Adr.max.toNat.succ) =
      coalition := by
    apply Finset.filter_true_of_mem
    intro account _
    have := Adr.toNat_lt_size account
    rw [Adr.max_toNat]
    omega
  rw [whole]

/-- A duplicate-free covering footprint carries the full address sum. -/
theorem footprintSum_eq_sum {keys : List Adr} {balances : Adr → B256} (nodup : keys.Nodup)
    (covers : FootprintCovers keys balances) :
    footprintSum keys balances = sum balances := by
  rw [sum_eq_ledgerSumOn (coalition := keys.toFinset)
    (fun account nonzero => List.mem_toFinset.mpr (covers account nonzero))]
  unfold footprintSum ledgerSumOn
  rw [List.sum_toFinset _ nodup]

/-- A footprint stays covering when it is extended by every key whose row moved. -/
theorem FootprintCovers.extend {keys touched : List Adr} {before after : Adr → B256}
    (covers : FootprintCovers keys before)
    (frame : ∀ account, account ∉ touched → after account = before account) :
    FootprintCovers (keys ++ touched).dedup after := by
  intro account nonzero
  rw [List.mem_dedup, List.mem_append]
  by_cases moved : account ∈ touched
  · exact Or.inr moved
  · rw [frame account moved] at nonzero
    exact Or.inl (covers account nonzero)

/-- **Control.**  Repeating one nonzero key of a duplicate-free covering footprint breaks the
equation with the full sum: duplicate-freedom of the footprint is not a proof convenience. -/
theorem footprintSum_dup_ne_sum {keys : List Adr} {balances : Adr → B256} {key : Adr}
    (nodup : keys.Nodup) (covers : FootprintCovers keys balances) (nonzero : balances key ≠ 0) :
    footprintSum (key :: keys) balances ≠ sum balances := by
  have whole := footprintSum_eq_sum nodup covers
  have positive : 0 < (balances key).toNat := by
    apply Nat.pos_of_ne_zero
    intro zero
    exact nonzero (B256.toNat_inj _ 0 (by rw [zero, B256.toNat_zero]))
  unfold footprintSum at whole ⊢
  rw [List.map_cons, List.sum_cons, whole]
  omega

end Blanc
