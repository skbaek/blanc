-- LedgerConservation.lean : ledger conservation at an arbitrary supply slot.

import Blanc.BalanceAlgebra

/-!
# Conservation of a token ledger at an arbitrary supply slot

A token contract that keeps balances at address-shaped keys and a total supply
at one reserved non-address key satisfies one invariant: the word at the supply
slot is exactly the sum of the balances.  Everything the invariant needs rests
on a single bit fact — the supply slot is not address-shaped — which is
simultaneously why the supply slot self-excludes from the sum, why a supply
write cannot move the sum, and why a balance write cannot move the supply.

Nothing here names a contract.  `Blanc/Conserved.lean` proves the same algebra
for fmint's own supply slot and predates this module; folding it onto this one
belongs to the fmint family rather than to a consumer.
-/

namespace Blanc

open Jaune

/-- The ledger at `slot` is conserved: the supply word is exactly the sum of
every address-shaped balance. -/
def LedgerConserved (slot : B256) (s : Stor) : Prop :=
  (s.get slot).toNat = balSum s


variable {slot : B256}

/-- The one bit fact, in the form the storage lemmas want. -/
theorem toB256_ne_of_not_validAdr (slotNotAdr : ¬ ValidAdr slot) (a : Adr) :
    a.toB256 ≠ slot :=
  fun h => slotNotAdr ⟨a, h⟩

/-- Supply writes are invisible to the sum: the supply slot is not an
address-shaped key, so `Stor.rest` cannot see it. -/
theorem rest_set_slot (slotNotAdr : ¬ ValidAdr slot) (s : Stor) (v : B256) :
    Stor.rest (s.set slot v) = Stor.rest s := by
  funext a
  simp only [Stor.rest, Function.comp_apply]
  exact Stor.get_set_ne _ (toB256_ne_of_not_validAdr slotNotAdr a).symm _

/-- Balance writes are invisible to the supply slot: the converse direction,
and the reason the two storage regions never interfere. -/
theorem get_slot_set (slotNotAdr : ¬ ValidAdr slot) {s : Stor} {k v : B256}
    (h : ValidAdr k) : (s.set k v).get slot = s.get slot := by
  rcases h with ⟨a, rfl⟩
  exact Stor.get_set_ne _ (toB256_ne_of_not_validAdr slotNotAdr a) _

/-- A write at a key that is not address-shaped is invisible to the balances.
This is what a guarded allowance write delivers. -/
theorem rest_set_of_not_validAdr {s : Stor} {k v : B256} (h : ¬ ValidAdr k) :
    Stor.rest (s.set k v) = Stor.rest s := by
  funext a
  simp only [Stor.rest, Function.comp_apply]
  exact Stor.get_set_ne _ (fun keyEq => h ⟨a, keyEq.symm⟩) _

/-- A ledger transfer written as two `set`s -- debit the source, then credit
the destination read *after* the debit -- is a `Transfer`.  Reading the
destination after the debit is exactly what makes a self-transfer net to zero
instead of double-counting. -/
theorem transfer_of_debit_credit {s : Stor} {owner receiver : Adr}
    {amount : B256} (covered : amount ≤ Stor.rest s owner) :
    Transfer (Stor.rest s) owner amount receiver
      (Stor.rest ((s.set owner.toB256 (Stor.rest s owner - amount)).set
        receiver.toB256
        (Stor.rest (s.set owner.toB256 (Stor.rest s owner - amount)) receiver +
          amount))) := by
  refine ⟨covered,
    Stor.rest (s.set owner.toB256 (Stor.rest s owner - amount)), ?_, ?_⟩
  · intro a
    refine ⟨?_, ?_⟩
    · intro same
      subst same
      rw [Stor.rest_set_self]
    · intro different
      rw [Stor.rest_set_ne _ (Ne.symm different)]
  · intro a
    refine ⟨?_, ?_⟩
    · intro same
      subst same
      rw [Stor.rest_set_self]
    · intro different
      rw [Stor.rest_set_ne _ (Ne.symm different)]

namespace LedgerConserved

/-- The sum never overflows a word: it *is* a word. -/
theorem sumNof {s : Stor} (h : LedgerConserved slot s) :
    SumNof (Stor.rest s) := by
  show balSum s < 2 ^ 256
  rw [← h]
  exact B256.toNat_lt _

/-- Every booked balance is at most the supply. -/
theorem le_supply {s : Stor} (h : LedgerConserved slot s) (a : Adr) :
    (Stor.rest s a).toNat ≤ (s.get slot).toNat := by
  rw [h]; exact le_sum

/-- Storage reading `0` at every key is conserved. -/
theorem of_get_eq_zero {s : Stor} (h : ∀ k, s.get k = 0) :
    LedgerConserved slot s := by
  show (s.get slot).toNat = balSum s
  have h_rest : Stor.rest s = fun _ => (0 : B256) := funext fun a => h _
  rw [h, balSum, sum, h_rest, sumBelow_zero]
  rfl

/-- An account created with no storage entries satisfies the invariant. -/
theorem of_empty : LedgerConserved slot Stor.empty :=
  of_get_eq_zero fun _ => rfl

/-- Storage unchanged. -/
theorem of_eq {s s' : Stor} (h : LedgerConserved slot s) (h_eq : s = s') :
    LedgerConserved slot s' := h_eq ▸ h

/-- A write whose key is neither address-shaped nor the supply slot leaves both
sides of the invariant alone.  This is what a guarded allowance write
delivers. -/
theorem of_rest_eq {s s' : Stor} (h : LedgerConserved slot s)
    (h_rest : Stor.rest s = Stor.rest s')
    (h_sup : s'.get slot = s.get slot) :
    LedgerConserved slot s' := by
  show _ = balSum s'
  rw [h_sup, h]
  simp only [balSum, h_rest]

/-- Value moves between two address-shaped keys and the supply is untouched. -/
theorem transfer {s s' : Stor} {a a' : Adr} {x : B256}
    (h : LedgerConserved slot s)
    (h_tr : Transfer (Stor.rest s) a x a' (Stor.rest s'))
    (h_sup : s'.get slot = s.get slot) :
    LedgerConserved slot s' := by
  show _ = balSum s'
  rw [h_sup, h]
  exact transfer_preserves_sum h.sumNof h_tr

/-- One balance rises by `v` and the supply rises by the same `v`. -/
theorem mint {s s' : Stor} {a : Adr} {v : B256}
    (h : LedgerConserved slot s)
    (h_inc : Increase a v (Stor.rest s) (Stor.rest s'))
    (h_nof : B256.Nof (s.get slot) v)
    (h_sup : s'.get slot = s.get slot + v) :
    LedgerConserved slot s' := by
  have h_bal : B256.Nof (Stor.rest s a) v := by
    have h_le := h.le_supply a
    unfold B256.Nof at h_nof ⊢
    omega
  show _ = balSum s'
  rw [h_sup, B256.toNat_add_eq_of_nof _ _ h_nof, h]
  exact sum_add_assoc h_inc h_bal

/-- One balance falls by `v` and the supply falls by the same `v`.  The caller
owes only `v ≤ balance`; the bound corollary turns that into `v ≤ supply`, which
is why no supply-underflow guard is needed. -/
theorem burn {s s' : Stor} {a : Adr} {v : B256}
    (h : LedgerConserved slot s)
    (h_dec : Decrease a v (Stor.rest s) (Stor.rest s'))
    (h_le : v ≤ Stor.rest s a)
    (h_sup : s'.get slot = s.get slot - v) :
    LedgerConserved slot s' := by
  have h_le_sup : v ≤ s.get slot :=
    B256.le_of_toNat_le_toNat
      (le_trans (B256.toNat_le_toNat h_le) (h.le_supply a))
  show _ = balSum s'
  rw [h_sup, B256.toNat_sub_eq_of_le _ _ h_le_sup, h]
  exact sum_sub_assoc h_dec h_le

/-- **The mint pair, in the exact `set` form a walked pair of `SSTORE`s
delivers**: a credit at an address-shaped key, then a supply write.  The supply
value may be read either before or after the credit — the credit is invisible
to the supply slot — so only the supply-side overflow bound is owed. -/
theorem mint_set {s : Stor} {a : Adr} {v : B256}
    (slotNotAdr : ¬ ValidAdr slot)
    (h : LedgerConserved slot s)
    (h_nof : B256.Nof (s.get slot) v) :
    LedgerConserved slot
      ((s.set a.toB256 (Stor.rest s a + v)).set slot (s.get slot + v)) := by
  refine h.mint (a := a) (v := v) ?_ h_nof ?_
  · intro b
    refine ⟨?_, ?_⟩
    · intro same
      subst same
      rw [rest_set_slot slotNotAdr, Stor.rest_set_self]
    · intro different
      rw [rest_set_slot slotNotAdr, Stor.rest_set_ne _ (Ne.symm different)]
  · exact Stor.get_set_self _ _ _

/-- **The burn pair, in the same `set` form**: a debit at an address-shaped
key, then a supply write.  The caller owes only `v ≤ balance`. -/
theorem burn_set {s : Stor} {a : Adr} {v : B256}
    (slotNotAdr : ¬ ValidAdr slot)
    (h : LedgerConserved slot s)
    (h_le : v ≤ Stor.rest s a) :
    LedgerConserved slot
      ((s.set a.toB256 (Stor.rest s a - v)).set slot (s.get slot - v)) := by
  refine h.burn (a := a) (v := v) ?_ h_le ?_
  · intro b
    refine ⟨?_, ?_⟩
    · intro same
      subst same
      rw [rest_set_slot slotNotAdr, Stor.rest_set_self]
    · intro different
      rw [rest_set_slot slotNotAdr, Stor.rest_set_ne _ (Ne.symm different)]
  · exact Stor.get_set_self _ _ _

end LedgerConserved


end Blanc
