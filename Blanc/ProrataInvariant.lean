-- ProrataInvariant.lean : the fork-independent PRORATA accounting invariant.

import Blanc.ProrataArithmetic
import Blanc.Ladder

namespace Blanc

open Jaune

namespace Prorata

/-- Total issued shares, read from PRORATA's distinguished supply slot. -/
def supplyN (s : Stor) : Nat :=
  (s.get supplySlot).toNat

/-- PRORATA's frame invariant.

The first conjunct couples the caller-indexed share ledger to total supply.
The second carries the program's arithmetic cap.  The final inequality is the
genesis-price/backing bound.  During a PRORATA frame, `value` has already been
credited to `balance`, so subtracting its scaled contribution recovers the
pre-credit price bound used by `deposit`. -/
def Inv (s : Stor) (value balance : B256) : Prop :=
  balSum s = supplyN s ∧
    supplyN s ≤ maxSupply.toNat ∧
    supplyN s + offset.toNat * value.toNat ≤
      offset.toNat * balance.toNat

theorem Inv.balSum_eq {s : Stor} {value balance : B256}
    (h : Inv s value balance) : balSum s = supplyN s :=
  h.1

theorem Inv.supply_le {s : Stor} {value balance : B256}
    (h : Inv s value balance) : supplyN s ≤ maxSupply.toNat :=
  h.2.1

theorem Inv.backed {s : Stor} {value balance : B256}
    (h : Inv s value balance) :
    supplyN s + offset.toNat * value.toNat ≤
      offset.toNat * balance.toNat :=
  h.2.2

/-- In-flight callvalue cannot exceed the already-credited contract balance. -/
theorem Inv.value_le_balance {s : Stor} {value balance : B256}
    (h : Inv s value balance) : value.toNat ≤ balance.toNat := by
  have hback := h.backed
  rw [offset_toNat] at hback
  omega

/-- Remove the credited in-flight value to expose `deposit`'s pre-credit
genesis-price bound. -/
theorem Inv.precredit_price {s : Stor} {value balance : B256}
    (h : Inv s value balance) :
    supplyN s ≤ offset.toNat * (balance.toNat - value.toNat) := by
  have hback := h.backed
  rw [offset_toNat] at hback ⊢
  omega

/-- Once a frame terminates, no callvalue remains in flight. -/
theorem Inv.forget {s : Stor} {value balance : B256}
    (h : Inv s value balance) : Inv s 0 balance := by
  refine ⟨h.balSum_eq, h.supply_le, ?_⟩
  have hback := h.backed
  rw [offset_toNat] at hback ⊢
  rw [B256.toNat_zero]
  omega

/-- A bare rise in ETH balance preserves PRORATA's backing invariant. -/
theorem Inv.mono {s : Stor} {value balance balance' : B256}
    (h : Inv s value balance)
    (hle : balance.toNat ≤ balance'.toNat) :
    Inv s value balance' := by
  refine ⟨h.balSum_eq, h.supply_le, ?_⟩
  have hback := h.backed
  rw [offset_toNat] at hback ⊢
  omega

/-- A value transfer already credited to the contract may be put in flight. -/
theorem Inv.recv {s : Stor} {value balance balance' : B256}
    (h : Inv s 0 balance)
    (hbalance : balance'.toNat = balance.toNat + value.toNat) :
    Inv s value balance' := by
  refine ⟨h.balSum_eq, h.supply_le, ?_⟩
  have hback := h.backed
  rw [offset_toNat] at hback ⊢
  rw [B256.toNat_zero] at hback
  omega

/-! ## The ledger/supply-slot split -/

/-- PRORATA's all-ones supply slot is not address-shaped. -/
theorem supplySlot_not_validAdr : ¬ ValidAdr supplySlot := by
  rw [validAdr_iff]
  decide

/-- Address-shaped share-balance keys cannot collide with the supply slot. -/
theorem toB256_ne_supplySlot (a : Adr) : a.toB256 ≠ supplySlot :=
  fun h => supplySlot_not_validAdr ⟨a, h⟩

/-- Supply writes are invisible to the sum of caller-indexed balances. -/
theorem Stor.rest_set_prorataSupplySlot (s : Stor) (v : B256) :
    Stor.rest (s.set supplySlot v) = Stor.rest s := by
  funext a
  simp only [Stor.rest, Function.comp_apply]
  exact Stor.get_set_ne _ (toB256_ne_supplySlot a).symm _

/-- Caller-balance writes are invisible to PRORATA's supply slot. -/
theorem Stor.get_prorataSupplySlot_set {s : Stor} {k v : B256}
    (h : ValidAdr k) :
    (s.set k v).get supplySlot = s.get supplySlot := by
  rcases h with ⟨a, rfl⟩
  exact Stor.get_set_ne _ (toB256_ne_supplySlot a) _

/-- Every caller's booked share balance is bounded by total supply. -/
theorem Inv.share_le_supply {s : Stor} {value balance : B256}
    (h : Inv s value balance) (a : Adr) :
    (Stor.rest s a).toNat ≤ supplyN s := by
  rw [← h.balSum_eq]
  exact le_sum

/-- The Nat supply cap reflected back into the stored word order. -/
theorem Inv.supply_word_le {s : Stor} {value balance : B256}
    (h : Inv s value balance) : s.get supplySlot ≤ maxSupply :=
  B256.le_of_toNat_le_toNat h.supply_le

/-- A caller's share word is bounded by the stored total-supply word. -/
theorem Inv.share_word_le_supply {s : Stor} {value balance : B256}
    (h : Inv s value balance) (a : Adr) :
    s.get a.toB256 ≤ s.get supplySlot :=
  B256.le_of_toNat_le_toNat (h.share_le_supply a)

/-- The caller-indexed share sum cannot overflow under the supply cap. -/
theorem Inv.sumNof {s : Stor} {value balance : B256}
    (h : Inv s value balance) : SumNof (Stor.rest s) := by
  show balSum s < 2 ^ 256
  rw [h.balSum_eq]
  exact lt_of_le_of_lt h.supply_le (B256.toNat_lt maxSupply)

/-- Empty storage, zero in-flight value, and zero ETH balance establish the
genesis invariant before PRORATA has run. -/
theorem Inv.of_get_eq_zero {s : Stor} (h : ∀ k, s.get k = 0) :
    Inv s 0 0 := by
  have h_supply : supplyN s = 0 := by
    unfold supplyN
    rw [h, B256.toNat_zero]
  have h_sum : balSum s = 0 := by
    have h_rest : Stor.rest s = fun _ => (0 : B256) :=
      funext fun a => h _
    have h_zero : ∀ n, sumBelow (fun _ => (0 : B256)) n = 0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [sumBelow_succ, ih, B256.toNat_zero, Nat.add_zero]
    rw [balSum, sum, h_rest, h_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [h_sum, h_supply]
  · rw [h_supply]
    exact Nat.zero_le _
  · rw [h_supply, B256.toNat_zero]
    exact Nat.le_refl _

/-- The canonical empty storage map establishes PRORATA's genesis invariant. -/
theorem Inv.of_empty : Inv Stor.empty 0 0 :=
  Inv.of_get_eq_zero fun _ => rfl

/-! ## Contract-spec adapter -/

/-- PRORATA's invariant packaged for Blanc's generic execution ladder. -/
def prorataSpec : ContractSpec where
  prog := prorata
  Inv := Inv
  Side := SumNof
  inv_forget := Inv.forget
  inv_mono := Inv.mono
  inv_recv := Inv.recv
  side_le := by
    intro f g h hle
    unfold SumNof at h ⊢
    omega
  side_transfer := by
    intro st st' caller callee wad h_sub h_side
    have h_nof : sum st.bal < 2 ^ 256 := h_side
    rcases of_state_transfer (callee := callee) h_sub h_nof with
      ⟨-, -, h_sum, -, -, -⟩
    show sum _ < 2 ^ 256
    rw [h_sum]
    exact h_nof
  side_addBal := by
    intro w a val h_bound _
    show sum _ < 2 ^ 256
    rw [sum_addBal_eq w a val h_bound]
    omega
  inv_transfer := by
    intro st st' caller callee ca wad value h_sub h_ne h_side h_inv
    have h_nof : sum st.bal < 2 ^ 256 := h_side
    rcases of_state_transfer (callee := callee) h_sub h_nof with
      ⟨h_t_stor, -, -, h_t_le, -, -⟩
    have h_mid : st'.bal ca = st.bal ca := by
      rcases State.of_subBal h_sub with ⟨-, h_st'⟩
      rw [h_st']
      show ((st.setBal caller _).get ca).bal = (st.get ca).bal
      rw [State.setBal_get_ne h_ne]
    have h_stor : (st'.addBal callee wad).getStor ca = st.getStor ca :=
      h_t_stor ca
    have h_ge :
        (st.bal ca).toNat ≤ ((st'.addBal callee wad).bal ca).toNat := by
      by_cases h_eq : callee = ca
      · have h_add : (st'.addBal callee wad).bal ca = st.bal ca + wad := by
          rw [h_eq]
          show ((st'.setBal ca (st'.bal ca + wad)).get ca).bal = _
          rw [State.setBal_get_self]
          show st'.bal ca + wad = _
          rw [h_mid]
        rw [h_add]
        have h_le_wad : wad.toNat ≤ (st.bal caller).toNat :=
          B256.toNat_le_toNat h_t_le
        have h_two :
            (st.bal ca).toNat + (st.bal caller).toNat ≤ sum st.bal :=
          add_le_sum_of_ne st.bal (fun hc => h_ne hc.symm)
        have h_nof' : B256.Nof (st.bal ca) wad := by
          unfold B256.Nof
          omega
        rw [B256.toNat_add_eq_of_nof _ _ h_nof']
        omega
      · have h_other : (st'.addBal callee wad).bal ca = st.bal ca := by
          show ((st'.setBal callee _).get ca).bal = _
          rw [State.setBal_get_ne h_eq]
          exact h_mid
        rw [h_other]
    rw [h_stor]
    exact h_inv.mono h_ge
  inv_recv_transfer := by
    intro st st' caller ca wad h_sub h_ne h_side h_inv
    have h_nof : sum st.bal < 2 ^ 256 := h_side
    rcases of_state_transfer (callee := ca) h_sub h_nof with
      ⟨h_t_stor, -, -, -, -, -⟩
    have h_stor : (st'.addBal ca wad).getStor ca = st.getStor ca :=
      h_t_stor ca
    have h_bal : ((st'.addBal ca wad).bal ca).toNat =
        (st.bal ca).toNat + wad.toNat :=
      of_transfer_bal_target h_sub h_ne h_nof
    rw [h_stor]
    exact h_inv.recv h_bal
  inv_addBal := by
    intro w ca a val value h_bound _ h_inv
    have h_nof_a : B256.Nof (w.bal a) val := by
      unfold B256.Nof
      have := @le_sum w.bal a
      omega
    have h_stor : (w.addBal a val).getStor ca = w.getStor ca := by
      show ((w.setBal a _).get ca).stor = (w.get ca).stor
      rw [State.setBal_get_stor]
    have h_ge : (w.bal ca).toNat ≤ ((w.addBal a val).bal ca).toNat := by
      by_cases h_eq : a = ca
      · subst h_eq
        show (w.bal a).toNat ≤
          ((w.setBal a (w.bal a + val)).get a).bal.toNat
        rw [State.setBal_get_self]
        change (w.bal a).toNat ≤ (w.bal a + val).toNat
        rw [B256.toNat_add_eq_of_nof _ _ h_nof_a]
        omega
      · show (w.bal ca).toNat ≤ ((w.setBal a _).get ca).bal.toNat
        rw [State.setBal_get_ne h_eq]
        exact Nat.le_refl _
    rw [h_stor]
    exact h_inv.mono h_ge

end Prorata

end Blanc
