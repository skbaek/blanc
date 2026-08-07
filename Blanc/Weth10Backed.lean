-- WETH10's backing invariant and relation-level preservation algebra.
-- This property layer deliberately contains no runtime or ContractSpec.

import Blanc.BalanceAlgebra
import Blanc.Weth10Core

namespace Blanc

open Jaune
open Weth10

/-- Booked balances and in-flight callvalue are backed by ETH plus the bounded
temporary flash-minted amount. Force-sent ETH may make the inequality strict. -/
def Stor.Weth10Inv (s : Stor) (v b : B256) : Prop :=
  balSum s + v.toNat ≤ b.toNat + (s.get flashMintedSlot).toNat ∧
  (s.get flashMintedSlot).toNat ≤ maxFlashMinted

/-- A storage transition invisible to the backing invariant. -/
def Stor.Weth10Silent (s s' : Stor) : Prop :=
  Stor.rest s = Stor.rest s' ∧
  s'.get flashMintedSlot = s.get flashMintedSlot

theorem Stor.Weth10Silent.rfl {s : Stor} : Stor.Weth10Silent s s :=
  ⟨Eq.refl _, Eq.refl _⟩

theorem Stor.Weth10Silent.of_eq {s s' : Stor} (h : s = s') :
    Stor.Weth10Silent s s' :=
  h ▸ Stor.Weth10Silent.rfl

theorem Stor.Weth10Silent.trans {s s' s'' : Stor}
    (h : Stor.Weth10Silent s s') (h' : Stor.Weth10Silent s' s'') :
    Stor.Weth10Silent s s'' :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

/-- Any write outside both the address-shaped balance region and the flash
slot is silent. -/
theorem Stor.Weth10Silent.set {s : Stor} {k value : B256}
    (h_not_balance : ¬ ValidAdr k)
    (h_not_flash : k ≠ flashMintedSlot) :
    Stor.Weth10Silent s (s.set k value) := by
  refine ⟨?_, Stor.get_set_ne _ h_not_flash _⟩
  funext a
  simp only [Stor.rest, Function.comp_apply]
  exact (Stor.get_set_ne _ (fun h => h_not_balance ⟨a, h.symm⟩) _).symm

theorem Stor.Weth10Silent.set_nonce (s : Stor) (a : Adr) (value : B256) :
    Stor.Weth10Silent s (s.set (nonceKey a) value) :=
  Stor.Weth10Silent.set (nonceKey_not_valid a) (nonceKey_ne_flashMintedSlot a)

theorem Stor.Weth10Silent.set_allowance
    (s : Stor) (owner spender : Adr) (value : B256) :
    Stor.Weth10Silent s (s.set (allowanceKey owner spender) value) :=
  Stor.Weth10Silent.set
    (allowanceKey_not_valid owner spender)
    (allowanceKey_ne_flashMintedSlot owner spender)

/-- Silent storage writes preserve backing and the flash-mint cap. -/
theorem Stor.Weth10Inv.silent {s s' : Stor} {v b : B256}
    (h : Stor.Weth10Inv s v b)
    (hs : Stor.Weth10Silent s s') :
    Stor.Weth10Inv s' v b := by
  rcases h with ⟨h_backed, h_cap⟩
  constructor
  · simpa only [balSum, ← hs.1, hs.2] using h_backed
  · simpa only [hs.2] using h_cap

/-- A deposit credits at most its callvalue and consumes the in-flight
callvalue term. Unchecked balance wrap can only reduce the booked sum. -/
theorem Stor.Weth10Inv.deposit {s s' : Stor} {a : Adr} {v b : B256}
    (h : Stor.Weth10Inv s v b)
    (h_inc : Increase a v (Stor.rest s) (Stor.rest s'))
    (h_flash : s'.get flashMintedSlot = s.get flashMintedSlot) :
    Stor.Weth10Inv s' 0 b := by
  unfold Stor.Weth10Inv at h ⊢
  rw [h_flash]
  rcases h with ⟨h_backed, h_cap⟩
  constructor
  · simp only [B256.toNat_zero, Nat.add_zero]
    exact Nat.le_trans (sum_increase_le h_inc) h_backed
  · exact h_cap

/-- Moving booked value between addresses cannot increase the total, including
when the unchecked recipient credit wraps. -/
theorem Stor.Weth10Inv.transfer
    {s s' : Stor} {src dst : Adr} {v x b : B256}
    (h : Stor.Weth10Inv s v b)
    (h_tr : Transfer (Stor.rest s) src x dst (Stor.rest s'))
    (h_flash : s'.get flashMintedSlot = s.get flashMintedSlot) :
    Stor.Weth10Inv s' v b := by
  unfold Stor.Weth10Inv at h ⊢
  rw [h_flash]
  rcases h with ⟨h_backed, h_cap⟩
  constructor
  · exact Nat.le_trans
      (Nat.add_le_add_right (transfer_does_not_increase_sum h_tr) v.toNat)
      h_backed
  · exact h_cap

/-- Flash minting credits at most `x` balances and adds exactly `x` to the
non-overflowing, capped flash counter. -/
theorem Stor.Weth10Inv.flashMint
    {s s' : Stor} {a : Adr} {cv b x : B256}
    (h : Stor.Weth10Inv s cv b)
    (h_inc : Increase a x (Stor.rest s) (Stor.rest s'))
    (h_nof : B256.Nof (s.get flashMintedSlot) x)
    (h_flash : s'.get flashMintedSlot = s.get flashMintedSlot + x)
    (h_cap : (s'.get flashMintedSlot).toNat ≤ maxFlashMinted) :
    Stor.Weth10Inv s' cv b := by
  unfold Stor.Weth10Inv at h ⊢
  rcases h with ⟨h_backed, _⟩
  constructor
  · rw [h_flash, B256.toNat_add_eq_of_nof _ _ h_nof]
    have h_sum : balSum s' ≤ balSum s + x.toNat := sum_increase_le h_inc
    omega
  · exact h_cap

/-- Flash burning removes exactly `x` from one balance and the flash counter. -/
theorem Stor.Weth10Inv.flashBurn
    {s s' : Stor} {a : Adr} {cv b x : B256}
    (h : Stor.Weth10Inv s cv b)
    (h_dec : Decrease a x (Stor.rest s) (Stor.rest s'))
    (h_le_bal : x ≤ Stor.rest s a)
    (h_le_flash : x ≤ s.get flashMintedSlot)
    (h_flash : s'.get flashMintedSlot = s.get flashMintedSlot - x) :
    Stor.Weth10Inv s' cv b := by
  unfold Stor.Weth10Inv at h ⊢
  rcases h with ⟨h_backed, h_cap⟩
  have h_sum : balSum s - x.toNat = balSum s' :=
    sum_sub_assoc h_dec h_le_bal
  have h_x_sum : x.toNat ≤ balSum s :=
    Nat.le_trans (B256.toNat_le_toNat h_le_bal) le_sum
  have h_x_flash : x.toNat ≤ (s.get flashMintedSlot).toNat :=
    B256.toNat_le_toNat h_le_flash
  constructor
  · rw [h_flash, B256.toNat_sub_eq_of_le _ _ h_le_flash]
    omega
  · rw [h_flash, B256.toNat_sub_eq_of_le _ _ h_le_flash]
    omega

/-- A successful withdrawal burns `x` booked tokens and sends the same `x`
ETH, leaving the flash counter unchanged. -/
theorem Stor.Weth10Inv.withdraw
    {s s' : Stor} {a : Adr} {b x : B256}
    (h : Stor.Weth10Inv s 0 b)
    (h_dec : Decrease a x (Stor.rest s) (Stor.rest s'))
    (h_le_bal : x ≤ Stor.rest s a)
    (h_le_eth : x ≤ b)
    (h_flash : s'.get flashMintedSlot = s.get flashMintedSlot) :
    Stor.Weth10Inv s' 0 (b - x) := by
  unfold Stor.Weth10Inv at h ⊢
  rw [h_flash]
  rcases h with ⟨h_backed, h_cap⟩
  have h_sum : balSum s - x.toNat = balSum s' :=
    sum_sub_assoc h_dec h_le_bal
  have h_x_sum : x.toNat ≤ balSum s :=
    Nat.le_trans (B256.toNat_le_toNat h_le_bal) le_sum
  have h_x_eth : x.toNat ≤ b.toNat :=
    B256.toNat_le_toNat h_le_eth
  constructor
  · simp only [B256.toNat_zero, Nat.add_zero] at h_backed ⊢
    rw [B256.toNat_sub_eq_of_le _ _ h_le_eth]
    omega
  · exact h_cap

/-- The canonical empty storage establishes the backing invariant. -/
theorem Stor.Weth10Inv.of_empty :
    Stor.Weth10Inv Stor.empty 0 0 := by
  unfold Stor.Weth10Inv
  have h_flash : Stor.empty.get flashMintedSlot = 0 := rfl
  rw [h_flash, B256.toNat_zero, Nat.add_zero]
  constructor
  · have h_rest : Stor.rest Stor.empty = fun _ => (0 : B256) := by
      funext a
      rfl
    rw [balSum, sum, h_rest, sumBelow_zero]
  · exact Nat.zero_le _

end Blanc
