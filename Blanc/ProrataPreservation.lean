-- ProrataPreservation.lean : preservation facts for PRORATA's accounting invariant.

import Blanc.ProrataDeposit
import Blanc.ProrataInvariant
import Blanc.ProrataWithdraw

namespace Blanc

open Jaune

namespace Prorata

/-- A no-overflow mint raises the caller-indexed ledger sum and the stored
total supply by the same amount. -/
theorem Inv.mint_balSum_eq {s : Stor} {value balance : B256}
    (h : Inv s value balance) (a : Adr) (m : B256)
    (hnof : B256.Nof (s.get supplySlot) m) :
    balSum ((s.set supplySlot (s.get supplySlot + m)).set a.toB256
      (s.get a.toB256 + m)) =
    supplyN ((s.set supplySlot (s.get supplySlot + m)).set a.toB256
      (s.get a.toB256 + m)) := by
  let t := s.set supplySlot (s.get supplySlot + m)
  let u := t.set a.toB256 (s.get a.toB256 + m)
  change balSum u = supplyN u
  have hnof_a : B256.Nof (s.get a.toB256) m := by
    unfold B256.Nof at hnof ⊢
    have hle := B256.toNat_le_toNat (h.share_word_le_supply a)
    omega
  have hnof_t : B256.Nof (t.get a.toB256) m := by
    dsimp [t]
    rw [Stor.get_set_ne _ (toB256_ne_supplySlot a).symm _]
    exact hnof_a
  have hinc : Increase a m (Stor.rest t) (Stor.rest u) := by
    simpa only [u, t, Stor.get_set_ne _ (toB256_ne_supplySlot a).symm _,
      B256.add_comm] using Stor.increase_set t a m
  calc
    balSum u = balSum t + m.toNat := (sum_add_assoc hinc hnof_t).symm
    _ = balSum s + m.toNat := by
      unfold balSum
      dsimp [t]
      rw [Stor.rest_set_prorataSupplySlot]
    _ = supplyN s + m.toNat := by rw [h.balSum_eq]
    _ = supplyN u := by
      unfold supplyN
      dsimp [u]
      rw [Stor.get_prorataSupplySlot_set (validAdr_toB256 a)]
      dsimp [t]
      rw [Stor.get_set_self]
      rw [B256.toNat_add_eq_of_nof _ _ hnof]

/-- A covered burn lowers the caller-indexed ledger sum and the stored total
supply by the same amount. -/
theorem Inv.burn_balSum_eq {s : Stor} {value balance : B256}
    (h : Inv s value balance) (a : Adr) (x : B256)
    (hcover : x ≤ s.get a.toB256) :
    balSum ((s.set a.toB256 (s.get a.toB256 - x)).set supplySlot
      (s.get supplySlot - x)) =
    supplyN ((s.set a.toB256 (s.get a.toB256 - x)).set supplySlot
      (s.get supplySlot - x)) := by
  let t := s.set a.toB256 (s.get a.toB256 - x)
  let u := t.set supplySlot (s.get supplySlot - x)
  change balSum u = supplyN u
  have hsupply : x ≤ s.get supplySlot :=
    hcover.trans (h.share_word_le_supply a)
  have hdec : Decrease a x (Stor.rest s) (Stor.rest t) := by
    simpa only [t] using Stor.decrease_set s a x
  calc
    balSum u = balSum t := by
      unfold balSum
      dsimp [u]
      rw [Stor.rest_set_prorataSupplySlot]
    _ = balSum s - x.toNat := (sum_sub_assoc hdec hcover).symm
    _ = supplyN s - x.toNat := by rw [h.balSum_eq]
    _ = supplyN u := by
      unfold supplyN
      dsimp [u]
      rw [Stor.get_set_self]
      rw [B256.toNat_sub_eq_of_le _ _ hsupply]

/-! ## Pricing adapters -/

/-- The invariant and deposit caps make the total-supply mint non-overflowing. -/
theorem Inv.deposit_mint_nof {s : Stor} {value balance : B256}
    (h : Inv s value balance)
    (hv : value ≤ maxValue) (hb : balance - value ≤ maxBalance) :
    B256.Nof (s.get supplySlot)
      (value * (s.get supplySlot + offset) / (balance - value + 1)) := by
  have hvb : value ≤ balance :=
    B256.le_of_toNat_le_toNat h.value_le_balance
  have hprice :
      supplyN s ≤ offset.toNat * (balance - value).toNat := by
    rw [B256.toNat_sub_eq_of_le _ _ hvb]
    exact h.precredit_price
  have hmint := mintN_le_offset_mul (amount := value.toNat) hprice
  have hvn := B256.toNat_le_toNat hv
  unfold B256.Nof
  change supplyN s +
      (value * (s.get supplySlot + offset) / (balance - value + 1)).toNat <
    2 ^ 256
  rw [deposit_quote_toNat hv h.supply_word_le hb]
  calc
    supplyN s + mintN offset.toNat value.toNat
          (s.get supplySlot).toNat (balance - value).toNat
        ≤ maxSupply.toNat + offset.toNat * maxValue.toNat :=
      Nat.add_le_add h.supply_le
        (hmint.trans (Nat.mul_le_mul_left offset.toNat hvn))
    _ < 2 ^ 256 := by
      rw [maxSupply_toNat, maxValue_toNat, offset_toNat]
      decide +kernel

/-- Deposit settlement preserves the genesis-price backing inequality. -/
theorem Inv.deposit_price_bound {s : Stor} {value balance : B256}
    (h : Inv s value balance)
    (hv : value ≤ maxValue) (hb : balance - value ≤ maxBalance) :
    let m := value * (s.get supplySlot + offset) / (balance - value + 1)
    supplyN s + m.toNat ≤ offset.toNat * balance.toNat := by
  dsimp
  have hvb : value ≤ balance :=
    B256.le_of_toNat_le_toNat h.value_le_balance
  have hprice :
      supplyN s ≤ offset.toNat * (balance - value).toNat := by
    rw [B256.toNat_sub_eq_of_le _ _ hvb]
    exact h.precredit_price
  have hp := deposit_preserves_genesis_price
    (amount := value.toNat) hprice
  rw [deposit_quote_toNat hv h.supply_word_le hb]
  rw [B256.toNat_sub_eq_of_le _ _ hvb] at hp
  rw [Nat.sub_add_cancel h.value_le_balance] at hp
  simpa only [supplyN, B256.toNat_sub_eq_of_le _ _ hvb] using hp

/-- A covered withdrawal cannot quote more ETH than the contract holds. -/
theorem Inv.withdraw_pay_word_le_balance
    {s : Stor} {value balance shares : B256}
    (h : Inv s value balance) (a : Adr)
    (hcover : shares ≤ s.get a.toB256) (hb : balance ≤ maxBalance) :
    shares * (balance + 1) / (s.get supplySlot + offset) ≤ balance := by
  have hsharesSupply : shares ≤ s.get supplySlot :=
    hcover.trans (h.share_word_le_supply a)
  have hsharesCap : shares ≤ maxSupply :=
    hsharesSupply.trans h.supply_word_le
  apply B256.le_of_toNat_le_toNat
  rw [withdraw_quote_toNat hsharesCap h.supply_word_le hb]
  exact payN_le_balance (by rw [offset_toNat]; decide)
    (B256.toNat_le_toNat hsharesSupply)

/-- Withdrawal settlement preserves the genesis-price backing inequality. -/
theorem Inv.withdraw_price_bound
    {s : Stor} {value balance shares : B256}
    (h : Inv s value balance) (a : Adr)
    (hcover : shares ≤ s.get a.toB256) (hb : balance ≤ maxBalance) :
    let p := shares * (balance + 1) / (s.get supplySlot + offset)
    supplyN s - shares.toNat ≤
      offset.toNat * (balance.toNat - p.toNat) := by
  dsimp
  have hsharesSupply : shares ≤ s.get supplySlot :=
    hcover.trans (h.share_word_le_supply a)
  have hsharesCap : shares ≤ maxSupply :=
    hsharesSupply.trans h.supply_word_le
  have hprice : supplyN s ≤ offset.toNat * balance.toNat := by
    have hback := h.backed
    omega
  have hp := withdraw_preserves_genesis_price
    (o := offset.toNat)
    (by rw [offset_toNat]; decide)
    (B256.toNat_le_toNat hsharesSupply)
    hprice
  rw [withdraw_quote_toNat hsharesCap h.supply_word_le hb]
  simpa only [supplyN] using hp

/-! ## Successful body effects -/

/-- The exact successful deposit effect re-establishes the frame invariant
with no callvalue left in flight. -/
theorem DepositEffect.preserves_inv {sevm : Sevm} {pre post : Devm}
    (he : DepositEffect sevm pre post)
    (h : Inv (Devm.getStor pre sevm.currentTarget) sevm.value
      (Devm.getBal pre sevm.currentTarget)) :
    Inv (Devm.getStor post sevm.currentTarget) 0
      (Devm.getBal post sevm.currentTarget) := by
  let stor := Devm.getStor pre sevm.currentTarget
  let B := Devm.getBal pre sevm.currentTarget
  let S := stor.get supplySlot
  let m := sevm.value * (S + offset) / (B - sevm.value + 1)
  change Inv stor sevm.value B at h
  change sevm.value ≤ maxValue ∧ B - sevm.value ≤ maxBalance ∧
    S + m ≤ maxSupply ∧
    Devm.getStor post sevm.currentTarget =
      (stor.set supplySlot (S + m)).set sevm.caller.toB256
        (stor.get sevm.caller.toB256 + m) ∧
    Devm.getBal post = Devm.getBal pre ∧
    Devm.getCode post = Devm.getCode pre ∧
    post.logs = pre.logs ∧ ReturnsWord m post at he
  rcases he with ⟨hv, hb, hcap, hstor, hbal, -, -, -⟩
  rw [hstor, hbal]
  change Inv
    ((stor.set supplySlot (S + m)).set sevm.caller.toB256
      (stor.get sevm.caller.toB256 + m)) 0 B
  have hnof : B256.Nof (stor.get supplySlot) m := by
    simpa only [m, S] using h.deposit_mint_nof hv hb
  refine ⟨?_, ?_, ?_⟩
  · simpa only [S] using h.mint_balSum_eq sevm.caller m hnof
  · unfold supplyN
    rw [Stor.get_prorataSupplySlot_set (validAdr_toB256 sevm.caller)]
    rw [Stor.get_set_self]
    exact B256.toNat_le_toNat hcap
  · rw [B256.toNat_zero, Nat.mul_zero, Nat.add_zero]
    calc
      supplyN ((stor.set supplySlot (S + m)).set sevm.caller.toB256
          (stor.get sevm.caller.toB256 + m)) =
          supplyN stor + m.toNat := by
        unfold supplyN
        rw [Stor.get_prorataSupplySlot_set (validAdr_toB256 sevm.caller)]
        rw [Stor.get_set_self]
        rw [B256.toNat_add_eq_of_nof _ _ hnof]
      _ ≤ offset.toNat * B.toNat := by
        simpa only [m, S] using h.deposit_price_bound hv hb

/-- The settled outer state immediately before the outbound withdrawal call
satisfies the invariant at the balance that will remain after payout.  This is
intentionally a pre-callback boundary, not a callback-final storage claim. -/
theorem WithdrawPreCallEffect.settlement_inv
    {sevm : Sevm} {pre callPre : Devm}
    (he : WithdrawPreCallEffect sevm pre callPre)
    (h : Inv (Devm.getStor pre sevm.currentTarget) sevm.value
      (Devm.getBal pre sevm.currentTarget)) :
    let shares := Sevm.argWord sevm 0
    let B := Devm.getBal pre sevm.currentTarget
    let S := (Devm.getStor pre sevm.currentTarget).get supplySlot
    let p := shares * (B + 1) / (S + offset)
    Inv (Devm.getStor callPre sevm.currentTarget) 0 (B - p) := by
  let shares := Sevm.argWord sevm 0
  let stor := Devm.getStor pre sevm.currentTarget
  let B := Devm.getBal pre sevm.currentTarget
  let C := stor.get sevm.caller.toB256
  let S := stor.get supplySlot
  let p := shares * (B + 1) / (S + offset)
  dsimp
  change Inv stor sevm.value B at h
  change shares ≤ C ∧ B ≤ maxBalance ∧
    Devm.getStor callPre sevm.currentTarget =
      (stor.set sevm.caller.toB256 (C - shares)).set supplySlot
        (S - shares) ∧
    Devm.getBal callPre = Devm.getBal pre ∧
    Devm.getCode callPre = Devm.getCode pre ∧
    callPre.logs = pre.logs ∧ callPre.output = pre.output ∧
    callPre.memory = pre.memory ∧
    ∃ gasWord,
      gasWord :: sevm.caller.toB256 :: p :: 0 :: 0 :: 0 :: 0 :: p :: S ::
        (S + offset) :: shares :: supplySlot :: [] <<+ callPre.stack at he
  rcases he with ⟨hcover, hb, hstor, -, -, -, -, -, -⟩
  rw [hstor]
  change Inv
    ((stor.set sevm.caller.toB256 (C - shares)).set supplySlot
      (S - shares)) 0 (B - p)
  have hsupply : shares ≤ stor.get supplySlot :=
    hcover.trans (h.share_word_le_supply sevm.caller)
  have hpay : p ≤ B := by
    simpa only [p, S, C] using
      h.withdraw_pay_word_le_balance sevm.caller hcover hb
  refine ⟨?_, ?_, ?_⟩
  · simpa only [C, S] using
      h.burn_balSum_eq sevm.caller shares hcover
  · unfold supplyN
    rw [Stor.get_set_self]
    rw [B256.toNat_sub_eq_of_le _ _ hsupply]
    exact (Nat.sub_le _ _).trans h.supply_le
  · rw [B256.toNat_zero, Nat.mul_zero, Nat.add_zero]
    rw [B256.toNat_sub_eq_of_le _ _ hpay]
    calc
      supplyN ((stor.set sevm.caller.toB256 (C - shares)).set supplySlot
          (S - shares)) = supplyN stor - shares.toNat := by
        unfold supplyN
        rw [Stor.get_set_self]
        rw [B256.toNat_sub_eq_of_le _ _ hsupply]
      _ ≤ offset.toNat * (B.toNat - p.toNat) := by
        simpa only [p, S, C] using
          h.withdraw_price_bound sevm.caller hcover hb

end Prorata

end Blanc
