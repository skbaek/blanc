-- Exact arithmetic facts for PRORATA's guarded pricing formulas.

import Blanc.Prorata
import Jaune.MulDiv

namespace Blanc

open Jaune

namespace Prorata

/-- Nat-level deposit pricing, parameterized by the virtual-share offset. -/
def mintN (o amount supply balance : Nat) : Nat :=
  amount * (supply + o) / (balance + 1)

/-- Nat-level withdrawal pricing, parameterized by the virtual-share offset. -/
def payN (o shares supply balance : Nat) : Nat :=
  shares * (balance + 1) / (supply + o)

@[simp] theorem offset_toNat : offset.toNat = 1000 := by
  rfl

@[simp] theorem maxValue_toNat :
    maxValue.toNat = 2 ^ 96 - 1 := by
  unfold maxValue
  rw [B256.toNat_toB256_of_lt]
  norm_num

@[simp] theorem maxSupply_toNat :
    maxSupply.toNat = 2 ^ 126 - 1 := by
  unfold maxSupply
  rw [B256.toNat_toB256_of_lt]
  norm_num

@[simp] theorem maxBalance_toNat :
    maxBalance.toNat = 2 ^ 126 - 1 := by
  unfold maxBalance
  rw [B256.toNat_toB256_of_lt]
  norm_num

/-- The stored supply cap leaves ample room for the virtual-share addition. -/
theorem supply_add_offset_nof {supply : B256}
    (h_supply : supply ≤ maxSupply) :
    B256.Nof supply offset := by
  unfold B256.Nof
  have h := B256.toNat_le_toNat h_supply
  rw [maxSupply_toNat] at h
  rw [offset_toNat]
  omega

/-- The target-balance cap leaves ample room for the virtual-asset addition. -/
theorem balance_add_one_nof {balance : B256}
    (h_balance : balance ≤ maxBalance) :
    B256.Nof balance 1 := by
  unfold B256.Nof
  have h := B256.toNat_le_toNat h_balance
  rw [maxBalance_toNat] at h
  rw [B256.toNat_one]
  omega

theorem balance_add_one_ne_zero {balance : B256}
    (h_balance : balance ≤ maxBalance) :
    balance + 1 ≠ 0 := by
  intro hzero
  have h := congrArg B256.toNat hzero
  rw [B256.toNat_add_eq_of_nof _ _ (balance_add_one_nof h_balance)] at h
  rw [B256.toNat_one, B256.toNat_zero] at h
  omega

theorem supply_add_offset_ne_zero {supply : B256}
    (h_supply : supply ≤ maxSupply) :
    supply + offset ≠ 0 := by
  intro hzero
  have h := congrArg B256.toNat hzero
  rw [B256.toNat_add_eq_of_nof _ _ (supply_add_offset_nof h_supply),
    offset_toNat] at h
  rw [B256.toNat_zero] at h
  omega

/-- PRORATA's deposit guards make its word multiplication exact. -/
theorem deposit_product_nofm {amount supply : B256}
    (h_amount : amount ≤ maxValue)
    (h_supply : supply ≤ maxSupply) :
    B256.Nofm amount (supply + offset) := by
  unfold B256.Nofm
  have ha := B256.toNat_le_toNat h_amount
  have hs := B256.toNat_le_toNat h_supply
  rw [maxValue_toNat] at ha
  rw [maxSupply_toNat] at hs
  rw [B256.toNat_add_eq_of_nof _ _ (supply_add_offset_nof h_supply),
    offset_toNat]
  calc
    amount.toNat * (supply.toNat + 1000)
        ≤ (2 ^ 96 - 1) * ((2 ^ 126 - 1) + 1000) :=
      Nat.mul_le_mul ha (Nat.add_le_add_right hs 1000)
    _ < 2 ^ 256 := by decide +kernel

/-- PRORATA's withdrawal guards make its word multiplication exact. -/
theorem withdraw_product_nofm {shares balance : B256}
    (h_shares : shares ≤ maxSupply)
    (h_balance : balance ≤ maxBalance) :
    B256.Nofm shares (balance + 1) := by
  unfold B256.Nofm
  have hs := B256.toNat_le_toNat h_shares
  have hb := B256.toNat_le_toNat h_balance
  rw [maxSupply_toNat] at hs
  rw [maxBalance_toNat] at hb
  rw [B256.toNat_add_eq_of_nof _ _ (balance_add_one_nof h_balance)]
  norm_num
  calc
    shares.toNat * (balance.toNat + 1)
        ≤ (2 ^ 126 - 1) * ((2 ^ 126 - 1) + 1) :=
      Nat.mul_le_mul hs (Nat.add_le_add_right hb 1)
    _ < 2 ^ 256 := by decide +kernel

/-- The guarded word-level deposit quote is exactly its Nat-level formula. -/
theorem deposit_quote_toNat
    {amount supply balance : B256}
    (h_amount : amount ≤ maxValue)
    (h_supply : supply ≤ maxSupply)
    (h_balance : balance ≤ maxBalance) :
    (amount * (supply + offset) / (balance + 1)).toNat =
      mintN offset.toNat amount.toNat supply.toNat balance.toNat := by
  rw [B256.toNat_mul_div_of_nofm
    (deposit_product_nofm h_amount h_supply)
    (balance_add_one_ne_zero h_balance)]
  rw [B256.toNat_add_eq_of_nof _ _ (supply_add_offset_nof h_supply)]
  rw [B256.toNat_add_eq_of_nof _ _ (balance_add_one_nof h_balance)]
  rfl

/-- The guarded word-level withdrawal quote is exactly its Nat-level formula. -/
theorem withdraw_quote_toNat
    {shares supply balance : B256}
    (h_shares : shares ≤ maxSupply)
    (h_supply : supply ≤ maxSupply)
    (h_balance : balance ≤ maxBalance) :
    (shares * (balance + 1) / (supply + offset)).toNat =
      payN offset.toNat shares.toNat supply.toNat balance.toNat := by
  rw [B256.toNat_mul_div_of_nofm
    (withdraw_product_nofm h_shares h_balance)
    (supply_add_offset_ne_zero h_supply)]
  rw [B256.toNat_add_eq_of_nof _ _ (balance_add_one_nof h_balance)]
  rw [B256.toNat_add_eq_of_nof _ _ (supply_add_offset_nof h_supply)]
  rfl

/-- Deposit pricing floors in the ledger's favor. -/
theorem mintN_never_overmints (o amount supply balance : Nat) :
    mintN o amount supply balance * (balance + 1) ≤
      amount * (supply + o) := by
  unfold mintN
  exact Nat.div_mul_le_self _ _

/-- Withdrawal pricing floors in the ledger's favor. -/
theorem payN_never_overpays (o shares supply balance : Nat) :
    payN o shares supply balance * (supply + o) ≤
      shares * (balance + 1) := by
  unfold payN
  exact Nat.div_mul_le_self _ _

/-- Rounding the required share burn upward makes the withdrawal cover the
requested asset amount. -/
theorem withdraw_ceil_shares_covers_assets
    {o supply balance assets : Nat} (ho : o ≠ 0) :
    assets ≤
      ceilDiv (assets * (supply + o)) (balance + 1) *
        (balance + 1) / (supply + o) := by
  exact Nat.le_ceilDiv_mul_div (by omega) (by omega) assets

/-- The ceil-valued assets of a floor-priced deposit never exceed the
deposited asset amount. -/
theorem deposit_floor_shares_ceil_assets_le
    {o supply balance assets : Nat} (ho : o ≠ 0) :
    ceilDiv (mintN o assets supply balance * (balance + 1))
      (supply + o) ≤ assets := by
  simpa only [mintN] using
    (ceilDiv_mul_div_mul_le (p := supply + o) (by omega)
      assets (balance + 1))

/-- The exact deposit-floor residue. -/
def depositResidueN (o amount supply balance : Nat) : Nat :=
  amount * (supply + o) % (balance + 1)

/-- The exact withdrawal-floor residue. -/
def withdrawResidueN (o shares supply balance : Nat) : Nat :=
  shares * (balance + 1) % (supply + o)

theorem mintN_residue_eq (o amount supply balance : Nat) :
    amount * (supply + o) =
      mintN o amount supply balance * (balance + 1) +
        depositResidueN o amount supply balance := by
  simpa only [mintN, depositResidueN] using
    (Nat.div_add_mod' (amount * (supply + o)) (balance + 1)).symm

theorem mintN_residue_lt (o amount supply balance : Nat) :
    depositResidueN o amount supply balance < balance + 1 := by
  unfold depositResidueN
  exact Nat.mod_lt _ (by omega)

theorem payN_residue_eq (o shares supply balance : Nat) :
    shares * (balance + 1) =
      payN o shares supply balance * (supply + o) +
        withdrawResidueN o shares supply balance := by
  simpa only [payN, withdrawResidueN] using
    (Nat.div_add_mod' (shares * (balance + 1)) (supply + o)).symm

theorem payN_residue_lt {o shares supply balance : Nat} (ho : o ≠ 0) :
    withdrawResidueN o shares supply balance < supply + o := by
  unfold withdrawResidueN
  exact Nat.mod_lt _ (by omega)

/-- The two exact pricing residues telescope even though both the numerator
and denominator change between deposit and immediate withdrawal. -/
theorem roundtrip_dust_eq
    {amount D X minted paid rhoDeposit rhoWithdraw : Nat}
    (h_deposit : amount * D = minted * X + rhoDeposit)
    (h_withdraw :
      minted * (X + amount) = paid * (D + minted) + rhoWithdraw) :
    amount * (D + minted) =
      paid * (D + minted) + rhoDeposit + rhoWithdraw := by
  calc
    amount * (D + minted) = amount * D + amount * minted := by
      rw [Nat.mul_add]
    _ = (minted * X + rhoDeposit) + amount * minted := by
      rw [h_deposit]
    _ = minted * X + minted * amount + rhoDeposit := by
      rw [Nat.mul_comm amount minted]
      omega
    _ = minted * (X + amount) + rhoDeposit := by
      rw [Nat.mul_add]
    _ = (paid * (D + minted) + rhoWithdraw) + rhoDeposit := by
      rw [h_withdraw]
    _ = paid * (D + minted) + rhoDeposit + rhoWithdraw := by
      omega

/-- A withdrawal cannot ask the contract to send more than its current
balance when the burned shares belong to the capped supply. -/
theorem payN_le_balance
    {o shares supply balance : Nat}
    (ho : o ≠ 0) (h_shares : shares ≤ supply) :
    payN o shares supply balance ≤ balance := by
  unfold payN
  have h_den : 0 < supply + o := by omega
  have h_num :
      shares * (balance + 1) <
        (balance + 1) * (supply + o) := by
    have h_lt : shares < supply + o := by omega
    simpa only [Nat.mul_comm] using
      Nat.mul_lt_mul_of_pos_right h_lt (by omega : 0 < balance + 1)
  have h_quot :
      shares * (balance + 1) / (supply + o) < balance + 1 := by
    rw [Nat.div_lt_iff_lt_mul h_den]
    exact h_num
  omega

/-- Deposit settlement cannot lower the cross-multiplied share price. -/
theorem deposit_price_nondecreasing
    (o amount supply balance : Nat) :
    (balance + 1) * (supply + mintN o amount supply balance + o) ≤
      (balance + amount + 1) * (supply + o) := by
  have h := mintN_never_overmints o amount supply balance
  have h' :
      (balance + 1) * mintN o amount supply balance ≤
        amount * (supply + o) := by
    simpa only [Nat.mul_comm] using h
  rw [show supply + mintN o amount supply balance + o =
      (supply + o) + mintN o amount supply balance by omega,
    Nat.mul_add,
    show balance + amount + 1 = (balance + 1) + amount by omega,
    Nat.add_mul (balance + 1) amount (supply + o)]
  exact Nat.add_le_add_left h' _

private theorem floor_withdraw_price_nondecreasing
    {X D shares paid : Nat}
    (h_shares : shares ≤ D)
    (h_floor : paid * D ≤ shares * X) :
    X * (D - shares) ≤ (X - paid) * D := by
  rw [Nat.sub_mul]
  apply Nat.le_sub_of_add_le
  calc
    X * (D - shares) + paid * D
        ≤ X * (D - shares) + shares * X :=
      Nat.add_le_add_left h_floor _
    _ = X * D := by
      rw [Nat.mul_comm shares X, ← Nat.mul_add,
        Nat.sub_add_cancel h_shares]

/-- Withdrawal settlement cannot lower the cross-multiplied share price. -/
theorem withdraw_price_nondecreasing
    {o shares supply balance : Nat}
    (ho : o ≠ 0) (h_shares : shares ≤ supply) :
    (balance + 1) * (supply - shares + o) ≤
      (balance - payN o shares supply balance + 1) * (supply + o) := by
  have h_paid :=
    payN_le_balance (balance := balance) ho h_shares
  have h :=
    floor_withdraw_price_nondecreasing
      (X := balance + 1) (D := supply + o)
      (shares := shares) (paid := payN o shares supply balance)
      (by omega)
      (payN_never_overpays o shares supply balance)
  rw [← Nat.sub_add_comm h_shares, ← Nat.sub_add_comm h_paid]
  exact h

/-- Under the genesis price bound, a deposit mints at most `o` shares per
asset unit. -/
theorem mintN_le_offset_mul
    {o amount supply balance : Nat}
    (h_price : supply ≤ o * balance) :
    mintN o amount supply balance ≤ o * amount := by
  have h_num :
      amount * (supply + o) ≤
        (o * amount) * (balance + 1) := by
    calc
      amount * (supply + o)
          ≤ amount * (o * balance + o) :=
        Nat.mul_le_mul_left amount (Nat.add_le_add_right h_price o)
      _ = (o * amount) * (balance + 1) := by
        simp only [Nat.mul_add]
        ac_rfl
  unfold mintN
  calc
    amount * (supply + o) / (balance + 1)
        ≤ ((o * amount) * (balance + 1)) / (balance + 1) :=
      Nat.div_le_div_right h_num
    _ = o * amount := Nat.mul_div_cancel _ (by omega)

theorem deposit_preserves_genesis_price
    {o amount supply balance : Nat}
    (h_price : supply ≤ o * balance) :
    supply + mintN o amount supply balance ≤
      o * (balance + amount) := by
  have h_mint :=
    mintN_le_offset_mul (amount := amount) h_price
  rw [Nat.mul_add]
  exact Nat.add_le_add h_price h_mint

/-- The same genesis price bound survives a successful withdrawal. -/
theorem withdraw_preserves_genesis_price
    {o shares supply balance : Nat}
    (ho : o ≠ 0)
    (h_shares : shares ≤ supply)
    (h_price : supply ≤ o * balance) :
    supply - shares ≤
      o * (balance - payN o shares supply balance) := by
  let paid := payN o shares supply balance
  let D := supply + o
  let X := balance + 1
  let slack := o * balance - supply
  have hD : 0 < D := by simp only [D]; omega
  have hsD : shares ≤ D := by simp only [D]; omega
  have h_supply_slack : supply + slack = o * balance := by
    simp only [slack]
    exact Nat.add_sub_of_le h_price
  have h_D_slack : D + slack = o * X := by
    simp only [D, X]
    calc
      supply + o + slack = (supply + slack) + o := by omega
      _ = o * balance + o := by rw [h_supply_slack]
      _ = o * (balance + 1) := by rw [Nat.mul_add, Nat.mul_one]
  have h_floor : paid * D ≤ shares * X := by
    simpa only [paid, D, X] using
      payN_never_overpays o shares supply balance
  have h_scaled_floor :
      (o * paid) * D ≤ o * shares * X := by
    calc
      (o * paid) * D = o * (paid * D) := by ac_rfl
      _ ≤ o * (shares * X) := Nat.mul_le_mul_left o h_floor
      _ = o * shares * X := by ac_rfl
  have h_slack_bound :
      o * shares * X ≤ (slack + shares) * D := by
    calc
      o * shares * X = shares * (o * X) := by ac_rfl
      _ = shares * (D + slack) := by rw [h_D_slack]
      _ = shares * D + shares * slack := by rw [Nat.mul_add]
      _ ≤ shares * D + slack * D := by
        exact Nat.add_le_add_left
          (by
            simpa only [Nat.mul_comm] using
              Nat.mul_le_mul_left slack hsD)
          _
      _ = (slack + shares) * D := by
        rw [Nat.add_mul]
        ac_rfl
  have h_opaid :
      o * paid ≤ slack + shares :=
    Nat.le_of_mul_le_mul_right
      (Nat.le_trans h_scaled_floor h_slack_bound) hD
  have h_sum :
      supply - shares + o * paid ≤ o * balance := by
    omega
  simp only [paid] at h_sum ⊢
  rw [Nat.mul_sub]
  exact Nat.le_sub_of_add_le h_sum

private theorem div_le_div_of_cross
    {n₁ n₂ d₁ d₂ : Nat}
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (h_cross : n₁ * d₂ ≤ n₂ * d₁) :
    n₁ / d₁ ≤ n₂ / d₂ := by
  apply (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hd₂)).2
  apply Nat.le_of_mul_le_mul_right (c := d₁) _ (Nat.pos_of_ne_zero hd₁)
  calc
    (n₁ / d₁ * d₂) * d₁ =
        (n₁ / d₁ * d₁) * d₂ := by ac_rfl
    _ ≤ n₁ * d₂ :=
      Nat.mul_le_mul_right d₂ (Nat.div_mul_le_self n₁ d₁)
    _ ≤ n₂ * d₁ := h_cross

/-- An immediate full-share withdrawal loses at most one old-price quantum,
with the exact ceiling frozen for P1. -/
theorem immediate_roundtrip_loss_le
    {o amount supply balance : Nat} (ho : o ≠ 0) :
    amount -
        payN o (mintN o amount supply balance)
          (supply + mintN o amount supply balance)
          (balance + amount) ≤
      ceilDiv ((balance + 1) - 1) (supply + o) := by
  let D := supply + o
  let X := balance + 1
  let minted := mintN o amount supply balance
  let paid := payN o minted (supply + minted) (balance + amount)
  have hDpos : 0 < D := by simp only [D]; omega
  have hD : D ≠ 0 := Nat.ne_of_gt hDpos
  have hX : X ≠ 0 := by simp only [X]; omega
  have h_price :
      X * (D + minted) ≤ (X + amount) * D := by
    simpa only [D, X, minted, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using deposit_price_nondecreasing o amount supply balance
  have h_old_le_new :
      minted * X / D ≤ minted * (X + amount) / (D + minted) := by
    apply div_le_div_of_cross hD (by omega)
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left minted h_price
  have h_paid :
      paid = minted * (X + amount) / (D + minted) := by
    simp only [paid, payN, D, X, minted]
    rw [show balance + amount + 1 = balance + 1 + amount by omega,
      show supply + mintN o amount supply balance + o =
        supply + o + mintN o amount supply balance by omega]
  rw [← h_paid] at h_old_le_new
  have h_minted :
      minted = amount * D / X := by
    simp only [minted, mintN, D, X]
  have h_a4 :=
    Nat.mul_div_mul_div_add_ceilDiv hD amount X
  rw [← h_minted] at h_a4
  have h_residue : amount * D % X ≤ X - 1 := by
    have hmod := Nat.mod_lt (amount * D) (Nat.pos_of_ne_zero hX)
    omega
  have h_ceil :
      ceilDiv (amount * D % X) D ≤ ceilDiv (X - 1) D :=
    ceilDiv_le_ceilDiv_right h_residue hD
  change amount - paid ≤ ceilDiv (X - 1) D
  omega

end Prorata

end Blanc
