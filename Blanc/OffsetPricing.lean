-- OffsetPricing.lean : virtual-offset share pricing, over the naturals.

import Jaune.MulDiv

/-!
# Virtual-offset share pricing

A vault that issues shares against a held asset prices them with a *virtual
offset*: `o` phantom shares and one phantom asset unit, so that the first
deposit cannot be front-run into a division by zero and a donation cannot move
the price without bound.  `mintN` and `payN` are the two directions, and every
result here is a statement about them and the offset alone.

Nothing names an asset, a contract or a program.  That is the point: the same
arithmetic prices PRORATA's ETH-denominated shares and the WETH-backed
ERC-4626 vault's, and the second consumer is what moved this out of
`Blanc/ProrataArithmetic.lean`, where it was stated only for the first.  The
B256-level lemmas that pin PRORATA's own constants stayed behind.
-/

namespace Blanc

open Jaune

namespace Prorata

/-- Nat-level deposit pricing, parameterized by the virtual-share offset. -/
def mintN (o amount supply balance : Nat) : Nat :=
  amount * (supply + o) / (balance + 1)

/-- Nat-level withdrawal pricing, parameterized by the virtual-share offset. -/
def payN (o shares supply balance : Nat) : Nat :=
  shares * (balance + 1) / (supply + o)

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
