-- Fork-independent arithmetic support for PRORATA attack analysis.

import Blanc.ProrataAccounting

namespace Blanc

namespace Prorata

/-- Cross-multiplied comparison of the virtual-asset price per share. -/
def PriceLe (o : Nat) (a b : AccountingSnapshot) : Prop :=
  (a.balance + 1) * (b.supply + o) ≤
    (b.balance + 1) * (a.supply + o)

/-- The asset claim represented by `shares` at a Nat-level snapshot. -/
def claimN (o shares supply balance : Nat) : Nat :=
  payN o shares supply balance

namespace PriceLe

theorem refl (o : Nat) (snapshot : AccountingSnapshot) :
    PriceLe o snapshot snapshot := by
  exact Nat.le_refl _

theorem trans {o : Nat} (ho : o ≠ 0) {a b c : AccountingSnapshot}
    (hab : PriceLe o a b) (hbc : PriceLe o b c) :
    PriceLe o a c := by
  unfold PriceLe at hab hbc ⊢
  apply Nat.le_of_mul_le_mul_right (c := b.supply + o) _ (by omega)
  calc
    ((a.balance + 1) * (c.supply + o)) * (b.supply + o) =
        ((a.balance + 1) * (b.supply + o)) * (c.supply + o) := by
      ac_rfl
    _ ≤ ((b.balance + 1) * (a.supply + o)) * (c.supply + o) :=
      Nat.mul_le_mul_right (c.supply + o) hab
    _ = ((b.balance + 1) * (c.supply + o)) * (a.supply + o) := by
      ac_rfl
    _ ≤ ((c.balance + 1) * (b.supply + o)) * (a.supply + o) :=
      Nat.mul_le_mul_right (a.supply + o) hbc
    _ = ((c.balance + 1) * (a.supply + o)) * (b.supply + o) := by
      ac_rfl

end PriceLe

namespace ProrataAccountingEffect

/-- Every classified accounting effect weakly increases the share price. -/
theorem priceLe {o : Nat} (ho : o ≠ 0)
    {pre post : AccountingSnapshot} {kind : ProrataAccountingKind}
    (effect : ProrataAccountingEffect o pre kind post) :
    PriceLe o pre post := by
  cases effect with
  | deposit supply balance amount minted hquote =>
      subst minted
      simpa only [PriceLe] using
        deposit_price_nondecreasing o amount supply balance
  | withdraw supply balance shares paid hshares hquote =>
      subst paid
      simpa only [PriceLe] using
        withdraw_price_nondecreasing ho hshares
  | externalCredit supply balance amount hpositive =>
      unfold PriceLe
      simpa only using
        Nat.mul_le_mul_right (supply + o)
          (Nat.add_le_add_right (Nat.le_add_right balance amount) 1)
  | silent snapshot =>
      exact PriceLe.refl o pre

end ProrataAccountingEffect

/-- A holder cannot claim more than the contract balance when its shares are
part of the accounted supply. -/
theorem claimN_le_balance {o shares supply balance : Nat}
    (ho : o ≠ 0) (hshares : shares ≤ supply) :
    claimN o shares supply balance ≤ balance := by
  simpa only [claimN] using
    payN_le_balance (balance := balance) ho hshares

private theorem nat_div_le_nat_div_of_cross
    {n₁ n₂ d₁ d₂ : Nat}
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (hcross : n₁ * d₂ ≤ n₂ * d₁) :
    n₁ / d₁ ≤ n₂ / d₂ := by
  apply (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hd₂)).2
  apply Nat.le_of_mul_le_mul_right (c := d₁) _ (Nat.pos_of_ne_zero hd₁)
  calc
    (n₁ / d₁ * d₂) * d₁ =
        (n₁ / d₁ * d₁) * d₂ := by
      ac_rfl
    _ ≤ n₁ * d₂ :=
      Nat.mul_le_mul_right d₂ (Nat.div_mul_le_self n₁ d₁)
    _ ≤ n₂ * d₁ := hcross

/-- A fixed share balance has a weakly larger floor-valued claim at a weakly
larger share price. -/
theorem payN_mono_price {o shares : Nat} (ho : o ≠ 0)
    {pre post : AccountingSnapshot} (hprice : PriceLe o pre post) :
    payN o shares pre.supply pre.balance ≤
      payN o shares post.supply post.balance := by
  unfold payN
  apply nat_div_le_nat_div_of_cross (by omega) (by omega)
  unfold PriceLe at hprice
  calc
    shares * (pre.balance + 1) * (post.supply + o) =
        shares * ((pre.balance + 1) * (post.supply + o)) := by
      ac_rfl
    _ ≤ shares * ((post.balance + 1) * (pre.supply + o)) :=
      Nat.mul_le_mul_left shares hprice
    _ = shares * (post.balance + 1) * (pre.supply + o) := by
      ac_rfl

/-- An external credit can increase an accounted holder's claim by at most the
credited amount. -/
theorem claimN_externalCredit_le {o shares supply balance amount : Nat}
    (ho : o ≠ 0) (hshares : shares ≤ supply) :
    claimN o shares supply (balance + amount) ≤
      claimN o shares supply balance + amount := by
  unfold claimN payN
  have hD : 0 < supply + o := by omega
  have hsharesD : shares ≤ supply + o :=
    hshares.trans (Nat.le_add_right supply o)
  have hscaled :
      shares * amount ≤ (supply + o) * amount :=
    Nat.mul_le_mul_right amount hsharesD
  rw [show balance + amount + 1 = (balance + 1) + amount by omega,
    Nat.mul_add]
  calc
    (shares * (balance + 1) + shares * amount) / (supply + o)
        ≤ (shares * (balance + 1) + (supply + o) * amount) /
            (supply + o) :=
      Nat.div_le_div_right (Nat.add_le_add_left hscaled _)
    _ = shares * (balance + 1) / (supply + o) + amount :=
      Nat.add_mul_div_left _ _ hD

end Prorata

end Blanc
