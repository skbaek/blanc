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

private theorem deposit_claim_update_of_residues
    {D X attacker amount claim minted r t : Nat}
    (hD : 0 < D) (hAmount : 0 < amount) (hattacker : attacker < D)
    (hclaim : attacker * X = claim * D + r) (hr : r < D)
    (hmint : amount * D = minted * X + t) :
    (attacker + minted) * (X + amount) / (D + minted) ≤
      claim + amount := by
  have hmt : 0 < minted ∨ 0 < t := by
    by_cases hm : minted = 0
    · right
      have hprod : 0 < amount * D := Nat.mul_pos hAmount hD
      simp only [hm, Nat.zero_mul, Nat.zero_add] at hmint
      omega
    · left
      exact Nat.pos_of_ne_zero hm
  have hslack :
      minted * r + attacker * t < minted * D + D * t := by
    rcases hmt with hm | ht
    · exact Nat.add_lt_add_of_lt_of_le
        (Nat.mul_lt_mul_of_pos_left hr hm)
        (Nat.mul_le_mul_right t (Nat.le_of_lt hattacker))
    · exact Nat.add_lt_add_of_le_of_lt
        (Nat.mul_le_mul_left minted (Nat.le_of_lt hr))
        (Nat.mul_lt_mul_of_pos_right hattacker ht)
  have hscaledEq :
      (attacker * amount) * D =
        (claim * minted) * D + (minted * r + attacker * t) := by
    calc
      (attacker * amount) * D = attacker * (amount * D) := by
        ac_rfl
      _ = attacker * (minted * X + t) := by rw [hmint]
      _ = attacker * (minted * X) + attacker * t := by
        rw [Nat.mul_add]
      _ = minted * (attacker * X) + attacker * t := by
        ac_rfl
      _ = minted * (claim * D + r) + attacker * t := by
        rw [hclaim]
      _ = (claim * minted) * D + (minted * r + attacker * t) := by
        rw [Nat.mul_add]
        ac_rfl
  have hscaled :
      (attacker * amount) * D <
        ((claim + 1) * minted + t) * D := by
    calc
      (attacker * amount) * D =
          (claim * minted) * D + (minted * r + attacker * t) :=
        hscaledEq
      _ < (claim * minted) * D + (minted * D + D * t) :=
        Nat.add_lt_add_left hslack _
      _ = ((claim + 1) * minted + t) * D := by
        simp only [Nat.add_mul, Nat.one_mul]
        ac_rfl
  have hcross : attacker * amount < (claim + 1) * minted + t :=
    Nat.lt_of_mul_lt_mul_right hscaled
  have hgap :
      r + attacker * amount < D + ((claim + 1) * minted + t) :=
    Nat.add_lt_add hr hcross
  have hnum :
      (attacker + minted) * (X + amount) <
        (claim + amount + 1) * (D + minted) := by
    calc
      (attacker + minted) * (X + amount) =
          claim * D + minted * X + minted * amount +
            (r + attacker * amount) := by
        calc
          (attacker + minted) * (X + amount) =
              attacker * X + minted * X + minted * amount +
                attacker * amount := by
            simp only [Nat.add_mul, Nat.mul_add]
            ac_rfl
          _ = (claim * D + r) + minted * X + minted * amount +
                attacker * amount := by
            rw [hclaim]
          _ = claim * D + minted * X + minted * amount +
                (r + attacker * amount) := by
            omega
      _ < claim * D + minted * X + minted * amount +
            (D + ((claim + 1) * minted + t)) :=
        Nat.add_lt_add_left hgap _
      _ = (claim + amount + 1) * (D + minted) := by
        calc
          claim * D + minted * X + minted * amount +
              (D + ((claim + 1) * minted + t)) =
              claim * D + amount * D + D + claim * minted +
                amount * minted + minted := by
            rw [hmint]
            simp only [Nat.add_mul, Nat.one_mul]
            ac_rfl
          _ = (claim + amount + 1) * (D + minted) := by
            simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
            ac_rfl
  have hquot :
      (attacker + minted) * (X + amount) / (D + minted) <
        claim + amount + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    exact hnum
  omega

/-- A coalition deposit can increase its redemption claim by at most the
deposited amount. -/
theorem claimN_deposit_le
    {o attacker supply balance amount minted : Nat}
    (ho : o ≠ 0) (hattacker : attacker ≤ supply)
    (hminted : minted = mintN o amount supply balance) :
    claimN o (attacker + minted) (supply + minted) (balance + amount) ≤
      claimN o attacker supply balance + amount := by
  subst minted
  by_cases hAmount : amount = 0
  · subst amount
    simp only [mintN, Nat.zero_mul, Nat.zero_div, Nat.add_zero]
    exact Nat.le_refl _
  · have hD : 0 < supply + o := by omega
    have hattackerD : attacker < supply + o := by omega
    have hclaim :
        attacker * (balance + 1) =
          claimN o attacker supply balance * (supply + o) +
            withdrawResidueN o attacker supply balance := by
      simpa only [claimN] using payN_residue_eq o attacker supply balance
    have hr :
        withdrawResidueN o attacker supply balance < supply + o :=
      payN_residue_lt (shares := attacker) (supply := supply)
        (balance := balance) ho
    have h :=
      deposit_claim_update_of_residues
        (D := supply + o) (X := balance + 1)
        (attacker := attacker) (amount := amount)
        (claim := claimN o attacker supply balance)
        (minted := mintN o amount supply balance)
        (r := withdrawResidueN o attacker supply balance)
        (t := depositResidueN o amount supply balance)
        hD (Nat.pos_of_ne_zero hAmount) hattackerD hclaim hr
        (mintN_residue_eq o amount supply balance)
    simpa only [claimN, payN, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using h

private theorem withdraw_claim_update_of_residues
    {D X attacker burned claim paid rAll rBurn : Nat}
    (hattackerD : attacker < D)
    (hburned : burned ≤ attacker) (hpaidClaim : paid ≤ claim)
    (hpaidX : paid ≤ X)
    (hAll : attacker * X = claim * D + rAll)
    (hAllResidue : rAll < D)
    (hBurn : burned * X = paid * D + rBurn) :
    paid + (attacker - burned) * (X - paid) / (D - burned) ≤
      claim := by
  have hburnedD : burned < D := hburned.trans_lt hattackerD
  have hDr : 0 < D - rAll := by omega
  have hkey :
      burned * (claim + 1) <
        attacker * paid + (D - rAll + rBurn) := by
    by_cases hcase : burned * (claim + 1) ≤ attacker * paid
    · omega
    · have hap : attacker * paid < burned * (claim + 1) := by omega
      have hraw :
          attacker * paid * D +
              (burned * (D - rAll) + attacker * rBurn) =
            burned * (claim + 1) * D := by
        calc
          attacker * paid * D +
                (burned * (D - rAll) + attacker * rBurn) =
              attacker * (paid * D + rBurn) +
                burned * (D - rAll) := by
            simp only [Nat.mul_add]
            ac_rfl
          _ = attacker * (burned * X) + burned * (D - rAll) := by
            rw [← hBurn]
          _ = burned * (attacker * X) + burned * (D - rAll) := by
            ac_rfl
          _ = burned * (claim * D + rAll) + burned * (D - rAll) := by
            rw [hAll]
          _ = burned * (claim * D + rAll + (D - rAll)) := by
            simp only [Nat.mul_add]
          _ = burned * (claim * D + D) := by
            rw [Nat.add_assoc,
              Nat.add_sub_of_le (Nat.le_of_lt hAllResidue)]
          _ = burned * ((claim + 1) * D) := by
            rw [Nat.add_mul, Nat.one_mul]
          _ = burned * (claim + 1) * D := by
            ac_rfl
      have hscaledEq :
          (burned * (claim + 1) - attacker * paid) * D =
            burned * (D - rAll) + attacker * rBurn := by
        rw [Nat.sub_mul]
        omega
      have hleft :
          burned * (D - rAll) < D * (D - rAll) :=
        Nat.mul_lt_mul_of_pos_right hburnedD hDr
      have hright : attacker * rBurn ≤ D * rBurn :=
        Nat.mul_le_mul_right rBurn (Nat.le_of_lt hattackerD)
      have hresBound :
          burned * (D - rAll) + attacker * rBurn <
            (D - rAll + rBurn) * D := by
        calc
          burned * (D - rAll) + attacker * rBurn <
              D * (D - rAll) + D * rBurn :=
            Nat.add_lt_add_of_lt_of_le hleft hright
          _ = (D - rAll + rBurn) * D := by
            simp only [Nat.add_mul]
            ac_rfl
      have hdiff :
          burned * (claim + 1) - attacker * paid <
            D - rAll + rBurn :=
        Nat.lt_of_mul_lt_mul_right
          (by
            calc
              (burned * (claim + 1) - attacker * paid) * D =
                  burned * (D - rAll) + attacker * rBurn := hscaledEq
              _ < (D - rAll + rBurn) * D := hresBound)
      omega
  have hnum :
      (attacker - burned) * (X - paid) <
        (claim - paid + 1) * (D - burned) := by
    have hremX :
        (attacker - burned) * (X - paid) +
            (attacker - burned) * paid =
          (attacker - burned) * X := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hpaidX]
    have haPaid :
        (attacker - burned) * paid + burned * paid =
          attacker * paid := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hburned]
    have haX :
        (attacker - burned) * X + burned * X =
          attacker * X := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hburned]
    have hqD :
        (claim - paid) * D + paid * D = claim * D := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hpaidClaim]
    have hqBurned :
        (claim - paid) * burned + paid * burned =
          claim * burned := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hpaidClaim]
    have hremD :
        (claim - paid) * (D - burned) +
            (claim - paid) * burned =
          (claim - paid) * D := by
      rw [← Nat.mul_add,
        Nat.sub_add_cancel (Nat.le_of_lt hburnedD)]
    have hDsplit : D - burned + burned = D :=
      Nat.sub_add_cancel (Nat.le_of_lt hburnedD)
    have hR :
        (claim - paid + 1) * (D - burned) =
          (claim - paid) * (D - burned) + (D - burned) := by
      simp only [Nat.add_mul, Nat.one_mul]
    have hBurnClaim :
        burned * (claim + 1) = claim * burned + burned := by
      simp only [Nat.mul_add, Nat.mul_one, Nat.mul_comm burned claim]
    have hleft :
        (attacker - burned) * (X - paid) + attacker * paid =
          (attacker - burned) * X + burned * paid := by
      omega
    have hright :
        (claim - paid + 1) * (D - burned) +
            burned * (claim + 1) =
          (claim - paid) * D + D + paid * burned := by
      omega
    have hresCore :
        (attacker - burned) * X + rBurn =
          (claim - paid) * D + rAll := by
      omega
    have hresShift :
        (attacker - burned) * X + (D - rAll + rBurn) =
          (claim - paid) * D + D := by
      omega
    have hpaidBurn : burned * paid = paid * burned :=
      Nat.mul_comm burned paid
    have hbalance :
        (attacker - burned) * (X - paid) +
            (attacker * paid + (D - rAll + rBurn)) =
          (claim - paid + 1) * (D - burned) +
            burned * (claim + 1) := by
      omega
    omega
  have hquot :
      (attacker - burned) * (X - paid) / (D - burned) <
        claim - paid + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    exact hnum
  omega

/-- A coalition withdrawal plus its remaining redemption claim cannot exceed
its pre-withdrawal claim. -/
theorem claimN_withdraw_le
    {o attacker supply balance burned paid : Nat}
    (ho : o ≠ 0) (hburned : burned ≤ attacker)
    (hattacker : attacker ≤ supply)
    (hpaid : paid = payN o burned supply balance) :
    paid + claimN o (attacker - burned) (supply - burned) (balance - paid) ≤
      claimN o attacker supply balance := by
  subst paid
  have hburnedSupply : burned ≤ supply := hburned.trans hattacker
  have hpaidBalance :
      payN o burned supply balance ≤ balance :=
    payN_le_balance ho hburnedSupply
  have h :=
    withdraw_claim_update_of_residues
      (D := supply + o) (X := balance + 1)
      (attacker := attacker) (burned := burned)
      (claim := claimN o attacker supply balance)
      (paid := payN o burned supply balance)
      (rAll := withdrawResidueN o attacker supply balance)
      (rBurn := withdrawResidueN o burned supply balance)
      (by omega) hburned
      (by
        unfold claimN payN
        exact Nat.div_le_div_right
          (Nat.mul_le_mul_right (balance + 1) hburned))
      (by omega)
      (by simpa only [claimN] using
        payN_residue_eq o attacker supply balance)
      (payN_residue_lt (shares := attacker) (supply := supply)
        (balance := balance) ho)
      (payN_residue_eq o burned supply balance)
  change payN o burned supply balance +
      payN o (attacker - burned) (supply - burned)
        (balance - payN o burned supply balance) ≤
    payN o attacker supply balance
  unfold claimN at h
  unfold payN at h hpaidBalance ⊢
  rw [show balance - burned * (balance + 1) / (supply + o) + 1 =
      balance + 1 - burned * (balance + 1) / (supply + o) by omega,
    show supply - burned + o = supply + o - burned by omega]
  exact h

/-- A deposit by another holder leaves the pre-existing full-supply claimant
with a redemption claim no larger than the pre-deposit balance. -/
theorem fullSupply_claim_after_deposit_le
    {o supply balance amount minted : Nat}
    (ho : o ≠ 0) (hminted : minted = mintN o amount supply balance) :
    claimN o supply (supply + minted) (balance + amount) ≤ balance := by
  subst minted
  by_cases hAmount : amount = 0
  · subst amount
    simpa only [mintN, Nat.zero_mul, Nat.zero_div, Nat.add_zero] using
      (claimN_le_balance (o := o) (shares := supply) (supply := supply)
        (balance := balance) ho (Nat.le_refl supply))
  · have hD : 0 < supply + o := by omega
    have hSupplyD : supply < supply + o := by omega
    have hmint := mintN_residue_eq o amount supply balance
    have ht := mintN_residue_lt o amount supply balance
    have hXle : balance + 1 ≤ o * (balance + 1) := by
      simpa only [Nat.one_mul] using
        Nat.mul_le_mul_right (balance + 1) (show 1 ≤ o by omega)
    have hSupplyAmount :
        supply * amount <
          (balance + 1) * (o + mintN o amount supply balance) := by
      calc
        supply * amount < amount * (supply + o) := by
          simpa only [Nat.mul_comm] using
            Nat.mul_lt_mul_of_pos_right hSupplyD
              (Nat.pos_of_ne_zero hAmount)
        _ = mintN o amount supply balance * (balance + 1) +
              depositResidueN o amount supply balance := hmint
        _ < mintN o amount supply balance * (balance + 1) +
              o * (balance + 1) :=
          Nat.add_lt_add_left (ht.trans_le hXle) _
        _ = (balance + 1) * (o + mintN o amount supply balance) := by
          simp only [Nat.mul_add]
          simp only [Nat.add_mul, Nat.mul_one, Nat.one_mul]
          ac_rfl
    have hnum :
        supply * (balance + amount + 1) <
          (balance + 1) *
            (supply + mintN o amount supply balance + o) := by
      calc
        supply * (balance + amount + 1) =
            supply * (balance + 1) + supply * amount := by
          rw [show balance + amount + 1 = (balance + 1) + amount by omega,
            Nat.mul_add]
        _ < supply * (balance + 1) +
              (balance + 1) * (o + mintN o amount supply balance) :=
          Nat.add_lt_add_left hSupplyAmount _
        _ = (balance + 1) *
              (supply + mintN o amount supply balance + o) := by
          simp only [Nat.mul_add]
          simp only [Nat.add_mul, Nat.mul_one, Nat.one_mul]
          ac_rfl
    unfold claimN payN
    have hquot :
        supply * (balance + amount + 1) /
            (supply + mintN o amount supply balance + o) <
          balance + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      exact hnum
    omega

/-- The genesis price bound and `2 ≤ o` absorb one old-price ceiling quantum. -/
theorem ceilDiv_balance_mul_le_offset
    {o supply balance : Nat} (ho : 2 ≤ o)
    (hprice : supply ≤ o * balance) :
    Jaune.ceilDiv balance (supply + o) * (supply + o) ≤
      o * (balance + 1) := by
  have hD : 0 < supply + o := by omega
  have hDprice : supply + o ≤ o * (balance + 1) := by
    calc
      supply + o ≤ o * balance + o :=
        Nat.add_le_add_right hprice o
      _ = o * (balance + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
  by_cases hsmall : balance < supply + o
  · have hceil :
        Jaune.ceilDiv balance (supply + o) ≤ 1 :=
      (Jaune.ceilDiv_le_iff (Nat.ne_of_gt hD) balance 1).2
        (by simpa only [Nat.one_mul] using Nat.le_of_lt hsmall)
    have hceilD :
        Jaune.ceilDiv balance (supply + o) * (supply + o) ≤
          supply + o := by
      simpa only [Nat.one_mul] using
        Nat.mul_le_mul_right (supply + o) hceil
    exact hceilD.trans hDprice
  · have hDbalance : supply + o ≤ balance := by omega
    have hover :=
      Jaune.ceilDiv_mul_lt (Nat.ne_of_gt hD) balance
    have hsum : balance + (supply + o) ≤ o * (balance + 1) := by
      calc
        balance + (supply + o) ≤ 2 * balance := by omega
        _ ≤ o * balance := Nat.mul_le_mul_right balance ho
        _ ≤ o * (balance + 1) :=
          Nat.mul_le_mul_left o (Nat.le_add_right balance 1)
    exact Nat.le_of_lt (hover.trans_le hsum)

/-- After a victim fully exits at a no-lower price, the remaining coalition's
claim is bounded by the balance excluding the victim's deposit. -/
theorem victim_full_exit_claim_le
    {o initialSupply initialBalance victim minted attacker balance paid : Nat}
    (ho : 2 ≤ o) (hgenesis : initialSupply ≤ o * initialBalance)
    (hminted : minted = mintN o victim initialSupply initialBalance)
    (hprice : PriceLe o ⟨initialSupply, initialBalance⟩
      ⟨attacker + minted, balance⟩)
    (hpaid : paid = payN o minted (attacker + minted) balance) :
    claimN o attacker attacker (balance - paid) ≤ balance - victim := by
  subst minted
  subst paid
  have ho0 : o ≠ 0 := by omega
  have hD0 : initialSupply + o ≠ 0 := by omega
  have hX0 : initialBalance + 1 ≠ 0 := by omega
  have hpaidBalance :
      payN o (mintN o victim initialSupply initialBalance)
          (attacker + mintN o victim initialSupply initialBalance) balance ≤
        balance :=
    payN_le_balance ho0 (by omega)
  have holdPaidLe :
      payN o (mintN o victim initialSupply initialBalance)
          initialSupply initialBalance ≤
        payN o (mintN o victim initialSupply initialBalance)
          (attacker + mintN o victim initialSupply initialBalance) balance :=
    payN_mono_price ho0 hprice
  have holdLoss :
      victim -
          payN o (mintN o victim initialSupply initialBalance)
            initialSupply initialBalance ≤
        Jaune.ceilDiv initialBalance (initialSupply + o) := by
    simpa only [mintN, payN, Nat.add_sub_cancel_right] using
      (Jaune.Nat.sub_mul_div_mul_div_le hD0 hX0 victim)
  have hloss :
      victim -
          payN o (mintN o victim initialSupply initialBalance)
            (attacker + mintN o victim initialSupply initialBalance) balance ≤
        Jaune.ceilDiv initialBalance (initialSupply + o) :=
    (Nat.sub_le_sub_left holdPaidLe victim).trans holdLoss
  have hmintLt :
      victim * (initialSupply + o) <
        (initialBalance + 1) *
          (mintN o victim initialSupply initialBalance + 1) := by
    simpa only [mintN] using
      (Jaune.Nat.lt_mul_div_add_one hX0 victim (initialSupply + o))
  have hmintOffset :
      victim * (initialSupply + o) <
        (initialBalance + 1) *
          (mintN o victim initialSupply initialBalance + o) :=
    hmintLt.trans_le
      (Nat.mul_le_mul_left (initialBalance + 1) (by omega))
  unfold PriceLe at hprice
  have hsumLt :
      attacker * (initialBalance + 1) +
          victim * (initialSupply + o) <
        (balance + 1) * (initialSupply + o) := by
    calc
      attacker * (initialBalance + 1) +
            victim * (initialSupply + o) <
          attacker * (initialBalance + 1) +
            (initialBalance + 1) *
              (mintN o victim initialSupply initialBalance + o) :=
        Nat.add_lt_add_left hmintOffset _
      _ = (initialBalance + 1) *
            (attacker + mintN o victim initialSupply initialBalance + o) := by
        rw [Nat.mul_add (initialBalance + 1)
            (attacker + mintN o victim initialSupply initialBalance) o,
          Nat.mul_add (initialBalance + 1) attacker
            (mintN o victim initialSupply initialBalance),
          Nat.mul_add (initialBalance + 1)
            (mintN o victim initialSupply initialBalance) o]
        ac_rfl
      _ ≤ (balance + 1) * (initialSupply + o) := by
        simpa only using hprice
  have hvX : victim < balance + 1 := by
    apply Nat.lt_of_mul_lt_mul_right
    calc
      victim * (initialSupply + o) ≤
          attacker * (initialBalance + 1) +
            victim * (initialSupply + o) :=
        Nat.le_add_left _ _
      _ < (balance + 1) * (initialSupply + o) := hsumLt
  have hvBalance : victim ≤ balance := by omega
  have hcoalition :
      attacker * (initialBalance + 1) <
        (balance + 1 - victim) * (initialSupply + o) := by
    have hsplit :
        (balance + 1 - victim) * (initialSupply + o) +
            victim * (initialSupply + o) =
          (balance + 1) * (initialSupply + o) := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hvX)]
    omega
  have hceil :=
    ceilDiv_balance_mul_le_offset ho hgenesis
  have hreserve :
      attacker *
          (victim -
            payN o (mintN o victim initialSupply initialBalance)
              (attacker + mintN o victim initialSupply initialBalance)
                balance) <
        o * (balance + 1 - victim) := by
    by_cases hlossZero :
        victim -
            payN o (mintN o victim initialSupply initialBalance)
              (attacker + mintN o victim initialSupply initialBalance)
                balance = 0
    · rw [hlossZero, Nat.mul_zero]
      exact Nat.mul_pos (by omega) (by omega)
    · have hceilPos :
          0 < Jaune.ceilDiv initialBalance (initialSupply + o) := by
        omega
      have hscaled :
          (attacker *
              Jaune.ceilDiv initialBalance (initialSupply + o)) *
              (initialBalance + 1) <
            (o * (balance + 1 - victim)) *
              (initialBalance + 1) := by
        calc
          (attacker *
                Jaune.ceilDiv initialBalance (initialSupply + o)) *
                (initialBalance + 1) =
              (attacker * (initialBalance + 1)) *
                Jaune.ceilDiv initialBalance (initialSupply + o) := by
            ac_rfl
          _ < ((balance + 1 - victim) * (initialSupply + o)) *
                Jaune.ceilDiv initialBalance (initialSupply + o) :=
            Nat.mul_lt_mul_of_pos_right hcoalition hceilPos
          _ = (Jaune.ceilDiv initialBalance (initialSupply + o) *
                (initialSupply + o)) * (balance + 1 - victim) := by
            ac_rfl
          _ ≤ (o * (initialBalance + 1)) *
                (balance + 1 - victim) :=
            Nat.mul_le_mul_right (balance + 1 - victim) hceil
          _ = (o * (balance + 1 - victim)) *
                (initialBalance + 1) := by
            ac_rfl
      have hceilReserve :
          attacker * Jaune.ceilDiv initialBalance (initialSupply + o) <
            o * (balance + 1 - victim) :=
        Nat.lt_of_mul_lt_mul_right hscaled
      exact
        (Nat.mul_le_mul_left attacker hloss).trans_lt hceilReserve
  have hnum :
      attacker *
          (balance -
              payN o (mintN o victim initialSupply initialBalance)
                (attacker + mintN o victim initialSupply initialBalance)
                  balance + 1) <
        (balance - victim + 1) * (attacker + o) := by
    by_cases hpaidVictim :
        payN o (mintN o victim initialSupply initialBalance)
            (attacker + mintN o victim initialSupply initialBalance)
              balance ≤ victim
    · have hsplit :
          balance -
                payN o (mintN o victim initialSupply initialBalance)
                  (attacker + mintN o victim initialSupply initialBalance)
                    balance + 1 =
            (balance + 1 - victim) +
              (victim -
                payN o (mintN o victim initialSupply initialBalance)
                  (attacker + mintN o victim initialSupply initialBalance)
                    balance) := by
        omega
      have htarget : balance - victim + 1 = balance + 1 - victim := by
        omega
      calc
        attacker *
              (balance -
                  payN o (mintN o victim initialSupply initialBalance)
                    (attacker + mintN o victim initialSupply initialBalance)
                      balance + 1) =
            attacker * (balance + 1 - victim) +
              attacker *
                (victim -
                  payN o (mintN o victim initialSupply initialBalance)
                    (attacker + mintN o victim initialSupply initialBalance)
                      balance) := by
          rw [hsplit, Nat.mul_add]
        _ < attacker * (balance + 1 - victim) +
              o * (balance + 1 - victim) :=
          Nat.add_lt_add_left hreserve _
        _ = (balance - victim + 1) * (attacker + o) := by
          rw [htarget,
            Nat.mul_add (balance + 1 - victim) attacker o]
          ac_rfl
    · have hremaining :
          balance -
                payN o (mintN o victim initialSupply initialBalance)
                  (attacker + mintN o victim initialSupply initialBalance)
                    balance + 1 ≤
            balance - victim + 1 := by
        omega
      calc
        attacker *
              (balance -
                  payN o (mintN o victim initialSupply initialBalance)
                    (attacker + mintN o victim initialSupply initialBalance)
                      balance + 1) ≤
            attacker * (balance - victim + 1) :=
          Nat.mul_le_mul_left attacker hremaining
        _ < (attacker + o) * (balance - victim + 1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        _ = (balance - victim + 1) * (attacker + o) :=
          Nat.mul_comm _ _
  unfold claimN payN
  have hquot :
      attacker *
            (balance -
                mintN o victim initialSupply initialBalance * (balance + 1) /
                  (attacker + mintN o victim initialSupply initialBalance + o) +
              1) /
          (attacker + o) <
        balance - victim + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    simpa only [payN] using hnum
  omega

/-- A victim's full-exit loss at a no-lower post-deposit price is at most one
old-price ceiling quantum. -/
theorem victim_loss_le_ceil
    {o initialSupply initialBalance victim minted
      exitSupply exitBalance paid : Nat}
    (ho : o ≠ 0)
    (hminted : minted = mintN o victim initialSupply initialBalance)
    (hprice : PriceLe o
      ⟨initialSupply + minted, initialBalance + victim⟩
      ⟨exitSupply, exitBalance⟩)
    (hpaid : paid = payN o minted exitSupply exitBalance) :
    victim - paid ≤
      Jaune.ceilDiv initialBalance (initialSupply + o) := by
  subst minted
  subst paid
  have hpayoutMono :
      payN o (mintN o victim initialSupply initialBalance)
          (initialSupply + mintN o victim initialSupply initialBalance)
          (initialBalance + victim) ≤
        payN o (mintN o victim initialSupply initialBalance)
          exitSupply exitBalance :=
    payN_mono_price ho hprice
  have himmediate :=
    immediate_roundtrip_loss_le
      (o := o) (amount := victim) (supply := initialSupply)
      (balance := initialBalance) ho
  exact
    (Nat.sub_le_sub_left hpayoutMono victim).trans
      (by simpa only [Nat.add_sub_cancel_right] using himmediate)

/-- The ceiling loss bound implies the looser division spelling used by the
frozen security statement. -/
theorem victim_loss_le_div_add_one
    {o initialSupply initialBalance victim minted
      exitSupply exitBalance paid : Nat}
    (ho : o ≠ 0)
    (hminted : minted = mintN o victim initialSupply initialBalance)
    (hprice : PriceLe o
      ⟨initialSupply + minted, initialBalance + victim⟩
      ⟨exitSupply, exitBalance⟩)
    (hpaid : paid = payN o minted exitSupply exitBalance) :
    victim - paid ≤
      Nat.div (initialBalance + 1) (initialSupply + o) + 1 := by
  have hceil := victim_loss_le_ceil ho hminted hprice hpaid
  apply hceil.trans
  have hdiv :
      Nat.div initialBalance (initialSupply + o) ≤
        Nat.div (initialBalance + 1) (initialSupply + o) :=
    Nat.div_le_div_right (Nat.le_add_right initialBalance 1)
  rw [Jaune.ceilDiv_eq_div_add_ite]
  split
  · rw [Nat.add_zero]
    exact hdiv.trans (Nat.le_add_right _ 1)
  · exact Nat.add_le_add_right hdiv 1

end Prorata

end Blanc
