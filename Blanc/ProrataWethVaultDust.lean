-- ProrataWethVaultDust.lean : the port's dust and attack headlines.

import Blanc.ProrataWethVaultArithmetic
import Blanc.ProrataAttackModel

/-!
# Dust and attack headlines, WETH-denominated

The port changes the asset, not the arithmetic. `Blanc/OffsetPricing.lean`
states virtual-offset pricing over the naturals with the offset as a parameter,
and `Blanc/ProrataAttackModel.lean` proves the dust and inflation-attack
results about it. The vault's converters *are* that pricing at `offsetN`, by
`rfl` — see `convertToSharesN_eq_mintN` — so the results below are those
theorems instantiated, not restated.

That instantiation is the point. Re-proving the same inequalities in
WETH-denominated notation would have produced a second copy of an argument the
tree already carries, which is exactly what the proof-duplication ratchet
exists to prevent, and it would have left two places to be wrong.

**The carrier.** `ProrataAccountingPath offsetN` is the reachable carrier: a
connected sequence of classified steps — deposits, withdrawals, third-party
donations, and no-ops — each carrying an exact effect. Every such step weakly
increases the share price, so a whole path does, and that is what discharges
the price premise of the attack bound for an arbitrary history rather than for
a hand-picked pair.

What the carrier does *not* yet do is tie a vault EVM operation to the step it
induces. These results therefore quantify over accounting histories the pricing
admits, not yet over histories the compiled vault can produce. Closing that gap
is the remaining attack work, and the compiled effects already give the exact
supply and asset transitions it needs.
-/

namespace Blanc

open Jaune

namespace ProrataWethVault

/-- **Immediate round trip does not profit.** Depositing `amount` and redeeming
the shares it minted, against the same snapshot, returns at most `amount`, and
the shortfall is at most the pre-deposit price rounded up.

This is the rounding-favours-the-vault property the offset exists to guarantee,
in its exact form rather than as an inequality with slack. -/
theorem roundtrip_loss_le
    {amount assets supply : Nat} :
    amount -
        convertToAssetsN (convertToSharesN amount assets supply)
          (assets + amount)
          (supply + convertToSharesN amount assets supply) ≤
      Jaune.ceilDiv ((assets + 1) - 1) (supply + offsetN) :=
  Blanc.Prorata.immediate_roundtrip_loss_le offsetN_ne_zero

/-- **A redemption never overdraws the held assets.** A holder of at most the
whole supply is paid at most the vault's whole WETH row. -/
theorem redemption_le_assets
    {shares assets supply : Nat} (hshares : shares ≤ supply) :
    convertToAssetsN shares assets supply ≤ assets :=
  Blanc.Prorata.claimN_le_balance offsetN_ne_zero hshares

/-- **The victim's loss is bounded by the pre-attack price, plus one.**

The inflation attack's shape: a victim deposits `victim` assets into a snapshot
the attacker has already moved, and exits at a later snapshot no cheaper than
the one it entered. Whatever the attacker did in between, the victim's shortfall
is at most `(assets + 1) / (supply + offsetN) + 1` — a bound that shrinks as the
offset grows, which is what the offset buys. -/
theorem victim_loss_le
    {initialSupply initialAssets victim minted exitSupply exitAssets paid : Nat}
    (hminted : minted = convertToSharesN victim initialAssets initialSupply)
    (hprice : Blanc.Prorata.PriceLe offsetN
      ⟨initialSupply + minted, initialAssets + victim⟩
      ⟨exitSupply, exitAssets⟩)
    (hpaid : paid = convertToAssetsN minted exitAssets exitSupply) :
    victim - paid ≤
      Nat.div (initialAssets + 1) (initialSupply + offsetN) + 1 :=
  Blanc.Prorata.victim_loss_le_div_add_one offsetN_ne_zero hminted hprice hpaid



/-- **The attack bound over a whole history.**  Take any history the pricing
admits — any sequence of deposits, withdrawals, third-party donations and
no-ops — beginning immediately after a victim's deposit.  However the attacker
arranges it, the victim's shortfall on exiting at the end is at most the
pre-deposit price plus one.

The price premise is discharged by the carrier rather than assumed: every
classified step weakly increases the price, so the path does. -/
theorem victim_loss_le_over_history
    {initialSupply initialAssets victim minted paid : Nat}
    (path : Blanc.Prorata.ProrataAccountingPath offsetN)
    (hminted : minted = convertToSharesN victim initialAssets initialSupply)
    (hstart : path.first =
      ⟨initialSupply + minted, initialAssets + victim⟩)
    (hpaid : paid =
      convertToAssetsN minted path.last.balance path.last.supply) :
    victim - paid ≤
      Nat.div (initialAssets + 1) (initialSupply + offsetN) + 1 := by
  refine victim_loss_le hminted ?_ hpaid
  rw [← hstart]
  exact Blanc.Prorata.ProrataAccountingPath.priceLe_first_last
    offsetN_ne_zero path

/-- **Cumulative rounding residue over a whole history, exactly.**

Not a bound: an equality.  The numerator at the end of a history, scaled by the
product of the denominators along it, is the initial numerator scaled the same
way plus the exact sum of the per-step residues, each weighted by the
denominators on either side of it.  This is the port's dust accounting, and it
is the ETH-denominated statement at `offsetN` because the arithmetic is the
same. -/
theorem dust_trace_exact
    (path : Blanc.Prorata.ProrataAccountingPath offsetN) :
    let n := path.steps.length
    path.XAt n * (∏ j ∈ Finset.range n, path.DAt j) =
      path.XAt 0 * (∏ j ∈ Finset.Icc 1 n, path.DAt j) +
        ∑ i ∈ Finset.range n,
          (path.rhoAt i + path.kappaAt i) *
            (∏ j ∈ Finset.range i, path.DAt j) *
              (∏ j ∈ Finset.Icc (i + 2) n, path.DAt j) :=
  Blanc.Prorata.ProrataAccountingPath.prorata_dust_trace_exact
    offsetN_ne_zero path

end ProrataWethVault

end Blanc
