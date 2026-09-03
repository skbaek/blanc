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

**What these are about.** They are statements about the pricing arithmetic at a
pair of accounting snapshots. They are not yet statements about reachable vault
histories: nothing here says that a particular snapshot pair is reachable by
vault operations. Connecting them to a reachable carrier is the rest of the
attack workstream, and until that lands these bound what the arithmetic can do
rather than what an attacker can arrange.
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

end ProrataWethVault

end Blanc
