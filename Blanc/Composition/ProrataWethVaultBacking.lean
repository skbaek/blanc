import Blanc.Composition.ProrataWethVaultInbound
import Blanc.Composition.ProrataWethVaultOutbound

/-!
# The joint two-contract backing invariant

The vault issues shares against WETH it holds in WETH's own ledger.  Nothing
about that relation is visible to either contract alone: the vault's storage
knows the supply, WETH's storage knows the balance, and only a statement over
both can say the shares are backed.

The invariant has three conjuncts.  The first is ledger conservation inside the
vault.  The second is the arithmetic cap the vault's own guards maintain.  The
third is the backing bound proper, and it is the only one that mentions WETH.

The bound is `supply ≤ offset * assets` and it is exactly what makes every
share redeemable: with the virtual offset, redeeming the whole supply pays
`supply * (assets + 1) / (supply + offset)`, and that is at most `assets`
precisely when the bound holds.  `backing_corollary` is that calculation.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune
open Source

/-- Total issued shares, read from the vault's distinguished supply slot. -/
def supplyN (s : Stor) : Nat :=
  (s.get Blanc.ProrataWethVault.supplySlot).toNat

/-- The joint invariant: the vault's share ledger is conserved, its supply
respects the arithmetic cap, and the supply is backed by the WETH row the
vault holds in WETH's own ledger. -/
def PairBacked (vault : Adr) (vaultStor wethStor : Stor) : Prop :=
  LedgerConserved Blanc.ProrataWethVault.supplySlot vaultStor ∧
    supplyN vaultStor ≤ Blanc.ProrataWethVault.maxSupplyN ∧
    supplyN vaultStor ≤
      Blanc.ProrataWethVault.offsetN * (Stor.rest wethStor vault).toNat

/-- **The backing corollary.**  Redeeming the entire supply pays at most the
WETH the vault actually holds.  This is the statement the invariant exists to
support, and it is where the virtual offset earns its place: without it the
bound would be an equality that rounding could break. -/
theorem PairBacked.redeemable {vault : Adr} {vaultStor wethStor : Stor}
    (h : PairBacked vault vaultStor wethStor) :
    Blanc.ProrataWethVault.convertToAssetsN (supplyN vaultStor)
        (Stor.rest wethStor vault).toNat (supplyN vaultStor) ≤
      (Stor.rest wethStor vault).toNat := by
  obtain ⟨-, -, backed⟩ := h
  unfold Blanc.ProrataWethVault.convertToAssetsN
    Blanc.ProrataWethVault.assetFactorN Blanc.ProrataWethVault.denominatorN
  refine Nat.div_le_of_le_mul ?_
  have expand :
      supplyN vaultStor * ((Stor.rest wethStor vault).toNat + 1) =
        supplyN vaultStor * (Stor.rest wethStor vault).toNat +
          supplyN vaultStor := by
    ring
  have target :
      (supplyN vaultStor + Blanc.ProrataWethVault.offsetN) *
          (Stor.rest wethStor vault).toNat =
        supplyN vaultStor * (Stor.rest wethStor vault).toNat +
          Blanc.ProrataWethVault.offsetN *
            (Stor.rest wethStor vault).toNat := by
    ring
  rw [expand, target]
  omega

/-- **Genesis.**  A vault whose storage reads zero everywhere is backed, for
any WETH ledger: it has issued no shares. -/
theorem PairBacked.of_vault_empty {vault : Adr} {vaultStor wethStor : Stor}
    (h : ∀ k, vaultStor.get k = 0) :
    PairBacked vault vaultStor wethStor := by
  refine ⟨LedgerConserved.of_get_eq_zero h, ?_, ?_⟩
  · show (vaultStor.get Blanc.ProrataWethVault.supplySlot).toNat ≤ _
    rw [h, show ((0 : B256)).toNat = 0 by decide +kernel]
    exact Nat.zero_le _
  · show (vaultStor.get Blanc.ProrataWethVault.supplySlot).toNat ≤ _
    rw [h, show ((0 : B256)).toNat = 0 by decide +kernel]
    exact Nat.zero_le _

/-- **Donation.**  A third-party WETH transfer *into* the vault can only help:
the backing bound is monotone in the WETH row, so a rise in that row preserves
the invariant with the vault's own storage untouched. -/
theorem PairBacked.donation {vault : Adr} {vaultStor wethStor wethStor' : Stor}
    (h : PairBacked vault vaultStor wethStor)
    (rise : (Stor.rest wethStor vault).toNat ≤
      (Stor.rest wethStor' vault).toNat) :
    PairBacked vault vaultStor wethStor' := by
  obtain ⟨conserved, capped, backed⟩ := h
  exact ⟨conserved, capped, le_trans backed (Nat.mul_le_mul_left _ rise)⟩

end Blanc.Composition.ProrataWethVault
