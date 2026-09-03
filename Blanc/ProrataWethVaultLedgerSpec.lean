-- ProrataWethVaultLedgerSpec.lean : the vault's ledger invariant on the ladder.

import Blanc.ProrataWethVaultShares
import Blanc.StorageOnlySpec

/-!
# The vault's share ledger, packaged for the generic execution ladder

`Blanc/ProrataWethVaultShares.lean` proves that each share operation preserves
`LedgerConserved supplySlot`; `Blanc/Composition/ProrataWethVault*.lean` proves
it for the four ERC-4626 flows.  Those are *frame*-level facts about one
compiled walk.  This module lifts them to the contract-level obligation the
ladder consumes, so that conservation can be carried across a message, a block
and a configured history by `Blanc/Ladder.lean` rather than by new machinery.

## What fits here and what does not

The vault's joint invariant (`Blanc/Composition/ProrataWethVaultBacking.lean`)
has three conjuncts.  Two of them — conservation and the supply cap — are
properties of the vault's own storage, so `ContractSpec.ofStorageOnly` carries
them.  The third, the backing bound, relates the vault's supply to the vault's
*WETH* balance, which lives in a second account's storage.  `ContractSpec.Inv`
reads one account's storage plus the callvalue and the contract's **ETH**
balance, and that is exactly how the ETH-backed PRORATA
(`Blanc/ProrataInvariant.lean`) carries its own backing bound.  Replacing the
native asset with an ERC-20 is what moves that conjunct out of the record's
reach; it is the substance of the port, not an oversight here.
-/

namespace Blanc

open Jaune

namespace ProrataWethVault

/-- The vault's ledger instance.  `Inv` is conservation of the share supply and
ignores both the callvalue and the ETH balance: this contract holds no ether,
and its backing asset is WETH. -/
def vaultSpec : ContractSpec :=
  ContractSpec.ofStorageOnly vault Conserved

/-- Reduce a dispatch target's obligation to the bare storage implication. -/
theorem vaultSpec_funcSound {ca : Adr} (f : Func)
    (h_cons : ∀ {sevm : Sevm} {s r : Devm},
      Func.Run (vault.main :: vaultAux) sevm s f r →
      Conserved (Devm.getStor s sevm.currentTarget) →
      Conserved (Devm.getStor r sevm.currentTarget)) :
    vaultSpec.FuncSoundNoMem ca vaultAux f :=
  ContractSpec.ofStorageOnly_funcSound f h_cons

/-- The eighteen dispatch targets that write no storage.  Listed here rather
than filtered out of `vaultFuncs` so that the obligation below is one `rcases`
over a literal, exactly as fmint's is. -/
def readOnlyFuncs : List (B256 × Func) :=
  [ (selector "totalAssets" [], routed 0 totalAssets),
    (selector "name" [], routed 0 name),
    (selector "convertToAssets" [.uint256], routed 1 convertToAssets),
    (selector "previewWithdraw" [.uint256], routed 1 previewWithdraw),
    (selector "totalSupply" [], routed 0 totalSupply),
    (selector "decimals" [], routed 0 decimals),
    (selector "asset" [], routed 0 asset),
    (selector "maxDeposit" [.address], routed 1 maxDeposit),
    (selector "previewRedeem" [.uint256], routed 1 previewRedeem),
    (selector "balanceOf" [.address], routed 1 balanceOf),
    (selector "symbol" [], routed 0 symbol),
    (selector "previewMint" [.uint256], routed 1 previewMint),
    (selector "maxMint" [.address], routed 1 maxMint),
    (selector "convertToShares" [.uint256], routed 1 convertToShares),
    (selector "maxWithdraw" [.address], routed 1 maxWithdraw),
    (selector "maxRedeem" [.address], routed 1 maxRedeem),
    (selector "allowance" [.address, .address], routed 2 allowance),
    (selector "previewDeposit" [.uint256], routed 1 previewDeposit) ]

/-! ## The eighteen read-only targets

None of them writes storage, but several *read another contract*: every
live-quoting view reaches WETH's `balanceOf` through `readTotalAssets`, which
is a `STATICCALL`.  That rules out `func_inv` at `Devm.getStor` — entering
interpreted code preserves the storage *observation*, not the `Stor` tree — so
the certificate is `Func.SilentIn` at `Devm.storageView`, and the invariant is
transported along the resulting pointwise equality.

The targets also tail-jump, so the certificate is context-fixed and the
permitted slots have to be closed. -/

/-- The two aux entries a read-only target may tail-jump into. -/
def ReadOnlySilentSlot (k : Nat) : Prop :=
  k = returnWordSlot ∨ k = maxMintAfterAssetCapSlot

/-- Discharge a permitted-slot obligation. -/
syntax "readOnly_slot" : tactic
macro_rules
| `(tactic| readOnly_slot) =>
  `(tactic| first
      | (change ReadOnlySilentSlot returnWordSlot
         simp only [ReadOnlySilentSlot, true_or])
      | (change ReadOnlySilentSlot maxMintAfterAssetCapSlot
         simp only [ReadOnlySilentSlot, or_true]))

theorem silentIn_returnWord :
    Func.SilentIn Devm.storageView ReadOnlySilentSlot returnWord := by
  silent_structure

theorem silentIn_maxMintAfterAssetCap :
    Func.SilentIn Devm.storageView ReadOnlySilentSlot maxMintAfterAssetCap := by
  silent_structure with readOnly_slot

/-- The permitted set is closed: both entries are themselves silent. -/
theorem readOnlySilentSlot_closed :
    ∀ k g, ReadOnlySilentSlot k → (vault.main :: vaultAux)[k]? = some g →
      Func.SilentIn Devm.storageView ReadOnlySilentSlot g := by
  intro k g allowed lookup
  rcases allowed with h | h <;> subst k
  · obtain rfl : returnWord = g := Option.some.inj
      ((show (vault.main :: vaultAux)[returnWordSlot]? = some returnWord from rfl).symm.trans
        lookup)
    exact silentIn_returnWord
  · obtain rfl : maxMintAfterAssetCap = g := Option.some.inj
      ((show (vault.main :: vaultAux)[maxMintAfterAssetCapSlot]? =
          some maxMintAfterAssetCap from rfl).symm.trans lookup)
    exact silentIn_maxMintAfterAssetCap

/-- Every read-only dispatch target is storage-silent in the observation. -/
theorem readOnly_silent :
    ∀ p ∈ readOnlyFuncs,
      Func.SilentIn Devm.storageView ReadOnlySilentSlot p.2 := by
  intro p h_mem
  simp only [readOnlyFuncs, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (cases h) <;>
    silent_structure with readOnly_slot

/-- Conservation rides across every read-only target. -/
theorem readOnly_preserves_conserved :
    ∀ p ∈ readOnlyFuncs, ∀ {sevm : Sevm} {s r : Devm},
      Func.Run (vault.main :: vaultAux) sevm s p.2 r →
      Conserved (Devm.getStor s sevm.currentTarget) →
      Conserved (Devm.getStor r sevm.currentTarget) := by
  intro p h_mem sevm s r run h
  have view := Func.observe_eq_of_run_silentIn readOnlySilentSlot_closed run
    (readOnly_silent p h_mem)
  exact h.of_get_eq fun key =>
    (congrFun (congrFun view sevm.currentTarget) key).symm

/-- The fallback is `Func.revert`, which no `Func.Run` witnesses, so the
obligation is vacuous: an unrecognized selector cannot move the ledger. -/
theorem vaultSpec_funcSound_revert {ca : Adr} :
    vaultSpec.FuncSoundNoMem ca vaultAux Func.revert := by
  intro _ _ _ _ _ _ h_run
  exact absurd h_run not_run_revert

end ProrataWethVault

end Blanc
