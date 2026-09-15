import Blanc.Composition.ProrataWethVaultBacking
import Blanc.ProrataAttackModel

/-!
# Exact four-quote accounting for the WETH vault

The older `ProrataAccountingEffect` carrier has forward-quoted deposit and
redeem classes.  This module records the four ERC-4626 quote directions at the
joint snapshot boundary without pretending that inverse quotes are those old
classes.  In particular, an outbound WETH transfer to the vault itself burns
shares while retaining the vault's asset row; it is an explicit retained-asset
term, not an ordinary asset debit.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune

namespace FourQuote

abbrev Snapshot := Blanc.Prorata.AccountingSnapshot

def X (q : Snapshot) : Nat := q.balance + 1
def D (q : Snapshot) : Nat := q.supply + Blanc.ProrataWethVault.offsetN

def depositResidue (assets shares : Nat) (pre : Snapshot) : Nat :=
  assets * D pre - shares * X pre

def outboundResidue (assets shares : Nat) (pre : Snapshot) : Nat :=
  shares * X pre - assets * D pre

def normalInbound (assets shares : Nat) (pre : Snapshot) : Snapshot :=
  ⟨pre.supply + shares, pre.balance + assets⟩

def normalOutbound (assets shares : Nat) (pre : Snapshot) : Snapshot :=
  ⟨pre.supply - shares, pre.balance - assets⟩

def retainedOutbound (shares : Nat) (pre : Snapshot) : Snapshot :=
  ⟨pre.supply - shares, pre.balance⟩

theorem deposit_residue_eq (assets : Nat) (pre : Snapshot) :
    assets * D pre =
      Blanc.ProrataWethVault.convertToSharesN assets pre.balance pre.supply * X pre +
        depositResidue assets
          (Blanc.ProrataWethVault.convertToSharesN assets pre.balance pre.supply) pre := by
  unfold depositResidue X D
  have h := Blanc.ProrataWethVault.convertToSharesN_floor_le
    assets pre.balance pre.supply
  have h' : Blanc.ProrataWethVault.convertToSharesN assets pre.balance pre.supply * X pre ≤
      assets * D pre := by
    simpa [X, D, Blanc.ProrataWethVault.assetFactorN,
      Blanc.ProrataWethVault.denominatorN, Nat.mul_comm] using h
  unfold X D at h'
  clear h
  omega

theorem deposit_residue_lt (assets : Nat) (pre : Snapshot) :
    depositResidue assets
        (Blanc.ProrataWethVault.convertToSharesN assets pre.balance pre.supply) pre <
      X pre := by
  unfold depositResidue X D
  have h := Blanc.ProrataWethVault.convertToSharesN_lt_floor_add_one
    assets pre.balance pre.supply
  have h' : assets * D pre <
      Blanc.ProrataWethVault.convertToSharesN assets pre.balance pre.supply * X pre + X pre := by
    simpa [X, D, Blanc.ProrataWethVault.assetFactorN,
      Blanc.ProrataWethVault.denominatorN, Nat.mul_add, Nat.mul_comm] using h
  unfold X D at h'
  clear h
  omega

theorem mint_residue_eq (shares : Nat) (pre : Snapshot) :
    Blanc.ProrataWethVault.previewMintN shares pre.balance pre.supply * D pre =
      shares * X pre +
        depositResidue
          (Blanc.ProrataWethVault.previewMintN shares pre.balance pre.supply)
          shares pre := by
  unfold depositResidue X D
  have h := Blanc.ProrataWethVault.previewMintN_covers shares pre.balance pre.supply
  have h' : shares * X pre ≤
      Blanc.ProrataWethVault.previewMintN shares pre.balance pre.supply * D pre := by
    simpa [X, D, Blanc.ProrataWethVault.assetFactorN,
      Blanc.ProrataWethVault.denominatorN, Nat.mul_comm] using h
  unfold X D at h'
  clear h
  omega

theorem mint_residue_lt (shares : Nat) (pre : Snapshot) :
    depositResidue
        (Blanc.ProrataWethVault.previewMintN shares pre.balance pre.supply)
        shares pre < D pre := by
  unfold depositResidue X D
  have h := Blanc.ProrataWethVault.previewMintN_lt_add_denominator
    shares pre.balance pre.supply
  have h' : Blanc.ProrataWethVault.previewMintN shares pre.balance pre.supply * D pre <
      shares * X pre + D pre := by
    simpa [X, D, Blanc.ProrataWethVault.assetFactorN,
      Blanc.ProrataWethVault.denominatorN, Nat.mul_comm] using h
  unfold X D at h'
  clear h
  have hcover := Blanc.ProrataWethVault.previewMintN_covers shares pre.balance pre.supply
  have hcover' : shares * (pre.balance + 1) ≤
      Blanc.ProrataWethVault.previewMintN shares pre.balance pre.supply *
        (pre.supply + Blanc.ProrataWethVault.offsetN) := by
    simpa [Blanc.ProrataWethVault.assetFactorN,
      Blanc.ProrataWethVault.denominatorN, Nat.mul_comm] using hcover
  omega

theorem withdraw_residue_eq (assets : Nat) (pre : Snapshot) :
    Blanc.ProrataWethVault.previewWithdrawN assets pre.balance pre.supply * X pre =
      assets * D pre +
        outboundResidue assets
          (Blanc.ProrataWethVault.previewWithdrawN assets pre.balance pre.supply) pre := by
  unfold outboundResidue X D
  have h := Blanc.ProrataWethVault.previewWithdrawN_covers
    assets pre.balance pre.supply
  have h' : assets * D pre ≤
      Blanc.ProrataWethVault.previewWithdrawN assets pre.balance pre.supply * X pre := by
    simpa [X, D, Blanc.ProrataWethVault.assetFactorN,
      Blanc.ProrataWethVault.denominatorN, Nat.mul_comm] using h
  unfold X D at h'
  clear h
  omega

theorem withdraw_residue_lt (assets : Nat) (pre : Snapshot) :
    outboundResidue assets
        (Blanc.ProrataWethVault.previewWithdrawN assets pre.balance pre.supply) pre <
      X pre := by
  unfold outboundResidue X D
  have h := Blanc.ProrataWethVault.previewWithdrawN_lt_add_assetFactor
    assets pre.balance pre.supply
  have h' : Blanc.ProrataWethVault.previewWithdrawN assets pre.balance pre.supply * X pre <
      assets * D pre + X pre := by
    simpa [X, D, Blanc.ProrataWethVault.assetFactorN,
      Blanc.ProrataWethVault.denominatorN, Nat.mul_add, Nat.mul_comm] using h
  unfold X D at h'
  clear h
  omega

theorem redeem_residue_eq (shares : Nat) (pre : Snapshot) :
    shares * X pre =
      Blanc.ProrataWethVault.convertToAssetsN shares pre.balance pre.supply * D pre +
        outboundResidue
          (Blanc.ProrataWethVault.convertToAssetsN shares pre.balance pre.supply)
          shares pre := by
  unfold outboundResidue X D
  have h := Blanc.ProrataWethVault.convertToAssetsN_floor_le
    shares pre.balance pre.supply
  have h' : Blanc.ProrataWethVault.convertToAssetsN shares pre.balance pre.supply * D pre ≤
      shares * X pre := by
    simpa [X, D, Blanc.ProrataWethVault.assetFactorN,
      Blanc.ProrataWethVault.denominatorN, Nat.mul_comm] using h
  unfold X D at h'
  clear h
  omega

theorem redeem_residue_lt (shares : Nat) (pre : Snapshot) :
    outboundResidue
        (Blanc.ProrataWethVault.convertToAssetsN shares pre.balance pre.supply)
        shares pre < D pre := by
  unfold outboundResidue X D
  have h := Blanc.ProrataWethVault.convertToAssetsN_lt_floor_add_one
    shares pre.balance pre.supply
  have h' : shares * X pre <
      Blanc.ProrataWethVault.convertToAssetsN shares pre.balance pre.supply * D pre + D pre := by
    simpa [X, D, Blanc.ProrataWethVault.assetFactorN,
      Blanc.ProrataWethVault.denominatorN, Nat.mul_add, Nat.mul_comm] using h
  unfold X D at h'
  clear h
  have hfloor := Blanc.ProrataWethVault.convertToAssetsN_floor_le
    shares pre.balance pre.supply
  have hfloor' : Blanc.ProrataWethVault.convertToAssetsN shares pre.balance pre.supply *
      (pre.supply + Blanc.ProrataWethVault.offsetN) ≤ shares * (pre.balance + 1) := by
    simpa [Blanc.ProrataWethVault.assetFactorN,
      Blanc.ProrataWethVault.denominatorN, Nat.mul_comm] using hfloor
  omega

theorem normalInbound_price
    (assets shares : Nat) (pre : Snapshot)
    (quote : shares = Blanc.ProrataWethVault.convertToSharesN assets pre.balance pre.supply) :
    X (normalInbound assets shares pre) * D pre =
      X pre * D (normalInbound assets shares pre) +
        depositResidue assets shares pre := by
  subst shares
  have h := deposit_residue_eq assets pre
  unfold X D normalInbound
  rw [show pre.balance + assets + 1 = (pre.balance + 1) + assets by omega,
    show pre.supply +
        Blanc.ProrataWethVault.convertToSharesN assets pre.balance pre.supply +
        Blanc.ProrataWethVault.offsetN =
      (pre.supply + Blanc.ProrataWethVault.offsetN) +
        Blanc.ProrataWethVault.convertToSharesN assets pre.balance pre.supply by omega]
  calc
    (pre.balance + 1 + assets) * (pre.supply + Blanc.ProrataWethVault.offsetN) =
        (pre.balance + 1) * (pre.supply + Blanc.ProrataWethVault.offsetN) +
          assets * (pre.supply + Blanc.ProrataWethVault.offsetN) := by ring
    _ = (pre.balance + 1) * (pre.supply + Blanc.ProrataWethVault.offsetN) +
          (Blanc.ProrataWethVault.convertToSharesN assets pre.balance pre.supply *
            (pre.balance + 1) +
              depositResidue assets
                (Blanc.ProrataWethVault.convertToSharesN assets pre.balance pre.supply) pre) := by
          simpa only [X, D] using congrArg (fun z =>
            (pre.balance + 1) * (pre.supply + Blanc.ProrataWethVault.offsetN) + z) h
    _ = _ := by ring

theorem normalInbound_price_mint (shares : Nat) (pre : Snapshot) :
    X (normalInbound (Blanc.ProrataWethVault.previewMintN shares pre.balance pre.supply)
        shares pre) * D pre =
      X pre * D (normalInbound
        (Blanc.ProrataWethVault.previewMintN shares pre.balance pre.supply) shares pre) +
        depositResidue
          (Blanc.ProrataWethVault.previewMintN shares pre.balance pre.supply)
          shares pre := by
  have h := mint_residue_eq shares pre
  unfold X D normalInbound
  rw [show pre.balance + Blanc.ProrataWethVault.previewMintN shares pre.balance pre.supply + 1 =
      (pre.balance + 1) + Blanc.ProrataWethVault.previewMintN shares pre.balance pre.supply by omega,
    show pre.supply + shares + Blanc.ProrataWethVault.offsetN =
      (pre.supply + Blanc.ProrataWethVault.offsetN) + shares by omega]
  calc
    (pre.balance + 1 + Blanc.ProrataWethVault.previewMintN shares pre.balance pre.supply) *
        (pre.supply + Blanc.ProrataWethVault.offsetN) =
      (pre.balance + 1) * (pre.supply + Blanc.ProrataWethVault.offsetN) +
        Blanc.ProrataWethVault.previewMintN shares pre.balance pre.supply *
          (pre.supply + Blanc.ProrataWethVault.offsetN) := by ring
    _ = (pre.balance + 1) * (pre.supply + Blanc.ProrataWethVault.offsetN) +
        (shares * (pre.balance + 1) + depositResidue
          (Blanc.ProrataWethVault.previewMintN shares pre.balance pre.supply) shares pre) := by
          simpa only [X, D] using congrArg (fun z =>
            (pre.balance + 1) * (pre.supply + Blanc.ProrataWethVault.offsetN) + z) h
    _ = _ := by ring

/-- An inbound effect determines the joint snapshot without committing to a
particular quote direction.  The no-wrap and distinct-caller premises are the
local ledger facts needed to read the real WETH credit. -/
theorem inboundEffect_normal_snapshot
    {sevm : Sevm} {pre post : Devm}
    {receiver assets shares returned : B256}
    (depositorNotVault : sevm.caller ≠ sevm.currentTarget)
    (supplyNof : B256.Nof (Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot) shares)
    (rowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount)
      sevm.currentTarget) assets)
    (effect : InboundEffect sevm receiver assets shares returned pre post) :
    snapshotAt sevm post =
      normalInbound assets.toNat shares.toNat (snapshotAt sevm pre) := by
  obtain ⟨-, movement, vaultStorage, -, -⟩ := effect
  apply congrArg₂ Blanc.Prorata.AccountingSnapshot.mk
  · show (Devm.getStorVal post sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot).toNat = _
    change ((Devm.getStor post sevm.currentTarget).get
      Blanc.ProrataWethVault.supplySlot).toNat = _
    rw [vaultStorage, Stor.get_set_self]
    exact B256.toNat_add_eq_of_nof _ _ supplyNof
  · show (Stor.rest (Devm.getStor post wethAccount) sevm.currentTarget).toNat = _
    rw [credited_of_transfer movement depositorNotVault]
    exact B256.toNat_add_eq_of_nof _ _ rowNof

/-- The common normal-debit recurrence for either outbound quote direction. -/
theorem normalOutbound_price
    (assets shares : Nat) (pre : Snapshot)
    (burnable : shares ≤ pre.supply) (covered : assets ≤ pre.balance)
    (residue : shares * X pre = assets * D pre + outboundResidue assets shares pre) :
    X (normalOutbound assets shares pre) * D pre =
      X pre * D (normalOutbound assets shares pre) +
        outboundResidue assets shares pre := by
  rcases pre with ⟨supply, balance⟩
  obtain ⟨s, hs⟩ : ∃ s, supply = s + shares :=
    ⟨supply - shares, (Nat.sub_add_cancel burnable).symm⟩
  obtain ⟨a, ha⟩ : ∃ a, balance = a + assets :=
    ⟨balance - assets, (Nat.sub_add_cancel covered).symm⟩
  subst supply
  subst balance
  simp only [normalOutbound, X, D, Nat.add_sub_cancel] at residue ⊢
  ring_nf at residue ⊢
  omega

theorem normalOutbound_price_withdraw
    (assets : Nat) (pre : Snapshot)
    (burnable : Blanc.ProrataWethVault.previewWithdrawN assets pre.balance pre.supply ≤ pre.supply)
    (covered : assets ≤ pre.balance) :
    X (normalOutbound assets
        (Blanc.ProrataWethVault.previewWithdrawN assets pre.balance pre.supply) pre) * D pre =
      X pre * D (normalOutbound assets
        (Blanc.ProrataWethVault.previewWithdrawN assets pre.balance pre.supply) pre) +
        outboundResidue assets
          (Blanc.ProrataWethVault.previewWithdrawN assets pre.balance pre.supply) pre :=
  normalOutbound_price assets _ pre burnable covered (withdraw_residue_eq assets pre)

theorem normalOutbound_price_redeem
    (shares : Nat) (pre : Snapshot)
    (burnable : shares ≤ pre.supply)
    (covered : Blanc.ProrataWethVault.convertToAssetsN shares pre.balance pre.supply ≤ pre.balance) :
    X (normalOutbound
        (Blanc.ProrataWethVault.convertToAssetsN shares pre.balance pre.supply) shares pre) * D pre =
      X pre * D (normalOutbound
        (Blanc.ProrataWethVault.convertToAssetsN shares pre.balance pre.supply) shares pre) +
        outboundResidue
          (Blanc.ProrataWethVault.convertToAssetsN shares pre.balance pre.supply) shares pre :=
  normalOutbound_price _ shares pre burnable covered (redeem_residue_eq shares pre)

/-- The exact configured WETH transfer gives the real normal outbound snapshot
when its receiver is distinct from the vault. -/
theorem outboundEffect_normal_snapshot
    {sevm : Sevm} {pre post : Devm}
    {receiver owner assets shares returned : B256}
    (receiverNotVault : sevm.currentTarget ≠ receiver.toAdr)
    (burnable : shares.toNat ≤ (snapshotAt sevm pre).supply)
    (covered : assets.toNat ≤ (snapshotAt sevm pre).balance)
    (effect : OutboundEffect sevm receiver owner assets shares returned pre post) :
    snapshotAt sevm post =
      normalOutbound assets.toNat shares.toNat (snapshotAt sevm pre) := by
  obtain ⟨-, movement, -, supplyRow, -, -, -, -⟩ := effect
  apply congrArg₂ Blanc.Prorata.AccountingSnapshot.mk
  · show (Devm.getStorVal post sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot).toNat = _
    rw [supplyRow]
    exact B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat burnable)
  · show (Stor.rest (Devm.getStor post wethAccount) sevm.currentTarget).toNat = _
    rw [debitedSub_of_transfer movement receiverNotVault]
    exact B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat covered)

theorem retainedOutbound_price
    (assets shares : Nat) (pre : Snapshot)
    (burnable : shares ≤ pre.supply)
    (residue : shares * X pre = assets * D pre + outboundResidue assets shares pre) :
    X (retainedOutbound shares pre) * D pre =
      X pre * D (retainedOutbound shares pre) +
        outboundResidue assets shares pre + assets * D pre := by
  rcases pre with ⟨supply, balance⟩
  obtain ⟨s, hs⟩ : ∃ s, supply = s + shares :=
    ⟨supply - shares, (Nat.sub_add_cancel burnable).symm⟩
  subst supply
  unfold X D at residue
  unfold retainedOutbound X D
  simp only [Nat.add_sub_cancel] at residue ⊢
  calc
    (balance + 1) * (s + shares + Blanc.ProrataWethVault.offsetN) =
        (balance + 1) * (s + Blanc.ProrataWethVault.offsetN) +
          shares * (balance + 1) := by ring
    _ = _ := by rw [residue]; ring

/-- A successful outbound transfer paid to the vault itself burns shares but
leaves the vault's WETH row unchanged. -/
theorem outboundEffect_retained_snapshot
    {sevm : Sevm} {pre post : Devm}
    {receiver owner assets shares returned : B256}
    (receiverIsVault : receiver.toAdr = sevm.currentTarget)
    (burnable : shares.toNat ≤ (snapshotAt sevm pre).supply)
    (effect : OutboundEffect sevm receiver owner assets shares returned pre post) :
    snapshotAt sevm post = retainedOutbound shares.toNat (snapshotAt sevm pre) := by
  obtain ⟨-, movement, -, supplyRow, -, -, -, -⟩ := effect
  apply congrArg₂ Blanc.Prorata.AccountingSnapshot.mk
  · show (Devm.getStorVal post sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot).toNat = _
    rw [supplyRow]
    exact B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat burnable)
  · obtain ⟨covered, mid, decrease, increase⟩ := movement
    have hdec : Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget - assets =
        mid sevm.currentTarget := by
      exact (decrease sevm.currentTarget).left rfl
    have hinc : mid sevm.currentTarget + assets =
        Stor.rest (Devm.getStor post wethAccount) sevm.currentTarget := by
      simpa only [receiverIsVault] using
        (increase sevm.currentTarget).left receiverIsVault
    show (Stor.rest (Devm.getStor post wethAccount) sevm.currentTarget).toNat =
      (Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget).toNat
    rw [← hinc, ← hdec, B256.sub_add_cancel]

theorem externalCredit_price (assets : Nat) (pre : Snapshot) :
    X (normalInbound assets 0 pre) * D pre = X pre * D pre + assets * D pre := by
  unfold normalInbound X D
  ring

/-- The actual compiled `mint` occurrence exposes the inverse quote as a
named natural-number charge and retains its exact configured WETH effect. -/
theorem mint_compiled_quote
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm = selector "mint" [.uint256, .address]) :
    ∃ supply charged : B256,
      supply = Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot ∧
      charged.toNat = Blanc.ProrataWethVault.previewMintN
        (Sevm.argWord sevm 0).toNat
        (Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget).toNat supply.toNat ∧
      InboundEffect sevm (Sevm.argWord sevm 1) charged (Sevm.argWord sevm 0)
        charged pre post := by
  obtain ⟨-, supply, supplyEq, -, chargeFits, -, -, -, -, effect⟩ :=
    mint_compiled_effect config memoryWf run selectorEq
  refine ⟨supply, _, supplyEq, ?_, effect⟩
  exact B256.toNat_toB256_of_lt chargeFits

/-- The actual compiled `withdraw` occurrence exposes the inverse quote as a
named natural-number burn and retains its exact configured WETH effect. -/
theorem withdraw_compiled_quote
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "withdraw" [.uint256, .address, .address]) :
    ∃ supply burned : B256,
      supply = Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot ∧
      burned.toNat = Blanc.ProrataWethVault.previewWithdrawN
        (Sevm.argWord sevm 0).toNat
        (Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget).toNat supply.toNat ∧
      OutboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
        (Sevm.argWord sevm 0) burned burned pre post := by
  obtain ⟨-, supply, supplyEq, -, burnFits, -, -, -, -, -, -, -, effect⟩ :=
    withdraw_compiled_effect config memoryWf run selectorEq
  refine ⟨supply, _, supplyEq, ?_, effect⟩
  exact B256.toNat_toB256_of_lt burnFits

/-- The compiled inverse-withdraw call reaches the actual normal outbound
boundary whenever its receiver differs from the vault and the two local debit
bounds hold. -/
theorem withdraw_compiled_normal_snapshot
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "withdraw" [.uint256, .address, .address])
    (receiverNotVault : sevm.currentTarget ≠ (Sevm.argWord sevm 1).toAdr)
    (burnable : Blanc.ProrataWethVault.previewWithdrawN
      (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
        (snapshotAt sevm pre).supply ≤ (snapshotAt sevm pre).supply)
    (covered : (Sevm.argWord sevm 0).toNat ≤ (snapshotAt sevm pre).balance) :
    ∃ burned : B256,
      burned.toNat = Blanc.ProrataWethVault.previewWithdrawN
        (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
          (snapshotAt sevm pre).supply ∧
      snapshotAt sevm post = normalOutbound (Sevm.argWord sevm 0).toNat
        burned.toNat (snapshotAt sevm pre) := by
  obtain ⟨supply, burned, supplyEq, quote, effect⟩ :=
    withdraw_compiled_quote config memoryWf run selectorEq
  have quote' : burned.toNat = Blanc.ProrataWethVault.previewWithdrawN
      (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
        (snapshotAt sevm pre).supply := by
    simpa [snapshotAt, vaultSnapshot, supplyEq] using quote
  refine ⟨burned, quote', outboundEffect_normal_snapshot receiverNotVault ?_ covered effect⟩
  rw [quote']
  exact burnable

end FourQuote

end Blanc.Composition.ProrataWethVault
