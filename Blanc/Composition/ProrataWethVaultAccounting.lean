import Blanc.Composition.ProrataWethVaultBacking
import Blanc.ExecutionStateTrace
import Blanc.ProrataAttackModel
import Blanc.ProrataAttackTrace

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

/-- The source-side availability inside an exact outbound effect is already
the natural coverage fact needed by the snapshot bridge. -/
theorem outboundEffect_covered
    {sevm : Sevm} {pre post : Devm}
    {receiver owner assets shares returned : B256}
    (effect : OutboundEffect sevm receiver owner assets shares returned pre post) :
    assets.toNat ≤ (snapshotAt sevm pre).balance := by
  obtain ⟨-, movement, -, -, -, -, -, -⟩ := effect
  exact B256.toNat_le_toNat movement.1

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
      supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN ∧
      (Sevm.argWord sevm 0).toNat ≤ Blanc.ProrataWethVault.shareRoomN supply.toNat ∧
      InboundEffect sevm (Sevm.argWord sevm 1) charged (Sevm.argWord sevm 0)
        charged pre post := by
  obtain ⟨-, supply, supplyEq, stable, chargeFits, -, -, -, room, effect⟩ :=
    mint_compiled_effect config memoryWf run selectorEq
  refine ⟨supply, _, supplyEq, ?_, stable, room, effect⟩
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
      burned.toNat ≤ supply.toNat ∧
      OutboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
        (Sevm.argWord sevm 0) burned burned pre post := by
  obtain ⟨-, supply, supplyEq, -, burnFits, -, -, -, -, -, -, burnable, effect⟩ :=
    withdraw_compiled_effect config memoryWf run selectorEq
  refine ⟨supply, _, supplyEq, ?_, ?_, effect⟩
  exact B256.toNat_toB256_of_lt burnFits
  exact burnable

/-- The compiled inverse-withdraw call reaches the actual normal outbound
boundary whenever its receiver differs from the vault; the effect and compiled
guard already provide its debit bounds. -/
theorem withdraw_compiled_normal_snapshot
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "withdraw" [.uint256, .address, .address])
    (receiverNotVault : sevm.currentTarget ≠ (Sevm.argWord sevm 1).toAdr) :
    ∃ burned : B256,
      burned.toNat = Blanc.ProrataWethVault.previewWithdrawN
        (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
          (snapshotAt sevm pre).supply ∧
      snapshotAt sevm post = normalOutbound (Sevm.argWord sevm 0).toNat
        burned.toNat (snapshotAt sevm pre) := by
  obtain ⟨supply, burned, supplyEq, quote, burnable, effect⟩ :=
    withdraw_compiled_quote config memoryWf run selectorEq
  have quote' : burned.toNat = Blanc.ProrataWethVault.previewWithdrawN
      (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
        (snapshotAt sevm pre).supply := by
    simpa [snapshotAt, vaultSnapshot, supplyEq] using quote
  have burnable' : burned.toNat ≤ (snapshotAt sevm pre).supply := by
    simpa [snapshotAt, vaultSnapshot, supplyEq] using burnable
  exact ⟨burned, quote', outboundEffect_normal_snapshot receiverNotVault burnable'
    (outboundEffect_covered effect) effect⟩

/-- A supply bounded by the frozen capacity, plus a quote admitted by the
remaining share room, cannot wrap its supply-row addition. -/
theorem supplyNof_of_capacity {supply shares : B256}
    (stable : supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN)
    (room : shares.toNat ≤ Blanc.ProrataWethVault.shareRoomN supply.toNat) :
    B256.Nof supply shares := by
  unfold B256.Nof
  have bounded := Blanc.ProrataWethVault.supply_add_le_maxSupplyN_of_le_shareRoomN
    stable room
  unfold Blanc.ProrataWethVault.maxSupplyN Blanc.maxWordN Blanc.wordModulusN at bounded
  omega

/-- The compiled `deposit` occurrence exposes its floor quote together with
the capacity facts that make the supply-row addition non-wrapping. -/
theorem deposit_compiled_quote
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm = selector "deposit" [.uint256, .address]) :
    ∃ supply shares : B256,
      supply = Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot ∧
      shares.toNat = Blanc.ProrataWethVault.convertToSharesN
        (Sevm.argWord sevm 0).toNat
        (Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget).toNat supply.toNat ∧
      supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN ∧
      shares.toNat ≤ Blanc.ProrataWethVault.shareRoomN supply.toNat ∧
      InboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 0)
        shares shares pre post := by
  obtain ⟨supply, shares, supplyEq, quote, stable, room, effect⟩ :=
    deposit_compiled_effect_named config memoryWf run selectorEq
  exact ⟨supply, shares, supplyEq, quote, stable, room, effect⟩

/-- The compiled `redeem` occurrence exposes its floor asset quote in the
same named form as the other three public endpoints. -/
theorem redeem_compiled_quote
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "redeem" [.uint256, .address, .address]) :
    ∃ supply assets : B256,
      supply = Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot ∧
      assets.toNat = Blanc.ProrataWethVault.convertToAssetsN
        (Sevm.argWord sevm 0).toNat
        (Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget).toNat supply.toNat ∧
      (Sevm.argWord sevm 0).toNat ≤ supply.toNat ∧
      OutboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
        assets (Sevm.argWord sevm 0) assets pre post := by
  obtain ⟨supply, assets, supplyEq, quote, burnable, effect⟩ :=
    redeem_compiled_effect_named config memoryWf run selectorEq
  exact ⟨supply, assets, supplyEq, quote, burnable, effect⟩

/-- A compiled `deposit` reaches the real normal inbound boundary once its
WETH-row addition is known not to wrap; capacity and share-room guards derive
the supply-row fact. -/
theorem deposit_compiled_normal_snapshot
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm = selector "deposit" [.uint256, .address])
    (depositorNotVault : sevm.caller ≠ sevm.currentTarget)
    (rowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount)
      sevm.currentTarget) (Sevm.argWord sevm 0)) :
    ∃ shares : B256,
      shares.toNat = Blanc.ProrataWethVault.convertToSharesN
        (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
          (snapshotAt sevm pre).supply ∧
      snapshotAt sevm post = normalInbound (Sevm.argWord sevm 0).toNat
        shares.toNat (snapshotAt sevm pre) := by
  obtain ⟨supply, shares, supplyEq, quote, stable, room, effect⟩ :=
    deposit_compiled_quote config memoryWf run selectorEq
  have quote' : shares.toNat = Blanc.ProrataWethVault.convertToSharesN
      (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
        (snapshotAt sevm pre).supply := by
    simpa [snapshotAt, vaultSnapshot, supplyEq] using quote
  have supplyNof : B256.Nof (Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot) shares := by
    rw [← supplyEq]
    exact supplyNof_of_capacity stable room
  exact ⟨shares, quote',
    inboundEffect_normal_snapshot depositorNotVault supplyNof rowNof effect⟩

/-- A compiled `mint` reaches the same real inbound boundary, retaining the
inverse ceil quote rather than coercing it to the deposit quote. -/
theorem mint_compiled_normal_snapshot
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm = selector "mint" [.uint256, .address])
    (depositorNotVault : sevm.caller ≠ sevm.currentTarget)
    (rowNof : ∀ charged : B256,
      charged.toNat = Blanc.ProrataWethVault.previewMintN
        (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
          (snapshotAt sevm pre).supply →
      B256.Nof (Stor.rest (Devm.getStor pre wethAccount)
        sevm.currentTarget) charged) :
    ∃ charged : B256,
      charged.toNat = Blanc.ProrataWethVault.previewMintN
        (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
          (snapshotAt sevm pre).supply ∧
      snapshotAt sevm post = normalInbound charged.toNat
        (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre) := by
  obtain ⟨supply, charged, supplyEq, quote, stable, room, effect⟩ :=
    mint_compiled_quote config memoryWf run selectorEq
  have quote' : charged.toNat = Blanc.ProrataWethVault.previewMintN
      (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
        (snapshotAt sevm pre).supply := by
    simpa [snapshotAt, vaultSnapshot, supplyEq] using quote
  have supplyNof : B256.Nof (Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot) (Sevm.argWord sevm 0) := by
    rw [← supplyEq]
    exact supplyNof_of_capacity stable room
  exact ⟨charged, quote',
    inboundEffect_normal_snapshot depositorNotVault supplyNof
      (rowNof charged quote') effect⟩

/-- The compiled inverse-withdraw call reaches the retained boundary when it
pays the vault itself. -/
theorem withdraw_compiled_retained_snapshot
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "withdraw" [.uint256, .address, .address])
    (receiverIsVault : (Sevm.argWord sevm 1).toAdr = sevm.currentTarget) :
    ∃ burned : B256,
      burned.toNat = Blanc.ProrataWethVault.previewWithdrawN
        (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
          (snapshotAt sevm pre).supply ∧
      snapshotAt sevm post = retainedOutbound burned.toNat (snapshotAt sevm pre) := by
  obtain ⟨supply, burned, supplyEq, quote, burnable, effect⟩ :=
    withdraw_compiled_quote config memoryWf run selectorEq
  have quote' : burned.toNat = Blanc.ProrataWethVault.previewWithdrawN
      (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
        (snapshotAt sevm pre).supply := by
    simpa [snapshotAt, vaultSnapshot, supplyEq] using quote
  exact ⟨burned, quote',
    outboundEffect_retained_snapshot receiverIsVault
      (by simpa [snapshotAt, vaultSnapshot, supplyEq] using burnable) effect⟩

/-- The compiled `redeem` reaches the real normal debit boundary when its
receiver differs from the vault. -/
theorem redeem_compiled_normal_snapshot
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "redeem" [.uint256, .address, .address])
    (receiverNotVault : sevm.currentTarget ≠ (Sevm.argWord sevm 1).toAdr) :
    ∃ assets : B256,
      assets.toNat = Blanc.ProrataWethVault.convertToAssetsN
        (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
          (snapshotAt sevm pre).supply ∧
      snapshotAt sevm post = normalOutbound assets.toNat
        (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre) := by
  obtain ⟨supply, assets, supplyEq, quote, burnable, effect⟩ :=
    redeem_compiled_quote config memoryWf run selectorEq
  have quote' : assets.toNat = Blanc.ProrataWethVault.convertToAssetsN
      (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
        (snapshotAt sevm pre).supply := by
    simpa [snapshotAt, vaultSnapshot, supplyEq] using quote
  exact ⟨assets, quote', outboundEffect_normal_snapshot receiverNotVault
    (by simpa [snapshotAt, vaultSnapshot, supplyEq] using burnable)
    (outboundEffect_covered effect) effect⟩

/-- The compiled `redeem` reaches the retained boundary when it pays the vault
itself. -/
theorem redeem_compiled_retained_snapshot
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "redeem" [.uint256, .address, .address])
    (receiverIsVault : (Sevm.argWord sevm 1).toAdr = sevm.currentTarget) :
    ∃ assets : B256,
      assets.toNat = Blanc.ProrataWethVault.convertToAssetsN
        (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
          (snapshotAt sevm pre).supply ∧
      snapshotAt sevm post = retainedOutbound (Sevm.argWord sevm 0).toNat
        (snapshotAt sevm pre) := by
  obtain ⟨supply, assets, supplyEq, quote, burnable, effect⟩ :=
    redeem_compiled_quote config memoryWf run selectorEq
  have quote' : assets.toNat = Blanc.ProrataWethVault.convertToAssetsN
      (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
        (snapshotAt sevm pre).supply := by
    simpa [snapshotAt, vaultSnapshot, supplyEq] using quote
  exact ⟨assets, quote', outboundEffect_retained_snapshot receiverIsVault
    (by simpa [snapshotAt, vaultSnapshot, supplyEq] using burnable) effect⟩

/-- A third-party WETH transfer with an unchanged vault supply row reaches the
credited snapshot boundary.  This is deliberately a raw local effect bridge;
configured-history admission is a later invariant obligation. -/
theorem externalCredit_snapshot
    {pre post : Devm} {vault source : Adr} {assets : B256}
    (sourceNotVault : source ≠ vault)
    (supplyKept : Devm.getStorVal post vault Blanc.ProrataWethVault.supplySlot =
      Devm.getStorVal pre vault Blanc.ProrataWethVault.supplySlot)
    (rowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount) vault) assets)
    (effect : Transfer (Stor.rest (Devm.getStor pre wethAccount)) source assets vault
      (Stor.rest (Devm.getStor post wethAccount))) :
    vaultSnapshot vault post = normalInbound assets.toNat 0 (vaultSnapshot vault pre) := by
  apply congrArg₂ Blanc.Prorata.AccountingSnapshot.mk
  · show (Devm.getStorVal post vault Blanc.ProrataWethVault.supplySlot).toNat = _
    rw [supplyKept]
    simp [vaultSnapshot]
  · show (Stor.rest (Devm.getStor post wethAccount) vault).toNat = _
    rw [credited_of_transfer effect sourceNotVault]
    simpa [vaultSnapshot] using
      B256.toNat_add_eq_of_nof
        (Stor.rest (Devm.getStor pre wethAccount) vault) assets rowNof

/-- The two accounting coordinates read directly from a stable `State`
boundary. -/
def stateSnapshot (vault : Adr) (state : State) : Snapshot :=
  ⟨((state.getStor vault).get Blanc.ProrataWethVault.supplySlot).toNat,
    (Stor.rest (state.getStor wethAccount) vault).toNat⟩

@[simp] theorem vaultSnapshot_state (vault : Adr) (state : Devm) :
    vaultSnapshot vault state = stateSnapshot vault state.state := rfl

/-- The words retained by either inbound endpoint. -/
structure InboundWords where
  receiver : B256
  assets : B256
  shares : B256
  returned : B256

/-- The words retained by either outbound endpoint. -/
structure OutboundWords where
  receiver : B256
  owner : B256
  assets : B256
  shares : B256
  returned : B256

/-- The source and amount retained by an outside WETH credit. -/
structure CreditWords where
  source : Adr
  amount : B256

/-- The actual owner, receiver and amount words of `transfer`. -/
structure ShareTransferWords where
  owner : Adr
  receiver : B256
  amount : B256

/-- The actual spender, owner, receiver and amount words of `transferFrom`. -/
structure ShareTransferFromWords where
  spender : Adr
  owner : B256
  receiver : B256
  amount : B256

/-- The actual owner, spender and amount words of `approve`. -/
structure ShareApprovalWords where
  owner : Adr
  spender : B256
  amount : B256

/-- The ten actual-effect operations that a local four-quote path may use.
Each quote and accounting contribution is retained in the constructor that
proves its concrete WETH/vault storage movement. -/
inductive FourQuoteOperation (vault : Adr) (sevm : Sevm) (pre post : Devm) : Type where
  | deposit (words : InboundWords)
      (target : sevm.currentTarget = vault)
      (depositorNotVault : sevm.caller ≠ sevm.currentTarget)
      (supplyNof : B256.Nof (Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot) words.shares)
      (rowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount)
        sevm.currentTarget) words.assets)
      (quote : words.shares.toNat = Blanc.ProrataWethVault.convertToSharesN words.assets.toNat
        (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply)
      (effect : InboundEffect sevm words.receiver words.assets words.shares words.returned pre post) :
      FourQuoteOperation vault sevm pre post
  | mint (words : InboundWords)
      (target : sevm.currentTarget = vault)
      (depositorNotVault : sevm.caller ≠ sevm.currentTarget)
      (supplyNof : B256.Nof (Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot) words.shares)
      (rowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount)
        sevm.currentTarget) words.assets)
      (quote : words.assets.toNat = Blanc.ProrataWethVault.previewMintN words.shares.toNat
        (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply)
      (effect : InboundEffect sevm words.receiver words.assets words.shares words.returned pre post) :
      FourQuoteOperation vault sevm pre post
  | withdrawNormal (words : OutboundWords)
      (target : sevm.currentTarget = vault)
      (receiverNotVault : sevm.currentTarget ≠ words.receiver.toAdr)
      (burnable : words.shares.toNat ≤ (snapshotAt sevm pre).supply)
      (quote : words.shares.toNat = Blanc.ProrataWethVault.previewWithdrawN words.assets.toNat
        (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply)
      (effect : OutboundEffect sevm words.receiver words.owner words.assets words.shares words.returned pre post) :
      FourQuoteOperation vault sevm pre post
  | redeemNormal (words : OutboundWords)
      (target : sevm.currentTarget = vault)
      (receiverNotVault : sevm.currentTarget ≠ words.receiver.toAdr)
      (burnable : words.shares.toNat ≤ (snapshotAt sevm pre).supply)
      (quote : words.assets.toNat = Blanc.ProrataWethVault.convertToAssetsN words.shares.toNat
        (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply)
      (effect : OutboundEffect sevm words.receiver words.owner words.assets words.shares words.returned pre post) :
      FourQuoteOperation vault sevm pre post
  | withdrawSelf (words : OutboundWords)
      (target : sevm.currentTarget = vault)
      (receiverIsVault : words.receiver.toAdr = sevm.currentTarget)
      (burnable : words.shares.toNat ≤ (snapshotAt sevm pre).supply)
      (quote : words.shares.toNat = Blanc.ProrataWethVault.previewWithdrawN words.assets.toNat
        (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply)
      (effect : OutboundEffect sevm words.receiver words.owner words.assets words.shares words.returned pre post) :
      FourQuoteOperation vault sevm pre post
  | redeemSelf (words : OutboundWords)
      (target : sevm.currentTarget = vault)
      (receiverIsVault : words.receiver.toAdr = sevm.currentTarget)
      (burnable : words.shares.toNat ≤ (snapshotAt sevm pre).supply)
      (quote : words.assets.toNat = Blanc.ProrataWethVault.convertToAssetsN words.shares.toNat
        (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply)
      (effect : OutboundEffect sevm words.receiver words.owner words.assets words.shares words.returned pre post) :
      FourQuoteOperation vault sevm pre post
  | credit (words : CreditWords)
      (wethTarget : sevm.currentTarget = wethAccount)
      (sourceNotVault : words.source ≠ vault)
      (supplyKept : Devm.getStorVal post vault Blanc.ProrataWethVault.supplySlot =
        Devm.getStorVal pre vault Blanc.ProrataWethVault.supplySlot)
      (rowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount) vault) words.amount)
      (effect : Transfer (Stor.rest (Devm.getStor pre wethAccount)) words.source words.amount vault
        (Stor.rest (Devm.getStor post wethAccount))) :
      FourQuoteOperation vault sevm pre post
  | transfer (words : ShareTransferWords)
      (target : sevm.currentTarget = vault)
      (owner : words.owner = sevm.caller)
      (receiver : words.receiver = Sevm.argWord sevm 0)
      (amount : words.amount = Sevm.argWord sevm 1)
      (config : DirectWethConfiguration sevm.currentTarget sevm pre)
      (memoryWf : Mem.Wf pre.memory)
      (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
      (selectorEq : Sevm.selector sevm = selector "transfer" [.address, .uint256]) :
      FourQuoteOperation vault sevm pre post
  | transferFrom (words : ShareTransferFromWords)
      (target : sevm.currentTarget = vault)
      (spender : words.spender = sevm.caller)
      (owner : words.owner = Sevm.argWord sevm 0)
      (receiver : words.receiver = Sevm.argWord sevm 1)
      (amount : words.amount = Sevm.argWord sevm 2)
      (config : DirectWethConfiguration sevm.currentTarget sevm pre)
      (memoryWf : Mem.Wf pre.memory)
      (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
      (selectorEq : Sevm.selector sevm =
        selector "transferFrom" [.address, .address, .uint256]) :
      FourQuoteOperation vault sevm pre post
  | approve (words : ShareApprovalWords)
      (target : sevm.currentTarget = vault)
      (owner : words.owner = sevm.caller)
      (spender : words.spender = Sevm.argWord sevm 0)
      (amount : words.amount = Sevm.argWord sevm 1)
      (config : DirectWethConfiguration sevm.currentTarget sevm pre)
      (memoryWf : Mem.Wf pre.memory)
      (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
      (selectorEq : Sevm.selector sevm = selector "approve" [.address, .uint256]) :
      FourQuoteOperation vault sevm pre post

/-- The bounded quote-residue part of an actual operation. -/
def roundingContribution {vault : Adr} {sevm : Sevm} {pre post : Devm} :
    FourQuoteOperation vault sevm pre post → Nat
  | .deposit words _ _ _ _ _ _ =>
      depositResidue words.assets.toNat words.shares.toNat (vaultSnapshot vault pre)
  | .mint words _ _ _ _ _ _ =>
      depositResidue words.assets.toNat words.shares.toNat (vaultSnapshot vault pre)
  | .withdrawNormal words _ _ _ _ _ =>
      outboundResidue words.assets.toNat words.shares.toNat (vaultSnapshot vault pre)
  | .redeemNormal words _ _ _ _ _ =>
      outboundResidue words.assets.toNat words.shares.toNat (vaultSnapshot vault pre)
  | .withdrawSelf words _ _ _ _ _ =>
      outboundResidue words.assets.toNat words.shares.toNat (vaultSnapshot vault pre)
  | .redeemSelf words _ _ _ _ _ =>
      outboundResidue words.assets.toNat words.shares.toNat (vaultSnapshot vault pre)
  | .credit _ _ _ _ _ _ => 0
  | .transfer _ _ _ _ _ _ _ _ _ => 0
  | .transferFrom _ _ _ _ _ _ _ _ _ _ => 0
  | .approve _ _ _ _ _ _ _ _ _ => 0

/-- The retained-asset contribution is present only when an outbound receiver
is the vault itself. -/
def retainedContribution {vault : Adr} {sevm : Sevm} {pre post : Devm} :
    FourQuoteOperation vault sevm pre post → Nat
  | .deposit _ _ _ _ _ _ _ => 0
  | .mint _ _ _ _ _ _ _ => 0
  | .withdrawNormal _ _ _ _ _ _ => 0
  | .redeemNormal _ _ _ _ _ _ => 0
  | .withdrawSelf words _ _ _ _ _ => words.assets.toNat * D (vaultSnapshot vault pre)
  | .redeemSelf words _ _ _ _ _ => words.assets.toNat * D (vaultSnapshot vault pre)
  | .credit _ _ _ _ _ _ => 0
  | .transfer _ _ _ _ _ _ _ _ _ => 0
  | .transferFrom _ _ _ _ _ _ _ _ _ _ => 0
  | .approve _ _ _ _ _ _ _ _ _ => 0

/-- The outside-credit contribution is present only for the raw third-party
WETH transfer tag. -/
def creditContribution {vault : Adr} {sevm : Sevm} {pre post : Devm} :
    FourQuoteOperation vault sevm pre post → Nat
  | .deposit _ _ _ _ _ _ _ => 0
  | .mint _ _ _ _ _ _ _ => 0
  | .withdrawNormal _ _ _ _ _ _ => 0
  | .redeemNormal _ _ _ _ _ _ => 0
  | .withdrawSelf _ _ _ _ _ _ => 0
  | .redeemSelf _ _ _ _ _ _ => 0
  | .credit words _ _ _ _ _ => words.amount.toNat * D (vaultSnapshot vault pre)
  | .transfer _ _ _ _ _ _ _ _ _ => 0
  | .transferFrom _ _ _ _ _ _ _ _ _ _ => 0
  | .approve _ _ _ _ _ _ _ _ _ => 0

private theorem deposit_step_exact {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (words : InboundWords) (target : sevm.currentTarget = vault)
    (depositorNotVault : sevm.caller ≠ sevm.currentTarget)
    (supplyNof : B256.Nof (Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot) words.shares)
    (rowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount)
      sevm.currentTarget) words.assets)
    (quote : words.shares.toNat = Blanc.ProrataWethVault.convertToSharesN words.assets.toNat
      (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply)
    (effect : InboundEffect sevm words.receiver words.assets words.shares words.returned pre post) :
    X (vaultSnapshot vault post) * D (vaultSnapshot vault pre) =
      X (vaultSnapshot vault pre) * D (vaultSnapshot vault post) +
        depositResidue words.assets.toNat words.shares.toNat (vaultSnapshot vault pre) := by
  have shape := inboundEffect_normal_snapshot depositorNotVault supplyNof rowNof effect
  simp only [snapshotAt_eq] at shape quote
  rw [target] at shape quote
  rw [shape]
  simpa using normalInbound_price words.assets.toNat words.shares.toNat
    (vaultSnapshot vault pre) quote

private theorem mint_step_exact {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (words : InboundWords) (target : sevm.currentTarget = vault)
    (depositorNotVault : sevm.caller ≠ sevm.currentTarget)
    (supplyNof : B256.Nof (Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot) words.shares)
    (rowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount)
      sevm.currentTarget) words.assets)
    (quote : words.assets.toNat = Blanc.ProrataWethVault.previewMintN words.shares.toNat
      (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply)
    (effect : InboundEffect sevm words.receiver words.assets words.shares words.returned pre post) :
    X (vaultSnapshot vault post) * D (vaultSnapshot vault pre) =
      X (vaultSnapshot vault pre) * D (vaultSnapshot vault post) +
        depositResidue words.assets.toNat words.shares.toNat (vaultSnapshot vault pre) := by
  have shape := inboundEffect_normal_snapshot depositorNotVault supplyNof rowNof effect
  simp only [snapshotAt_eq] at shape quote
  rw [target] at shape quote
  rw [quote] at shape
  rw [shape]
  simpa [quote] using normalInbound_price_mint words.shares.toNat (vaultSnapshot vault pre)

private theorem withdrawNormal_step_exact {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (words : OutboundWords) (target : sevm.currentTarget = vault)
    (receiverNotVault : sevm.currentTarget ≠ words.receiver.toAdr)
    (burnable : words.shares.toNat ≤ (snapshotAt sevm pre).supply)
    (quote : words.shares.toNat = Blanc.ProrataWethVault.previewWithdrawN words.assets.toNat
      (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply)
    (effect : OutboundEffect sevm words.receiver words.owner words.assets words.shares words.returned pre post) :
    X (vaultSnapshot vault post) * D (vaultSnapshot vault pre) =
      X (vaultSnapshot vault pre) * D (vaultSnapshot vault post) +
        outboundResidue words.assets.toNat words.shares.toNat (vaultSnapshot vault pre) := by
  have covered := outboundEffect_covered effect
  have shape := outboundEffect_normal_snapshot receiverNotVault burnable covered effect
  simp only [snapshotAt_eq] at burnable quote covered shape
  rw [target] at burnable quote covered shape
  have burnable' : Blanc.ProrataWethVault.previewWithdrawN words.assets.toNat
      (vaultSnapshot vault pre).balance (vaultSnapshot vault pre).supply ≤
      (vaultSnapshot vault pre).supply := by
    simpa [quote] using burnable
  rw [quote] at shape
  rw [shape]
  simpa [quote] using normalOutbound_price_withdraw words.assets.toNat
    (vaultSnapshot vault pre) burnable' covered

private theorem redeemNormal_step_exact {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (words : OutboundWords) (target : sevm.currentTarget = vault)
    (receiverNotVault : sevm.currentTarget ≠ words.receiver.toAdr)
    (burnable : words.shares.toNat ≤ (snapshotAt sevm pre).supply)
    (quote : words.assets.toNat = Blanc.ProrataWethVault.convertToAssetsN words.shares.toNat
      (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply)
    (effect : OutboundEffect sevm words.receiver words.owner words.assets words.shares words.returned pre post) :
    X (vaultSnapshot vault post) * D (vaultSnapshot vault pre) =
      X (vaultSnapshot vault pre) * D (vaultSnapshot vault post) +
        outboundResidue words.assets.toNat words.shares.toNat (vaultSnapshot vault pre) := by
  have covered := outboundEffect_covered effect
  have shape := outboundEffect_normal_snapshot receiverNotVault burnable covered effect
  simp only [snapshotAt_eq] at burnable quote covered shape
  rw [target] at burnable quote covered shape
  have covered' : Blanc.ProrataWethVault.convertToAssetsN words.shares.toNat
      (vaultSnapshot vault pre).balance (vaultSnapshot vault pre).supply ≤
      (vaultSnapshot vault pre).balance := by
    simpa [quote] using covered
  rw [quote] at shape
  rw [shape]
  simpa [quote] using normalOutbound_price_redeem words.shares.toNat
    (vaultSnapshot vault pre) burnable covered'

private theorem withdrawSelf_step_exact {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (words : OutboundWords) (target : sevm.currentTarget = vault)
    (receiverIsVault : words.receiver.toAdr = sevm.currentTarget)
    (burnable : words.shares.toNat ≤ (snapshotAt sevm pre).supply)
    (quote : words.shares.toNat = Blanc.ProrataWethVault.previewWithdrawN words.assets.toNat
      (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply)
    (effect : OutboundEffect sevm words.receiver words.owner words.assets words.shares words.returned pre post) :
    X (vaultSnapshot vault post) * D (vaultSnapshot vault pre) =
      X (vaultSnapshot vault pre) * D (vaultSnapshot vault post) +
        outboundResidue words.assets.toNat words.shares.toNat (vaultSnapshot vault pre) +
          words.assets.toNat * D (vaultSnapshot vault pre) := by
  have shape := outboundEffect_retained_snapshot receiverIsVault burnable effect
  simp only [snapshotAt_eq] at burnable quote shape
  rw [target] at burnable quote shape
  have residue : words.shares.toNat * X (vaultSnapshot vault pre) =
      words.assets.toNat * D (vaultSnapshot vault pre) +
        outboundResidue words.assets.toNat words.shares.toNat (vaultSnapshot vault pre) := by
    simpa [quote] using withdraw_residue_eq words.assets.toNat (vaultSnapshot vault pre)
  rw [shape]
  exact retainedOutbound_price words.assets.toNat words.shares.toNat
    (vaultSnapshot vault pre) burnable residue

private theorem redeemSelf_step_exact {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (words : OutboundWords) (target : sevm.currentTarget = vault)
    (receiverIsVault : words.receiver.toAdr = sevm.currentTarget)
    (burnable : words.shares.toNat ≤ (snapshotAt sevm pre).supply)
    (quote : words.assets.toNat = Blanc.ProrataWethVault.convertToAssetsN words.shares.toNat
      (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply)
    (effect : OutboundEffect sevm words.receiver words.owner words.assets words.shares words.returned pre post) :
    X (vaultSnapshot vault post) * D (vaultSnapshot vault pre) =
      X (vaultSnapshot vault pre) * D (vaultSnapshot vault post) +
        outboundResidue words.assets.toNat words.shares.toNat (vaultSnapshot vault pre) +
          words.assets.toNat * D (vaultSnapshot vault pre) := by
  have shape := outboundEffect_retained_snapshot receiverIsVault burnable effect
  simp only [snapshotAt_eq] at burnable quote shape
  rw [target] at burnable quote shape
  have residue : words.shares.toNat * X (vaultSnapshot vault pre) =
      words.assets.toNat * D (vaultSnapshot vault pre) +
        outboundResidue words.assets.toNat words.shares.toNat (vaultSnapshot vault pre) := by
    simpa [quote] using redeem_residue_eq words.shares.toNat (vaultSnapshot vault pre)
  rw [shape]
  exact retainedOutbound_price words.assets.toNat words.shares.toNat
    (vaultSnapshot vault pre) burnable residue

private theorem credit_step_exact {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (words : CreditWords) (_wethTarget : sevm.currentTarget = wethAccount)
    (sourceNotVault : words.source ≠ vault)
    (supplyKept : Devm.getStorVal post vault Blanc.ProrataWethVault.supplySlot =
      Devm.getStorVal pre vault Blanc.ProrataWethVault.supplySlot)
    (rowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount) vault) words.amount)
    (effect : Transfer (Stor.rest (Devm.getStor pre wethAccount)) words.source words.amount vault
      (Stor.rest (Devm.getStor post wethAccount))) :
    X (vaultSnapshot vault post) * D (vaultSnapshot vault pre) =
      X (vaultSnapshot vault pre) * D (vaultSnapshot vault post) +
        words.amount.toNat * D (vaultSnapshot vault pre) := by
  have shape := externalCredit_snapshot sourceNotVault supplyKept rowNof effect
  rw [shape]
  exact externalCredit_price words.amount.toNat (vaultSnapshot vault pre)

/-- A compiled share operation preserves both accounting coordinates. -/
private theorem silent_step_exact {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (target : sevm.currentTarget = vault)
    (effect : Blanc.Prorata.ProrataAccountingEffect Blanc.ProrataWethVault.offsetN
      (snapshotAt sevm pre) .silent (snapshotAt sevm post)) :
    X (vaultSnapshot vault post) * D (vaultSnapshot vault pre) =
      X (vaultSnapshot vault pre) * D (vaultSnapshot vault post) + 0 + 0 + 0 := by
  have shape := Blanc.Prorata.ProrataAccountingEffect.silent_inv effect
  simp only [snapshotAt_eq] at shape
  rw [target] at shape
  rw [shape]
  simp

/-- One State-linked, actual-effect accounting transition. -/
structure FourQuoteTransition (vault : Adr) (before after : State) : Type where
  sevm : Sevm
  entry : Devm
  exit : Devm
  /-- Separate calls may have unrelated machine-local fields, but their
  storage states are the consecutive accounting worlds. -/
  preState : entry.state = before
  postState : exit.state = after
  operation : FourQuoteOperation vault sevm entry exit

/-- Forget the dynamic frame details of one actual effect, retaining the
standard StateTrace boundary whose origin is that exact effect witness. -/
def FourQuoteTransition.stateTransition {vault before after}
    (event : FourQuoteTransition vault before after) :
    StateTransition (FourQuoteOperation vault event.sevm event.entry event.exit) :=
  { origin := event.operation
    before := before
    after := after }

/-- Every tagged actual effect satisfies its exact price recurrence. -/
theorem FourQuoteOperation.step_exact {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (operation : FourQuoteOperation vault sevm pre post) :
    X (vaultSnapshot vault post) * D (vaultSnapshot vault pre) =
      X (vaultSnapshot vault pre) * D (vaultSnapshot vault post) +
        roundingContribution operation + retainedContribution operation + creditContribution operation := by
  cases operation with
  | deposit words target depositorNotVault supplyNof rowNof quote effect =>
      simpa [roundingContribution, retainedContribution, creditContribution] using
        deposit_step_exact words target depositorNotVault supplyNof rowNof quote effect
  | mint words target depositorNotVault supplyNof rowNof quote effect =>
      simpa [roundingContribution, retainedContribution, creditContribution] using
        mint_step_exact words target depositorNotVault supplyNof rowNof quote effect
  | withdrawNormal words target receiverNotVault burnable quote effect =>
      simpa [roundingContribution, retainedContribution, creditContribution] using
        withdrawNormal_step_exact words target receiverNotVault burnable quote effect
  | redeemNormal words target receiverNotVault burnable quote effect =>
      simpa [roundingContribution, retainedContribution, creditContribution] using
        redeemNormal_step_exact words target receiverNotVault burnable quote effect
  | withdrawSelf words target receiverIsVault burnable quote effect =>
      simpa [roundingContribution, retainedContribution, creditContribution] using
        withdrawSelf_step_exact words target receiverIsVault burnable quote effect
  | redeemSelf words target receiverIsVault burnable quote effect =>
      simpa [roundingContribution, retainedContribution, creditContribution] using
        redeemSelf_step_exact words target receiverIsVault burnable quote effect
  | credit words wethTarget sourceNotVault supplyKept rowNof effect =>
      simpa [roundingContribution, retainedContribution, creditContribution] using
        credit_step_exact words wethTarget sourceNotVault supplyKept rowNof effect
  | transfer words target owner receiver amount config memoryWf run selectorEq =>
      simpa [roundingContribution, retainedContribution, creditContribution] using
        silent_step_exact target (transferEffect_accountingStep config memoryWf run selectorEq)
  | transferFrom words target spender owner receiver amount config memoryWf run selectorEq =>
      simpa [roundingContribution, retainedContribution, creditContribution] using
        silent_step_exact target
          (transferFromEffect_accountingStep config memoryWf run selectorEq)
  | approve words target owner spender amount config memoryWf run selectorEq =>
      simpa [roundingContribution, retainedContribution, creditContribution] using
        silent_step_exact target (approveEffect_accountingStep config memoryWf run selectorEq)

/-- Every actual four-quote operation weakly increases the virtual-asset
price per share. -/
theorem FourQuoteOperation.priceLe {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (operation : FourQuoteOperation vault sevm pre post) :
    Blanc.Prorata.PriceLe Blanc.ProrataWethVault.offsetN
      (vaultSnapshot vault pre) (vaultSnapshot vault post) := by
  unfold Blanc.Prorata.PriceLe
  change X (vaultSnapshot vault pre) * D (vaultSnapshot vault post) ≤
    X (vaultSnapshot vault post) * D (vaultSnapshot vault pre)
  rw [operation.step_exact]
  omega

/-- One actual transition packaged with its stable-state endpoints. -/
structure FourQuoteStep (vault : Adr) : Type where
  before : State
  after : State
  event : FourQuoteTransition vault before after

/-- The common state-trace boundary for a packaged tagged step. -/
def FourQuoteStep.stateTransition {vault : Adr} (step : FourQuoteStep vault) :
    StateTransition (FourQuoteOperation vault step.event.sevm step.event.entry step.event.exit) :=
  step.event.stateTransition

/-- The exact recurrence expressed at the standard StateTrace boundary. -/
theorem FourQuoteStep.trace_exact {vault : Adr} (step : FourQuoteStep vault) :
    X (stateSnapshot vault step.stateTransition.after) *
        D (stateSnapshot vault step.stateTransition.before) =
      X (stateSnapshot vault step.stateTransition.before) *
          D (stateSnapshot vault step.stateTransition.after) +
        roundingContribution step.event.operation + retainedContribution step.event.operation +
          creditContribution step.event.operation := by
  rcases step with ⟨before, after, sevm, entry, exit, preState, postState, operation⟩
  have hstep := operation.step_exact
  simpa [FourQuoteStep.stateTransition, FourQuoteTransition.stateTransition,
    vaultSnapshot_state, preState, postState] using hstep

/-- A connected finite trace of State-linked actual effects. -/
structure FourQuotePath (vault : Adr) : Type where
  steps : List (FourQuoteStep vault)
  world : Fin (steps.length + 1) → State
  pre_eq (i : Fin steps.length) :
    world i.castSucc = (steps.get i).before
  post_eq (i : Fin steps.length) :
    world i.succ = (steps.get i).after

namespace FourQuotePath

/-- Total state lookup; the direct telescope only uses in-range indices. -/
def worldAt {vault : Adr} (path : FourQuotePath vault) (i : Nat) : State :=
  path.world ⟨min i path.steps.length,
    Nat.lt_succ_of_le (Nat.min_le_right i path.steps.length)⟩

def snapshotAt {vault : Adr} (path : FourQuotePath vault) (i : Nat) : Snapshot :=
  stateSnapshot vault (path.worldAt i)

def xAt {vault : Adr} (path : FourQuotePath vault) (i : Nat) : Nat :=
  X (path.snapshotAt i)

def dAt {vault : Adr} (path : FourQuotePath vault) (i : Nat) : Nat :=
  D (path.snapshotAt i)

def roundingAt {vault : Adr} (path : FourQuotePath vault) (i : Nat) : Nat :=
  if hi : i < path.steps.length then
    roundingContribution (path.steps.get ⟨i, hi⟩).event.operation
  else 0

def retainedAt {vault : Adr} (path : FourQuotePath vault) (i : Nat) : Nat :=
  if hi : i < path.steps.length then
    retainedContribution (path.steps.get ⟨i, hi⟩).event.operation
  else 0

def creditAt {vault : Adr} (path : FourQuotePath vault) (i : Nat) : Nat :=
  if hi : i < path.steps.length then
    creditContribution (path.steps.get ⟨i, hi⟩).event.operation
  else 0

/-- An in-range boundary exposes the exact three-contribution recurrence. -/
theorem step_exact_at {vault : Adr} (path : FourQuotePath vault)
    {i : Nat} (hi : i < path.steps.length) :
    path.xAt (i + 1) * path.dAt i =
      path.xAt i * path.dAt (i + 1) +
        path.roundingAt i + path.retainedAt i + path.creditAt i := by
  let index : Fin path.steps.length := ⟨i, hi⟩
  let step := path.steps.get index
  have hpre : path.worldAt i = step.before := by
    calc
      path.worldAt i = path.world index.castSucc := by
        apply congrArg path.world
        apply Fin.ext
        simp [index, Nat.min_eq_left (Nat.le_of_lt hi)]
      _ = step.before := by
        simpa only [step] using path.pre_eq index
  have hpost : path.worldAt (i + 1) = step.after := by
    calc
      path.worldAt (i + 1) = path.world index.succ := by
        apply congrArg path.world
        apply Fin.ext
        simp [index, Nat.min_eq_left (Nat.succ_le_iff.mpr hi)]
      _ = step.after := by
        simpa only [step] using path.post_eq index
  have hstep := step.trace_exact
  simpa only [xAt, dAt, snapshotAt, roundingAt, retainedAt, creditAt,
    FourQuoteStep.stateTransition, FourQuoteTransition.stateTransition,
    hi, dite_true, hpre, hpost] using hstep

/-- The actual effect at one in-range path boundary weakly increases price. -/
theorem priceLe_step_at {vault : Adr} (path : FourQuotePath vault)
    {i : Nat} (hi : i < path.steps.length) :
    Blanc.Prorata.PriceLe Blanc.ProrataWethVault.offsetN
      (path.snapshotAt i) (path.snapshotAt (i + 1)) := by
  let index : Fin path.steps.length := ⟨i, hi⟩
  let step := path.steps.get index
  have hpre : path.worldAt i = step.before := by
    calc
      path.worldAt i = path.world index.castSucc := by
        apply congrArg path.world
        apply Fin.ext
        simp [index, Nat.min_eq_left (Nat.le_of_lt hi)]
      _ = step.before := by
        simpa only [step] using path.pre_eq index
  have hpost : path.worldAt (i + 1) = step.after := by
    calc
      path.worldAt (i + 1) = path.world index.succ := by
        apply congrArg path.world
        apply Fin.ext
        simp [index, Nat.min_eq_left (Nat.succ_le_iff.mpr hi)]
      _ = step.after := by
        simpa only [step] using path.post_eq index
  have hprice := step.event.operation.priceLe
  simpa only [snapshotAt, vaultSnapshot_state, step.event.preState,
    step.event.postState, hpre, hpost] using hprice

/-- Every clamped boundary of a connected actual-effect path is priced no
lower than its first boundary. -/
theorem priceLe_snapshotAt {vault : Adr} (path : FourQuotePath vault) :
    ∀ i : Nat, Blanc.Prorata.PriceLe Blanc.ProrataWethVault.offsetN
      (path.snapshotAt 0) (path.snapshotAt i) := by
  intro i
  induction i with
  | zero => exact Blanc.Prorata.PriceLe.refl _ _
  | succ i ih =>
      by_cases hi : i < path.steps.length
      · exact Blanc.Prorata.PriceLe.trans Blanc.ProrataWethVault.offsetN_ne_zero
          ih (path.priceLe_step_at hi)
      · have hstay : path.snapshotAt (i + 1) = path.snapshotAt i := by
          unfold snapshotAt worldAt
          apply congrArg (stateSnapshot vault)
          apply congrArg path.world
          apply Fin.ext
          have hle : path.steps.length ≤ i := Nat.le_of_not_lt hi
          simp [Nat.min_eq_right hle,
            Nat.min_eq_right (Nat.le_succ_of_le hle)]
        rw [hstay]
        exact ih

/-- A zero-snapshot actual-effect path preserves the local supply/asset bound
at every clamped boundary. -/
theorem supply_le_offset_mul_balance {vault : Adr} (path : FourQuotePath vault)
    (hzero : path.snapshotAt 0 = ⟨0, 0⟩) (i : Nat) :
    (path.snapshotAt i).supply ≤ Blanc.ProrataWethVault.offsetN *
      (path.snapshotAt i).balance := by
  apply Blanc.Prorata.backed_of_priceLe_genesis
  rw [← hzero]
  exact path.priceLe_snapshotAt i

/-- Direct Nat-semiring telescope for a connected finite trace of actual
four-quote effects. -/
theorem dust_telescope {vault : Adr} (path : FourQuotePath vault) :
    let n := path.steps.length
    path.xAt n * (∏ j ∈ Finset.range n, path.dAt j) =
      path.xAt 0 * (∏ j ∈ Finset.Icc 1 n, path.dAt j) +
        ∑ i ∈ Finset.range n,
          (path.roundingAt i + path.retainedAt i + path.creditAt i) *
              (∏ j ∈ Finset.range i, path.dAt j) *
                (∏ j ∈ Finset.Icc (i + 2) n, path.dAt j) := by
  dsimp only
  apply Blanc.Prorata.dust_telescope_of_step
  intro i hi
  simpa only [Nat.add_assoc] using path.step_exact_at hi

/-- The same telescope with rounding, retained-asset, and external-credit
terms exposed as three separately weighted sums. -/
theorem dust_telescope_separate {vault : Adr} (path : FourQuotePath vault) :
    let n := path.steps.length
    path.xAt n * (∏ j ∈ Finset.range n, path.dAt j) =
      path.xAt 0 * (∏ j ∈ Finset.Icc 1 n, path.dAt j) +
        (∑ i ∈ Finset.range n,
          path.roundingAt i * (∏ j ∈ Finset.range i, path.dAt j) *
            (∏ j ∈ Finset.Icc (i + 2) n, path.dAt j)) +
        (∑ i ∈ Finset.range n,
          path.retainedAt i * (∏ j ∈ Finset.range i, path.dAt j) *
            (∏ j ∈ Finset.Icc (i + 2) n, path.dAt j)) +
        ∑ i ∈ Finset.range n,
          path.creditAt i * (∏ j ∈ Finset.range i, path.dAt j) *
            (∏ j ∈ Finset.Icc (i + 2) n, path.dAt j) := by
  dsimp only
  rw [dust_telescope]
  simp only [Nat.add_mul, Finset.sum_add_distrib]
  ac_rfl

end FourQuotePath

end FourQuote

end Blanc.Composition.ProrataWethVault
