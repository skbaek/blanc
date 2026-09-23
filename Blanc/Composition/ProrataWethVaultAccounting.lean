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
    (hfork : CoveredFork sevm.benvStat.fork)
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
    mint_compiled_effect (hfork := hfork) config memoryWf run selectorEq
  refine ⟨supply, _, supplyEq, ?_, stable, room, effect⟩
  exact B256.toNat_toB256_of_lt chargeFits

/-- The actual compiled `withdraw` occurrence exposes the inverse quote as a
named natural-number burn and retains its exact configured WETH effect. -/
theorem withdraw_compiled_quote
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
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
    withdraw_compiled_effect (hfork := hfork) config memoryWf run selectorEq
  refine ⟨supply, _, supplyEq, ?_, ?_, effect⟩
  exact B256.toNat_toB256_of_lt burnFits
  exact burnable

/-- The compiled inverse-withdraw call reaches the actual normal outbound
boundary whenever its receiver differs from the vault; the effect and compiled
guard already provide its debit bounds. -/
theorem withdraw_compiled_normal_snapshot
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
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
    withdraw_compiled_quote (hfork := hfork) config memoryWf run selectorEq
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
    (hfork : CoveredFork sevm.benvStat.fork)
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
    deposit_compiled_effect_named (hfork := hfork) config memoryWf run selectorEq
  exact ⟨supply, shares, supplyEq, quote, stable, room, effect⟩

/-- The compiled `redeem` occurrence exposes its floor asset quote in the
same named form as the other three public endpoints. -/
theorem redeem_compiled_quote
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
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
    redeem_compiled_effect_named (hfork := hfork) config memoryWf run selectorEq
  exact ⟨supply, assets, supplyEq, quote, burnable, effect⟩

/-- A compiled `deposit` reaches the real normal inbound boundary once its
WETH-row addition is known not to wrap; capacity and share-room guards derive
the supply-row fact. -/
theorem deposit_compiled_normal_snapshot
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
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
    deposit_compiled_quote (hfork := hfork) config memoryWf run selectorEq
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
    (hfork : CoveredFork sevm.benvStat.fork)
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
    mint_compiled_quote (hfork := hfork) config memoryWf run selectorEq
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
    (hfork : CoveredFork sevm.benvStat.fork)
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
    withdraw_compiled_quote (hfork := hfork) config memoryWf run selectorEq
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
    (hfork : CoveredFork sevm.benvStat.fork)
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
    redeem_compiled_quote (hfork := hfork) config memoryWf run selectorEq
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
    (hfork : CoveredFork sevm.benvStat.fork)
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
    redeem_compiled_quote (hfork := hfork) config memoryWf run selectorEq
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

/-- The vault-side storage equation of an actual inbound effect is one exact
share-ledger credit.  The supply write is invisible to `Stor.rest`. -/
theorem inboundEffect_share_increase
    {sevm : Sevm} {pre post : Devm} {receiver assets shares returned : B256}
    {receiverAdr : Adr}
    (receiverWord : receiverAdr.toB256 = receiver)
    (effect : InboundEffect sevm receiver assets shares returned pre post) :
    Increase receiverAdr shares
      (Stor.rest (Devm.getStor pre sevm.currentTarget))
      (Stor.rest (Devm.getStor post sevm.currentTarget)) := by
  obtain ⟨-, -, vaultStorage, -, -⟩ := effect
  rw [vaultStorage, ← receiverWord]
  intro account
  constructor
  · intro same
    subst same
    rw [rest_set_slot Blanc.ProrataWethVault.supplySlot_not_validAdr,
      Stor.rest_set_self]
    rfl
  · intro different
    rw [rest_set_slot Blanc.ProrataWethVault.supplySlot_not_validAdr,
      Stor.rest_set_ne _ (Ne.symm different)]

/-- The vault-side storage equation of an actual outbound effect is one exact
share-ledger debit.  The allowance write remains outside `Stor.rest`. -/
theorem outboundEffect_share_decrease
    {sevm : Sevm} {pre post : Devm} {receiver owner assets shares returned : B256}
    {ownerAdr : Adr}
    (ownerWord : ownerAdr.toB256 = owner)
    (effect : OutboundEffect sevm receiver owner assets shares returned pre post) :
    Decrease ownerAdr shares
      (Stor.rest (Devm.getStor pre sevm.currentTarget))
      (Stor.rest (Devm.getStor post sevm.currentTarget)) := by
  obtain ⟨-, -, ownerRow, -, otherRows, -, -, -⟩ := effect
  intro account
  constructor
  · intro same
    subst same
    change (Devm.getStor pre sevm.currentTarget).get ownerAdr.toB256 - shares =
      (Devm.getStor post sevm.currentTarget).get ownerAdr.toB256
    rw [ownerWord]
    exact ownerRow.symm
  · intro different
    change (Devm.getStor pre sevm.currentTarget).get account.toB256 =
      (Devm.getStor post sevm.currentTarget).get account.toB256
    exact (otherRows account.toB256 ⟨account, rfl⟩ (by
      intro keyEq
      exact different (Adr.toB256_inj (keyEq.trans ownerWord.symm)).symm)).symm

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

/-- Bounded-entry actual-root evidence for one direct WETH `transfer` credit.

The record retains the exact bounded entry that G6 will later derive from an
actual body occurrence: WETH target and code address, the credited source as
caller, zero value, the exact `transferCalldata` payload, empty entry stack,
memory and logs, the exact compiled-code identity, one actual `Exec` ending in
the retained post state, and a clean post error.  It claims no history
closure. -/
structure ActualDirectWethCredit (vault : Adr) (words : CreditWords)
    (sevm : Sevm) (pre post : Devm) : Type where
  target : sevm.currentTarget = wethAccount
  codeAddress : sevm.codeAddress = some wethAccount
  caller : sevm.caller = words.source
  value : sevm.value = 0
  data : sevm.data = transferCalldata vault words.amount
  stack : pre.stack = []
  memory : pre.memory = Mem.empty
  logs : pre.logs = []
  code : some sevm.code.toList = Prog.compile Blanc.weth
  run : Exec 0 sevm pre (.ok post)
  clean : post.error = none

/-- The closed WETH program has no dangling program counters.  Proved locally
so the frozen WETH program keeps its existing visibility. -/
private theorem directWethCredit_pcFree : Prog.pcFree Blanc.weth = true := by
  decide +kernel

/-- The bounded entry recovers the exact world-strength WETH program run: the
actual `Exec` becomes a gas-exact compiled run through `runCompiled_of_exec`,
and the retained pre/post storage worlds with the exact log frame are the
initial and final observations. -/
theorem ActualDirectWethCredit.worldProgramRun
    {vault : Adr} {words : CreditWords} {sevm : Sevm} {pre post : Devm}
    (actual : ActualDirectWethCredit vault words sevm pre post) :
    SuccessfulWethWorldProgramRun words.source
      (transferCalldata vault words.amount) post.output
      (Devm.getStor pre) (Devm.getStor post) [] post.logs := by
  rcases actual with ⟨target, codeAddress, caller, valueZero, dataEq,
    stackEmpty, memoryEmpty, logsEmpty, codeEq, run, clean⟩
  have compiled : Prog.RunCompiled sevm pre Blanc.weth post :=
    Prog.runCompiled_of_exec sevm pre Blanc.weth post
      directWethCredit_pcFree run codeEq
  have logsEq : post.logs = [] ++ post.logs := (List.nil_append _).symm
  exact ⟨sevm, pre, post, target, codeAddress, caller, valueZero, dataEq,
    stackEmpty, memoryEmpty, logsEmpty, rfl, compiled, clean, rfl, logsEq,
    rfl⟩

/-- The actual foreign-storage frame at the vault: WETH execution leaves every
non-WETH account untouched, so the vault's own storage is exactly kept. -/
private theorem actual_credit_vault_storage_eq
    {vault : Adr} {words : CreditWords} {sevm : Sevm} {pre post : Devm}
    (actual : ActualDirectWethCredit vault words sevm pre post)
    (separation : wethAccount ≠ vault) :
    Devm.getStor post vault = Devm.getStor pre vault := by
  obtain ⟨_, foreign, _, _⟩ :=
    SuccessfulWethWorldProgramRun.transfer_effect actual.worldProgramRun
  exact foreign vault separation

/-- Actual share evidence is indexed by the accepted ten-tag operation.  It
retains endpoint guards and canonical ABI roles; public projections derive,
rather than assume, the resulting row movement.  The credit case retains the
vault storage equation instead of endpoint guards. -/
inductive FourQuoteShareEvidence {vault : Adr} {sevm : Sevm} {pre post : Devm} :
    FourQuoteOperation vault sevm pre post → Prop where
  | deposit (words : InboundWords) (target : sevm.currentTarget = vault)
      (depositorNotVault : sevm.caller ≠ sevm.currentTarget)
      (supplyNof : B256.Nof (Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot) words.shares)
      (wethRowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount)
        sevm.currentTarget) words.assets)
      (quote : words.shares.toNat = Blanc.ProrataWethVault.convertToSharesN words.assets.toNat
        (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply)
      (effect : InboundEffect sevm words.receiver words.assets words.shares words.returned pre post)
      (receiverArg : words.receiver = Sevm.argWord sevm 1)
      (receiverValid : ValidAdr words.receiver) (supply : B256)
      (supplyEq : supply = Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot)
      (stable : supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN)
      (room : words.shares.toNat ≤ Blanc.ProrataWethVault.shareRoomN supply.toNat) :
      FourQuoteShareEvidence (.deposit words target depositorNotVault supplyNof wethRowNof quote effect)
  | mint (words : InboundWords) (target : sevm.currentTarget = vault)
      (depositorNotVault : sevm.caller ≠ sevm.currentTarget)
      (supplyNof : B256.Nof (Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot) words.shares)
      (wethRowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount)
        sevm.currentTarget) words.assets)
      (quote : words.assets.toNat = Blanc.ProrataWethVault.previewMintN words.shares.toNat
        (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply)
      (effect : InboundEffect sevm words.receiver words.assets words.shares words.returned pre post)
      (receiverArg : words.receiver = Sevm.argWord sevm 1)
      (receiverValid : ValidAdr words.receiver) (supply : B256)
      (supplyEq : supply = Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot)
      (stable : supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN)
      (room : words.shares.toNat ≤ Blanc.ProrataWethVault.shareRoomN supply.toNat) :
      FourQuoteShareEvidence (.mint words target depositorNotVault supplyNof wethRowNof quote effect)
  | withdrawNormal (words : OutboundWords) (target : sevm.currentTarget = vault)
      (receiverNotVault : sevm.currentTarget ≠ words.receiver.toAdr)
      (burnable : words.shares.toNat ≤ (snapshotAt sevm pre).supply)
      (quote : words.shares.toNat = Blanc.ProrataWethVault.previewWithdrawN words.assets.toNat
        (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply)
      (effect : OutboundEffect sevm words.receiver words.owner words.assets words.shares words.returned pre post)
      (receiverArg : words.receiver = Sevm.argWord sevm 1)
      (ownerArg : words.owner = Sevm.argWord sevm 2)
      (receiverValid : ValidAdr words.receiver)
      (ownerValid : ValidAdr words.owner)
      (covered : words.shares.toNat ≤
        (Devm.getStorVal pre sevm.currentTarget words.owner).toNat) :
      FourQuoteShareEvidence (.withdrawNormal words target receiverNotVault burnable quote effect)
  | redeemNormal (words : OutboundWords) (target : sevm.currentTarget = vault)
      (receiverNotVault : sevm.currentTarget ≠ words.receiver.toAdr)
      (burnable : words.shares.toNat ≤ (snapshotAt sevm pre).supply)
      (quote : words.assets.toNat = Blanc.ProrataWethVault.convertToAssetsN words.shares.toNat
        (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply)
      (effect : OutboundEffect sevm words.receiver words.owner words.assets words.shares words.returned pre post)
      (receiverArg : words.receiver = Sevm.argWord sevm 1)
      (ownerArg : words.owner = Sevm.argWord sevm 2)
      (receiverValid : ValidAdr words.receiver)
      (ownerValid : ValidAdr words.owner)
      (covered : words.shares.toNat ≤
        (Devm.getStorVal pre sevm.currentTarget words.owner).toNat) :
      FourQuoteShareEvidence (.redeemNormal words target receiverNotVault burnable quote effect)
  | withdrawSelf (words : OutboundWords) (target : sevm.currentTarget = vault)
      (receiverIsVault : words.receiver.toAdr = sevm.currentTarget)
      (burnable : words.shares.toNat ≤ (snapshotAt sevm pre).supply)
      (quote : words.shares.toNat = Blanc.ProrataWethVault.previewWithdrawN words.assets.toNat
        (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply)
      (effect : OutboundEffect sevm words.receiver words.owner words.assets words.shares words.returned pre post)
      (receiverArg : words.receiver = Sevm.argWord sevm 1)
      (ownerArg : words.owner = Sevm.argWord sevm 2)
      (receiverValid : ValidAdr words.receiver)
      (ownerValid : ValidAdr words.owner)
      (covered : words.shares.toNat ≤
        (Devm.getStorVal pre sevm.currentTarget words.owner).toNat) :
      FourQuoteShareEvidence (.withdrawSelf words target receiverIsVault burnable quote effect)
  | redeemSelf (words : OutboundWords) (target : sevm.currentTarget = vault)
      (receiverIsVault : words.receiver.toAdr = sevm.currentTarget)
      (burnable : words.shares.toNat ≤ (snapshotAt sevm pre).supply)
      (quote : words.assets.toNat = Blanc.ProrataWethVault.convertToAssetsN words.shares.toNat
        (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply)
      (effect : OutboundEffect sevm words.receiver words.owner words.assets words.shares words.returned pre post)
      (receiverArg : words.receiver = Sevm.argWord sevm 1)
      (ownerArg : words.owner = Sevm.argWord sevm 2)
      (receiverValid : ValidAdr words.receiver)
      (ownerValid : ValidAdr words.owner)
      (covered : words.shares.toNat ≤
        (Devm.getStorVal pre sevm.currentTarget words.owner).toNat) :
      FourQuoteShareEvidence (.redeemSelf words target receiverIsVault burnable quote effect)
  | credit (words : CreditWords)
      (wethTarget : sevm.currentTarget = wethAccount)
      (sourceNotVault : words.source ≠ vault)
      (supplyKept : Devm.getStorVal post vault
        Blanc.ProrataWethVault.supplySlot =
        Devm.getStorVal pre vault Blanc.ProrataWethVault.supplySlot)
      (rowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount) vault)
        words.amount)
      (effect : Transfer (Stor.rest (Devm.getStor pre wethAccount)) words.source
        words.amount vault (Stor.rest (Devm.getStor post wethAccount)))
      (vaultKept : Devm.getStor post vault = Devm.getStor pre vault) :
      FourQuoteShareEvidence
        (.credit words wethTarget sourceNotVault supplyKept rowNof effect)
  | transfer (words : ShareTransferWords) (target : sevm.currentTarget = vault)
      (owner : words.owner = sevm.caller) (receiver : words.receiver = Sevm.argWord sevm 0)
      (amount : words.amount = Sevm.argWord sevm 1)
      (config : DirectWethConfiguration sevm.currentTarget sevm pre)
      (memoryWf : Mem.Wf pre.memory)
      (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
      (selectorEq : Sevm.selector sevm = selector "transfer" [.address, .uint256]) :
      FourQuoteShareEvidence (.transfer words target owner receiver amount config memoryWf run selectorEq)
  | transferFrom (words : ShareTransferFromWords) (target : sevm.currentTarget = vault)
      (spender : words.spender = sevm.caller) (owner : words.owner = Sevm.argWord sevm 0)
      (receiver : words.receiver = Sevm.argWord sevm 1) (amount : words.amount = Sevm.argWord sevm 2)
      (config : DirectWethConfiguration sevm.currentTarget sevm pre)
      (memoryWf : Mem.Wf pre.memory)
      (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
      (selectorEq : Sevm.selector sevm =
        selector "transferFrom" [.address, .address, .uint256]) :
      FourQuoteShareEvidence (.transferFrom words target spender owner receiver amount config memoryWf run selectorEq)
  | approve (words : ShareApprovalWords) (target : sevm.currentTarget = vault)
      (owner : words.owner = sevm.caller) (spender : words.spender = Sevm.argWord sevm 0)
      (amount : words.amount = Sevm.argWord sevm 1)
      (config : DirectWethConfiguration sevm.currentTarget sevm pre)
      (memoryWf : Mem.Wf pre.memory)
      (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
      (selectorEq : Sevm.selector sevm = selector "approve" [.address, .uint256]) :
      FourQuoteShareEvidence (.approve words target owner spender amount config memoryWf run selectorEq)

/-- The actual address-shaped share-row movement selected by an accepted
operation.  A credit leaves the vault rows exactly unchanged. -/
def FourQuoteShareRowsMove {vault : Adr} {sevm : Sevm} {pre post : Devm} :
    FourQuoteOperation vault sevm pre post → Prop
  | .deposit words _ _ _ _ _ _ =>
      Increase words.receiver.toAdr words.shares
        (Stor.rest (Devm.getStor pre sevm.currentTarget))
        (Stor.rest (Devm.getStor post sevm.currentTarget))
  | .mint words _ _ _ _ _ _ =>
      Increase words.receiver.toAdr words.shares
        (Stor.rest (Devm.getStor pre sevm.currentTarget))
        (Stor.rest (Devm.getStor post sevm.currentTarget))
  | .withdrawNormal words _ _ _ _ _ =>
      Decrease words.owner.toAdr words.shares
        (Stor.rest (Devm.getStor pre sevm.currentTarget))
        (Stor.rest (Devm.getStor post sevm.currentTarget))
  | .redeemNormal words _ _ _ _ _ =>
      Decrease words.owner.toAdr words.shares
        (Stor.rest (Devm.getStor pre sevm.currentTarget))
        (Stor.rest (Devm.getStor post sevm.currentTarget))
  | .withdrawSelf words _ _ _ _ _ =>
      Decrease words.owner.toAdr words.shares
        (Stor.rest (Devm.getStor pre sevm.currentTarget))
        (Stor.rest (Devm.getStor post sevm.currentTarget))
  | .redeemSelf words _ _ _ _ _ =>
      Decrease words.owner.toAdr words.shares
        (Stor.rest (Devm.getStor pre sevm.currentTarget))
        (Stor.rest (Devm.getStor post sevm.currentTarget))
  | .credit _ _ _ _ _ _ =>
      Stor.rest (Devm.getStor post vault) =
        Stor.rest (Devm.getStor pre vault)
  | .transfer words _ _ _ _ _ _ _ _ =>
      Transfer (Stor.rest (Devm.getStor pre sevm.currentTarget)) words.owner
        words.amount words.receiver.toAdr
        (Stor.rest (Devm.getStor post sevm.currentTarget))
  | .transferFrom words _ _ _ _ _ _ _ _ _ =>
      Transfer (Stor.rest (Devm.getStor pre sevm.currentTarget)) words.owner.toAdr
        words.amount words.receiver.toAdr
        (Stor.rest (Devm.getStor post sevm.currentTarget))
  | .approve _ _ _ _ _ _ _ _ _ =>
      Stor.rest (Devm.getStor post sevm.currentTarget) =
        Stor.rest (Devm.getStor pre sevm.currentTarget)

/-- The exact finite-coalition share movement for each operation; a credit
leaves the vault coalition sum exactly unchanged.  Its use still explicitly
requires a pre-state ledger conservation witness. -/
def FourQuoteShareCoalition {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (coalition : Finset Adr) : FourQuoteOperation vault sevm pre post → Prop
  | .deposit words _ _ _ _ _ _ =>
      ledgerSumOn coalition (Stor.rest (Devm.getStor post sevm.currentTarget)) =
        ledgerSumOn coalition (Stor.rest (Devm.getStor pre sevm.currentTarget)) +
          if words.receiver.toAdr ∈ coalition then words.shares.toNat else 0
  | .mint words _ _ _ _ _ _ =>
      ledgerSumOn coalition (Stor.rest (Devm.getStor post sevm.currentTarget)) =
        ledgerSumOn coalition (Stor.rest (Devm.getStor pre sevm.currentTarget)) +
          if words.receiver.toAdr ∈ coalition then words.shares.toNat else 0
  | .withdrawNormal words _ _ _ _ _ =>
      ledgerSumOn coalition (Stor.rest (Devm.getStor post sevm.currentTarget)) +
          (if words.owner.toAdr ∈ coalition then words.shares.toNat else 0) =
        ledgerSumOn coalition (Stor.rest (Devm.getStor pre sevm.currentTarget))
  | .redeemNormal words _ _ _ _ _ =>
      ledgerSumOn coalition (Stor.rest (Devm.getStor post sevm.currentTarget)) +
          (if words.owner.toAdr ∈ coalition then words.shares.toNat else 0) =
        ledgerSumOn coalition (Stor.rest (Devm.getStor pre sevm.currentTarget))
  | .withdrawSelf words _ _ _ _ _ =>
      ledgerSumOn coalition (Stor.rest (Devm.getStor post sevm.currentTarget)) +
          (if words.owner.toAdr ∈ coalition then words.shares.toNat else 0) =
        ledgerSumOn coalition (Stor.rest (Devm.getStor pre sevm.currentTarget))
  | .redeemSelf words _ _ _ _ _ =>
      ledgerSumOn coalition (Stor.rest (Devm.getStor post sevm.currentTarget)) +
          (if words.owner.toAdr ∈ coalition then words.shares.toNat else 0) =
        ledgerSumOn coalition (Stor.rest (Devm.getStor pre sevm.currentTarget))
  | .credit _ _ _ _ _ _ =>
      ledgerSumOn coalition (Stor.rest (Devm.getStor post vault)) =
        ledgerSumOn coalition (Stor.rest (Devm.getStor pre vault))
  | .transfer words _ _ _ _ _ _ _ _ =>
      ledgerSumOn coalition (Stor.rest (Devm.getStor post sevm.currentTarget)) +
          (if words.owner ∈ coalition then words.amount.toNat else 0) =
        ledgerSumOn coalition (Stor.rest (Devm.getStor pre sevm.currentTarget)) +
          (if words.receiver.toAdr ∈ coalition then words.amount.toNat else 0)
  | .transferFrom words _ _ _ _ _ _ _ _ _ =>
      ledgerSumOn coalition (Stor.rest (Devm.getStor post sevm.currentTarget)) +
          (if words.owner.toAdr ∈ coalition then words.amount.toNat else 0) =
        ledgerSumOn coalition (Stor.rest (Devm.getStor pre sevm.currentTarget)) +
          (if words.receiver.toAdr ∈ coalition then words.amount.toNat else 0)
  | .approve _ _ _ _ _ _ _ _ _ =>
      ledgerSumOn coalition (Stor.rest (Devm.getStor post sevm.currentTarget)) =
        ledgerSumOn coalition (Stor.rest (Devm.getStor pre sevm.currentTarget))

private theorem inbound_share_nof_of_conserved
    {sevm : Sevm} {pre : Devm} {receiver : Adr} {shares supply : B256}
    (supplyEq : supply = Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot)
    (stable : supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN)
    (room : shares.toNat ≤ Blanc.ProrataWethVault.shareRoomN supply.toNat)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre sevm.currentTarget)) :
    B256.Nof (Stor.rest (Devm.getStor pre sevm.currentTarget) receiver) shares := by
  have supplyNof : B256.Nof supply shares := supplyNof_of_capacity stable room
  rw [supplyEq] at supplyNof
  unfold B256.Nof at supplyNof ⊢
  exact lt_of_le_of_lt
    (Nat.add_le_add_right (conserved.le_supply receiver) _) supplyNof

private theorem share_covered_of_nat
    {sevm : Sevm} {pre : Devm} {owner shares : B256}
    (ownerValid : ValidAdr owner)
    (covered : shares.toNat ≤
      (Devm.getStorVal pre sevm.currentTarget owner).toNat) :
    shares ≤ Stor.rest (Devm.getStor pre sevm.currentTarget) owner.toAdr := by
  apply B256.le_of_toNat_le_toNat
  change shares.toNat ≤
    ((Devm.getStor pre sevm.currentTarget).get owner.toAdr.toB256).toNat
  rw [toB256_toAdr ownerValid]
  exact covered

private theorem transfer_share_rows_of_compiled
    {sevm : Sevm} {pre post : Devm} (words : ShareTransferWords)
    (owner : words.owner = sevm.caller)
    (receiver : words.receiver = Sevm.argWord sevm 0)
    (amount : words.amount = Sevm.argWord sevm 1)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm = selector "transfer" [.address, .uint256]) :
    Transfer (Stor.rest (Devm.getStor pre sevm.currentTarget)) words.owner
      words.amount words.receiver.toAdr
      (Stor.rest (Devm.getStor post sevm.currentTarget)) := by
  obtain ⟨-, -, receiverValid, -, -, -, ownerBalance, receiverBalance,
      ownerBalanceEq, covered, receiverBalanceEq, -, settleStorage, -, -⟩ :=
    Blanc.ProrataWethVault.transfer_compiled_effect memoryWf run selectorEq
  have receiverValid' := receiverValid
  obtain ⟨receiverAdr, receiverAdrEq⟩ := receiverValid'
  have coveredRest :
      Sevm.argWord sevm 1 ≤ Stor.rest (Devm.getStor pre sevm.currentTarget)
        sevm.caller := by
    have ownerRest : Stor.rest (Devm.getStor pre sevm.currentTarget)
        sevm.caller = ownerBalance := ownerBalanceEq.symm
    rw [ownerRest]
    exact B256.le_of_toNat_le_toNat covered
  have raw : Transfer (Stor.rest (Devm.getStor pre sevm.currentTarget))
      sevm.caller (Sevm.argWord sevm 1) receiverAdr
      (Stor.rest (Devm.getStor post sevm.currentTarget)) := by
    have shape := transfer_of_debit_credit
      (s := Devm.getStor pre sevm.currentTarget) (owner := sevm.caller)
      (receiver := receiverAdr) (amount := Sevm.argWord sevm 1) coveredRest
    rw [settleStorage]
    have ownerRest : Stor.rest (Devm.getStor pre sevm.currentTarget)
        sevm.caller = ownerBalance := ownerBalanceEq.symm
    have receiverRest :
        Stor.rest ((Devm.getStor pre sevm.currentTarget).set sevm.caller.toB256
          (ownerBalance - Sevm.argWord sevm 1)) receiverAdr = receiverBalance := by
      rw [← receiverAdrEq] at receiverBalanceEq
      exact receiverBalanceEq.symm
    rw [← receiverAdrEq]
    rw [ownerRest] at shape
    rw [receiverRest] at shape
    exact shape
  have wordsReceiverValid : ValidAdr words.receiver := by
    rw [receiver]
    exact receiverValid
  have receiverEq : receiverAdr = words.receiver.toAdr := by
    apply Adr.toB256_inj
    rw [receiverAdrEq, toB256_toAdr wordsReceiverValid, receiver]
  simpa [owner, amount, receiverEq] using raw

private theorem transferFrom_share_rows_of_compiled
    {sevm : Sevm} {pre post : Devm} (words : ShareTransferFromWords)
    (owner : words.owner = Sevm.argWord sevm 0)
    (receiver : words.receiver = Sevm.argWord sevm 1)
    (amount : words.amount = Sevm.argWord sevm 2)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "transferFrom" [.address, .address, .uint256]) :
    Transfer (Stor.rest (Devm.getStor pre sevm.currentTarget)) words.owner.toAdr
      words.amount words.receiver.toAdr
      (Stor.rest (Devm.getStor post sevm.currentTarget)) := by
  obtain ⟨-, -, ownerValid, -, receiverValid, -, -, keyNotAddress, -, -,
      allowance, afterAllowance, ownerBalance, receiverBalance, -, -, route,
      ownerBalanceEq, covered, receiverBalanceEq, -, settleStorage, -, -⟩ :=
    Blanc.ProrataWethVault.transferFrom_compiled_effect memoryWf run selectorEq
  have ownerValid' := ownerValid
  have receiverValid' := receiverValid
  obtain ⟨ownerAdr, ownerAdrEq⟩ := ownerValid'
  obtain ⟨receiverAdr, receiverAdrEq⟩ := receiverValid'
  have afterRest : Stor.rest afterAllowance =
      Stor.rest (Devm.getStor pre sevm.currentTarget) := by
    rcases route with ⟨-, unchanged⟩ | decremented
    · rw [unchanged]
    · rw [decremented, rest_set_of_not_validAdr keyNotAddress]
  have coveredRest : Sevm.argWord sevm 2 ≤ Stor.rest afterAllowance ownerAdr := by
    have ownerRest : Stor.rest afterAllowance ownerAdr = ownerBalance := by
      rw [← ownerAdrEq] at ownerBalanceEq
      exact ownerBalanceEq.symm
    rw [ownerRest]
    exact B256.le_of_toNat_le_toNat covered
  have raw : Transfer (Stor.rest afterAllowance) ownerAdr (Sevm.argWord sevm 2)
      receiverAdr (Stor.rest (Devm.getStor post sevm.currentTarget)) := by
    have shape := transfer_of_debit_credit (s := afterAllowance)
      (owner := ownerAdr) (receiver := receiverAdr) (amount := Sevm.argWord sevm 2)
      coveredRest
    rw [settleStorage]
    have ownerRest : Stor.rest afterAllowance ownerAdr = ownerBalance := by
      rw [← ownerAdrEq] at ownerBalanceEq
      exact ownerBalanceEq.symm
    have receiverRest :
        Stor.rest (afterAllowance.set ownerAdr.toB256
          (ownerBalance - Sevm.argWord sevm 2)) receiverAdr = receiverBalance := by
      rw [← ownerAdrEq, ← receiverAdrEq] at receiverBalanceEq
      exact receiverBalanceEq.symm
    rw [← ownerAdrEq, ← receiverAdrEq]
    rw [ownerRest] at shape
    rw [receiverRest] at shape
    exact shape
  rw [afterRest] at raw
  have wordsOwnerValid : ValidAdr words.owner := by
    rw [owner]
    exact ownerValid
  have wordsReceiverValid : ValidAdr words.receiver := by
    rw [receiver]
    exact receiverValid
  have ownerEq : ownerAdr = words.owner.toAdr := by
    apply Adr.toB256_inj
    rw [ownerAdrEq, toB256_toAdr wordsOwnerValid, owner]
  have receiverEq : receiverAdr = words.receiver.toAdr := by
    apply Adr.toB256_inj
    rw [receiverAdrEq, toB256_toAdr wordsReceiverValid, receiver]
  simpa [amount, ownerEq, receiverEq] using raw

private theorem approve_share_rows_of_compiled
    {sevm : Sevm} {pre post : Devm}
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm = selector "approve" [.address, .uint256]) :
    Stor.rest (Devm.getStor post sevm.currentTarget) =
      Stor.rest (Devm.getStor pre sevm.currentTarget) := by
  obtain ⟨-, -, -, -, keyNotAddress, -, -, storageEq, -, -⟩ :=
    Blanc.ProrataWethVault.approve_compiled_effect memoryWf run selectorEq
  rw [storageEq, rest_set_of_not_validAdr keyNotAddress]

/-- The retained endpoint guards let every vault-target companion reuse the
existing ledger-preservation adapter for its actual operation; the credit case
keeps vault conservation through the actual foreign-storage frame. -/
theorem FourQuoteShareEvidence.preserves_conserved
    {vault : Adr} {sevm : Sevm} {pre post : Devm}
    {operation : FourQuoteOperation vault sevm pre post}
    (evidence : FourQuoteShareEvidence operation)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre vault)) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor post vault) := by
  cases evidence with
  | deposit words target depositorNotVault supplyNof wethRowNof quote effect receiverArg receiverValid supply supplyEq stable room =>
      rw [← target] at conserved ⊢
      exact inboundEffect_preserves_conserved receiverValid supplyEq stable room effect conserved
  | mint words target depositorNotVault supplyNof wethRowNof quote effect receiverArg receiverValid supply supplyEq stable room =>
      rw [← target] at conserved ⊢
      exact inboundEffect_preserves_conserved receiverValid supplyEq stable room effect conserved
  | withdrawNormal words target receiverNotVault burnable quote effect receiverArg ownerArg receiverValid ownerValid covered =>
      rw [← target] at conserved ⊢
      exact outboundEffect_preserves_conserved ownerValid covered effect conserved
  | redeemNormal words target receiverNotVault burnable quote effect receiverArg ownerArg receiverValid ownerValid covered =>
      rw [← target] at conserved ⊢
      exact outboundEffect_preserves_conserved ownerValid covered effect conserved
  | withdrawSelf words target receiverIsVault burnable quote effect receiverArg ownerArg receiverValid ownerValid covered =>
      rw [← target] at conserved ⊢
      exact outboundEffect_preserves_conserved ownerValid covered effect conserved
  | redeemSelf words target receiverIsVault burnable quote effect receiverArg ownerArg receiverValid ownerValid covered =>
      rw [← target] at conserved ⊢
      exact outboundEffect_preserves_conserved ownerValid covered effect conserved
  | credit words wethTarget sourceNotVault supplyKept rowNof effect vaultKept =>
      rw [vaultKept]
      exact conserved
  | transfer words target owner receiver amount config memoryWf run selectorEq =>
      rw [← target] at conserved ⊢
      exact Blanc.ProrataWethVault.transfer_preserves_conserved memoryWf run selectorEq conserved
  | transferFrom words target spender owner receiver amount config memoryWf run selectorEq =>
      rw [← target] at conserved ⊢
      exact Blanc.ProrataWethVault.transferFrom_preserves_conserved memoryWf run selectorEq conserved
  | approve words target owner spender amount config memoryWf run selectorEq =>
      rw [← target] at conserved ⊢
      exact Blanc.ProrataWethVault.approve_preserves_conserved memoryWf run selectorEq conserved

/-- Each companion projects the exact address-shaped share-row movement
produced by its retained operation evidence; a credit projects exact
unchanged vault rows. -/
theorem FourQuoteShareEvidence.actual_share_rows_move
    {vault : Adr} {sevm : Sevm} {pre post : Devm}
    {operation : FourQuoteOperation vault sevm pre post}
    (evidence : FourQuoteShareEvidence operation) :
    FourQuoteShareRowsMove operation := by
  cases evidence with
  | deposit words target depositorNotVault supplyNof wethRowNof quote effect receiverArg receiverValid supply supplyEq stable room =>
      dsimp [FourQuoteShareRowsMove]
      exact inboundEffect_share_increase (toB256_toAdr receiverValid) effect
  | mint words target depositorNotVault supplyNof wethRowNof quote effect receiverArg receiverValid supply supplyEq stable room =>
      dsimp [FourQuoteShareRowsMove]
      exact inboundEffect_share_increase (toB256_toAdr receiverValid) effect
  | withdrawNormal words target receiverNotVault burnable quote effect receiverArg ownerArg receiverValid ownerValid covered =>
      dsimp [FourQuoteShareRowsMove]
      exact outboundEffect_share_decrease (toB256_toAdr ownerValid) effect
  | redeemNormal words target receiverNotVault burnable quote effect receiverArg ownerArg receiverValid ownerValid covered =>
      dsimp [FourQuoteShareRowsMove]
      exact outboundEffect_share_decrease (toB256_toAdr ownerValid) effect
  | withdrawSelf words target receiverIsVault burnable quote effect receiverArg ownerArg receiverValid ownerValid covered =>
      dsimp [FourQuoteShareRowsMove]
      exact outboundEffect_share_decrease (toB256_toAdr ownerValid) effect
  | redeemSelf words target receiverIsVault burnable quote effect receiverArg ownerArg receiverValid ownerValid covered =>
      dsimp [FourQuoteShareRowsMove]
      exact outboundEffect_share_decrease (toB256_toAdr ownerValid) effect
  | credit words wethTarget sourceNotVault supplyKept rowNof effect vaultKept =>
      dsimp [FourQuoteShareRowsMove]
      rw [vaultKept]
  | transfer words target owner receiver amount config memoryWf run selectorEq =>
      dsimp [FourQuoteShareRowsMove]
      exact transfer_share_rows_of_compiled words owner receiver amount memoryWf run selectorEq
  | transferFrom words target spender owner receiver amount config memoryWf run selectorEq =>
      dsimp [FourQuoteShareRowsMove]
      exact transferFrom_share_rows_of_compiled words owner receiver amount memoryWf run selectorEq
  | approve words target owner spender amount config memoryWf run selectorEq =>
      dsimp [FourQuoteShareRowsMove]
      exact approve_share_rows_of_compiled memoryWf run selectorEq

/-- A conserved pre-state turns each actual row movement into its exact
finite-coalition equation.  The inbound share-row no-wrap fact comes from the
supply capacity guard and the conserved pre-state, not from an endpoint
postcondition; a credit contributes an exact unchanged coalition sum. -/
theorem FourQuoteShareEvidence.coalition
    {vault : Adr} {sevm : Sevm} {pre post : Devm}
    {operation : FourQuoteOperation vault sevm pre post} {coalition : Finset Adr}
    (evidence : FourQuoteShareEvidence operation)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre sevm.currentTarget)) :
    FourQuoteShareCoalition coalition operation := by
  cases evidence with
  | deposit words target depositorNotVault supplyNof wethRowNof quote effect receiverArg receiverValid supply supplyEq stable room =>
      dsimp [FourQuoteShareCoalition]
      exact ledgerSumOn_increase
        (inboundEffect_share_increase (toB256_toAdr receiverValid) effect)
        (inbound_share_nof_of_conserved supplyEq stable room conserved)
  | mint words target depositorNotVault supplyNof wethRowNof quote effect receiverArg receiverValid supply supplyEq stable room =>
      dsimp [FourQuoteShareCoalition]
      exact ledgerSumOn_increase
        (inboundEffect_share_increase (toB256_toAdr receiverValid) effect)
        (inbound_share_nof_of_conserved supplyEq stable room conserved)
  | withdrawNormal words target receiverNotVault burnable quote effect receiverArg ownerArg receiverValid ownerValid covered =>
      dsimp [FourQuoteShareCoalition]
      exact ledgerSumOn_decrease
        (outboundEffect_share_decrease (toB256_toAdr ownerValid) effect)
        (share_covered_of_nat ownerValid covered)
  | redeemNormal words target receiverNotVault burnable quote effect receiverArg ownerArg receiverValid ownerValid covered =>
      dsimp [FourQuoteShareCoalition]
      exact ledgerSumOn_decrease
        (outboundEffect_share_decrease (toB256_toAdr ownerValid) effect)
        (share_covered_of_nat ownerValid covered)
  | withdrawSelf words target receiverIsVault burnable quote effect receiverArg ownerArg receiverValid ownerValid covered =>
      dsimp [FourQuoteShareCoalition]
      exact ledgerSumOn_decrease
        (outboundEffect_share_decrease (toB256_toAdr ownerValid) effect)
        (share_covered_of_nat ownerValid covered)
  | redeemSelf words target receiverIsVault burnable quote effect receiverArg ownerArg receiverValid ownerValid covered =>
      dsimp [FourQuoteShareCoalition]
      exact ledgerSumOn_decrease
        (outboundEffect_share_decrease (toB256_toAdr ownerValid) effect)
        (share_covered_of_nat ownerValid covered)
  | credit words wethTarget sourceNotVault supplyKept rowNof effect vaultKept =>
      dsimp [FourQuoteShareCoalition]
      rw [vaultKept]
  | transfer words target owner receiver amount config memoryWf run selectorEq =>
      dsimp [FourQuoteShareCoalition]
      exact ledgerSumOn_transfer conserved.sumNof
        (transfer_share_rows_of_compiled words owner receiver amount memoryWf run selectorEq)
  | transferFrom words target spender owner receiver amount config memoryWf run selectorEq =>
      dsimp [FourQuoteShareCoalition]
      exact ledgerSumOn_transfer conserved.sumNof
        (transferFrom_share_rows_of_compiled words owner receiver amount memoryWf run selectorEq)
  | approve words target owner spender amount config memoryWf run selectorEq =>
      dsimp [FourQuoteShareCoalition]
      rw [approve_share_rows_of_compiled memoryWf run selectorEq]

/-- A real `deposit` run supplies the indexed operation and its non-credit
share companion.  The WETH-row addition guard remains an explicit boundary
premise; it is distinct from the share-row guard derived later from
conservation. -/
theorem deposit_compiled_share_evidence
    {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (target : sevm.currentTarget = vault)
    (depositorNotVault : sevm.caller ≠ sevm.currentTarget)
    (wethRowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount)
      sevm.currentTarget) (Sevm.argWord sevm 0))
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm = selector "deposit" [.uint256, .address]) :
    ∃ (shares : B256)
      (supplyNof : B256.Nof (Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot) shares)
      (quote : shares.toNat = Blanc.ProrataWethVault.convertToSharesN
        (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
          (snapshotAt sevm pre).supply)
      (effect : InboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 0)
        shares shares pre post),
      FourQuoteShareEvidence (.deposit ⟨Sevm.argWord sevm 1, Sevm.argWord sevm 0,
        shares, shares⟩ target depositorNotVault supplyNof wethRowNof quote effect) := by
  obtain ⟨-, supply, supplyEq, stable, quoteFits, -, receiverValid, -, room,
      rawEffect⟩ :=
    deposit_compiled_effect (hfork := hfork) config memoryWf run selectorEq
  let shares := Nat.toB256 (Blanc.ProrataWethVault.convertToSharesN
    (Sevm.argWord sevm 0).toNat
    ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256).toNat supply.toNat)
  let words : InboundWords := ⟨Sevm.argWord sevm 1, Sevm.argWord sevm 0,
    shares, shares⟩
  have room' : shares.toNat ≤ Blanc.ProrataWethVault.shareRoomN supply.toNat := by
    simpa only [shares] using room
  have supplyNof' : B256.Nof supply shares :=
    supplyNof_of_capacity (supply := supply) (shares := shares) stable room'
  have supplyNof : B256.Nof (Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot) words.shares := by
    change B256.Nof (Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot) shares
    rw [← supplyEq]
    exact supplyNof'
  have quoteRaw : shares.toNat = Blanc.ProrataWethVault.convertToSharesN
      (Sevm.argWord sevm 0).toNat
        ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256).toNat supply.toNat :=
    B256.toNat_toB256_of_lt quoteFits
  have balanceEq :
      ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256).toNat =
        (Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget).toNat := rfl
  have quote : words.shares.toNat = Blanc.ProrataWethVault.convertToSharesN
      words.assets.toNat (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply := by
    change shares.toNat = Blanc.ProrataWethVault.convertToSharesN
      (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
        (snapshotAt sevm pre).supply
    simpa [snapshotAt, vaultSnapshot, supplyEq, balanceEq] using
      quoteRaw
  have effect : InboundEffect sevm words.receiver words.assets words.shares
      words.returned pre post := by
    change InboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 0)
      shares shares pre post
    exact rawEffect
  refine ⟨shares, supplyNof, quote, effect, ?_⟩
  exact .deposit words target depositorNotVault supplyNof wethRowNof quote effect
    rfl receiverValid supply supplyEq stable room

/-- A real `mint` run supplies the indexed operation and its non-credit share
companion.  Its charged WETH amount is named only after the compiled endpoint
has fixed the ceil quote. -/
theorem mint_compiled_share_evidence
    {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (target : sevm.currentTarget = vault)
    (depositorNotVault : sevm.caller ≠ sevm.currentTarget)
    (wethRowNof : ∀ charged : B256,
      charged.toNat = Blanc.ProrataWethVault.previewMintN (Sevm.argWord sevm 0).toNat
        (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply →
      B256.Nof (Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget) charged)
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm = selector "mint" [.uint256, .address]) :
    ∃ (assets : B256)
      (supplyNof : B256.Nof (Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot) (Sevm.argWord sevm 0))
      (rowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount)
        sevm.currentTarget) assets)
      (quote : assets.toNat = Blanc.ProrataWethVault.previewMintN
        (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
          (snapshotAt sevm pre).supply)
      (effect : InboundEffect sevm (Sevm.argWord sevm 1) assets
        (Sevm.argWord sevm 0) assets pre post),
      FourQuoteShareEvidence (.mint ⟨Sevm.argWord sevm 1, assets,
        Sevm.argWord sevm 0, assets⟩ target depositorNotVault supplyNof rowNof quote effect) := by
  obtain ⟨-, supply, supplyEq, stable, quoteFits, -, receiverValid, -, room,
      rawEffect⟩ :=
    mint_compiled_effect (hfork := hfork) config memoryWf run selectorEq
  let assets := Nat.toB256 (Blanc.ProrataWethVault.previewMintN
    (Sevm.argWord sevm 0).toNat
    ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256).toNat supply.toNat)
  let words : InboundWords := ⟨Sevm.argWord sevm 1, assets, Sevm.argWord sevm 0,
    assets⟩
  have room' : (Sevm.argWord sevm 0).toNat ≤
      Blanc.ProrataWethVault.shareRoomN supply.toNat := room
  have supplyNof' : B256.Nof supply (Sevm.argWord sevm 0) :=
    supplyNof_of_capacity (supply := supply) (shares := Sevm.argWord sevm 0)
      stable room'
  have supplyNof : B256.Nof (Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot) words.shares := by
    change B256.Nof (Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot) (Sevm.argWord sevm 0)
    rw [← supplyEq]
    exact supplyNof'
  have quoteRaw : assets.toNat = Blanc.ProrataWethVault.previewMintN
      (Sevm.argWord sevm 0).toNat
        ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256).toNat supply.toNat :=
    B256.toNat_toB256_of_lt quoteFits
  have balanceEq :
      ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256).toNat =
        (Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget).toNat := rfl
  have quote : words.assets.toNat = Blanc.ProrataWethVault.previewMintN
      words.shares.toNat (snapshotAt sevm pre).balance (snapshotAt sevm pre).supply := by
    change assets.toNat = Blanc.ProrataWethVault.previewMintN
      (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
        (snapshotAt sevm pre).supply
    simpa [snapshotAt, vaultSnapshot, supplyEq, balanceEq] using
      quoteRaw
  have effect : InboundEffect sevm words.receiver words.assets words.shares
      words.returned pre post := by
    change InboundEffect sevm (Sevm.argWord sevm 1) assets
      (Sevm.argWord sevm 0) assets pre post
    exact rawEffect
  have rowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount)
      sevm.currentTarget) words.assets :=
    wethRowNof words.assets quote
  refine ⟨assets, supplyNof, rowNof, quote, effect, ?_⟩
  exact .mint words target depositorNotVault supplyNof rowNof quote effect
    rfl receiverValid supply supplyEq stable room

private theorem withdraw_compiled_share_raw
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "withdraw" [.uint256, .address, .address]) :
    ∃ (shares : B256)
      (_ : shares.toNat ≤ (snapshotAt sevm pre).supply)
      (_ : shares.toNat = Blanc.ProrataWethVault.previewWithdrawN
        (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
          (snapshotAt sevm pre).supply)
      (_ : OutboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
        (Sevm.argWord sevm 0) shares shares pre post),
      ValidAdr (Sevm.argWord sevm 1) ∧ ValidAdr (Sevm.argWord sevm 2) ∧
        shares.toNat ≤ (Devm.getStorVal pre sevm.currentTarget
          (Sevm.argWord sevm 2)).toNat := by
  obtain ⟨-, supply, supplyEq, -, quoteFits, -, receiverValid, -, ownerValid,
      -, covered, rawBurnable, rawEffect⟩ :=
    withdraw_compiled_effect (hfork := hfork) config memoryWf run selectorEq
  let shares := Nat.toB256 (Blanc.ProrataWethVault.previewWithdrawN
    (Sevm.argWord sevm 0).toNat
    ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256).toNat supply.toNat)
  have quoteRaw : shares.toNat = Blanc.ProrataWethVault.previewWithdrawN
      (Sevm.argWord sevm 0).toNat
        ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256).toNat supply.toNat :=
    B256.toNat_toB256_of_lt quoteFits
  have balanceEq :
      ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256).toNat =
        (Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget).toNat := rfl
  have quote : shares.toNat = Blanc.ProrataWethVault.previewWithdrawN
      (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
        (snapshotAt sevm pre).supply := by
    simpa [snapshotAt, vaultSnapshot, supplyEq, balanceEq] using quoteRaw
  have burnable : shares.toNat ≤ (snapshotAt sevm pre).supply := by
    change shares.toNat ≤ (Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot).toNat
    rw [← supplyEq]
    exact rawBurnable
  have effect : OutboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
      (Sevm.argWord sevm 0) shares shares pre post := by
    exact rawEffect
  exact ⟨shares, burnable, quote, effect, receiverValid, ownerValid, covered⟩

private theorem redeem_compiled_share_raw
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "redeem" [.uint256, .address, .address]) :
    ∃ (assets : B256)
      (_ : (Sevm.argWord sevm 0).toNat ≤ (snapshotAt sevm pre).supply)
      (_ : assets.toNat = Blanc.ProrataWethVault.convertToAssetsN
        (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
          (snapshotAt sevm pre).supply)
      (_ : OutboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
        assets (Sevm.argWord sevm 0) assets pre post),
      ValidAdr (Sevm.argWord sevm 1) ∧ ValidAdr (Sevm.argWord sevm 2) ∧
        (Sevm.argWord sevm 0).toNat ≤ (Devm.getStorVal pre sevm.currentTarget
          (Sevm.argWord sevm 2)).toNat := by
  obtain ⟨-, supply, supplyEq, -, quoteFits, -, receiverValid, -, ownerValid,
      -, covered, rawBurnable, rawEffect⟩ :=
    redeem_compiled_effect (hfork := hfork) config memoryWf run selectorEq
  let assets := Nat.toB256 (Blanc.ProrataWethVault.convertToAssetsN
    (Sevm.argWord sevm 0).toNat
    ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256).toNat supply.toNat)
  have quoteRaw : assets.toNat = Blanc.ProrataWethVault.convertToAssetsN
      (Sevm.argWord sevm 0).toNat
        ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256).toNat supply.toNat :=
    B256.toNat_toB256_of_lt quoteFits
  have balanceEq :
      ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256).toNat =
        (Stor.rest (Devm.getStor pre wethAccount) sevm.currentTarget).toNat := rfl
  have quote : assets.toNat = Blanc.ProrataWethVault.convertToAssetsN
      (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
        (snapshotAt sevm pre).supply := by
    simpa [snapshotAt, vaultSnapshot, supplyEq, balanceEq] using quoteRaw
  have burnable : (Sevm.argWord sevm 0).toNat ≤ (snapshotAt sevm pre).supply := by
    change (Sevm.argWord sevm 0).toNat ≤ (Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot).toNat
    rw [← supplyEq]
    exact rawBurnable
  have effect : OutboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
      assets (Sevm.argWord sevm 0) assets pre post := by
    exact rawEffect
  exact ⟨assets, burnable, quote, effect, receiverValid, ownerValid, covered⟩

/-- A real `withdraw` with a non-vault receiver yields the normal outbound
tag and its actual share companion. -/
theorem withdrawNormal_compiled_share_evidence
    {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (target : sevm.currentTarget = vault)
    (receiverNotVault : sevm.currentTarget ≠ (Sevm.argWord sevm 1).toAdr)
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "withdraw" [.uint256, .address, .address]) :
    ∃ (shares : B256)
      (burnable : shares.toNat ≤ (snapshotAt sevm pre).supply)
      (quote : shares.toNat = Blanc.ProrataWethVault.previewWithdrawN
        (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
          (snapshotAt sevm pre).supply)
      (effect : OutboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
        (Sevm.argWord sevm 0) shares shares pre post),
      FourQuoteShareEvidence (.withdrawNormal
        ⟨Sevm.argWord sevm 1, Sevm.argWord sevm 2, Sevm.argWord sevm 0, shares, shares⟩
        target receiverNotVault burnable quote effect) := by
  obtain ⟨shares, burnable, quote, effect, receiverValid, ownerValid, covered⟩ :=
    withdraw_compiled_share_raw (hfork := hfork) config memoryWf run selectorEq
  refine ⟨shares, burnable, quote, effect, ?_⟩
  exact .withdrawNormal
    (words := ⟨Sevm.argWord sevm 1, Sevm.argWord sevm 2, Sevm.argWord sevm 0,
      shares, shares⟩)
    target receiverNotVault burnable quote effect
    rfl rfl receiverValid ownerValid covered

/-- A real `withdraw` that names the vault as receiver yields the retained
outbound tag and its actual share companion. -/
theorem withdrawSelf_compiled_share_evidence
    {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (target : sevm.currentTarget = vault)
    (receiverIsVault : (Sevm.argWord sevm 1).toAdr = sevm.currentTarget)
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "withdraw" [.uint256, .address, .address]) :
    ∃ (shares : B256)
      (burnable : shares.toNat ≤ (snapshotAt sevm pre).supply)
      (quote : shares.toNat = Blanc.ProrataWethVault.previewWithdrawN
        (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
          (snapshotAt sevm pre).supply)
      (effect : OutboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
        (Sevm.argWord sevm 0) shares shares pre post),
      FourQuoteShareEvidence (.withdrawSelf
        ⟨Sevm.argWord sevm 1, Sevm.argWord sevm 2, Sevm.argWord sevm 0, shares, shares⟩
        target receiverIsVault burnable quote effect) := by
  obtain ⟨shares, burnable, quote, effect, receiverValid, ownerValid, covered⟩ :=
    withdraw_compiled_share_raw (hfork := hfork) config memoryWf run selectorEq
  refine ⟨shares, burnable, quote, effect, ?_⟩
  exact .withdrawSelf
    (words := ⟨Sevm.argWord sevm 1, Sevm.argWord sevm 2, Sevm.argWord sevm 0,
      shares, shares⟩)
    target receiverIsVault burnable quote effect
    rfl rfl receiverValid ownerValid covered

/-- A real `redeem` with a non-vault receiver yields the normal outbound tag
and its actual share companion. -/
theorem redeemNormal_compiled_share_evidence
    {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (target : sevm.currentTarget = vault)
    (receiverNotVault : sevm.currentTarget ≠ (Sevm.argWord sevm 1).toAdr)
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "redeem" [.uint256, .address, .address]) :
    ∃ (assets : B256)
      (burnable : (Sevm.argWord sevm 0).toNat ≤ (snapshotAt sevm pre).supply)
      (quote : assets.toNat = Blanc.ProrataWethVault.convertToAssetsN
        (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
          (snapshotAt sevm pre).supply)
      (effect : OutboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
        assets (Sevm.argWord sevm 0) assets pre post),
      FourQuoteShareEvidence (.redeemNormal
        ⟨Sevm.argWord sevm 1, Sevm.argWord sevm 2, assets, Sevm.argWord sevm 0, assets⟩
        target receiverNotVault burnable quote effect) := by
  obtain ⟨assets, burnable, quote, effect, receiverValid, ownerValid, covered⟩ :=
    redeem_compiled_share_raw (hfork := hfork) config memoryWf run selectorEq
  refine ⟨assets, burnable, quote, effect, ?_⟩
  exact .redeemNormal
    (words := ⟨Sevm.argWord sevm 1, Sevm.argWord sevm 2, assets,
      Sevm.argWord sevm 0, assets⟩)
    target receiverNotVault burnable quote effect
    rfl rfl receiverValid ownerValid covered

/-- A real `redeem` that names the vault as receiver yields the retained
outbound tag and its actual share companion. -/
theorem redeemSelf_compiled_share_evidence
    {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (target : sevm.currentTarget = vault)
    (receiverIsVault : (Sevm.argWord sevm 1).toAdr = sevm.currentTarget)
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "redeem" [.uint256, .address, .address]) :
    ∃ (assets : B256)
      (burnable : (Sevm.argWord sevm 0).toNat ≤ (snapshotAt sevm pre).supply)
      (quote : assets.toNat = Blanc.ProrataWethVault.convertToAssetsN
        (Sevm.argWord sevm 0).toNat (snapshotAt sevm pre).balance
          (snapshotAt sevm pre).supply)
      (effect : OutboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
        assets (Sevm.argWord sevm 0) assets pre post),
      FourQuoteShareEvidence (.redeemSelf
        ⟨Sevm.argWord sevm 1, Sevm.argWord sevm 2, assets, Sevm.argWord sevm 0, assets⟩
        target receiverIsVault burnable quote effect) := by
  obtain ⟨assets, burnable, quote, effect, receiverValid, ownerValid, covered⟩ :=
    redeem_compiled_share_raw (hfork := hfork) config memoryWf run selectorEq
  refine ⟨assets, burnable, quote, effect, ?_⟩
  exact .redeemSelf
    (words := ⟨Sevm.argWord sevm 1, Sevm.argWord sevm 2, assets,
      Sevm.argWord sevm 0, assets⟩)
    target receiverIsVault burnable quote effect
    rfl rfl receiverValid ownerValid covered

/-- The compiled direct-share transfer carries all canonical role words in the
accepted transfer tag; its exact `Transfer` row projection is derived from the
same retained run by `actual_share_rows_move`. -/
theorem transfer_compiled_share_evidence
    {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (target : sevm.currentTarget = vault)
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm = selector "transfer" [.address, .uint256]) :
    FourQuoteShareEvidence (.transfer
      ⟨sevm.caller, Sevm.argWord sevm 0, Sevm.argWord sevm 1⟩
      target rfl rfl rfl config memoryWf run selectorEq) := by
  exact .transfer
    (words := ⟨sevm.caller, Sevm.argWord sevm 0, Sevm.argWord sevm 1⟩)
    target rfl rfl rfl config memoryWf run selectorEq

/-- The compiled delegated transfer preserves the distinct caller/spender and
owner roles even when their concrete addresses coincide. -/
theorem transferFrom_compiled_share_evidence
    {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (target : sevm.currentTarget = vault)
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "transferFrom" [.address, .address, .uint256]) :
    FourQuoteShareEvidence (.transferFrom
      ⟨sevm.caller, Sevm.argWord sevm 0, Sevm.argWord sevm 1, Sevm.argWord sevm 2⟩
      target rfl rfl rfl rfl config memoryWf run selectorEq) := by
  exact .transferFrom
    (words := ⟨sevm.caller, Sevm.argWord sevm 0, Sevm.argWord sevm 1,
      Sevm.argWord sevm 2⟩)
    target rfl rfl rfl rfl config memoryWf run selectorEq

/-- The compiled approval changes only its proven non-address allowance row,
so the accepted approval tag has exact unchanged-share-row evidence. -/
theorem approve_compiled_share_evidence
    {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (target : sevm.currentTarget = vault)
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm = selector "approve" [.address, .uint256]) :
    FourQuoteShareEvidence (.approve
      ⟨sevm.caller, Sevm.argWord sevm 0, Sevm.argWord sevm 1⟩
      target rfl rfl rfl config memoryWf run selectorEq) := by
  exact .approve
    (words := ⟨sevm.caller, Sevm.argWord sevm 0, Sevm.argWord sevm 1⟩)
    target rfl rfl rfl config memoryWf run selectorEq

/-- An actual direct WETH transfer into the vault carries the accepted credit
tag: the WETH-row `Transfer` and the kept vault supply row are both read off
the actual run, while `sourceNotVault`, separation and the receiver-row
no-wrap fact stay explicit until G6 derives them. -/
theorem credit_compiled_share_evidence
    {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (words : CreditWords)
    (actual : ActualDirectWethCredit vault words sevm pre post)
    (sourceNotVault : words.source ≠ vault)
    (separation : wethAccount ≠ vault)
    (rowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount) vault)
      words.amount) :
    ∃ (supplyKept : Devm.getStorVal post vault
          Blanc.ProrataWethVault.supplySlot =
          Devm.getStorVal pre vault Blanc.ProrataWethVault.supplySlot)
      (effect : Transfer (Stor.rest (Devm.getStor pre wethAccount)) words.source
        words.amount vault (Stor.rest (Devm.getStor post wethAccount))),
      FourQuoteShareEvidence
        (.credit words actual.target sourceNotVault supplyKept rowNof
          effect) := by
  obtain ⟨movement, _, _, _⟩ :=
    SuccessfulWethWorldProgramRun.transfer_effect actual.worldProgramRun
  have vaultStor := actual_credit_vault_storage_eq actual separation
  have supplyKept : Devm.getStorVal post vault
      Blanc.ProrataWethVault.supplySlot =
      Devm.getStorVal pre vault Blanc.ProrataWethVault.supplySlot := by
    show (Devm.getStor post vault).get _ = (Devm.getStor pre vault).get _
    rw [vaultStor]
  exact ⟨supplyKept, movement,
    .credit words actual.target sourceNotVault supplyKept rowNof movement
      vaultStor⟩

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

/-- The actual credit yields one State-linked transition over the exact retained
pre/post states, carrying precisely the accepted credit operation: the retained
`FourQuoteShareEvidence` for the credit tag together with a transition whose
operation is that tag. -/
theorem credit_compiled_transition
    {vault : Adr} {sevm : Sevm} {pre post : Devm}
    (words : CreditWords)
    (actual : ActualDirectWethCredit vault words sevm pre post)
    (sourceNotVault : words.source ≠ vault)
    (separation : wethAccount ≠ vault)
    (rowNof : B256.Nof (Stor.rest (Devm.getStor pre wethAccount) vault)
      words.amount) :
    ∃ (supplyKept : Devm.getStorVal post vault
          Blanc.ProrataWethVault.supplySlot =
          Devm.getStorVal pre vault Blanc.ProrataWethVault.supplySlot)
      (effect : Transfer (Stor.rest (Devm.getStor pre wethAccount)) words.source
        words.amount vault (Stor.rest (Devm.getStor post wethAccount)))
      (t : FourQuoteTransition vault pre.state post.state),
      FourQuoteShareEvidence
        (.credit words actual.target sourceNotVault supplyKept rowNof
          effect) ∧
      HEq t.operation
        (FourQuoteOperation.credit words actual.target sourceNotVault
          supplyKept rowNof effect) := by
  obtain ⟨supplyKept, effect, evidence⟩ :=
    credit_compiled_share_evidence words actual sourceNotVault separation
      rowNof
  exact ⟨supplyKept, effect, ⟨sevm, pre, post, rfl, rfl,
    .credit words actual.target sourceNotVault supplyKept rowNof effect⟩,
    evidence, HEq.rfl⟩

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
