import Blanc.Composition.ProrataWethVaultAccountingControlProducer

/-!
# Fixed checker for disposable G7 arithmetic-control candidates

The producer is the only mutated module.  These assertions consume the
published accounting quote and residue theorems at one concrete boundary.
This fixture is intentionally unimported by production modules.
-/

namespace Blanc.Composition.ProrataWethVaultAccountingControl

open Blanc.Composition.ProrataWethVault

namespace Checker

theorem deposit_quote_literal_fixed : Producer.depositShares = 285 := by
  rfl

theorem deposit_quote_fixed :
    Producer.depositShares =
      Blanc.ProrataWethVault.convertToSharesN
        Producer.depositAssets Producer.pre.balance Producer.pre.supply := by
  rfl

theorem mint_quote_literal_fixed : Producer.mintAssets = 2 := by
  rfl

theorem mint_quote_fixed :
    Producer.mintAssets =
      Blanc.ProrataWethVault.previewMintN
        Producer.mintShares Producer.pre.balance Producer.pre.supply := by
  rfl

theorem withdraw_quote_literal_fixed : Producer.withdrawShares = 286 := by
  rfl

theorem withdraw_quote_fixed :
    Producer.withdrawShares =
      Blanc.ProrataWethVault.previewWithdrawN
        Producer.withdrawAssets Producer.pre.balance Producer.pre.supply := by
  rfl

theorem redeem_quote_literal_fixed : Producer.redeemAssets = 1 := by
  rfl

theorem redeem_quote_fixed :
    Producer.redeemAssets =
      Blanc.ProrataWethVault.convertToAssetsN
        Producer.redeemShares Producer.pre.balance Producer.pre.supply := by
  rfl

theorem inbound_residue_literal_fixed : Producer.inboundResidue = 5 := by
  rfl

theorem inbound_residue_fixed :
    Producer.inboundResidue =
      FourQuote.depositResidue Producer.depositAssets Producer.depositShares Producer.pre := by
  rfl

theorem outbound_residue_literal_fixed : Producer.outboundResidue = 2 := by
  rfl

theorem outbound_residue_fixed :
    Producer.outboundResidue =
      FourQuote.outboundResidue Producer.withdrawAssets Producer.withdrawShares Producer.pre := by
  rfl

theorem deposit_residue_from_production :
    Producer.depositAssets * FourQuote.D Producer.pre =
      Producer.depositShares * FourQuote.X Producer.pre + Producer.inboundResidue := by
  simpa only [deposit_quote_fixed, inbound_residue_fixed] using
    FourQuote.deposit_residue_eq Producer.depositAssets Producer.pre

theorem mint_residue_from_production :
    Producer.mintAssets * FourQuote.D Producer.pre =
      Producer.mintShares * FourQuote.X Producer.pre +
        FourQuote.depositResidue Producer.mintAssets Producer.mintShares Producer.pre := by
  simpa only [mint_quote_fixed] using
    FourQuote.mint_residue_eq Producer.mintShares Producer.pre

theorem withdraw_residue_from_production :
    Producer.withdrawShares * FourQuote.X Producer.pre =
      Producer.withdrawAssets * FourQuote.D Producer.pre + Producer.outboundResidue := by
  simpa only [withdraw_quote_fixed, outbound_residue_fixed] using
    FourQuote.withdraw_residue_eq Producer.withdrawAssets Producer.pre

theorem redeem_residue_from_production :
    Producer.redeemShares * FourQuote.X Producer.pre =
      Producer.redeemAssets * FourQuote.D Producer.pre +
        FourQuote.outboundResidue Producer.redeemAssets Producer.redeemShares Producer.pre := by
  simpa only [redeem_quote_fixed] using
    FourQuote.redeem_residue_eq Producer.redeemShares Producer.pre

theorem deposit_recurrence_fixed :
    FourQuote.X (FourQuote.normalInbound
      Producer.depositAssets Producer.depositShares Producer.pre) * FourQuote.D Producer.pre =
      FourQuote.X Producer.pre * FourQuote.D (FourQuote.normalInbound
        Producer.depositAssets Producer.depositShares Producer.pre) + Producer.inboundResidue := by
  simpa only [inbound_residue_fixed] using
    FourQuote.normalInbound_price
      Producer.depositAssets Producer.depositShares Producer.pre deposit_quote_fixed

theorem mint_recurrence_fixed :
    FourQuote.X (FourQuote.normalInbound
      Producer.mintAssets Producer.mintShares Producer.pre) * FourQuote.D Producer.pre =
      FourQuote.X Producer.pre * FourQuote.D (FourQuote.normalInbound
        Producer.mintAssets Producer.mintShares Producer.pre) +
        FourQuote.depositResidue Producer.mintAssets Producer.mintShares Producer.pre := by
  simpa only [mint_quote_fixed] using
    FourQuote.normalInbound_price_mint Producer.mintShares Producer.pre

theorem withdraw_recurrence_fixed :
    FourQuote.X (FourQuote.normalOutbound
      Producer.withdrawAssets Producer.withdrawShares Producer.pre) * FourQuote.D Producer.pre =
      FourQuote.X Producer.pre * FourQuote.D (FourQuote.normalOutbound
        Producer.withdrawAssets Producer.withdrawShares Producer.pre) + Producer.outboundResidue := by
  simpa only [withdraw_quote_fixed, outbound_residue_fixed] using
    FourQuote.normalOutbound_price_withdraw Producer.withdrawAssets Producer.pre
      (by norm_num [Producer.withdrawShares, Producer.withdrawAssets, Producer.pre,
        Blanc.ProrataWethVault.previewWithdrawN, Blanc.ProrataWethVault.assetFactorN,
        Blanc.ProrataWethVault.denominatorN, Blanc.ProrataWethVault.offsetN, Jaune.ceilDiv])
      (by norm_num [Producer.withdrawAssets, Producer.pre])

theorem redeem_recurrence_fixed :
    FourQuote.X (FourQuote.normalOutbound
      Producer.redeemAssets Producer.redeemShares Producer.pre) * FourQuote.D Producer.pre =
      FourQuote.X Producer.pre * FourQuote.D (FourQuote.normalOutbound
        Producer.redeemAssets Producer.redeemShares Producer.pre) +
        FourQuote.outboundResidue Producer.redeemAssets Producer.redeemShares Producer.pre := by
  simpa only [redeem_quote_fixed] using
    FourQuote.normalOutbound_price_redeem Producer.redeemShares Producer.pre
      (by norm_num [Producer.redeemShares, Producer.pre])
      (by norm_num [Producer.redeemShares, Producer.pre,
        Blanc.ProrataWethVault.convertToAssetsN, Blanc.ProrataWethVault.assetFactorN,
        Blanc.ProrataWethVault.denominatorN, Blanc.ProrataWethVault.offsetN])

theorem self_post_literal_fixed : Producer.selfPost = ⟨714, 6⟩ := by
  rfl

theorem self_post_fixed :
    Producer.selfPost = FourQuote.retainedOutbound Producer.withdrawShares Producer.pre := by
  rfl

theorem self_endpoint_fixed :
    FourQuote.X Producer.selfPost * FourQuote.D Producer.pre =
      FourQuote.X Producer.pre * FourQuote.D Producer.selfPost +
        Producer.outboundResidue + Producer.withdrawAssets * FourQuote.D Producer.pre := by
  simpa only [self_post_fixed, outbound_residue_fixed] using
    FourQuote.retainedOutbound_price
      Producer.withdrawAssets Producer.withdrawShares Producer.pre
      (by norm_num [Producer.withdrawShares, Producer.withdrawAssets, Producer.pre,
        Blanc.ProrataWethVault.previewWithdrawN, Blanc.ProrataWethVault.assetFactorN,
        Blanc.ProrataWethVault.denominatorN, Blanc.ProrataWethVault.offsetN, Jaune.ceilDiv])
      withdraw_residue_from_production

end Checker

end Blanc.Composition.ProrataWethVaultAccountingControl
