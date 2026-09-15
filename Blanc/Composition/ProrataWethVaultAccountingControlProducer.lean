import Blanc.Composition.ProrataWethVaultAccounting

/-!
# Disposable G7 accounting-control producer

This unimported control fixture supplies a small concrete snapshot to the
fixed checker module.  Campaign mutations alter this file only.
-/

namespace Blanc.Composition.ProrataWethVaultAccountingControl

namespace Producer

open Blanc.Composition.ProrataWethVault

def pre : FourQuote.Snapshot := ⟨1000, 6⟩

def depositAssets : Nat := 1
def depositShares : Nat :=
  Blanc.ProrataWethVault.convertToSharesN depositAssets pre.balance pre.supply

def mintShares : Nat := 300
def mintAssets : Nat :=
  Blanc.ProrataWethVault.previewMintN mintShares pre.balance pre.supply

def withdrawAssets : Nat := 1
def withdrawShares : Nat :=
  Blanc.ProrataWethVault.previewWithdrawN withdrawAssets pre.balance pre.supply

def redeemShares : Nat := 300
def redeemAssets : Nat :=
  Blanc.ProrataWethVault.convertToAssetsN redeemShares pre.balance pre.supply

def inboundResidue : Nat :=
  FourQuote.depositResidue depositAssets depositShares pre

def outboundResidue : Nat :=
  FourQuote.outboundResidue withdrawAssets withdrawShares pre

def selfPost : FourQuote.Snapshot :=
  FourQuote.retainedOutbound withdrawShares pre

end Producer

end Blanc.Composition.ProrataWethVaultAccountingControl
