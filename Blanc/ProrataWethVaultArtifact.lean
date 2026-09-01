-- ProrataWethVaultArtifact.lean : executable G2 identity and surface pins.

import Blanc.ProrataWethVaultCode

namespace Blanc.ProrataWethVault

open Jaune

def vaultSelectors : List B256 := vaultFuncs.map Prod.fst

theorem vaultSelectors_exact :
    vaultSelectors =
      [ 0x01e1d114, 0x06fdde03, 0x07a2d13a, 0x095ea7b3, 0x0a28a477,
        0x18160ddd, 0x23b872dd, 0x313ce567, 0x38d52e0f, 0x402d267d,
        0x4cdad506, 0x6e553f65, 0x70a08231, 0x94bf804d, 0x95d89b41,
        0xa9059cbb, 0xb3d7f6b9, 0xb460af94, 0xba087652, 0xc63d75b6,
        0xc6e6f592, 0xce96cb77, 0xd905777e, 0xdd62ed3e, 0xef8b30f7 ] := by
  decide +kernel

theorem vaultSelectorCount_exact : vaultSelectors.length = 25 := by
  decide +kernel

theorem noPermitSelector :
    selector "permit" [.address, .address, .uint256, .uint256, .uint 8,
      .bytes 32, .bytes 32] ∉ vaultSelectors := by
  decide +kernel

theorem assetAddress_exact : assetAddress = 0x1000 := rfl
theorem virtualShares_exact : virtualShares = 1000 := rfl
theorem supplySlot_exact : supplySlot = B256.max := rfl
theorem maxSupply_exact : maxSupply = B256.max - 1000 := rfl

theorem approvalEvent_exact :
    approvalEvent =
      0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925 := by
  decide +kernel

theorem transferEvent_exact :
    transferEvent =
      0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef := by
  decide +kernel

theorem depositEvent_exact :
    depositEvent =
      0xdcbc1c05240f31ff3ad067ef1ee35ce4997762752e3a095284754544f4c709d7 := by
  decide +kernel

theorem withdrawEvent_exact :
    withdrawEvent =
      0xfbde797d201c681b91056529119e0b02407c7bb96a4a2c75c01fc9667232c8db := by
  decide +kernel

theorem routed_exact (words : Nat) (body : Func) :
    routed words body = nonpayable (requireStaticArgs words body) := rfl

theorem fallback_exact : revertSlot = 1 := rfl

theorem auxLayout_exact :
    vaultAux =
      [ Func.rev,
        returnWord,
        depositAfterQuote,
        mintAfterQuote,
        withdrawAfterQuote,
        redeemAfterQuote,
        transferStaged,
        withdrawBurn,
        redeemBurn,
        maxMintAfterAssetCap ] := rfl

theorem programMain_exact :
    vault.main = Func.mainWith revertSlot vaultTree := rfl

theorem runtimeCodeSize_exact : prorataWethVaultCode.length = 17481 := by
  decide +kernel

theorem runtimeCodeWithinEip170 : prorataWethVaultCode.length ≤ 24576 := by
  rw [runtimeCodeSize_exact]
  decide

theorem runtimeCode_compile :
    Prog.compile vault = some prorataWethVaultCode :=
  prorataWethVaultCode_compile

end Blanc.ProrataWethVault
