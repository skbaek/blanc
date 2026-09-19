-- ProrataWethVaultMaxArithmetic.lean : exact `maxWithdraw` capacity, the
-- stable-state forms of the capacity views, and the round-trip no-profit bound.

import Blanc.ProrataWethVaultArithmetic

namespace Blanc

open Jaune

namespace ProrataWethVault

/-- **`maxWithdraw` is exact.**  An amount is at most `maxWithdrawN` exactly
when the share burn it quotes fits the owner's balance, so the capacity is the
largest amount the vault's own balance guard accepts, not a loose bound. -/
theorem le_maxWithdrawN_iff (amount balance assets supply : Nat) :
    amount ≤ maxWithdrawN balance assets supply ↔
      previewWithdrawN amount assets supply ≤ balance := by
  unfold maxWithdrawN convertToAssetsN previewWithdrawN
  rw [Nat.le_div_iff_mul_le (denominatorN_pos supply),
    ceilDiv_le_iff (assetFactorN_ne_zero assets)]

/-! The burn side of `maxWithdraw`'s attainability: withdrawing the advertised
maximum burns at most the owner's balance. -/
theorem previewWithdrawN_maxWithdrawN_le (balance assets supply : Nat) :
    previewWithdrawN (maxWithdrawN balance assets supply) assets supply ≤
      balance := by
  exact (le_maxWithdrawN_iff _ balance assets supply).mp le_rfl

/-! At a stable supply and a nonzero receiver the public `maxDeposit` view is
the bare capacity formula. -/
theorem maxDepositViewN_eq_of_stable {receiver assets supply : Nat}
    (receiverNonzero : receiver ≠ 0) (stable : supply ≤ maxSupplyN) :
    maxDepositViewN receiver assets supply = maxDepositN assets supply := by
  unfold maxDepositViewN
  rw [if_neg receiverNonzero, if_neg (Nat.not_lt_of_ge stable)]

/-! At a stable supply and a nonzero receiver the public `maxMint` view is the
bare capacity formula. -/
theorem maxMintViewN_eq_of_stable {receiver assets supply : Nat}
    (receiverNonzero : receiver ≠ 0) (stable : supply ≤ maxSupplyN) :
    maxMintViewN receiver assets supply = maxMintN assets supply := by
  unfold maxMintViewN
  rw [if_neg receiverNonzero, if_neg (Nat.not_lt_of_ge stable)]

/-! At a stable supply, a booked balance within the supply and a word-sized
asset row, the public `maxWithdraw` view is unsaturated. -/
theorem maxWithdrawViewN_eq_of_stable {balance assets supply : Nat}
    (stable : supply ≤ maxSupplyN) (balanceLe : balance ≤ supply)
    (assetsWord : assets ≤ maxWordN) :
    maxWithdrawViewN balance assets supply =
      maxWithdrawN balance assets supply := by
  unfold maxWithdrawViewN
  rw [if_neg (Nat.not_lt_of_ge stable)]
  exact Nat.min_eq_right ((maxWithdrawN_le_assets balanceLe).trans assetsWord)

/-! **An immediate round trip never profits.**  Depositing `amount` against
`(assets, supply)` and redeeming the minted shares at the post-deposit snapshot
pays at most `amount`.  Unlike `roundtrip_loss_le`, whose left side is a
truncated subtraction, this is the no-profit direction itself. -/
theorem roundtrip_no_profit (amount assets supply : Nat) :
    convertToAssetsN (convertToSharesN amount assets supply)
        (assets + amount)
        (supply + convertToSharesN amount assets supply) ≤ amount := by
  unfold convertToAssetsN
  rw [← Nat.lt_succ_iff,
    Nat.div_lt_iff_lt_mul
      (denominatorN_pos (supply + convertToSharesN amount assets supply))]
  have hfloor := convertToSharesN_floor_le amount assets supply
  have factor_add : assetFactorN (assets + amount) =
      assetFactorN assets + amount := by
    unfold assetFactorN
    omega
  have denominator_add : denominatorN (supply +
      convertToSharesN amount assets supply) =
      denominatorN supply + convertToSharesN amount assets supply := by
    unfold denominatorN
    omega
  calc
    convertToSharesN amount assets supply * assetFactorN (assets + amount) =
        convertToSharesN amount assets supply *
          (assetFactorN assets + amount) := by rw [factor_add]
    _ = assetFactorN assets * convertToSharesN amount assets supply +
          convertToSharesN amount assets supply * amount := by
            rw [Nat.mul_add]
            congr 1
            exact Nat.mul_comm _ _
    _ ≤ amount * denominatorN supply +
          convertToSharesN amount assets supply * amount :=
      Nat.add_le_add_right hfloor _
    _ = amount * (denominatorN supply + convertToSharesN amount assets supply) := by
      rw [Nat.mul_add]
      congr 1
      exact Nat.mul_comm _ _
    _ < (amount + 1) * (denominatorN supply +
        convertToSharesN amount assets supply) := by
      exact Nat.mul_lt_mul_of_pos_right (by omega)
        (denominatorN_pos supply |>.trans_le (Nat.le_add_right _ _))
    _ = (amount + 1) * denominatorN (supply + convertToSharesN amount assets supply) := by
      rw [denominator_add]

end ProrataWethVault

end Blanc
