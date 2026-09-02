-- ProrataWethVaultArithmetic.lean : full-width ERC-4626 ratio arithmetic.

import Blanc.ProrataWethVault
import Blanc.WordArithmetic
import Jaune.MulDiv

namespace Blanc

open Jaune

namespace ProrataWethVault

/-!
# Mathematical ratio model

These definitions state the G1-frozen vault formulas over `Nat`.  In
particular, `assetFactorN` is allowed to equal `2^256`; no theorem in this
module reduces a product to one EVM word.  The compiled arithmetic owner can
therefore refine the simple, wide, and exact-`2^256` source branches to one
common specification without adding a magnitude premise.
-/

def offsetN : Nat := 1000

def maxSupplyN : Nat := maxWordN - offsetN

def denominatorN (supply : Nat) : Nat := supply + offsetN

def assetFactorN (assets : Nat) : Nat := assets + 1

def convertToSharesN (amount assets supply : Nat) : Nat :=
  amount * denominatorN supply / assetFactorN assets

def convertToAssetsN (shares assets supply : Nat) : Nat :=
  shares * assetFactorN assets / denominatorN supply

def previewDepositN := convertToSharesN

def previewRedeemN := convertToAssetsN

def previewMintN (shares assets supply : Nat) : Nat :=
  ceilDiv (shares * assetFactorN assets) (denominatorN supply)

def previewWithdrawN (amount assets supply : Nat) : Nat :=
  ceilDiv (amount * denominatorN supply) (assetFactorN assets)

def shareRoomN (supply : Nat) : Nat := maxSupplyN - supply

def maxMintN (assets supply : Nat) : Nat :=
  min (shareRoomN supply)
    (maxWordN * denominatorN supply / assetFactorN assets)

def maxDepositN (assets supply : Nat) : Nat :=
  min maxWordN
    (ceilDiv ((shareRoomN supply + 1) * assetFactorN assets)
      (denominatorN supply) - 1)

def maxRedeemN (balance : Nat) : Nat := balance

def maxWithdrawN (balance assets supply : Nat) : Nat :=
  convertToAssetsN balance assets supply

theorem virtualShares_toNat : virtualShares.toNat = offsetN := by
  decide +kernel

theorem maxSupply_toNat : maxSupply.toNat = maxSupplyN := by
  decide +kernel

theorem offsetN_pos : 0 < offsetN := by
  decide

theorem denominatorN_pos (supply : Nat) : 0 < denominatorN supply := by
  unfold denominatorN offsetN
  omega

theorem denominatorN_ne_zero (supply : Nat) : denominatorN supply ≠ 0 :=
  Nat.ne_of_gt (denominatorN_pos supply)

theorem assetFactorN_pos (assets : Nat) : 0 < assetFactorN assets := by
  unfold assetFactorN
  omega

theorem assetFactorN_ne_zero (assets : Nat) : assetFactorN assets ≠ 0 :=
  Nat.ne_of_gt (assetFactorN_pos assets)

theorem assetFactorN_maxWord : assetFactorN maxWordN = wordModulusN := by
  unfold assetFactorN maxWordN
  have := wordModulusN_pos
  omega

theorem denominatorN_le_maxWord
    {supply : Nat} (stable : supply ≤ maxSupplyN) :
    denominatorN supply ≤ maxWordN := by
  simp only [denominatorN, maxSupplyN, offsetN] at stable ⊢
  have hlarge : 1000 ≤ maxWordN := by
    unfold maxWordN wordModulusN
    norm_num
  omega

theorem maxSupplyN_add_offsetN : maxSupplyN + offsetN = maxWordN := by
  unfold maxSupplyN
  exact Nat.sub_add_cancel (by
    unfold maxWordN wordModulusN offsetN
    norm_num)

theorem supply_add_shareRoomN
    {supply : Nat} (stable : supply ≤ maxSupplyN) :
    supply + shareRoomN supply = maxSupplyN := by
  unfold shareRoomN
  exact Nat.add_sub_of_le stable

theorem supply_add_le_maxSupplyN_of_le_shareRoomN
    {supply shares : Nat} (stable : supply ≤ maxSupplyN)
    (room : shares ≤ shareRoomN supply) :
    supply + shares ≤ maxSupplyN := by
  rw [← supply_add_shareRoomN stable]
  exact Nat.add_le_add_left room supply

/-! ## Exact two-word multiplication staging -/

/-- The low word staged by `multiply512`.  This family-local name records the
exact word expression used by the compiled vault helper. -/
def productLowWord (x y : B256) : B256 := x * y

/-- The high word staged by `multiply512`, including its `mulmod` carry
correction.  The definition deliberately mirrors the source helper instruction
for instruction; its correctness theorem below is over the untruncated product. -/
def productHighWord (x y : B256) : B256 :=
  let low := productLowWord x y
  let scratch := B256.mulmod x y B256.max
  (scratch - low) - (if scratch < low then 1 else 0)

theorem productLowWord_toNat (x y : B256) :
    (productLowWord x y).toNat = x.toNat * y.toNat % wordModulusN := by
  exact B256.toNat_mul_mod x y

private theorem product_quotient_lt_pred
    {m x y : Nat} (hm : 2 ≤ m) (hx : x < m) (hy : y < m) :
    x * y / m < m - 1 := by
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  calc
    x * y ≤ (m - 1) * (m - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    _ < (m - 1) * m :=
      Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    _ = (m - 1) * m := rfl

private theorem product_mod_pred_eq_quotient_add_remainder_mod
    {m p : Nat} (hm : 2 ≤ m) :
    p % (m - 1) = (p / m + p % m) % (m - 1) := by
  have hsplit : p = p / m * m + p % m := (Nat.div_add_mod' p m).symm
  have hmSplit : m = (m - 1) + 1 := by omega
  calc
    p % (m - 1) = (p / m * m + p % m) % (m - 1) :=
      congrArg (fun n => n % (m - 1)) hsplit
    _ = (p / m * ((m - 1) + 1) + p % m) % (m - 1) := by rw [← hmSplit]
    _ = (p / m * (m - 1) + (p / m + p % m)) % (m - 1) := by
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    _ = (p / m + p % m) % (m - 1) := by simp

/-- The staged high and low words recombine to the exact, untruncated product.
This is the arithmetic identity implemented by `multiply512`; there is no
single-word product or magnitude premise. -/
theorem productHighWord_mul_add_productLowWord_toNat (x y : B256) :
    (productHighWord x y).toNat * wordModulusN +
        (productLowWord x y).toNat =
      x.toNat * y.toNat := by
  let p := x.toNat * y.toNat
  let q := p / wordModulusN
  let r := p % wordModulusN
  let scratch := p % maxWordN
  have hmodulus : 2 ≤ wordModulusN := by
    unfold wordModulusN
    norm_num
  have hmaxWord : maxWordN = wordModulusN - 1 := rfl
  have hq : q < maxWordN := by
    exact product_quotient_lt_pred hmodulus (B256.toNat_lt x)
      (B256.toNat_lt y)
  have hr : r < wordModulusN := by
    exact Nat.mod_lt _ (by omega)
  have hsplit : q * wordModulusN + r = p := by
    exact Nat.div_add_mod' p wordModulusN
  have hscratch : scratch = (q + r) % maxWordN := by
    unfold scratch q r
    rw [hmaxWord]
    exact product_mod_pred_eq_quotient_add_remainder_mod hmodulus
  have hlow : (productLowWord x y).toNat = r := by
    unfold productLowWord r p wordModulusN
    exact B256.toNat_mul_mod x y
  have hscratchWord : (B256.mulmod x y B256.max).toNat = scratch := by
    rw [B256.toNat_mulmod (by decide), maxWord_toNat]
  by_cases hsum : q + r < maxWordN
  · have hscratchSmall : scratch = q + r := by
      rw [hscratch, Nat.mod_eq_of_lt hsum]
    have hgeNat :
        (productLowWord x y).toNat ≤
          (B256.mulmod x y B256.max).toNat := by
      calc
        (productLowWord x y).toNat = r := hlow
        _ ≤ q + r := Nat.le_add_left r q
        _ = (B256.mulmod x y B256.max).toNat :=
          (hscratchWord.trans hscratchSmall).symm
    have hnotBorrow :
        ¬B256.mulmod x y B256.max < productLowWord x y := by
      intro hlt
      exact (Nat.not_lt_of_ge hgeNat) (B256.toNat_lt_toNat hlt)
    have hleWord :
        productLowWord x y ≤ B256.mulmod x y B256.max :=
      B256.le_of_toNat_le_toNat hgeNat
    have hzeroLe :
        (0 : B256) ≤ B256.mulmod x y B256.max - productLowWord x y :=
      B256.le_of_toNat_le_toNat (Nat.zero_le _)
    have hhigh : (productHighWord x y).toNat = q := by
      rw [productHighWord, if_neg hnotBorrow]
      rw [B256.toNat_sub_eq_of_le _ _ hzeroLe, B256.toNat_zero,
        Nat.sub_zero]
      rw [B256.toNat_sub_eq_of_le _ _ hleWord, hscratchWord, hlow,
        hscratchSmall]
      omega
    rw [hhigh, hlow]
    change q * wordModulusN + r = p
    exact hsplit
  · have hsumLe : maxWordN ≤ q + r := by omega
    have hsumSub : q + r - maxWordN < maxWordN := by
      unfold maxWordN at hq hr hsumLe ⊢
      omega
    have hscratchLarge : scratch = q + r - maxWordN := by
      rw [hscratch, Nat.mod_eq_sub_mod hsumLe, Nat.mod_eq_of_lt hsumSub]
    have hborrow : B256.mulmod x y B256.max < productLowWord x y := by
      apply B256.lt_of_toNat_lt_toNat
      calc
        (B256.mulmod x y B256.max).toNat = q + r - maxWordN :=
          hscratchWord.trans hscratchLarge
        _ < r := by
          unfold maxWordN at hq hsumLe ⊢
          omega
        _ = (productLowWord x y).toNat := hlow.symm
    have hwrapped :
        ((B256.mulmod x y B256.max - productLowWord x y).toNat) = q + 1 := by
      rw [B256.toNat_sub, hscratchWord, hlow, hscratchLarge, Nat.lo_eq]
      have hinner :
          wordModulusN + (q + r - maxWordN) - r = q + 1 := by
        unfold maxWordN at hq hr hsumLe ⊢
        omega
      unfold wordModulusN at hinner
      rw [hinner, Nat.mod_eq_of_lt]
      unfold maxWordN at hq
      omega
    have honeLe :
        (1 : B256) ≤ B256.mulmod x y B256.max - productLowWord x y := by
      apply B256.le_of_toNat_le_toNat
      rw [B256.toNat_one, hwrapped]
      omega
    have hhigh : (productHighWord x y).toNat = q := by
      rw [productHighWord, if_pos hborrow]
      rw [B256.toNat_sub_eq_of_le _ _ honeLe, hwrapped, B256.toNat_one]
      omega
    rw [hhigh, hlow]
    change q * wordModulusN + r = p
    exact hsplit

theorem productHighWord_toNat (x y : B256) :
    (productHighWord x y).toNat =
      x.toNat * y.toNat / wordModulusN := by
  have hlow : (productLowWord x y).toNat < wordModulusN := by
    simpa [wordModulusN] using B256.toNat_lt (productLowWord x y)
  have hquotient :
      ((productHighWord x y).toNat * wordModulusN +
          (productLowWord x y).toNat) / wordModulusN =
        (productHighWord x y).toNat := by
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_add_right _ _
    · rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_lt_add_left hlow _
  calc
    (productHighWord x y).toNat =
        ((productHighWord x y).toNat * wordModulusN +
          (productLowWord x y).toNat) / wordModulusN := hquotient.symm
    _ = x.toNat * y.toNat / wordModulusN := by
      rw [productHighWord_mul_add_productLowWord_toNat]

private theorem maxWord_mul_div_wordModulus
    {d : Nat} (hd : 0 < d) (hle : d ≤ maxWordN) :
    maxWordN * d / wordModulusN = d - 1 := by
  apply Nat.div_eq_of_lt_le
  · rw [Nat.sub_mul, Nat.one_mul]
    unfold maxWordN
    rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm d wordModulusN]
    apply Nat.sub_le_sub_left
    exact hle.trans (Nat.le_of_lt maxWordN_lt_wordModulusN)
  · have hdOne : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
    rw [hdOne, Nat.mul_comm d wordModulusN]
    unfold maxWordN
    rw [Nat.sub_mul, Nat.one_mul]
    exact Nat.sub_lt (Nat.mul_pos wordModulusN_pos hd) hd

theorem maxWord_mul_denominator_div_assetFactor_maxWord
    {supply : Nat} (stable : supply ≤ maxSupplyN) :
    maxWordN * denominatorN supply / assetFactorN maxWordN =
      denominatorN supply - 1 := by
  rw [assetFactorN_maxWord]
  exact maxWord_mul_div_wordModulus (denominatorN_pos supply)
    (denominatorN_le_maxWord stable)

theorem maxMintN_at_maxAssets
    {supply : Nat} (stable : supply ≤ maxSupplyN) :
    maxMintN maxWordN supply =
      min (shareRoomN supply) (denominatorN supply - 1) := by
  unfold maxMintN
  rw [maxWord_mul_denominator_div_assetFactor_maxWord stable]

/-! ## Exact rounding directions -/

theorem convertToSharesN_floor_le (amount assets supply : Nat) :
    assetFactorN assets * convertToSharesN amount assets supply ≤
      amount * denominatorN supply := by
  exact Nat.mul_div_mul_le _ _ _

theorem convertToSharesN_lt_floor_add_one (amount assets supply : Nat) :
    amount * denominatorN supply <
      assetFactorN assets * (convertToSharesN amount assets supply + 1) := by
  exact Nat.lt_mul_div_add_one (assetFactorN_ne_zero assets) _ _

theorem convertToAssetsN_floor_le (shares assets supply : Nat) :
    denominatorN supply * convertToAssetsN shares assets supply ≤
      shares * assetFactorN assets := by
  exact Nat.mul_div_mul_le _ _ _

theorem convertToAssetsN_lt_floor_add_one (shares assets supply : Nat) :
    shares * assetFactorN assets <
      denominatorN supply * (convertToAssetsN shares assets supply + 1) := by
  exact Nat.lt_mul_div_add_one (denominatorN_ne_zero supply) _ _

theorem previewMintN_covers (shares assets supply : Nat) :
    shares * assetFactorN assets ≤
      previewMintN shares assets supply * denominatorN supply := by
  exact le_ceilDiv_mul (denominatorN_ne_zero supply) _

theorem previewMintN_lt_add_denominator (shares assets supply : Nat) :
    previewMintN shares assets supply * denominatorN supply <
      shares * assetFactorN assets + denominatorN supply := by
  exact ceilDiv_mul_lt (denominatorN_ne_zero supply) _

theorem previewWithdrawN_covers (amount assets supply : Nat) :
    amount * denominatorN supply ≤
      previewWithdrawN amount assets supply * assetFactorN assets := by
  exact le_ceilDiv_mul (assetFactorN_ne_zero assets) _

theorem previewWithdrawN_lt_add_assetFactor (amount assets supply : Nat) :
    previewWithdrawN amount assets supply * assetFactorN assets <
      amount * denominatorN supply + assetFactorN assets := by
  exact ceilDiv_mul_lt (assetFactorN_ne_zero assets) _

theorem previewDepositN_eq_convertToSharesN (amount assets supply : Nat) :
    previewDepositN amount assets supply = convertToSharesN amount assets supply :=
  rfl

theorem previewRedeemN_eq_convertToAssetsN (shares assets supply : Nat) :
    previewRedeemN shares assets supply = convertToAssetsN shares assets supply :=
  rfl

/-! ## Exact capacity characterizations -/

private theorem lt_ceilDiv_iff_mul_lt
    {n m d : Nat} (hd : d ≠ 0) :
    n < ceilDiv m d ↔ n * d < m := by
  constructor
  · intro h
    have hnext : n + 1 ≤ ceilDiv m d := by omega
    have hmul := Nat.mul_le_mul_right d hnext
    have hupper := ceilDiv_mul_lt hd m
    rw [Nat.add_mul] at hmul
    omega
  · intro h
    by_contra hn
    have hceil : ceilDiv m d ≤ n := Nat.le_of_not_gt hn
    have hmul := Nat.mul_le_mul_right d hceil
    have hlower := le_ceilDiv_mul hd m
    omega

private theorem mul_div_le_iff_lt_next_scaled
    {n d x room : Nat} (hd : d ≠ 0) (hx : 0 < x) :
    n * d / x ≤ room ↔
      n < ceilDiv ((room + 1) * x) d := by
  calc
    n * d / x ≤ room ↔ n * d / x < room + 1 := by omega
    _ ↔ n * d < (room + 1) * x := Nat.div_lt_iff_lt_mul hx
    _ ↔ n < ceilDiv ((room + 1) * x) d :=
      (lt_ceilDiv_iff_mul_lt hd).symm

theorem le_maxMintN_iff (shares assets supply : Nat) :
    shares ≤ maxMintN assets supply ↔
      shares ≤ shareRoomN supply ∧
        previewMintN shares assets supply ≤ maxWordN := by
  unfold maxMintN previewMintN
  rw [Nat.le_min]
  rw [ceilDiv_le_iff (denominatorN_ne_zero supply)]
  rw [Nat.le_div_iff_mul_le (assetFactorN_pos assets)]

theorem maxMintN_le_shareRoom (assets supply : Nat) :
    maxMintN assets supply ≤ shareRoomN supply :=
  (le_maxMintN_iff (maxMintN assets supply) assets supply).mp le_rfl |>.1

theorem previewMintN_maxMintN_le_maxWord (assets supply : Nat) :
    previewMintN (maxMintN assets supply) assets supply ≤ maxWordN :=
  (le_maxMintN_iff (maxMintN assets supply) assets supply).mp le_rfl |>.2

theorem maxDepositN_le_maxWord (assets supply : Nat) :
    maxDepositN assets supply ≤ maxWordN := by
  exact Nat.min_le_left _ _

theorem le_maxDepositN_iff
    {amount assets supply : Nat} (word : amount ≤ maxWordN) :
    amount ≤ maxDepositN assets supply ↔
      convertToSharesN amount assets supply ≤ shareRoomN supply := by
  let threshold := ceilDiv
    ((shareRoomN supply + 1) * assetFactorN assets) (denominatorN supply)
  have hnum : 0 < (shareRoomN supply + 1) * assetFactorN assets :=
    Nat.mul_pos (by omega) (assetFactorN_pos assets)
  have hthreshold : 0 < threshold := by
    by_contra hnot
    have hzero : threshold = 0 := Nat.eq_zero_of_not_pos hnot
    have hlower := le_ceilDiv_mul (denominatorN_ne_zero supply)
      ((shareRoomN supply + 1) * assetFactorN assets)
    change (shareRoomN supply + 1) * assetFactorN assets ≤
      threshold * denominatorN supply at hlower
    rw [hzero] at hlower
    simp only [Nat.zero_mul] at hlower
    omega
  have hcharacterization :
      convertToSharesN amount assets supply ≤ shareRoomN supply ↔
        amount < threshold := by
    exact mul_div_le_iff_lt_next_scaled
      (denominatorN_ne_zero supply) (assetFactorN_pos assets)
  constructor
  · intro h
    have hraw : amount ≤ threshold - 1 := by
      exact (Nat.le_min.mp h).2
    exact hcharacterization.mpr (by omega)
  · intro h
    apply Nat.le_min.mpr
    constructor
    · exact word
    have hlt := hcharacterization.mp h
    omega

theorem convertToSharesN_maxDepositN_le_shareRoom (assets supply : Nat) :
    convertToSharesN (maxDepositN assets supply) assets supply ≤
      shareRoomN supply := by
  exact (le_maxDepositN_iff (maxDepositN_le_maxWord assets supply)).mp le_rfl

theorem maxRedeemN_exact (balance : Nat) : maxRedeemN balance = balance := rfl

theorem maxWithdrawN_le_assets
    {balance assets supply : Nat} (balance_le : balance ≤ supply) :
    maxWithdrawN balance assets supply ≤ assets := by
  unfold maxWithdrawN convertToAssetsN
  have hscaled : balance * assetFactorN assets ≤
      supply * assetFactorN assets :=
    Nat.mul_le_mul_right (assetFactorN assets) balance_le
  have hstrict : supply * assetFactorN assets <
      denominatorN supply * assetFactorN assets := by
    apply Nat.mul_lt_mul_of_pos_right
    · unfold denominatorN
      have := offsetN_pos
      omega
    · exact assetFactorN_pos assets
  have hnum : balance * assetFactorN assets <
      (assets + 1) * denominatorN supply := by
    calc
      balance * assetFactorN assets ≤ supply * assetFactorN assets := hscaled
      _ < denominatorN supply * assetFactorN assets := hstrict
      _ = (assets + 1) * denominatorN supply := by
        rw [assetFactorN, Nat.mul_comm]
  have hquot :
      balance * assetFactorN assets / denominatorN supply < assets + 1 :=
    (Nat.div_lt_iff_lt_mul (denominatorN_pos supply)).mpr hnum
  omega

/-! ## Zero-amount behavior -/

theorem convertToSharesN_zero (assets supply : Nat) :
    convertToSharesN 0 assets supply = 0 := by
  simp [convertToSharesN]

theorem convertToAssetsN_zero (assets supply : Nat) :
    convertToAssetsN 0 assets supply = 0 := by
  simp [convertToAssetsN]

theorem previewMintN_zero (assets supply : Nat) :
    previewMintN 0 assets supply = 0 := by
  simp [previewMintN, ceilDiv_zero_dividend]

theorem previewWithdrawN_zero (assets supply : Nat) :
    previewWithdrawN 0 assets supply = 0 := by
  simp [previewWithdrawN, ceilDiv_zero_dividend]

end ProrataWethVault

end Blanc
