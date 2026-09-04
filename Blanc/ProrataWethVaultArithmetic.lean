-- ProrataWethVaultArithmetic.lean : full-width ERC-4626 ratio arithmetic.

import Blanc.ProrataWethVault
import Blanc.WordArithmetic
import Jaune.MulDiv
import Blanc.OffsetPricing

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

/-- Exact public `maxMint` result, including the frozen zero-receiver and
unstable-supply policy. -/
def maxMintViewN (receiver assets supply : Nat) : Nat :=
  if receiver = 0 then 0
  else if maxSupplyN < supply then 0
  else maxMintN assets supply

/-- Exact public `maxDeposit` result, including the frozen zero-receiver and
unstable-supply policy. -/
def maxDepositViewN (receiver assets supply : Nat) : Nat :=
  if receiver = 0 then 0
  else if maxSupplyN < supply then 0
  else maxDepositN assets supply

/-- Exact public `maxWithdraw` result.  The arithmetic claim is saturated at
one EVM word until the reachable-ledger premise `balance ≤ supply` removes
that saturation. -/
def maxWithdrawViewN (balance assets supply : Nat) : Nat :=
  if maxSupplyN < supply then 0
  else min maxWordN (maxWithdrawN balance assets supply)

theorem shareRoomN_lt_wordModulusN (supply : Nat) :
    shareRoomN supply < wordModulusN := by
  unfold shareRoomN maxSupplyN maxWordN
  have modulusPositive := wordModulusN_pos
  omega

theorem shareRoomN_add_one_lt_wordModulusN (supply : Nat) :
    shareRoomN supply + 1 < wordModulusN := by
  have roomLe : shareRoomN supply ≤ maxSupplyN := by
    unfold shareRoomN
    exact Nat.sub_le _ _
  have maxSupplyPlusOffset : maxSupplyN + offsetN = maxWordN := by
    unfold maxSupplyN
    exact Nat.sub_add_cancel (by
      unfold maxWordN wordModulusN offsetN
      norm_num)
  have offsetPositive : 0 < offsetN := by decide
  have roomPlusOneLe : shareRoomN supply + 1 ≤ maxWordN := by
    omega
  exact roomPlusOneLe.trans_lt maxWordN_lt_wordModulusN

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

/-- **`mint` never over-mints relative to the deposit price.**

`mint(s)` charges `previewMintN s` assets for exactly `s` shares, while a
`deposit` of those same assets would mint
`convertToSharesN (previewMintN s)` — and this says the latter is never
smaller. The two roundings compose in the pool's favour: the inverse quote
rounds the charge up, the forward quote rounds the mint down, so a minter
never receives more shares than the assets they paid would have bought.

This is the quantitative content of the `mint`/`withdraw` carrier gap.
`ProrataAccountingEffect.deposit` pins `minted = mintN o amount supply balance`
by *equality*, so a `mint` step whose round trip is strict cannot be exhibited
as one, and closing that needs either an inverse-quoted class or an explicit
slack term — a change to a model `Blanc/ProrataAccounting.lean` shares with
PRORATA, and so an owner's decision rather than a missing proof. What does not
need deciding is the direction of the slack, which is what this records: it
falls on the safe side, so the gap is a modelling incompleteness and not an
unsoundness. -/
theorem mint_never_overmints (shares assets supply : Nat) :
    shares ≤ convertToSharesN (previewMintN shares assets supply) assets supply := by
  unfold convertToSharesN
  rw [Nat.le_div_iff_mul_le (assetFactorN_pos assets)]
  exact previewMintN_covers shares assets supply

/-- **`withdraw` never overpays relative to the redemption price.**

The dual: `withdraw(a)` burns `previewWithdrawN a` shares to pay exactly `a`
assets, and redeeming those same shares would pay
`convertToAssetsN (previewWithdrawN a)`, which is never smaller. So the
withdrawer never extracts more than their burnt shares were worth, and the
`withdraw` half of the same carrier gap also falls on the safe side. -/
theorem withdraw_never_overpays (amount assets supply : Nat) :
    amount ≤ convertToAssetsN (previewWithdrawN amount assets supply) assets supply := by
  unfold convertToAssetsN
  rw [Nat.le_div_iff_mul_le (denominatorN_pos supply)]
  exact previewWithdrawN_covers amount assets supply

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

/-- Saturating the arithmetic asset cap at the largest word before taking
the share-room minimum does not change `maxMint`: stable or unstable, the
declared room itself is already no larger than one word. -/
theorem min_shareRoomN_min_maxWord (supply cap : Nat) :
    min (shareRoomN supply) (min maxWordN cap) =
      min (shareRoomN supply) cap := by
  have roomLe : shareRoomN supply ≤ maxWordN := by
    unfold shareRoomN maxSupplyN
    omega
  calc
    min (shareRoomN supply) (min maxWordN cap) =
        min (min (shareRoomN supply) maxWordN) cap :=
      (Nat.min_assoc _ _ _).symm
    _ = min (shareRoomN supply) cap := by
      rw [Nat.min_eq_left roomLe]

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


/-! ## The port is the same pricing, at the same offset

`Blanc/OffsetPricing.lean` states virtual-offset pricing over the naturals with
the offset as a parameter.  The vault's converters are that pricing at
`offsetN`, with the held asset in the `balance` position — which is the whole
content of "the port changes the asset, not the arithmetic".

Both bridges are `rfl`: `convertToSharesN amount assets supply` and
`mintN offsetN amount supply assets` are the same term, not merely equal ones.
That is what lets the ETH-denominated dust and attack results apply here
without restating a line of their arithmetic. -/

theorem convertToSharesN_eq_mintN (amount assets supply : Nat) :
    convertToSharesN amount assets supply =
      Blanc.Prorata.mintN offsetN amount supply assets := rfl

theorem convertToAssetsN_eq_payN (shares assets supply : Nat) :
    convertToAssetsN shares assets supply =
      Blanc.Prorata.payN offsetN shares supply assets := rfl

/-- The offset is nonzero, which is the side condition every offset-parameterised
result carries. -/
theorem offsetN_ne_zero : offsetN ≠ 0 := by decide

end ProrataWethVault

end Blanc
