-- ProrataWethVault.lean : a full-width ERC-4626 share vault over exact Blanc WETH.
--
-- This module owns the executable surface frozen in
-- `plans/reports/prorata-erc4626-port-sf.md`.  It deliberately imports only
-- CommonCore: the vault and WETH are sibling contracts, while their eventual
-- composition facts live above both families.

import Blanc.CommonCore

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace ProrataWethVault

/-! ## Configuration and storage -/

/-- Exact WETH account installed by the configured two-runtime root. -/
def assetAddress : B256 := 0x1000

/-- Virtual share offset.  The virtual asset offset is one. -/
def virtualShares : B256 := 1000

/-- Share supply is kept outside the address-shaped balance region. -/
def supplySlot : B256 := B256.max

/-- `U - O`, the largest representable stable share supply. -/
def maxSupply : B256 := B256.max - virtualShares

def pushSupplySlot : Line := [pushB256 0, not]

/-- Allowance hashes may alias neither a raw balance word nor the supply slot. -/
def checkAllowanceSlotCollision : Line :=
  (dup 0 :: checkAddress) ++
  (dup 1 :: isMax) ++
  [Ninst.or]

/-! ## ABI and small runtime helpers -/

def loadWord (word : B256) : Line := [pushB256 (word * 32), mload]

def returnWord : Func := mstoreAt 0 +++ returnMemoryRange 0 32

def returnConstant (w : B256) : Func := pushB256 w ::: returnWord

/-- Reject selector-matched calldata shorter than its static ABI head. -/
def requireStaticArgs (words : Nat) (body : Func) : Func :=
  pushB256 (Nat.toB256 (4 + 32 * words)) ::: calldatasize ::: lt :::
  (Func.revert <?> body)

/-- Reject dirty address words while retaining the zero address for views. -/
def canonicalAddressArg (k : B256) (body : Func) : Func :=
  arg k +++ checkNonAddress +++ (Func.revert <?> body)

/-- Reject dirty and zero address words. -/
def nonzeroAddressArg (k : B256) (body : Func) : Func :=
  arg k +++ dup 0 ::: checkNonAddress +++
  (Func.revert <?>
    (iszero ::: (Func.revert <?> body)))

/-- Mutating share operations also reject the zero EVM caller. -/
def nonzeroCaller (body : Func) : Func :=
  caller ::: iszero ::: (Func.revert <?> body)

def endpoint (words : Nat) (body : Func) : Func :=
  nonpayable (requireStaticArgs words body)

/-! ## Full-width arithmetic

The implementation is the standard exact 512-by-256 route: recover the high
product word with `mulmod`, subtract the full-width remainder, factor powers of
two out of the denominator, and multiply by its Newton-refined inverse modulo
`2^256`.  The `A = U` branches below represent `A + 1 = 2^256` as the two-word
numerator `(input, 0)` instead of wrapping it to zero.

Arithmetic uses private memory words 16--27.  Operation state starts at word
32, so WETH ABI frames at words 0--3 cannot clobber either region. -/

def xWord : B256 := 16
def yWord : B256 := 17
def denominatorWord : B256 := 18
def highWord : B256 := 19
def lowWord : B256 := 20
def remainderWord : B256 := 21
def twosWord : B256 := 22
def inverseWord : B256 := 23
def quotientWord : B256 := 24
def scratchWord : B256 := 25
def factorWord : B256 := 26
def borrowWord : B256 := 27

inductive QuotientMode
  | down
  | up
  | capDown
  | capCeilPred

/-- Finish from exact quotient and remainder staged in memory. -/
def finishQuotient (mode : QuotientMode) (continuation : Nat) : Func :=
  match mode with
  | .down =>
      loadWord quotientWord +++ .call continuation
  | .capDown =>
      loadWord quotientWord +++ .call continuation
  | .up =>
      loadWord remainderWord +++ iszero :::
      ( (loadWord quotientWord +++ .call continuation) <?>
        (loadWord quotientWord +++ dup 0 ::: isMax +++
          (Func.revert <?>
            (pushB256 1 ::: add ::: .call continuation))) )
  | .capCeilPred =>
      loadWord remainderWord +++ iszero :::
      ( (pushB256 1 ::: loadWord quotientWord +++ sub :::
          .call continuation) <?>
        (loadWord quotientWord +++ .call continuation) )

def divisionOverflow (mode : QuotientMode) (continuation : Nat) : Func :=
  match mode with
  | .capDown => pushB256 B256.max ::: .call continuation
  | .capCeilPred => pushB256 B256.max ::: .call continuation
  | _ => Func.revert

def divideSimple (mode : QuotientMode) (continuation : Nat) : Func :=
  loadWord denominatorWord +++ loadWord lowWord +++ mod :::
  mstoreAt remainderWord +++
  loadWord denominatorWord +++ loadWord lowWord +++ div :::
  mstoreAt quotientWord +++
  finishQuotient mode continuation

def newtonStep : Line :=
  loadWord denominatorWord ++
  loadWord inverseWord ++
  [mul, pushB256 2, sub] ++
  loadWord inverseWord ++
  [mul] ++
  mstoreAt inverseWord

def sixNewtonSteps : Line :=
  newtonStep ++ newtonStep ++ newtonStep ++
  newtonStep ++ newtonStep ++ newtonStep

/-- Divide the staged exact two-word numerator `(high,low)` by `denominator`. -/
def divideWideCore (mode : QuotientMode) (continuation : Nat) : Func :=
  -- factor = 2^256 mod denominator
  loadWord denominatorWord +++ pushB256 1 ::: pushB256 B256.max ::: addmod :::
  mstoreAt factorWord +++
  -- remainder = (high * factor + low) mod denominator
  loadWord denominatorWord +++ loadWord factorWord +++ loadWord highWord +++
  mulmod ::: mstoreAt scratchWord +++
  loadWord denominatorWord +++ loadWord lowWord +++ loadWord scratchWord +++
  addmod ::: mstoreAt remainderWord +++
  -- Subtract the remainder from the two-word numerator.
  loadWord remainderWord +++ loadWord lowWord +++ lt :::
  mstoreAt borrowWord +++
  loadWord remainderWord +++ loadWord lowWord +++ sub :::
  mstoreAt lowWord +++
  loadWord borrowWord +++ loadWord highWord +++ sub :::
  mstoreAt highWord +++
  -- Factor powers of two out of the denominator.
  loadWord denominatorWord +++ pushB256 0 ::: sub :::
  loadWord denominatorWord +++ Ninst.and ::: mstoreAt twosWord +++
  loadWord twosWord +++ loadWord denominatorWord +++ div :::
  mstoreAt denominatorWord +++
  loadWord twosWord +++ loadWord lowWord +++ div :::
  mstoreAt lowWord +++
  -- twos := 2^256 / oldTwos (with the all-ones modular representation).
  loadWord twosWord +++ loadWord twosWord +++ pushB256 0 ::: sub ::: div :::
  pushB256 1 ::: add ::: mstoreAt factorWord +++
  -- Fold the high word into the exact low-word dividend.
  loadWord factorWord +++ loadWord highWord +++ mul :::
  loadWord lowWord +++ Ninst.or ::: mstoreAt lowWord +++
  -- Invert the now-odd denominator modulo 2^256.
  loadWord denominatorWord +++ pushB256 3 ::: mul ::: pushB256 2 ::: xor :::
  mstoreAt inverseWord +++
  sixNewtonSteps +++
  loadWord inverseWord +++ loadWord lowWord +++ mul :::
  mstoreAt quotientWord +++
  finishQuotient mode continuation

def divideWide (mode : QuotientMode) (continuation : Nat) : Func :=
  loadWord denominatorWord +++ loadWord highWord +++ lt :::
  (divideWideCore mode continuation <?>
    divisionOverflow mode continuation)

def divide512 (mode : QuotientMode) (continuation : Nat) : Func :=
  loadWord denominatorWord +++ iszero :::
  (Func.revert <?>
    (loadWord highWord +++ iszero :::
      (divideSimple mode continuation <?>
        divideWide mode continuation)))

/-- Stage the exact 512-bit product of two word-valued instruction lines. -/
def multiply512 (x y : Line) (body : Func) : Func :=
  x +++ mstoreAt xWord +++
  y +++ mstoreAt yWord +++
  loadWord xWord +++ loadWord yWord +++ mul ::: mstoreAt lowWord +++
  pushB256 B256.max ::: loadWord yWord +++ loadWord xWord +++ mulmod :::
  mstoreAt scratchWord +++
  loadWord lowWord +++ loadWord scratchWord +++ sub :::
  mstoreAt highWord +++
  loadWord lowWord +++ loadWord scratchWord +++ lt :::
  mstoreAt borrowWord +++
  loadWord borrowWord +++ loadWord highWord +++ sub :::
  mstoreAt highWord +++
  body

def mulDiv (x y denominator : Line) (mode : QuotientMode)
    (continuation : Nat) : Func :=
  denominator +++ mstoreAt denominatorWord +++
  multiply512 x y (divide512 mode continuation)

/-- Divide `high * 2^256` by a word denominator. -/
def shiftedDiv (high denominator : Line) (mode : QuotientMode)
    (continuation : Nat) : Func :=
  high +++ mstoreAt highWord +++
  pushB256 0 ::: mstoreAt lowWord +++
  denominator +++ mstoreAt denominatorWord +++
  divide512 mode continuation

/-- Divide a product by exactly `2^256`: quotient=high, remainder=low. -/
def productOverTwoPow256 (x y : Line) (mode : QuotientMode)
    (continuation : Nat) : Func :=
  multiply512 x y <|
    loadWord highWord +++ mstoreAt quotientWord +++
    loadWord lowWord +++ mstoreAt remainderWord +++
    finishQuotient mode continuation

/-! ## WETH boundary -/

def wethBalanceOfSelector : B256 := selector "balanceOf" [.address]
def wethTransferSelector : B256 := selector "transfer" [.address, .uint256]
def wethTransferFromSelector : B256 :=
  selector "transferFrom" [.address, .address, .uint256]

/-- Exact `WETH.balanceOf(address(this))`, requiring one return word. -/
def readTotalAssets (body : Func) : Func :=
  pushB256 wethBalanceOfSelector ::: mstoreAt 0 +++
  address ::: mstoreAt 1 +++
  pushList [32, 0, 36, 28] +++
  pushB256 assetAddress ::: gas ::: staticcall :::
  iszero :::
  (Func.revert <?>
    (pushB256 32 ::: returndatasize ::: eq ::: iszero :::
      (Func.revert <?>
        (pushB256 0 ::: mload ::: body))))

/-- Require an exact one-word canonical `true` return after a WETH mutation. -/
def requireCanonicalWethTrue (body : Func) : Func :=
  pushB256 32 ::: returndatasize ::: eq ::: iszero :::
  (Func.revert <?>
    (pushB256 0 ::: mload ::: pushB256 1 ::: eq ::: iszero :::
      (Func.revert <?> body)))

/-! ## Long-lived operation memory -/

def amountWord : B256 := 32
def receiverWord : B256 := 33
def ownerWord : B256 := 34
def quoteWord : B256 := 35
def supplyWord : B256 := 36
def assetsWord : B256 := 37
def balanceWord : B256 := 38
def allowanceWord : B256 := 39

def stagedDenominator : Line :=
  loadWord supplyWord ++ [pushB256 virtualShares, add]

def stagedAssetFactor : Line :=
  loadWord assetsWord ++ [pushB256 1, add]

def guardStableSupply (body : Func) : Func :=
  loadWord supplyWord +++ pushB256 maxSupply ::: lt :::
  (Func.revert <?> body)

/-! ## Aux-table indices

The table is append-only once proof modules refer to these indices. -/

def revertSlot : Nat := 1
def returnWordSlot : Nat := 2
def depositAfterQuoteSlot : Nat := 3
def mintAfterQuoteSlot : Nat := 4
def withdrawAfterQuoteSlot : Nat := 5
def redeemAfterQuoteSlot : Nat := 6
def transferFromAfterAllowanceSlot : Nat := 7
def withdrawBurnSlot : Nat := 8
def redeemBurnSlot : Nat := 9
def maxMintAfterAssetCapSlot : Nat := 10

/-! ## Metadata and read-only share surface -/

def name : Func :=
  pushB256 (Blanc.String.toBytes "PRORATA WETH Vault").toB256 :::
  pushB256 112 ::: shl :::
  pushList [18, 32] +++
  mstoreAt 0 +++ mstoreAt 1 +++ mstoreAt 2 +++
  returnMemoryRange 0 96

def symbol : Func :=
  pushB256 (Blanc.String.toBytes "prWETH").toB256 :::
  pushB256 208 ::: shl :::
  pushList [6, 32] +++
  mstoreAt 0 +++ mstoreAt 1 +++ mstoreAt 2 +++
  returnMemoryRange 0 96

def decimals : Func := returnConstant 21
def asset : Func := returnConstant assetAddress

def totalSupply : Func := pushSupplySlot +++ sload ::: returnWord

def totalAssets : Func := readTotalAssets returnWord

def balanceOf : Func :=
  canonicalAddressArg 0 <| arg 0 +++ sload ::: returnWord

def allowance : Func :=
  canonicalAddressArg 0 <| canonicalAddressArg 1 <|
    arg 0 +++ mstoreAt 0 +++
    arg 1 +++ mstoreAt 1 +++
    pushList [64, 0] +++ keccak256 :::
    checkAllowanceSlotCollision +++
    (Func.revert <?> (sload ::: returnWord))

/-! ## Converters and previews -/

def convertToShares : Func :=
  readTotalAssets <|
    mstoreAt assetsWord +++
    pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
    guardStableSupply (
      loadWord assetsWord +++ isMax +++
      (productOverTwoPow256 (arg 0) stagedDenominator .down returnWordSlot <?>
        mulDiv (arg 0) stagedDenominator stagedAssetFactor .down returnWordSlot))

def convertToAssets : Func :=
  readTotalAssets <|
    mstoreAt assetsWord +++
    pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
    guardStableSupply (
      loadWord assetsWord +++ isMax +++
      (shiftedDiv (arg 0) stagedDenominator .down returnWordSlot <?>
        mulDiv (arg 0) stagedAssetFactor stagedDenominator .down returnWordSlot))

def previewDeposit : Func := convertToShares
def previewRedeem : Func := convertToAssets

def previewMint : Func :=
  readTotalAssets <|
    mstoreAt assetsWord +++
    pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
    guardStableSupply (
      loadWord assetsWord +++ isMax +++
      (shiftedDiv (arg 0) stagedDenominator .up returnWordSlot <?>
        mulDiv (arg 0) stagedAssetFactor stagedDenominator .up returnWordSlot))

def previewWithdraw : Func :=
  readTotalAssets <|
    mstoreAt assetsWord +++
    pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
    guardStableSupply (
      loadWord assetsWord +++ isMax +++
      (productOverTwoPow256 (arg 0) stagedDenominator .up returnWordSlot <?>
        mulDiv (arg 0) stagedDenominator stagedAssetFactor .up returnWordSlot))

/-! ## Exact capacity views -/

def shareRoom : Line :=
  loadWord supplyWord ++ [pushB256 maxSupply, sub]

def shareRoomPlusOne : Line := shareRoom ++ [pushB256 1, add]

def maxMintAfterAssetCap : Func :=
  mstoreAt quoteWord +++
  loadWord quoteWord +++ shareRoom +++ lt :::
  ((shareRoom +++ .call returnWordSlot) <?>
    (loadWord quoteWord +++ .call returnWordSlot))

def maxMint : Func :=
  canonicalAddressArg 0 <|
    arg 0 +++ iszero :::
    (returnConstant 0 <?>
      (pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
        loadWord supplyWord +++ pushB256 maxSupply ::: lt :::
        (returnConstant 0 <?>
          (readTotalAssets <|
            mstoreAt assetsWord +++
            loadWord assetsWord +++ isMax +++
            (productOverTwoPow256 [pushB256 B256.max] stagedDenominator .down
                maxMintAfterAssetCapSlot <?>
              mulDiv [pushB256 B256.max] stagedDenominator stagedAssetFactor
                .capDown maxMintAfterAssetCapSlot)))))

def maxRedeem : Func :=
  canonicalAddressArg 0 <| arg 0 +++ sload ::: returnWord

def maxDeposit : Func :=
  canonicalAddressArg 0 <|
    arg 0 +++ iszero :::
    (returnConstant 0 <?>
      (pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
        loadWord supplyWord +++ pushB256 maxSupply ::: lt :::
        (returnConstant 0 <?>
          (readTotalAssets <|
            mstoreAt assetsWord +++
            loadWord assetsWord +++ isMax +++
            (shiftedDiv shareRoomPlusOne stagedDenominator .capCeilPred
                returnWordSlot <?>
              mulDiv shareRoomPlusOne stagedAssetFactor stagedDenominator
                .capCeilPred returnWordSlot)))))

def maxWithdraw : Func :=
  canonicalAddressArg 0 <|
    arg 0 +++ sload ::: mstoreAt amountWord +++
    pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
    loadWord supplyWord +++ pushB256 maxSupply ::: lt :::
    (returnConstant 0 <?>
      (readTotalAssets <|
        mstoreAt assetsWord +++
        loadWord assetsWord +++ isMax +++
        (shiftedDiv (loadWord amountWord) stagedDenominator .capDown
            returnWordSlot <?>
          mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator
            .capDown returnWordSlot)))

/-! ## Share allowance and transfer machinery -/

def nonzeroStagedAddress (word : B256) (body : Func) : Func :=
  loadWord word +++ dup 0 ::: checkNonAddress +++
  (Func.revert <?>
    (iszero ::: (Func.revert <?> body)))

/-- Hash two staged address words and reject balance/supply aliases. -/
def guardedAllowanceKey (owner spender : Line) (body : Func) : Func :=
  owner +++ mstoreAt 0 +++
  spender +++ mstoreAt 1 +++
  pushList [64, 0] +++ keccak256 :::
  checkAllowanceSlotCollision +++
  (Func.revert <?> body)

/-- Spend a finite staged allowance, preserving `U`, then tail-jump. -/
def spendAllowance (owner spender amount : Line) (continuation : Nat) : Func :=
  guardedAllowanceKey owner spender <|
    mstoreAt scratchWord +++
    loadWord scratchWord +++ sload ::: mstoreAt allowanceWord +++
    loadWord allowanceWord +++ isMax +++
    (.call continuation <?>
      (amount +++ loadWord allowanceWord +++ lt :::
        (Func.revert <?>
          (amount +++ loadWord allowanceWord +++ sub :::
            loadWord scratchWord +++ sstore :::
            .call continuation))))

def logApproval : Line :=
  loadWord amountWord ++ mstoreAt 0 ++
  loadWord receiverWord ++ [caller, pushB256 approvalEvent] ++
  logWith 2 0 1

def logStagedTransfer : Line :=
  loadWord amountWord ++ mstoreAt 0 ++
  loadWord receiverWord ++ loadWord ownerWord ++
  [pushB256 transferEvent] ++ logWith 2 0 1

def approve : Func :=
  nonzeroCaller <| nonzeroAddressArg 0 <|
    caller ::: mstoreAt ownerWord +++
    arg 0 +++ mstoreAt receiverWord +++
    arg 1 +++ mstoreAt amountWord +++
    guardedAllowanceKey (loadWord ownerWord) (loadWord receiverWord) (
      loadWord amountWord +++ swap 0 ::: sstore :::
      logApproval +++ returnTrue)

/-- Transfer staged `amountWord` from `ownerWord` to `receiverWord`. -/
def transferStaged : Func :=
  loadWord ownerWord +++ sload ::: mstoreAt balanceWord +++
  loadWord amountWord +++ loadWord balanceWord +++ lt :::
  (Func.revert <?>
    (loadWord amountWord +++ loadWord balanceWord +++ sub :::
      loadWord ownerWord +++ sstore :::
      loadWord receiverWord +++ sload ::: mstoreAt balanceWord +++
      loadWord amountWord +++ loadWord balanceWord +++ add :::
      mstoreAt scratchWord +++
      loadWord balanceWord +++ loadWord scratchWord +++ lt :::
      (Func.revert <?>
        (loadWord scratchWord +++ loadWord receiverWord +++ sstore :::
          logStagedTransfer +++ returnTrue))))

def transfer : Func :=
  nonzeroCaller <| nonzeroAddressArg 0 <|
    caller ::: mstoreAt ownerWord +++
    arg 0 +++ mstoreAt receiverWord +++
    arg 1 +++ mstoreAt amountWord +++
    .call transferFromAfterAllowanceSlot

def transferFrom : Func :=
  nonzeroCaller <| nonzeroAddressArg 0 <| nonzeroAddressArg 1 <|
    arg 0 +++ mstoreAt ownerWord +++
    arg 1 +++ mstoreAt receiverWord +++
    arg 2 +++ mstoreAt amountWord +++
    spendAllowance (loadWord ownerWord) [caller] (loadWord amountWord)
      transferFromAfterAllowanceSlot

/-! ## Exact WETH mutation calls -/

def callWethTransferFrom (assets : Line) (body : Func) : Func :=
  pushB256 wethTransferFromSelector ::: mstoreAt 0 +++
  caller ::: mstoreAt 1 +++
  address ::: mstoreAt 2 +++
  assets +++ mstoreAt 3 +++
  pushList [32, 0, 100, 28, 0] +++
  pushB256 assetAddress ::: gas ::: call :::
  iszero ::: (Func.revert <?> requireCanonicalWethTrue body)

def callWethTransfer (receiver assets : Line) (body : Func) : Func :=
  pushB256 wethTransferSelector ::: mstoreAt 0 +++
  receiver +++ mstoreAt 1 +++
  assets +++ mstoreAt 2 +++
  pushList [32, 0, 68, 28, 0] +++
  pushB256 assetAddress ::: gas ::: call :::
  iszero ::: (Func.revert <?> requireCanonicalWethTrue body)

/-! ## ERC-4626 event helpers -/

def depositEvent : B256 :=
  signatureHash "Deposit" [.address, .address, .uint256, .uint256]

def withdrawEvent : B256 :=
  signatureHash "Withdraw"
    [.address, .address, .address, .uint256, .uint256]

def logMintTransfer (shares : Line) : Line :=
  shares ++ mstoreAt 0 ++
  loadWord receiverWord ++ [pushB256 0, pushB256 transferEvent] ++
  logWith 2 0 1

def logBurnTransfer (shares : Line) : Line :=
  shares ++ mstoreAt 0 ++
  [pushB256 0] ++ loadWord ownerWord ++ [pushB256 transferEvent] ++
  logWith 2 0 1

def logDeposit (assets shares : Line) : Line :=
  assets ++ mstoreAt 0 ++
  shares ++ mstoreAt 1 ++
  loadWord receiverWord ++ [caller, pushB256 depositEvent] ++
  logWith 2 0 2

def logWithdraw (assets shares : Line) : Line :=
  assets ++ mstoreAt 0 ++
  shares ++ mstoreAt 1 ++
  loadWord ownerWord ++ loadWord receiverWord ++
  [caller, pushB256 withdrawEvent] ++
  logWith 3 0 2

/-! ## Four mutable ERC-4626 flows -/

def snapshotQuoteState (body : Func) : Func :=
  readTotalAssets <|
    mstoreAt assetsWord +++
    pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
    guardStableSupply body

/-- Shared inbound tail.  The child settles before either share write/log. -/
def finishInbound (shares assets returned : Line) : Func :=
  -- Supply room is checked before the WETH child.
  shares +++ shareRoom +++ lt :::
  (Func.revert <?>
    (callWethTransferFrom assets <|
      -- Receiver balance addition is checked independently of PairStable.
      loadWord receiverWord +++ sload ::: mstoreAt balanceWord +++
      shares +++ loadWord balanceWord +++ add ::: mstoreAt scratchWord +++
      loadWord balanceWord +++ loadWord scratchWord +++ lt :::
      (Func.revert <?>
        (loadWord scratchWord +++ loadWord receiverWord +++ sstore :::
          shares +++ loadWord supplyWord +++ add :::
          pushSupplySlot +++ sstore :::
          logMintTransfer shares +++
          logDeposit assets shares +++
          returned +++ returnWord))))

def depositAfterQuote : Func :=
  mstoreAt quoteWord +++
  nonzeroCaller (nonzeroStagedAddress receiverWord (
    finishInbound (loadWord quoteWord) (loadWord amountWord)
      (loadWord quoteWord)))

def mintAfterQuote : Func :=
  mstoreAt quoteWord +++
  nonzeroCaller (nonzeroStagedAddress receiverWord (
    finishInbound (loadWord amountWord) (loadWord quoteWord)
      (loadWord quoteWord)))

def deposit : Func :=
  arg 0 +++ mstoreAt amountWord +++
  arg 1 +++ mstoreAt receiverWord +++
  snapshotQuoteState (
    loadWord assetsWord +++ isMax +++
    (productOverTwoPow256 (loadWord amountWord) stagedDenominator .down
        depositAfterQuoteSlot <?>
      mulDiv (loadWord amountWord) stagedDenominator stagedAssetFactor .down
        depositAfterQuoteSlot))

def mint : Func :=
  arg 0 +++ mstoreAt amountWord +++
  arg 1 +++ mstoreAt receiverWord +++
  snapshotQuoteState (
    loadWord assetsWord +++ isMax +++
    (shiftedDiv (loadWord amountWord) stagedDenominator .up
        mintAfterQuoteSlot <?>
      mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator .up
        mintAfterQuoteSlot))

def ownerHasShares (shares : Line) (body : Func) : Func :=
  loadWord ownerWord +++ sload ::: mstoreAt balanceWord +++
  shares +++ loadWord balanceWord +++ lt :::
  (Func.revert <?> body)

def withdrawAfterQuote : Func :=
  mstoreAt quoteWord +++
  nonzeroCaller (nonzeroStagedAddress receiverWord (
  nonzeroStagedAddress ownerWord (
    ownerHasShares (loadWord quoteWord) (
      loadWord ownerWord +++ caller ::: eq :::
      (.call withdrawBurnSlot <?>
        spendAllowance (loadWord ownerWord) [caller] (loadWord quoteWord)
          withdrawBurnSlot)))))

def redeemAfterQuote : Func :=
  mstoreAt quoteWord +++
  nonzeroCaller (nonzeroStagedAddress receiverWord (
  nonzeroStagedAddress ownerWord (
    ownerHasShares (loadWord amountWord) (
      loadWord ownerWord +++ caller ::: eq :::
      (.call redeemBurnSlot <?>
        spendAllowance (loadWord ownerWord) [caller] (loadWord amountWord)
          redeemBurnSlot)))))

def withdraw : Func :=
  arg 0 +++ mstoreAt amountWord +++
  arg 1 +++ mstoreAt receiverWord +++
  arg 2 +++ mstoreAt ownerWord +++
  snapshotQuoteState (
    loadWord assetsWord +++ isMax +++
    (productOverTwoPow256 (loadWord amountWord) stagedDenominator .up
        withdrawAfterQuoteSlot <?>
      mulDiv (loadWord amountWord) stagedDenominator stagedAssetFactor .up
        withdrawAfterQuoteSlot))

def redeem : Func :=
  arg 0 +++ mstoreAt amountWord +++
  arg 1 +++ mstoreAt receiverWord +++
  arg 2 +++ mstoreAt ownerWord +++
  snapshotQuoteState (
    loadWord assetsWord +++ isMax +++
    (shiftedDiv (loadWord amountWord) stagedDenominator .down
        redeemAfterQuoteSlot <?>
      mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator .down
        redeemAfterQuoteSlot))

/-- Shared outbound tail: burn, WETH child, `Withdraw`, return. -/
def finishOutbound (shares assets returned : Line) : Func :=
  shares +++ loadWord balanceWord +++ sub :::
  loadWord ownerWord +++ sstore :::
  shares +++ loadWord supplyWord +++ lt :::
  (Func.revert <?>
    (shares +++ loadWord supplyWord +++ sub :::
      pushSupplySlot +++ sstore :::
      logBurnTransfer shares +++
      callWethTransfer (loadWord receiverWord) assets (
        logWithdraw assets shares +++
        returned +++ returnWord)))

def withdrawBurn : Func :=
  finishOutbound (loadWord quoteWord) (loadWord amountWord)
    (loadWord quoteWord)

def redeemBurn : Func :=
  finishOutbound (loadWord amountWord) (loadWord quoteWord)
    (loadWord quoteWord)

/-! ## Dispatch and program -/

def routed (words : Nat) (body : Func) : Func := endpoint words body

def vaultFuncs : List (B256 × Func) :=
  [ (selector "totalAssets" [], routed 0 totalAssets),
    (selector "name" [], routed 0 name),
    (selector "convertToAssets" [.uint256], routed 1 convertToAssets),
    (selector "approve" [.address, .uint256], routed 2 approve),
    (selector "previewWithdraw" [.uint256], routed 1 previewWithdraw),
    (selector "totalSupply" [], routed 0 totalSupply),
    (selector "transferFrom" [.address, .address, .uint256], routed 3 transferFrom),
    (selector "decimals" [], routed 0 decimals),
    (selector "asset" [], routed 0 asset),
    (selector "maxDeposit" [.address], routed 1 maxDeposit),
    (selector "previewRedeem" [.uint256], routed 1 previewRedeem),
    (selector "deposit" [.uint256, .address], routed 2 deposit),
    (selector "balanceOf" [.address], routed 1 balanceOf),
    (selector "mint" [.uint256, .address], routed 2 mint),
    (selector "symbol" [], routed 0 symbol),
    (selector "transfer" [.address, .uint256], routed 2 transfer),
    (selector "previewMint" [.uint256], routed 1 previewMint),
    (selector "withdraw" [.uint256, .address, .address], routed 3 withdraw),
    (selector "redeem" [.uint256, .address, .address], routed 3 redeem),
    (selector "maxMint" [.address], routed 1 maxMint),
    (selector "convertToShares" [.uint256], routed 1 convertToShares),
    (selector "maxWithdraw" [.address], routed 1 maxWithdraw),
    (selector "maxRedeem" [.address], routed 1 maxRedeem),
    (selector "allowance" [.address, .address], routed 2 allowance),
    (selector "previewDeposit" [.uint256], routed 1 previewDeposit) ]

theorem vaultFuncs_sorted : DispatchTree.sorted vaultFuncs = true := by
  decide +kernel

def vaultTree : DispatchTree := .ofSorted vaultFuncs

def vaultAux : List Func :=
  [ Func.revert,
    returnWord,
    depositAfterQuote,
    mintAfterQuote,
    withdrawAfterQuote,
    redeemAfterQuote,
    transferStaged,
    withdrawBurn,
    redeemBurn,
    maxMintAfterAssetCap ]

def vault : Prog := ⟨Func.mainWith revertSlot vaultTree, vaultAux⟩

end ProrataWethVault

end Blanc
