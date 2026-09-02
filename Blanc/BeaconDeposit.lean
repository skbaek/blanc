import Blanc.BeaconDepositCore

/-!
# Beacon deposit executable runtime

Blanc's compiled port of the pinned beacon deposit contract.  The pure model
in `BeaconDepositModel` remains the specification; this module owns only the
finite EVM program that implements the four-selector runtime.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## Stable auxiliary coordinates -/

def emptyRevertSlot : Nat := 1
def bubbleRevertSlot : Nat := 2
def pubkeyLengthErrorSlot : Nat := 3
def withdrawalLengthErrorSlot : Nat := 4
def signatureLengthErrorSlot : Nat := 5
def valueTooLowErrorSlot : Nat := 6
def valueNotGweiErrorSlot : Nat := 7
def valueTooHighErrorSlot : Nat := 8
def rootMismatchErrorSlot : Nat := 9
def treeFullErrorSlot : Nat := 10
def rootLoopSlot : Nat := 11
def rootContinuationSlot : Nat := 12
def insertionLoopSlot : Nat := 13
def insertionContinuationSlot : Nat := 14

/-! ## Runtime memory and byte helpers -/

def oldCountWord : B256 := 18
def shiftedSizeWord : B256 := 19
def nodeWord : B256 := 20
def amountWord : B256 := 21
def intermediateWord : B256 := 22
def secondIntermediateWord : B256 := 23

private def abi32Limit : B256 := Nat.toB256 (2 ^ 32)

def loadWord (word : B256) : Line :=
  [pushB256 (word * 32), mload]

/-- Consume one word and write its low 64 bits in little-endian byte order. -/
def storeLe64At (base : B256) : Line :=
  [ dup 0, pushB256 base, mstore8, pushB256 8, shr,
    dup 0, pushB256 (base + 1), mstore8, pushB256 8, shr,
    dup 0, pushB256 (base + 2), mstore8, pushB256 8, shr,
    dup 0, pushB256 (base + 3), mstore8, pushB256 8, shr,
    dup 0, pushB256 (base + 4), mstore8, pushB256 8, shr,
    dup 0, pushB256 (base + 5), mstore8, pushB256 8, shr,
    dup 0, pushB256 (base + 6), mstore8, pushB256 8, shr,
    pushB256 (base + 7), mstore8 ]

/-- Copy a fixed payload slice using an already validated dynamic offset.
`offsetWord` is a word index; `delta`, `destination`, and `size` are bytes. -/
def copyDynamicPayload
    (offsetWord delta destination size : B256) : Line :=
  [pushB256 size] ++ loadWord offsetWord ++
    [ pushB256 (36 + delta), add,
      pushB256 destination, calldatacopy ]

/-- The pinned solc dynamic-`bytes` boundary for one argument.  On success it
stores the offset and length in the nominated memory words and restores the
incoming stack. -/
def validateDynamicTail
    (head offsetWord lengthWord : B256) (body : Func) : Func :=
  let accept : Func :=
    mstoreAt lengthWord +++ mstoreAt offsetWord +++ body
  let checkPaddedEnd : Func :=
    dup 0 ::: pushB256 31 ::: add :::
    pushB256 31 ::: Ninst.not ::: Ninst.and :::
    dup 2 ::: add ::: pushB256 36 ::: add :::
    calldatasize ::: lt :::
    ((.call emptyRevertSlot) <?> accept)
  let checkLength : Func :=
    dup 0 ::: pushB256 abi32Limit ::: swap 0 ::: lt ::: iszero :::
    ((.call emptyRevertSlot) <?> checkPaddedEnd)
  let loadLength : Func :=
    dup 0 ::: pushB256 4 ::: add ::: calldataload ::: checkLength
  let checkLengthWord : Func :=
    dup 0 ::: pushB256 36 ::: add ::: calldatasize ::: lt :::
    ((.call emptyRevertSlot) <?> loadLength)
  arg head +++
    dup 0 ::: pushB256 abi32Limit ::: swap 0 ::: lt ::: iszero :::
    ((.call emptyRevertSlot) <?> checkLengthWord)

/-- Validate the complete four-word head and all three dynamic tails before
entering any source-level deposit guard. -/
def validateDepositAbi (body : Func) : Func :=
  let decoded :=
    validateDynamicTail 0 0 3
      (validateDynamicTail 1 1 4
        (validateDynamicTail 2 2 5 body))
  pushB256 132 ::: calldatasize ::: lt :::
  ((.call emptyRevertSlot) <?> decoded)

/-! ## Source-shaped SHA-256 wrapper -/

/-- Hash the 64-byte memory window beginning at `inputWord` through precompile
address `0x2`, writing the first returned word at `outputWord`. A zero status
bubbles the complete returndata; a successful response shorter than 32 bytes
empty-reverts; longer successful responses are accepted exactly as Solidity's
`bytes32` decoder accepts them. -/
def sha64 (inputWord outputWord : B256) (success : Func) : Func :=
  pushList [32, outputWord * 32, 64, inputWord * 32, 2] +++
  gas ::: staticcall ::: iszero :::
  ((.call bubbleRevertSlot) <?>
    (returnDataShorterThan 32 +++
      ((.call emptyRevertSlot) <?> success)))

/-! ## Revert auxiliaries -/

def pubkeyLengthError : Func :=
  Func.revertWith (reasonString .pubkey_length)
def withdrawalLengthError : Func :=
  Func.revertWith (reasonString .withdrawal_credentials_length)
def signatureLengthError : Func :=
  Func.revertWith (reasonString .signature_length)
def valueTooLowError : Func :=
  Func.revertWith (reasonString .value_too_low)
def valueNotGweiError : Func :=
  Func.revertWith (reasonString .value_not_gwei_multiple)
def valueTooHighError : Func :=
  Func.revertWith (reasonString .value_too_high)
def rootMismatchError : Func :=
  Func.revertWith (reasonString .deposit_data_root_mismatch)
def treeFullError : Func :=
  Func.revertWith (reasonString .merkle_tree_full)

/-! ## ERC-165 and count views -/

def supportsInterfaceEndpoint : Func :=
  pushB256 36 ::: calldatasize ::: lt :::
  (Func.revert <?>
    (arg 0 +++ pushB256 224 ::: shr :::
      dup 0 ::: pushB256 erc165InterfaceId ::: eq ::: swap 0 :::
      pushB256 depositInterfaceId ::: eq ::: Ninst.or :::
      mstoreAt 0 +++ returnMemoryRange 0 32))

def getDepositCountEndpoint : Func :=
  pushB256 32 ::: mstoreAt 0 +++
  pushB256 8 ::: mstoreAt 1 +++
  pushB256 0 ::: mstoreAt 2 +++
  pushB256 depositCountSlot ::: sload ::: storeLe64At 64 +++
  returnMemoryRange 0 96

/-! ## Root fold -/

def rootFinish : Func :=
  pop :::
  loadWord nodeWord +++ mstoreAt 0 +++
  pushB256 0 ::: mstoreAt 1 +++
  loadWord oldCountWord +++ storeLe64At 32 +++
  sha64 0 nodeWord
    (loadWord nodeWord +++ mstoreAt 0 +++ returnMemoryRange 0 32)

def rootLiveStep : Func :=
  dup 0 ::: pushB256 branchBase ::: add ::: sload ::: mstoreAt 0 +++
  loadWord nodeWord +++ mstoreAt 1 +++
  sha64 0 nodeWord (.call rootContinuationSlot)

def rootDeadStep : Func :=
  loadWord nodeWord +++ mstoreAt 0 +++
  dup 0 ::: pushB256 zeroHashBase ::: add ::: sload ::: mstoreAt 1 +++
  sha64 0 nodeWord (.call rootContinuationSlot)

def rootLoop : Func :=
  dup 0 ::: pushB256 32 ::: swap 0 ::: lt :::
  ((loadWord shiftedSizeWord +++ pushB256 1 ::: Ninst.and :::
      (rootLiveStep <?> rootDeadStep)) <?>
    rootFinish)

def rootContinuation : Func :=
  loadWord shiftedSizeWord +++ pushB256 1 ::: shr :::
  mstoreAt shiftedSizeWord +++
  pushB256 1 ::: add ::: .call rootLoopSlot

def getDepositRootEndpoint : Func :=
  pushB256 depositCountSlot ::: sload ::: dup 0 :::
  mstoreAt oldCountWord +++ mstoreAt shiftedSizeWord +++
  pushB256 0 ::: mstoreAt nodeWord +++
  pushB256 0 ::: .call rootLoopSlot

/-! ## Deposit event and data-root reconstruction -/

/-- Stage and emit the exact 576-byte five-tail `DepositEvent`. The three
validated payloads are copied before their decoder temporaries in words `0..5`
are overwritten. The old count is retained in word `18`. -/
def stageDepositEvent : Line :=
  [pushB256 0] ++ mstoreAt 7 ++
  copyDynamicPayload 0 0 192 48 ++
  copyDynamicPayload 1 0 288 32 ++
  copyDynamicPayload 2 0 416 96 ++
  [pushB256 160] ++ mstoreAt 0 ++
  [pushB256 256] ++ mstoreAt 1 ++
  [pushB256 320] ++ mstoreAt 2 ++
  [pushB256 384] ++ mstoreAt 3 ++
  [pushB256 512] ++ mstoreAt 4 ++
  [pushB256 48] ++ mstoreAt 5 ++
  [pushB256 32] ++ mstoreAt 8 ++
  [pushB256 8] ++ mstoreAt 10 ++
  [pushB256 0] ++ mstoreAt 11 ++
  loadWord amountWord ++ storeLe64At 352 ++
  [pushB256 96] ++ mstoreAt 12 ++
  [pushB256 8] ++ mstoreAt 16 ++
  [pushB256 0] ++ mstoreAt 17 ++
  [pushB256 depositCountSlot, sload, dup 0] ++
  mstoreAt oldCountWord ++ storeLe64At 544 ++
  [pushB256 depositEventTopic] ++ logWith 0 0 18

/-- Reconstruct the deposit-data node through the seven distinct source-shaped
SHA-256 sites, leaving the result in `nodeWord` before `success`. -/
def reconstructDepositDataNode (success : Func) : Func :=
  let finish :=
    loadWord nodeWord +++ mstoreAt 0 +++
    loadWord intermediateWord +++ mstoreAt 1 +++
    sha64 0 nodeWord success
  let amountAndSignature :=
    loadWord 11 +++ mstoreAt 0 +++
    loadWord intermediateWord +++ mstoreAt 1 +++
    sha64 0 intermediateWord finish
  let pubkeyAndWithdrawal :=
    loadWord nodeWord +++ mstoreAt 0 +++
    loadWord 9 +++ mstoreAt 1 +++
    sha64 0 nodeWord amountAndSignature
  let signatureRoot :=
    loadWord intermediateWord +++ mstoreAt 0 +++
    loadWord secondIntermediateWord +++ mstoreAt 1 +++
    sha64 0 intermediateWord pubkeyAndWithdrawal
  let signatureSecondHalf :=
    loadWord 15 +++ mstoreAt 0 +++
    pushB256 0 ::: mstoreAt 1 +++
    sha64 0 secondIntermediateWord signatureRoot
  sha64 6 nodeWord
    (sha64 13 intermediateWord signatureSecondHalf)

/-! ## Deposit insertion walk -/

def insertionLive : Func :=
  dup 0 ::: pushB256 branchBase ::: add :::
  loadWord nodeWord +++ swap 0 ::: sstore :::
  pop ::: Func.stop

def insertionDead : Func :=
  dup 0 ::: pushB256 branchBase ::: add ::: sload ::: mstoreAt 0 +++
  loadWord nodeWord +++ mstoreAt 1 +++
  sha64 0 nodeWord (.call insertionContinuationSlot)

/-- The cap guard and `deposit_ne_assert_false` ensure that a live bit is
reached within 32 shifts, so no compiled terminal assert arm is needed. -/
def insertionLoop : Func :=
  loadWord shiftedSizeWord +++ pushB256 1 ::: Ninst.and :::
  (insertionLive <?> insertionDead)

def insertionContinuation : Func :=
  loadWord shiftedSizeWord +++ pushB256 1 ::: shr :::
  mstoreAt shiftedSizeWord +++
  pushB256 1 ::: add ::: .call insertionLoopSlot

def commitDeposit : Func :=
  loadWord oldCountWord +++ pushB256 1 ::: add ::: dup 0 :::
  mstoreAt shiftedSizeWord +++
  pushB256 depositCountSlot ::: sstore :::
  pushB256 0 ::: .call insertionLoopSlot

/-! ## Deposit guards and endpoint -/

def depositAfterEvent : Func :=
  let afterCap := commitDeposit
  let checkCap :=
    pushB256 (Nat.toB256 (2 ^ 32 - 1)) :::
    loadWord oldCountWord +++ lt ::: iszero :::
    ((.call treeFullErrorSlot) <?> afterCap)
  let checkRoot :=
    loadWord nodeWord +++ arg 3 +++ eq ::: iszero :::
    ((.call rootMismatchErrorSlot) <?> checkCap)
  reconstructDepositDataNode checkRoot

def depositBody : Func :=
  let afterGuards := stageDepositEvent +++ depositAfterEvent
  let checkAmountUpper :=
    pushB256 (Nat.toB256 oneGwei) ::: callvalue ::: div ::: dup 0 :::
    mstoreAt amountWord +++
    pushB256 (Nat.toB256 (2 ^ 64 - 1)) ::: lt :::
    ((.call valueTooHighErrorSlot) <?> afterGuards)
  let checkGweiMultiple :=
    pushB256 (Nat.toB256 oneGwei) ::: callvalue ::: mod :::
    ((.call valueNotGweiErrorSlot) <?> checkAmountUpper)
  let checkValueLower :=
    pushB256 (Nat.toB256 oneEther) ::: callvalue ::: lt :::
    ((.call valueTooLowErrorSlot) <?> checkGweiMultiple)
  let checkSignatureLength :=
    loadWord 5 +++ pushB256 96 ::: eq ::: iszero :::
    ((.call signatureLengthErrorSlot) <?> checkValueLower)
  let checkWithdrawalLength :=
    loadWord 4 +++ pushB256 32 ::: eq ::: iszero :::
    ((.call withdrawalLengthErrorSlot) <?> checkSignatureLength)
  loadWord 3 +++ pushB256 48 ::: eq ::: iszero :::
  ((.call pubkeyLengthErrorSlot) <?> checkWithdrawalLength)

def depositEndpoint : Func := validateDepositAbi depositBody

/-! ## Complete four-selector runtime -/

def nonpayableEndpoint (body : Func) : Func :=
  callvalue ::: (Func.revert <?> body)

def funcs : List (B256 × Func) :=
  [ (supportsInterfaceSelector, nonpayableEndpoint supportsInterfaceEndpoint),
    (depositSelector, depositEndpoint),
    (getDepositCountSelector, nonpayableEndpoint getDepositCountEndpoint),
    (getDepositRootSelector, nonpayableEndpoint getDepositRootEndpoint) ]

theorem funcs_sorted : DispatchTree.sorted funcs = true := by
  decide +kernel

def tree : DispatchTree :=
  .fork
    (.leaf supportsInterfaceSelector
      (nonpayableEndpoint supportsInterfaceEndpoint))
    (.fork
      (.leaf depositSelector depositEndpoint)
      (.fork
        (.leaf getDepositCountSelector
          (nonpayableEndpoint getDepositCountEndpoint))
        (.leaf getDepositRootSelector
          (nonpayableEndpoint getDepositRootEndpoint))))

theorem tree_funcs_exact :
    tree =
      .fork
        (.leaf supportsInterfaceSelector
          (nonpayableEndpoint supportsInterfaceEndpoint))
        (.fork
          (.leaf depositSelector depositEndpoint)
          (.fork
            (.leaf getDepositCountSelector
              (nonpayableEndpoint getDepositCountEndpoint))
            (.leaf getDepositRootSelector
              (nonpayableEndpoint getDepositRootEndpoint)))) ∧
    funcs =
      [ (supportsInterfaceSelector,
          nonpayableEndpoint supportsInterfaceEndpoint),
        (depositSelector, depositEndpoint),
        (getDepositCountSelector,
          nonpayableEndpoint getDepositCountEndpoint),
        (getDepositRootSelector,
          nonpayableEndpoint getDepositRootEndpoint) ] := by
  exact ⟨rfl, rfl⟩

def aux : List Func :=
  [ Func.revert,
    Func.revertReturnData,
    pubkeyLengthError,
    withdrawalLengthError,
    signatureLengthError,
    valueTooLowError,
    valueNotGweiError,
    valueTooHighError,
    rootMismatchError,
    treeFullError,
    rootLoop,
    rootContinuation,
    insertionLoop,
    insertionContinuation ]

def runtime : Prog :=
  ⟨calldatasize ::: (Func.main tree <?> Func.revert), aux⟩

end Blanc.BeaconDeposit
