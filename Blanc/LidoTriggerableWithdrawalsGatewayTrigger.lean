import Blanc.LidoTriggerableWithdrawalsGatewayCore

/-!
# Triggerable Withdrawals Gateway: `triggerFullWithdrawals`

This sibling-family module owns the previously missing executable packet for

```
triggerFullWithdrawals((uint256,uint256,bytes)[],address,uint256)
```

It imports only the shared TWG core.  The packet is deliberately separate from
the current dispatcher so that the final runtime integration can rebase its
local auxiliary slots in one place.

The calldata walk follows Solidity 0.8.9's relevant decoder boundary:

* top-level heads and the dynamic-array offset table are checked on entry;
* nested tuple/pubkey validation occurs when the source first indexes
  every `pubkey`, after its modifiers, quota consumption, and fee lookup;
* every dynamic offset and length is bounded by `uint64.max`, and every head,
  offset table, tuple head, bytes length word, and bytes payload is checked
  against `CALLDATASIZE` before it is read or copied;
* offsets need not be canonical, aligned, disjoint, or ordered, and trailing
  calldata is accepted;
* the address head must be clean;
* `pubkey` is treated as arbitrary `bytes`.  The pinned source documents 48
  bytes but never checks that length, so this packet does not invent one.

Two named integration seams are kept explicit:

* `coreFlatRoleGuard` is the concrete one-read nested-keccak membership guard.
  Its failure continuation is supplied by the caller because the
  pinned AccessControl source builds a dynamic `Error(string)` while the
  current family runtime owns a different role-error policy.
* `consumeExitRequestLimit` is the concrete quota continuation over Core's
  packed five-`uint32` limit word.  Its success and error continuations are
  explicit.

All other reverts in the packet are executable and payload-exact: the two
`ZeroArgument(string)` values, `ResumedExpected()`,
`ExitRequestsLimitExceeded(uint256,uint256)`,
`InsufficientFee(uint256,uint256)`, `FeeRefundFailed()`, Solidity arithmetic
and assertion panics, empty ABI-decoder failures, and bubbled external-call
revert data.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoTriggerableWithdrawalsGateway
namespace Trigger

/-! ## Local auxiliary-table contract -/

/-! Slot zero is the packet main function.  Every other number is local to the
standalone packet and must be offset when these functions are appended to a
larger runtime table. -/
def malformedAbiSlot : Nat := 1
def zeroMsgValueSlot : Nat := 2
def zeroValidatorsDataSlot : Nat := 3
def resumedExpectedSlot : Nat := 4
def exitLimitExceededSlot : Nat := 5
def insufficientFeeSlot : Nat := 6
def feeRefundFailedSlot : Nat := 7
def arithmeticPanicSlot : Nat := 8
def divisionPanicSlot : Nat := 9
def assertionPanicSlot : Nat := 10
def roleFailureBoundarySlot : Nat := 11
def validateArrayLoopSlot : Nat := 12
def afterValidationSlot : Nat := 13
def consumeQuotaSlot : Nat := 14
def afterQuotaSlot : Nat := 15
def encodeArraysLoopSlot : Nat := 16
def afterEncodingSlot : Nat := 17
def bubbleRevertSlot : Nat := 18
def afterVaultCallSlot : Nat := 19
def refundCallSlot : Nat := 20
def balanceCheckSlot : Nat := 21
def afterNestedValidationSlot : Nat := 22

def localAuxSlotCount : Nat := 22

/-! ## Fixed scratch-memory words

Word zero is intentionally reserved for selectors and 32-byte returndata.
The dynamic ABI images begin at byte `0x1000`, leaving the fixed scratch area
disjoint even when this packet grows. -/

def calldataSizeWord : B256 := 1
def validatorsOffsetWord : B256 := 2
def arrayLengthPtrWord : B256 := 3
def arrayElementsBaseWord : B256 := 4
def requestsCountWord : B256 := 5
def refundRecipientWord : B256 := 6
def exitTypeWord : B256 := 7
def loopIndexWord : B256 := 8
def elementOffsetWord : B256 := 9
def elementBaseWord : B256 := 10
def pubkeyOffsetWord : B256 := 11
def pubkeyLengthPtrWord : B256 := 12
def pubkeyLengthWord : B256 := 13
def pubkeyPayloadWord : B256 := 14
def paddedPubkeyLengthWord : B256 := 15
def pubkeysTailBytesWord : B256 := 16
def routerTupleBytesWord : B256 := 17
def balanceBeforeWord : B256 := 18
def currentLimitWord : B256 := 19
def secondsPassedWord : B256 := 20
def framesPassedWord : B256 := 21
def restoredLimitWord : B256 := 22
def withdrawalVaultWord : B256 := 23
def feeWord : B256 := 24
def totalFeeWord : B256 := 25
def refundWord : B256 := 26
def vaultSelectorPtrWord : B256 := 27
def pubkeysBaseWord : B256 := 28
def pubkeysSizeWord : B256 := 29
def amountsBaseWord : B256 := 30
def amountsSizeWord : B256 := 31
def vaultCallSizeWord : B256 := 32
def vaultTailCursorWord : B256 := 33
def routerSelectorPtrWord : B256 := 34
def routerArrayBaseWord : B256 := 35
def routerArraySizeWord : B256 := 36
def routerCallSizeWord : B256 := 37
def routerTupleCursorWord : B256 := 38
def stakingRouterWord : B256 := 39
def roundedPassedTimeWord : B256 := 40
def maximumLimitWord : B256 := 41
def previousLimitWord : B256 := 42
def previousTimestampWord : B256 := 43
def frameDurationWord : B256 := 44
def exitsPerFrameWord : B256 := 45
def packedLimitWord : B256 := 46

def dynamicMemoryBase : B256 := 0x1000
def maxUint64 : B256 := 0xffffffffffffffff
def maxUint32 : B256 := 0xffffffff

/-! ## Instruction and memory helpers -/

/-- A fixed-width immutable word.  Unlike `pushB256`, its instruction width is
independent of the deployed locator's leading bytes. -/
def pushImmutableWord (word : B256) : Ninst :=
  Ninst.push word.toBytes (by rw [B256.length_toBytes])

def loadWord (word : B256) : Line :=
  [pushB256 (word * 32), mload]

def storeWord (word : B256) : Line :=
  mstoreAt word

def loadPackedLimit : Line :=
  [pushB256 twrLimitPosition, sload] ++ storeWord packedLimitWord ++
  unpackUint32Lane packedLimitWord maximumLimitWord 0 ++
  unpackUint32Lane packedLimitWord previousLimitWord 32 ++
  unpackUint32Lane packedLimitWord previousTimestampWord 64 ++
  unpackUint32Lane packedLimitWord frameDurationWord 96 ++
  unpackUint32Lane packedLimitWord exitsPerFrameWord 128

def storePackedLimit : Line :=
  packFiveUint32Words maximumLimitWord previousLimitWord
    previousTimestampWord frameDurationWord exitsPerFrameWord ++
  [pushB256 twrLimitPosition, sstore]

def mstoreByteAt (offset : B256) : Line :=
  [pushB256 offset, mstore]

/-- Store the value on top of the stack at the byte pointer held in `ptrWord`. -/
def mstoreAtPtr (ptrWord : B256) : Line :=
  loadWord ptrWord ++ [mstore]

/-- Store the value on top of the stack `delta` bytes past a scratch pointer. -/
def mstoreAtPtrPlus (ptrWord delta : B256) : Line :=
  loadWord ptrWord ++ [pushB256 delta, add, mstore]

def calldataloadAt (ptrWord : B256) : Line :=
  loadWord ptrWord ++ [calldataload]

def calldataloadAtPlus (ptrWord delta : B256) : Line :=
  loadWord ptrWord ++ [pushB256 delta, add, calldataload]

def copyReturndataWord : Line :=
  pushList [32, 0, 0] ++ [returndatacopy]

def storeSelectorAtZero (sel : B256) : Line :=
  pushB256 sel :: mstoreAt 0

/-! ## Selectors and revert payloads -/

def withdrawalVaultSelector : B256 := rawSelector "withdrawalVault()"
def stakingRouterSelector : B256 := rawSelector "stakingRouter()"
def withdrawalRequestFeeSelector : B256 :=
  rawSelector "getWithdrawalRequestFee()"
def addWithdrawalRequestsSelector : B256 :=
  rawSelector "addWithdrawalRequests(bytes[],uint64[])"
def validatorExitTriggeredSelector : B256 :=
  rawSelector
    "onValidatorExitTriggered((uint256,uint256,bytes)[],uint256,uint256)"

def zeroArgumentSelector : B256 := 0x56e42893
def insufficientFeeSelector : B256 := 0xa458261b
def feeRefundFailedSelector : B256 := 0x7f832e95
def exitLimitExceededSelector : B256 := 0x83432d28
def resumedExpectedSelector : B256 := 0x14378398

/-- ABI data for the pinned custom error `ZeroArgument(string)`. -/
def zeroArgumentData (argumentName : String) : Bytes :=
  let data := Blanc.String.toBytes argumentName
  let pad := (32 - data.length % 32) % 32
  zeroArgumentSelector.toBytes.drop 28 ++
    (32 : B256).toBytes ++
    (Nat.toB256 data.length).toBytes ++
    data ++ List.replicate pad 0

def panicData (code : B256) : Bytes :=
  (signatureHash "Panic" [.uint256]).toBytes.take 4 ++ code.toBytes

def selectorRevert (sel : B256) : Func :=
  Func.revertSelector (sel.toBytes.drop 28) (by
    simp [B256.length_toBytes])

def zeroMsgValueRevert : Func :=
  Func.revertData (zeroArgumentData "msg.value")

def zeroValidatorsDataRevert : Func :=
  Func.revertData (zeroArgumentData "validatorsData")

def resumedExpectedRevert : Func :=
  selectorRevert resumedExpectedSelector

def feeRefundFailedRevert : Func :=
  selectorRevert feeRefundFailedSelector

def arithmeticPanicRevert : Func := Func.revertData (panicData 0x11)
def divisionPanicRevert : Func := Func.revertData (panicData 0x12)
def assertionPanicRevert : Func := Func.revertData (panicData 0x01)

/-- `InsufficientFee(totalFee, msg.value)`, with the selector occupying the
four bytes immediately before the two argument words. -/
def insufficientFeeRevert : Func :=
  pushB256 insufficientFeeSelector ::: mstoreAt 0 +++
  loadWord totalFeeWord +++ mstoreAt 1 +++
  callvalue ::: mstoreAt 2 +++
  pushB256 68 ::: pushB256 28 ::: .last .revert

/-- `ExitRequestsLimitExceeded(requestsCount, currentLimit)`. -/
def exitLimitExceededRevert : Func :=
  pushB256 exitLimitExceededSelector ::: mstoreAt 0 +++
  loadWord requestsCountWord +++ mstoreAt 1 +++
  loadWord currentLimitWord +++ mstoreAt 2 +++
  pushB256 68 ::: pushB256 28 ::: .last .revert

/-- Bubble the complete returndata of a failed high-level external call. -/
def bubbleRevert : Func :=
  returndatasize ::: dup 0 ::: pushB256 0 ::: pushB256 0 ::: returndatacopy :::
  pushB256 0 ::: .last .revert

/-! ## Exact calldata validation -/

/-- Recompute the current tuple and pubkey pointers after the validator has
established their safety.  The encode loop uses this same projection, so no
side table can drift from the data that was validated. -/
def loadCurrentElement : Line :=
  loadWord loopIndexWord ++ [pushB256 32, mul] ++
  loadWord arrayElementsBaseWord ++ [add, calldataload] ++
    storeWord elementOffsetWord ++
  loadWord arrayElementsBaseWord ++ loadWord elementOffsetWord ++ [add] ++
    storeWord elementBaseWord ++
  calldataloadAtPlus elementBaseWord 64 ++ storeWord pubkeyOffsetWord ++
  loadWord elementBaseWord ++ loadWord pubkeyOffsetWord ++ [add] ++
    storeWord pubkeyLengthPtrWord ++
  calldataloadAt pubkeyLengthPtrWord ++ storeWord pubkeyLengthWord ++
  loadWord pubkeyLengthPtrWord ++ [pushB256 32, add] ++
    storeWord pubkeyPayloadWord ++
  loadWord pubkeyLengthWord ++ [pushB256 31, add, pushB256 31, not, and] ++
    storeWord paddedPubkeyLengthWord

/-- Validate one dynamic tuple, accumulate the two canonical output sizes, and
tail-call the loop. -/
def validateArrayElement : Func :=
  -- elementOffset := calldata[arrayElementsBase + 32*i]
  loadWord loopIndexWord +++ pushB256 32 ::: mul :::
  loadWord arrayElementsBaseWord +++ add ::: calldataload :::
    storeWord elementOffsetWord +++
  -- Solidity's calldata decoder rejects dynamic offsets above uint64.max.
  pushB256 maxUint64 ::: loadWord elementOffsetWord +++ gt :::
  ((.call malformedAbiSlot) <?>
    (loadWord arrayElementsBaseWord +++ loadWord elementOffsetWord +++ add :::
       storeWord elementBaseWord +++
     -- A tuple has three head words.
     loadWord elementBaseWord +++ pushB256 96 ::: add :::
       loadWord calldataSizeWord +++ lt :::
     ((.call malformedAbiSlot) <?>
       (calldataloadAtPlus elementBaseWord 64 +++
          storeWord pubkeyOffsetWord +++
        pushB256 maxUint64 ::: loadWord pubkeyOffsetWord +++ gt :::
        ((.call malformedAbiSlot) <?>
          (loadWord elementBaseWord +++ loadWord pubkeyOffsetWord +++ add :::
             storeWord pubkeyLengthPtrWord +++
           -- The dynamic bytes length word must be present.
           loadWord pubkeyLengthPtrWord +++ pushB256 32 ::: add :::
             loadWord calldataSizeWord +++ lt :::
           ((.call malformedAbiSlot) <?>
             (calldataloadAt pubkeyLengthPtrWord +++
                storeWord pubkeyLengthWord +++
              pushB256 maxUint64 ::: loadWord pubkeyLengthWord +++ gt :::
              ((.call malformedAbiSlot) <?>
                (loadWord pubkeyLengthPtrWord +++ pushB256 32 ::: add :::
                   storeWord pubkeyPayloadWord +++
                 -- The source accepts every byte length that fits calldata;
                 -- there is intentionally no `length == 48` branch here.
                 loadWord pubkeyPayloadWord +++ loadWord pubkeyLengthWord +++
                   add ::: loadWord calldataSizeWord +++ lt :::
                 ((.call malformedAbiSlot) <?>
                   (loadWord pubkeyLengthWord +++ pushB256 31 ::: add :::
                      pushB256 31 ::: not ::: and :::
                      storeWord paddedPubkeyLengthWord +++
                    -- bytes[] needs length+payload; the router tuple needs
                    -- three heads plus the bytes length+payload.
                    loadWord pubkeysTailBytesWord +++ pushB256 32 :::
                      loadWord paddedPubkeyLengthWord +++ add ::: add :::
                      storeWord pubkeysTailBytesWord +++
                    loadWord routerTupleBytesWord +++ pushB256 128 :::
                      loadWord paddedPubkeyLengthWord +++ add ::: add :::
                      storeWord routerTupleBytesWord +++
                    loadWord loopIndexWord +++ pushB256 1 ::: add :::
                      storeWord loopIndexWord +++
                    .call validateArrayLoopSlot))))))))))))

def validateArrayLoop : Func :=
  loadWord requestsCountWord +++ loadWord loopIndexWord +++ lt :::
    (validateArrayElement <?> .call afterNestedValidationSlot)

/-- Decode the three top-level heads and validate the array offset table.
Nested element validation is deliberately performed in the source's pubkey
extraction phase.  `100 = 4 + 3*32` includes the selector. -/
def validateCalldata : Func :=
  pushB256 100 ::: calldatasize ::: lt :::
  ((.call malformedAbiSlot) <?>
    (calldatasize ::: storeWord calldataSizeWord +++
     -- Address decoding is strict about dirty high bits.
     arg 1 +++ checkNonAddress +++
     ((.call malformedAbiSlot) <?>
       (arg 1 +++ storeWord refundRecipientWord +++
        arg 2 +++ storeWord exitTypeWord +++
        -- Dynamic offsets and lengths use the uint64-bounded decoder path.
        pushB256 maxUint64 ::: arg 0 +++ gt :::
        ((.call malformedAbiSlot) <?>
          (arg 0 +++ storeWord validatorsOffsetWord +++
           arg 0 +++ pushB256 4 ::: add ::: storeWord arrayLengthPtrWord +++
           loadWord arrayLengthPtrWord +++ pushB256 32 ::: add :::
             loadWord calldataSizeWord +++ lt :::
           ((.call malformedAbiSlot) <?>
             (calldataloadAt arrayLengthPtrWord +++
                storeWord requestsCountWord +++
              pushB256 maxUint64 ::: loadWord requestsCountWord +++ gt :::
              ((.call malformedAbiSlot) <?>
                (loadWord arrayLengthPtrWord +++ pushB256 32 ::: add :::
                   storeWord arrayElementsBaseWord +++
                 loadWord arrayElementsBaseWord +++
                   loadWord requestsCountWord +++ pushB256 32 ::: mul ::: add :::
                   loadWord calldataSizeWord +++ lt :::
                 ((.call malformedAbiSlot) <?>
                   (pushB256 0 ::: storeWord loopIndexWord +++
                    pushB256 0 ::: storeWord pubkeysTailBytesWord +++
                    pushB256 0 ::: storeWord routerTupleBytesWord +++
                    .call afterValidationSlot))))))))))))

/-! ## Modifier and quota integration seams -/

/-- One-read nested-keccak role gate.  `onFailure` is the explicit compact
AccessControl error-policy boundary retained by the Blanc artifact. -/
def coreFlatRoleGuard (onFailure onAuthorized : Func) : Func :=
  roleMembershipSlotFrom [pushB256 addFullWithdrawalRequestRole] [caller] +++
    sload ::: iszero ::: (onFailure <?> onAuthorized)

/-- Consume a previously computed `currentLimitWord`, update the two mutable
quota projections, and continue. -/
def consumeComputedLimit (onConsumed : Func) : Func :=
  -- if currentLimit < requestsCount, report both exact values
  loadWord requestsCountWord +++ loadWord currentLimitWord +++ lt :::
  ((.call exitLimitExceededSlot) <?>
    (-- `updatePrevExitLimit` performs `% frameDuration` only after the
     -- insufficient-limit check above.
     loadWord frameDurationWord +++ iszero :::
     ((.call divisionPanicSlot) <?>
       (loadWord requestsCountWord +++ loadWord currentLimitWord +++ sub :::
          storeWord previousLimitWord +++
        -- passedTime -= passedTime % frameDuration
        loadWord frameDurationWord +++
          loadWord secondsPassedWord +++ mod :::
          loadWord secondsPassedWord +++ sub :::
          pushB256 maxUint32 ::: and ::: storeWord roundedPassedTimeWord +++
        -- `uint32 prevTimestamp += uint32(passedTime)` is checked in 0.8.9.
        loadWord previousTimestampWord +++
          loadWord roundedPassedTimeWord +++ add :::
          dup 0 ::: pushB256 maxUint32 ::: swap 0 ::: gt :::
        ((.call arithmeticPanicSlot) <?>
          (storeWord previousTimestampWord +++ storePackedLimit +++ onConsumed))))))

/-- The restored-limit arm of `calculateCurrentExitLimit`, including Solidity
0.8 checked multiplication and addition. -/
def consumeRestoredLimit (onConsumed : Func) : Func :=
  loadWord frameDurationWord +++
    loadWord secondsPassedWord +++ div ::: storeWord framesPassedWord +++
  loadWord exitsPerFrameWord +++ loadWord framesPassedWord +++ mul :::
    storeWord restoredLimitWord +++
  -- restored / frames must recover exitsPerFrame (frames is nonzero here)
  loadWord framesPassedWord +++ loadWord restoredLimitWord +++ div :::
    loadWord exitsPerFrameWord +++ eq ::: iszero :::
  ((.call arithmeticPanicSlot) <?>
    (loadWord previousLimitWord +++
       loadWord restoredLimitWord +++ add ::: storeWord currentLimitWord +++
     -- wrapped addition is Solidity Panic(0x11)
     loadWord previousLimitWord +++
       loadWord currentLimitWord +++ lt :::
     ((.call arithmeticPanicSlot) <?>
       (loadWord maximumLimitWord +++
          loadWord currentLimitWord +++ gt :::
        ((loadWord maximumLimitWord +++
            storeWord currentLimitWord +++ consumeComputedLimit onConsumed)
          <?> consumeComputedLimit onConsumed)))))

/-- Concrete `ExitLimitUtils` continuation over Core's packed fields.  The
unlimited `max == 0` arm performs no quota write. -/
def consumeExitRequestLimit (onConsumed : Func) : Func :=
  loadPackedLimit +++ loadWord maximumLimitWord +++ iszero :::
  (onConsumed <?>
    (-- timestamp - prevTimestamp is checked by Solidity
     loadWord previousTimestampWord +++ timestamp ::: lt :::
     ((.call arithmeticPanicSlot) <?>
       (loadWord previousTimestampWord +++ timestamp ::: sub :::
          storeWord secondsPassedWord +++
        loadWord frameDurationWord +++
          loadWord secondsPassedWord +++ lt :::
        loadWord exitsPerFrameWord +++ iszero ::: or :::
        ((loadWord previousLimitWord +++
            storeWord currentLimitWord +++ consumeComputedLimit onConsumed)
          <?>
          (-- The false arm has nonzero exits; a zero frame therefore reaches
           -- Solidity's checked division-by-zero panic.
           loadWord frameDurationWord +++ iszero :::
           ((.call divisionPanicSlot) <?>
             consumeRestoredLimit onConsumed)))))))

/-! ## Canonical outgoing encoders -/

/-- Initialize both outgoing ABI images after the fee is known.

The vault image comes first.  Its end is word-aligned and becomes the selector
word for the router image, so the two variable-size encodings cannot overlap. -/
def initializeOutgoingMemory : Line :=
  -- bytes[] size = length + offset table + each bytes tail
  pushB256 32 :: loadWord requestsCountWord ++ [pushB256 32, mul, add] ++
    loadWord pubkeysTailBytesWord ++ [add] ++ storeWord pubkeysSizeWord ++
  -- uint64[] is an all-zero word array
  pushB256 32 :: loadWord requestsCountWord ++ [pushB256 32, mul, add] ++
    storeWord amountsSizeWord ++
  pushB256 dynamicMemoryBase :: storeWord vaultSelectorPtrWord ++
  pushB256 addWithdrawalRequestsSelector :: mstoreAtPtr vaultSelectorPtrWord ++
  -- first head offset: bytes[] begins after the two heads
  pushB256 0x40 :: mstoreByteAt (dynamicMemoryBase + 32) ++
  pushB256 (dynamicMemoryBase + 96) :: storeWord pubkeysBaseWord ++
  -- second head offset: 0x40 + bytes[] size
  pushB256 0x40 :: loadWord pubkeysSizeWord ++ [add] ++
    mstoreByteAt (dynamicMemoryBase + 64) ++
  loadWord pubkeysBaseWord ++ loadWord pubkeysSizeWord ++ [add] ++
    storeWord amountsBaseWord ++
  loadWord requestsCountWord ++ mstoreAtPtr pubkeysBaseWord ++
  loadWord requestsCountWord ++ mstoreAtPtr amountsBaseWord ++
  -- vault CALL window is selector + two heads + the two arrays
  pushB256 68 :: loadWord pubkeysSizeWord ++ [add] ++
    loadWord amountsSizeWord ++ [add] ++ storeWord vaultCallSizeWord ++
  -- bytes tails begin after length and n offsets
  loadWord pubkeysBaseWord ++ [pushB256 32, add] ++
    loadWord requestsCountWord ++ [pushB256 32, mul, add] ++
    storeWord vaultTailCursorWord ++
  -- Router selector word starts at the word-aligned end of vault arguments.
  loadWord amountsBaseWord ++ loadWord amountsSizeWord ++ [add] ++
    storeWord routerSelectorPtrWord ++
  pushB256 validatorExitTriggeredSelector ::
    mstoreAtPtr routerSelectorPtrWord ++
  -- router heads: array offset, paid fee, exit type
  pushB256 0x60 :: mstoreAtPtrPlus routerSelectorPtrWord 32 ++
  loadWord feeWord ++ mstoreAtPtrPlus routerSelectorPtrWord 64 ++
  loadWord exitTypeWord ++ mstoreAtPtrPlus routerSelectorPtrWord 96 ++
  loadWord routerSelectorPtrWord ++ [pushB256 128, add] ++
    storeWord routerArrayBaseWord ++
  loadWord requestsCountWord ++ mstoreAtPtr routerArrayBaseWord ++
  -- tuple-array size = length + offset table + encoded tuples
  pushB256 32 :: loadWord requestsCountWord ++ [pushB256 32, mul, add] ++
    loadWord routerTupleBytesWord ++ [add] ++ storeWord routerArraySizeWord ++
  pushB256 100 :: loadWord routerArraySizeWord ++ [add] ++
    storeWord routerCallSizeWord ++
  loadWord routerArrayBaseWord ++ [pushB256 32, add] ++
    loadWord requestsCountWord ++ [pushB256 32, mul, add] ++
    storeWord routerTupleCursorWord ++
  pushB256 0 :: storeWord loopIndexWord

/-- Encode one `bytes[]` element, one zero `uint64` element, and one complete
router tuple. -/
def encodeArrayElement : Func :=
  loadCurrentElement +++
  -- pubkeys offset entry, relative to the first word after array length
  loadWord pubkeysBaseWord +++ pushB256 32 ::: add :::
    loadWord vaultTailCursorWord +++ sub :::
  loadWord pubkeysBaseWord +++ pushB256 32 ::: add :::
    loadWord loopIndexWord +++ pushB256 32 ::: mul ::: add ::: mstore :::
  loadWord pubkeyLengthWord +++ mstoreAtPtr vaultTailCursorWord +++
  -- copy exactly `length`; untouched fresh memory supplies canonical padding
  loadWord pubkeyLengthWord +++ loadWord pubkeyPayloadWord +++
    loadWord vaultTailCursorWord +++ pushB256 32 ::: add ::: calldatacopy :::
  loadWord vaultTailCursorWord +++ pushB256 32 :::
    loadWord paddedPubkeyLengthWord +++ add ::: add :::
    storeWord vaultTailCursorWord +++
  -- new uint64[](n): every element is the zero word
  pushB256 0 ::: loadWord amountsBaseWord +++ pushB256 32 ::: add :::
    loadWord loopIndexWord +++ pushB256 32 ::: mul ::: add ::: mstore :::
  -- router tuple offset, relative to the first word after array length
  loadWord routerArrayBaseWord +++ pushB256 32 ::: add :::
    loadWord routerTupleCursorWord +++ sub :::
  loadWord routerArrayBaseWord +++ pushB256 32 ::: add :::
    loadWord loopIndexWord +++ pushB256 32 ::: mul ::: add ::: mstore :::
  calldataloadAt elementBaseWord +++ mstoreAtPtr routerTupleCursorWord +++
  calldataloadAtPlus elementBaseWord 32 +++
    mstoreAtPtrPlus routerTupleCursorWord 32 +++
  pushB256 0x60 ::: mstoreAtPtrPlus routerTupleCursorWord 64 +++
  loadWord pubkeyLengthWord +++ mstoreAtPtrPlus routerTupleCursorWord 96 +++
  loadWord pubkeyLengthWord +++ loadWord pubkeyPayloadWord +++
    loadWord routerTupleCursorWord +++ pushB256 128 ::: add ::: calldatacopy :::
  loadWord routerTupleCursorWord +++ pushB256 128 :::
    loadWord paddedPubkeyLengthWord +++ add ::: add :::
    storeWord routerTupleCursorWord +++
  loadWord loopIndexWord +++ pushB256 1 ::: add ::: storeWord loopIndexWord +++
  .call encodeArraysLoopSlot

def encodeArraysLoop : Func :=
  loadWord requestsCountWord +++ loadWord loopIndexWord +++ lt :::
    (encodeArrayElement <?> .call afterEncodingSlot)

/-! ## Locator, vault, router, refund, and balance flow -/

/-- Solidity's typed external-call boundary.  A codeless target empty-reverts
before the call is issued; the raw refund `CALL` below intentionally does not
use this guard. -/
def requireTypedCallTarget (target : Line) (continuation : Func) : Func :=
  target +++ dup 0 ::: extcodesize ::: iszero :::
  ((.call malformedAbiSlot) <?> (pop ::: continuation))

def decodeAddressReturn (destinationWord : B256) (continuation : Func) : Func :=
  returnDataShorterThan 32 +++
  ((.call malformedAbiSlot) <?>
    (copyReturndataWord +++ pushB256 0 ::: mload ::: checkNonAddress +++
     ((.call malformedAbiSlot) <?>
       (pushB256 0 ::: mload ::: storeWord destinationWord +++
        continuation))))

def callLocatorWithdrawalVault (dp : DeployParams) (continuation : Func) : Func :=
  storeSelectorAtZero withdrawalVaultSelector +++
    (requireTypedCallTarget [pushImmutableWord dp.locator] <|
      pushList [32, 0, 4, 28] +++ pushImmutableWord dp.locator ::: gas ::: staticcall :::
        iszero :::
      ((.call bubbleRevertSlot) <?>
        decodeAddressReturn withdrawalVaultWord continuation))

def callWithdrawalRequestFee (continuation : Func) : Func :=
  storeSelectorAtZero withdrawalRequestFeeSelector +++
    (requireTypedCallTarget (loadWord withdrawalVaultWord) <|
      pushList [32, 0, 4, 28] +++ loadWord withdrawalVaultWord +++ gas ::: staticcall :::
        iszero :::
      ((.call bubbleRevertSlot) <?>
        (returnDataShorterThan 32 +++
         ((.call malformedAbiSlot) <?>
           (copyReturndataWord +++ pushB256 0 ::: mload ::: storeWord feeWord +++
            continuation)))))

def checkedFeeAndEncode : Func :=
  loadWord requestsCountWord +++ loadWord feeWord +++ mul :::
    storeWord totalFeeWord +++
  -- count is known nonzero; division detects checked-multiplication overflow.
  loadWord requestsCountWord +++ loadWord totalFeeWord +++ div :::
    loadWord feeWord +++ eq ::: iszero :::
  ((.call arithmeticPanicSlot) <?>
    (-- msg.value < totalFee
     loadWord totalFeeWord +++ callvalue ::: lt :::
     ((.call insufficientFeeSlot) <?>
       (loadWord totalFeeWord +++ callvalue ::: sub ::: storeWord refundWord +++
        .call validateArrayLoopSlot))))

/-- All nested calldata values have now been touched exactly where the source
extracts its pubkeys.  Build the two outgoing images and rescan the immutable
calldata to encode them canonically. -/
def afterNestedValidation : Func :=
  initializeOutgoingMemory +++ .call encodeArraysLoopSlot

def afterQuota (dp : DeployParams) : Func :=
  callLocatorWithdrawalVault dp <|
    callWithdrawalRequestFee checkedFeeAndEncode

def afterEncoding : Func :=
  -- withdrawalVault.addWithdrawalRequests{value: totalFee}(...)
  requireTypedCallTarget (loadWord withdrawalVaultWord) <|
    pushList [0, 0] +++ loadWord vaultCallSizeWord +++
      pushB256 (dynamicMemoryBase + 28) ::: loadWord totalFeeWord +++
      loadWord withdrawalVaultWord +++ gas ::: call ::: iszero :::
    ((.call bubbleRevertSlot) <?> .call afterVaultCallSlot)

def callLocatorStakingRouter (dp : DeployParams) (continuation : Func) : Func :=
  storeSelectorAtZero stakingRouterSelector +++
    (requireTypedCallTarget [pushImmutableWord dp.locator] <|
      pushList [32, 0, 4, 28] +++ pushImmutableWord dp.locator ::: gas ::: staticcall :::
        iszero :::
      ((.call bubbleRevertSlot) <?>
        decodeAddressReturn stakingRouterWord continuation))

def callStakingRouter : Func :=
  requireTypedCallTarget (loadWord stakingRouterWord) <|
    pushList [0, 0] +++ loadWord routerCallSizeWord +++
      loadWord routerSelectorPtrWord +++ pushB256 28 ::: add :::
      pushB256 0 ::: loadWord stakingRouterWord +++ gas ::: call ::: iszero :::
    ((.call bubbleRevertSlot) <?>
      (loadWord refundWord +++ iszero :::
        ((.call balanceCheckSlot) <?>
          (loadWord refundRecipientWord +++ iszero :::
            ((caller ::: storeWord refundRecipientWord +++ .call refundCallSlot)
              <?> .call refundCallSlot)))))

def afterVaultCall (dp : DeployParams) : Func :=
  callLocatorStakingRouter dp callStakingRouter

def refundCall : Func :=
  pushList [0, 0, 0, 0] +++ loadWord refundWord +++
    loadWord refundRecipientWord +++ gas ::: call ::: iszero :::
  ((.call feeRefundFailedSlot) <?> .call balanceCheckSlot)

def balanceCheck : Func :=
  selfbalance ::: loadWord balanceBeforeWord +++ eq :::
    (Func.stop <?> .call assertionPanicSlot)

/-! ## Entry, packet, and compile witness -/

def afterValidation : Func :=
  coreFlatRoleGuard (.call roleFailureBoundarySlot) <|
    -- preservesEthBalance starts after onlyRole and before whenResumed.
    callvalue ::: selfbalance ::: lt :::
    ((.call arithmeticPanicSlot) <?>
      (callvalue ::: selfbalance ::: sub ::: storeWord balanceBeforeWord +++
       pushB256 resumeSinceSlot ::: sload ::: timestamp ::: lt :::
       ((.call resumedExpectedSlot) <?>
         (callvalue ::: iszero :::
          ((.call zeroMsgValueSlot) <?>
            (loadWord requestsCountWord +++ iszero :::
             ((.call zeroValidatorsDataSlot) <?> .call consumeQuotaSlot)))))))

/-- The runtime-integration body.  Its local calls use the slot table above;
the final runtime must rebase them together with `localAux`. -/
def triggerFullWithdrawals (dp : DeployParams) : Func :=
  validateCalldata

def localAuxWithRoleFailure (dp : DeployParams) (roleFailure : Func) : List Func :=
  [ Func.revert,
    zeroMsgValueRevert,
    zeroValidatorsDataRevert,
    resumedExpectedRevert,
    exitLimitExceededRevert,
    insufficientFeeRevert,
    feeRefundFailedRevert,
    arithmeticPanicRevert,
    divisionPanicRevert,
    assertionPanicRevert,
    -- AccessControl's dynamic source string is the one deliberate policy hook.
    roleFailure,
    validateArrayLoop,
    afterValidation,
    consumeExitRequestLimit (.call afterQuotaSlot),
    afterQuota dp,
    encodeArraysLoop,
    afterEncoding,
    bubbleRevert,
    afterVaultCall dp,
    refundCall,
    balanceCheck,
    afterNestedValidation ]

/-- A closed standalone packet uses an empty revert at the AccessControl
policy boundary.  Runtime integration should normally use
`localAuxWithRoleFailure` to install the family-wide role failure body. -/
def localAux (dp : DeployParams) : List Func :=
  localAuxWithRoleFailure dp Func.revert

/-- Shift every local table call by `delta`.  If the first appended trigger aux
body will occupy global table slot `base`, use `delta = base - 1`: local slot
one then becomes `base`, local slot two becomes `base + 1`, and so on. -/
def rebaseLocalCalls (delta : Nat) : Func → Func
  | .branch left right =>
      .branch (rebaseLocalCalls delta left) (rebaseLocalCalls delta right)
  | .last op => .last op
  | .next op rest => .next op (rebaseLocalCalls delta rest)
  | .call slot => .call (delta + slot)

/-- Local-call rebasing commutes with the constant-store prefix used by
`Func.revertData`.  The prefix contains no local calls, so only its tail can
change. -/
theorem rebaseLocalCalls_prependStoresRev (delta : Nat)
    (stores : List (B256 × Nat)) (rest : Func) :
    rebaseLocalCalls delta (prependStoresRev stores rest) =
      prependStoresRev stores (rebaseLocalCalls delta rest) := by
  induction stores generalizing rest with
  | nil => rfl
  | cons iw iws ih =>
      simp only [prependStoresRev]
      rw [ih]
      rfl

/-- Constant-data reverters contain no local calls, so rebasing is the
identity on them. -/
theorem rebaseLocalCalls_revertData (delta : Nat) (blob : Bytes) :
    rebaseLocalCalls delta (Func.revertData blob) = Func.revertData blob := by
  unfold Func.revertData
  rw [rebaseLocalCalls_prependStoresRev]
  rfl

def rebasedTrigger (delta : Nat) (dp : DeployParams) : Func :=
  rebaseLocalCalls delta (triggerFullWithdrawals dp)

def rebasedLocalAuxWithRoleFailure
    (delta : Nat) (dp : DeployParams) (roleFailure : Func) : List Func :=
  (localAuxWithRoleFailure dp roleFailure).map (rebaseLocalCalls delta)

def packet (dp : DeployParams) : Prog :=
  ⟨triggerFullWithdrawals dp, localAux dp⟩

def packetCode (dp : DeployParams) : Bytes :=
  (Prog.compile (packet dp)).getD []

theorem localAux_length (dp : DeployParams) :
    (localAux dp).length = localAuxSlotCount := by
  rfl

theorem rebasedLocalAuxWithRoleFailure_length
    (delta : Nat) (dp : DeployParams) (roleFailure : Func) :
    (rebasedLocalAuxWithRoleFailure delta dp roleFailure).length =
      localAuxSlotCount := by
  simp [rebasedLocalAuxWithRoleFailure, localAuxWithRoleFailure,
    localAuxSlotCount]

theorem packet_compileShape_eq_zero (dp : DeployParams) :
    (packet dp).compileShape = (packet ⟨0⟩).compileShape := by
  rfl

private theorem packetCompilesZero :
    Prog.compiles (packet ⟨0⟩) = true := by
  decide +kernel

theorem packet_compiles (dp : DeployParams) :
    Prog.compiles (packet dp) = true := by
  rw [Prog.compiles_eq_of_compileShape (packet_compileShape_eq_zero dp)]
  exact packetCompilesZero

theorem packet_compile (dp : DeployParams) :
    Prog.compile (packet dp) = some (packetCode dp) := by
  simpa [packetCode] using
    Prog.compile_eq_some_getD_of_compiles (packet dp) (packet_compiles dp)

end Trigger
end LidoTriggerableWithdrawalsGateway
end Blanc
