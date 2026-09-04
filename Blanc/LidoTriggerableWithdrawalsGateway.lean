import Blanc.LidoTriggerableWithdrawalsGatewayTrigger
import Blanc.LinearDispatch

/-!
  Source-level Blanc runtime for the Triggerable Withdrawals Gateway.

  All selectors have an executable dispatch entry, including the nested
  `ValidatorExitData[]` decoder and outbound trigger choreography.
  The disposable P1 shape uses nested-keccak membership and direct per-role
  length/index/member storage; removal uses swap-pop with moved-index repair.
  Raw storage remains outside the public logical projection.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoTriggerableWithdrawalsGateway

/-! ## Small instruction helpers -/

def pushDeployWord (word : B256) : Ninst :=
  Ninst.push word.toBytes (by rw [B256.length_toBytes])

/-! `mloadWord` is separate from the storage vocabulary: its argument is an
ABI/event memory word, not a storage slot. -/
def mloadWord (word : B256) : Line :=
  [pushB256 (word * 32), mload]

def returnWord : Func :=
  mstoreAt 0 +++ returnMemoryRange 0 32

def returnWords (count : B256) : Func :=
  pushB256 (count * 32) ::: pushB256 0 ::: Func.return_

def customErrorData (name : String) (args : List ArgType := []) : Bytes :=
  (signatureHash name args).toBytes.take 4

def runtimeError (name : String) (args : List ArgType := []) : Func :=
  Func.revertSelector (customErrorData name args) (by
    simp [customErrorData, B256.length_toBytes])

def fallbackSlot : Nat := 1
def missingRoleSlot : Nat := 2
def pausedExpectedSlot : Nat := 3
def resumedExpectedSlot : Nat := 4
def zeroPauseDurationSlot : Nat := 5
def pauseUntilPastSlot : Nat := 6
def arithmeticPanicSlot : Nat := 7
def tooLargeMaxExitRequestsLimitSlot : Nat := 8
def tooLargeFrameDurationSlot : Nat := 9
def tooLargeExitsPerFrameSlot : Nat := 10
def zeroFrameDurationSlot : Nat := 11
def limitCurrentComputeSlot : Nat := 12
def limitCurrentContinueSlot : Nat := 13
def setLimitAfterCurrentSlot : Nat := 14
def setLimitWriteSlot : Nat := 15
def consumeAfterCurrentSlot : Nat := 16
def exitRequestsLimitExceededSlot : Nat := 17

def roleKeyFromMemory (region : Nat) : Line :=
  mloadWord 0 ++ mloadWord 1 ++
  [pushB256 addressMask, and, xor,
   pushB256 low252Mask, and, pushB256 (regionWord region), or]

def roleKeyFromMemoryAt (roleWord accountWord : Nat) (region : Nat) : Line :=
  mloadWord (Nat.toB256 roleWord) ++ mloadWord (Nat.toB256 accountWord) ++
  [pushB256 addressMask, and, xor,
   pushB256 low252Mask, and, pushB256 (regionWord region), or]

def roleKeyFromArgs (region : Nat) : Line :=
  arg 0 ++ arg 1 ++
  [pushB256 addressMask, and, xor,
   pushB256 low252Mask, and, pushB256 (regionWord region), or]

def roleKeyForCaller (role region : B256) : Line :=
  [pushB256 role, caller, pushB256 addressMask, and, xor,
   pushB256 low252Mask, and, pushB256 region, or]

def enumKeyFromMemory (region : Nat) : Line :=
  mloadWord 2 ++
  [pushB256 low252Mask, and, pushB256 (regionWord region), or]

def enumKeyFromMemoryAt (word : Nat) (region : Nat) : Line :=
  mloadWord (Nat.toB256 word) ++
  [pushB256 low252Mask, and, pushB256 (regionWord region), or]

def onlyRole (role : B256) (body : Func) : Func :=
  viewRoleMembershipSlotFrom [pushB256 role] [caller] +++
    (sload ::: iszero ::: ((.call missingRoleSlot) <?> body))

def requireStaticArgs (words : Nat) (body : Func) : Func :=
  pushB256 (Nat.toB256 (4 + 32 * words)) ::: calldatasize ::: lt :::
    (Func.revert <?> body)

def canonicalArg (index : B256) (body : Func) : Func :=
  (arg index ++ checkNonAddress) +++
    (Func.revert <?> body)

def emitOneWord (topic : B256) (word : B256) : Line :=
  [pushB256 word] ++ mstoreAt 0 ++ [pushB256 topic] ++ logWith 0 0 1

def emitNoData (topic : B256) : Line :=
  [pushB256 topic] ++ logWith 0 0 0

def emitRoleGranted : Line :=
  [caller] ++ mloadWord 1 ++ mloadWord 0 ++
    [pushB256 (signatureHash "RoleGranted" [.bytes 32, .address, .address])] ++
    logWith 3 0 0

def emitRoleRevoked : Line :=
  [caller] ++ mloadWord 1 ++ mloadWord 0 ++
    [pushB256 (signatureHash "RoleRevoked" [.bytes 32, .address, .address])] ++
    logWith 3 0 0

/-! ## Public constants and views -/

def constantWord (word : B256) : Func :=
  pushB256 word ::: returnWord

/-! Limit memory convention: words 0/1/2 are new setter values (and the
query's max/exits/frame); word 3 is the query's previous-limit output; word 4
is old previous-limit/current output; words 5/6/7 are old timestamp/frame/
exits-per-frame; word 8 is computed current limit; words 9/10 are refill
scratch; word 11 selects query (zero) versus setter (one); word 12 is the
current timestamp; word 13 is the old maximum; word 14 is the request count
for the reusable consume continuation. -/

def packedLimitScratchWord : B256 := 15

def loadPackedLimitWorkingWords : Line :=
  [pushB256 twrLimitPosition, sload] ++ mstoreAt packedLimitScratchWord ++
  unpackUint32Lane packedLimitScratchWord 13 0 ++
  unpackUint32Lane packedLimitScratchWord 4 32 ++
  unpackUint32Lane packedLimitScratchWord 5 64 ++
  unpackUint32Lane packedLimitScratchWord 6 96 ++
  unpackUint32Lane packedLimitScratchWord 7 128

def storePackedLimitWorkingWords : Line :=
  packFiveUint32Words 13 4 12 6 7 ++ [pushB256 twrLimitPosition, sstore]

def limitCurrentContinue : Func :=
  (mloadWord 11 ++ [iszero]) +++
    (((mloadWord 4 ++ mstoreAt 3 ++ mloadWord 8 ++ mstoreAt 4) +++
        returnWords 5)
      <?>
      ((mloadWord 11 ++ [pushB256 1, eq]) +++
        ((.call setLimitAfterCurrentSlot) <?> .call consumeAfterCurrentSlot)))

def limitRefilledContinue : Func :=
  (mloadWord 4 ++ mloadWord 10 ++ [add] ++ mstoreAt 10 ++
    mloadWord 10 ++ mloadWord 4 ++ [gt]) +++
    ((.call arithmeticPanicSlot) <?>
      ((mloadWord 13 ++ mloadWord 10 ++ [gt]) +++
        (((mloadWord 13 ++ mstoreAt 8) +++ .call limitCurrentContinueSlot)
          <?> ((mloadWord 10 ++ mstoreAt 8) +++
            .call limitCurrentContinueSlot))))

def limitRefillChecked : Func :=
  (mloadWord 6 ++ mloadWord 9 ++ [div] ++ mstoreAt 9 ++
    mloadWord 9 ++ mloadWord 7 ++ [mul] ++ mstoreAt 10 ++
    mloadWord 7 ++ mloadWord 10 ++ [div] ++ mloadWord 9 ++ [eq]) +++
    (limitRefilledContinue <?> .call arithmeticPanicSlot)

def limitElapsedContinue : Func :=
  (mloadWord 5 ++ mloadWord 12 ++ [sub] ++ mstoreAt 9 ++
    mloadWord 6 ++ mloadWord 9 ++ [lt] ++
    mloadWord 7 ++ [iszero, or]) +++
    (((mloadWord 4 ++ mstoreAt 8) +++ .call limitCurrentContinueSlot)
      <?> limitRefillChecked)

def limitCurrentCompute : Func :=
  (mloadWord 13 ++ [iszero]) +++
    ((([pushB256 pauseInfinitely] ++ mstoreAt 8) +++
        .call limitCurrentContinueSlot)
      <?>
      ((mloadWord 12 ++ mloadWord 5 ++ [gt]) +++
        ((.call arithmeticPanicSlot) <?> limitElapsedContinue)))

def setLimitWrite : Func :=
  (mloadWord 0 ++ mstoreAt 13 ++
   mloadWord 2 ++ mstoreAt 6 ++
   mloadWord 1 ++ mstoreAt 7 ++
   storePackedLimitWorkingWords ++
   mloadWord 0 ++ mstoreAt 0 ++ mloadWord 1 ++ mstoreAt 1 ++
   mloadWord 2 ++ mstoreAt 2 ++
   [pushB256 (signatureHash "ExitRequestsLimitSet" [.uint256, .uint256, .uint256])] ++
   logWith 0 0 3) +++ Func.stop

def setLimitAfterCurrent : Func :=
  (mloadWord 8 ++ mloadWord 13 ++ [sub] ++ mstoreAt 10 ++
   mloadWord 0 ++ mloadWord 10 ++ [lt, iszero]) +++
    ((([pushB256 0] ++ mstoreAt 4) +++ .call setLimitWriteSlot)
      <?>
      ((mloadWord 10 ++ mloadWord 0 ++ [sub] ++ mstoreAt 4) +++
        .call setLimitWriteSlot))

def consumeAfterCurrentSuccess : Func :=
  (mloadWord 14 ++ mloadWord 8 ++ [sub] ++ mstoreAt 4 ++
    mloadWord 12 ++ mloadWord 5 ++ [gt]) +++
    ((.call arithmeticPanicSlot) <?>
      ((mloadWord 5 ++ mloadWord 12 ++ [sub] ++ mstoreAt 9 ++
        mloadWord 6 ++ mloadWord 9 ++ [div] ++
        mloadWord 6 ++ [mul] ++ mstoreAt 10 ++
        mloadWord 5 ++ mloadWord 10 ++ [add] ++ mstoreAt 12 ++
        storePackedLimitWorkingWords) +++
        Func.stop))

def consumeAfterCurrent : Func :=
  (mloadWord 8 ++ mloadWord 14 ++ [gt]) +++
    ((.call exitRequestsLimitExceededSlot) <?>
      consumeAfterCurrentSuccess)

def consumeExitLimit : Func :=
  ( loadPackedLimitWorkingWords ++
    [timestamp] ++ mstoreAt 12 ++ [pushB256 2] ++ mstoreAt 11) +++
    ((mloadWord 13 ++ [iszero]) +++
      (Func.stop <?> .call limitCurrentComputeSlot))

def getExitRequestLimitFullInfo : Func :=
  ( loadPackedLimitWorkingWords ++
    mloadWord 13 ++ mstoreAt 0 ++
    mloadWord 7 ++ mstoreAt 1 ++
    mloadWord 6 ++ mstoreAt 2 ++
    [timestamp] ++ mstoreAt 12 ++ [pushB256 0] ++ mstoreAt 11) +++
    .call limitCurrentComputeSlot

def getResumeSinceTimestamp : Func :=
  pushB256 resumeSinceSlot ::: sload ::: returnWord

def getRoleAdmin : Func :=
  requireStaticArgs 1 <| pushB256 defaultAdminRole ::: returnWord

def getRoleMember : Func :=
  requireStaticArgs 2 <|
    (viewRoleEnumerationBaseSlotFrom (arg 0) ++ [sload] ++
        arg 1 ++ [lt]) +++
      (((viewRoleEnumerationMemberSlotFrom (arg 0) (arg 1) ++
          [sload]) +++ returnWord) <?> Func.revert)

def getRoleMemberCount : Func :=
  requireStaticArgs 1 <|
    (viewRoleEnumerationBaseSlotFrom (arg 0) ++ [sload]) +++ returnWord

def hasRole : Func :=
  requireStaticArgs 2 <| canonicalArg 1 <|
    (viewRoleMembershipSlotFrom (arg 0) (arg 1) ++
      [sload, iszero, iszero]) +++
      returnWord

def isPaused : Func :=
  ([pushB256 resumeSinceSlot, sload, timestamp, lt] +++ returnWord)

def supportsInterface : Func :=
  requireStaticArgs 1 <|
    (argBytes4 0 ++ [pushB256 0x01ffc9a7, eq] ++
      argBytes4 0 ++ [pushB256 0x7965db0b, eq, or] ++
      argBytes4 0 ++ [pushB256 0x5a05180f, eq, or]) +++
      returnWord

/-! ## Pause and role mutation -/

def pauseForSentinel : Func :=
  ([pushB256 pauseInfinitely, pushB256 resumeSinceSlot, sstore] ++
    emitOneWord (signatureHash "Paused" [.uint256]) pauseInfinitely) +++
    Func.stop

def pauseForFinite : Func :=
  ([timestamp] ++ arg 0 ++ [add, dup 0, timestamp, gt]) +++
    ((.call arithmeticPanicSlot) <?>
      (([pushB256 resumeSinceSlot, sstore] ++ arg 0 ++ mstoreAt 0 ++
        [pushB256 (signatureHash "Paused" [.uint256])] ++
        logWith 0 0 1) +++ Func.stop))

def pauseForUnpaused : Func :=
  (arg 0 ++ [iszero]) +++
    ((.call zeroPauseDurationSlot) <?>
      ((arg 0 ++ [pushB256 pauseInfinitely, eq]) +++
        (pauseForSentinel <?> pauseForFinite)))

def pauseFor : Func :=
  requireStaticArgs 1 <| onlyRole pauseRole <|
    ([pushB256 resumeSinceSlot, sload, timestamp, lt, iszero]) +++
      (pauseForUnpaused <?> .call resumedExpectedSlot)

def pauseUntilSentinel : Func :=
  ([pushB256 pauseInfinitely, pushB256 resumeSinceSlot, sstore] ++
    emitOneWord (signatureHash "Paused" [.uint256]) pauseInfinitely) +++
    Func.stop

def pauseUntilFinite : Func :=
  (arg 0 ++ [pushB256 1, add, dup 0] ++ arg 0 ++ [gt]) +++
    ((.call arithmeticPanicSlot) <?>
      (([dup 0] ++ mstoreAt 1 ++
        [pushB256 resumeSinceSlot, sstore] ++ mloadWord 1 ++
        [timestamp, swap 0, sub] ++ mstoreAt 0 ++
        [pushB256 (signatureHash "Paused" [.uint256])] ++
        logWith 0 0 1) +++ Func.stop))

def pauseUntilUnpaused : Func :=
  ([timestamp] ++ arg 0 ++ [lt]) +++
    ((.call pauseUntilPastSlot) <?>
      ((arg 0 ++ [pushB256 pauseInfinitely, eq]) +++
        (pauseUntilSentinel <?> pauseUntilFinite)))

def pauseUntil : Func :=
  requireStaticArgs 1 <| onlyRole pauseRole <|
    ([pushB256 resumeSinceSlot, sload, timestamp, lt, iszero]) +++
      (pauseUntilUnpaused <?> .call resumedExpectedSlot)

def resume : Func :=
  onlyRole resumeRole <|
    ([pushB256 resumeSinceSlot, sload, timestamp, lt]) +++
      ((([timestamp, pushB256 resumeSinceSlot, sstore] ++
          emitNoData (signatureHash "Resumed" [])) +++ Func.stop)
        <?> .call pausedExpectedSlot)

def grantRole : Func :=
  requireStaticArgs 2 <| canonicalArg 1 <| onlyRole defaultAdminRole <|
    ((arg 0 ++ mstoreAt 0 ++ arg 1 ++ mstoreAt 1 ++
      roleMembershipSlotFrom (mloadWord 0) (mloadWord 1) ++
        [dup 0] ++ mstoreAt 3 ++ [sload, iszero]) +++
      ((([pushB256 1] ++ mloadWord 3 ++ [sstore] ++
          roleEnumerationBaseSlotFrom (mloadWord 0) ++
            [dup 0] ++ mstoreAt 4 ++ [sload] ++ mstoreAt 2 ++
          mloadWord 1 ++ keccakWordLine (mloadWord 4) ++
            mloadWord 2 ++ [add, sstore] ++
          mloadWord 2 ++ [pushB256 1, add] ++
            keccakPairLinesRightFirst (mloadWord 1)
              (mloadWord 4 ++ [pushB256 1, add]) ++ [sstore] ++
          mloadWord 2 ++ [pushB256 1, add] ++ mloadWord 4 ++ [sstore] ++
          emitRoleGranted) +++ Func.stop)
        <?> Func.stop))

def clearRemovedLookup : Line :=
  [pushB256 0] ++ mloadWord 8 ++ [sstore] ++
  [pushB256 0] ++ mloadWord 2 ++ [sstore]

def clearRoleMembershipLast : Func :=
  ([pushB256 0] ++ keccakWordLine (mloadWord 3) ++
      mloadWord 5 ++ [add, sstore] ++
   clearRemovedLookup ++
   mloadWord 5 ++ mloadWord 3 ++ [sstore] ++
   emitRoleRevoked) +++ Func.stop

def clearRoleMembershipSwap : Func :=
  (keccakWordLine (mloadWord 3) ++ mloadWord 5 ++ [add, sload] ++
      mstoreAt 7 ++
   mloadWord 7 ++ keccakWordLine (mloadWord 3) ++
      mloadWord 6 ++ [add, sstore] ++
   mloadWord 4 ++ keccakPairLinesRightFirst (mloadWord 7)
      (mloadWord 3 ++ [pushB256 1, add]) ++ [sstore] ++
   [pushB256 0] ++ keccakWordLine (mloadWord 3) ++
      mloadWord 5 ++ [add, sstore] ++
   clearRemovedLookup ++
   mloadWord 5 ++ mloadWord 3 ++ [sstore] ++
   emitRoleRevoked) +++ Func.stop

def clearRoleMembership : Func :=
    (arg 0 ++ mstoreAt 0 ++ arg 1 ++ mstoreAt 1 ++
     roleMembershipSlotFrom (mloadWord 0) (mloadWord 1) ++
       [dup 0] ++ mstoreAt 2 ++ [sload, iszero]) +++
      (Func.stop <?>
          ((roleEnumerationBaseSlotFrom (mloadWord 0) ++
            [dup 0] ++ mstoreAt 3 ++
              [sload, pushB256 1, swap 0, sub] ++ mstoreAt 5 ++
          keccakPairLinesRightFirst (mloadWord 1)
            (mloadWord 3 ++ [pushB256 1, add]) ++
            [dup 0] ++ mstoreAt 8 ++ [sload] ++ mstoreAt 4 ++
          mloadWord 4 ++ [pushB256 1, swap 0, sub] ++ mstoreAt 6 ++
          mloadWord 6 ++ mloadWord 5 ++ [eq]) +++
            (clearRoleMembershipLast <?> clearRoleMembershipSwap)))

def revokeRole : Func :=
  requireStaticArgs 2 <| canonicalArg 1 <| onlyRole defaultAdminRole <|
    clearRoleMembership

def renounceRole : Func :=
  requireStaticArgs 2 <| canonicalArg 1 <|
    (arg 1 ++ [caller, eq]) +++ (clearRoleMembership <?> Func.revert)

/-! ## Exit-limit setter and trigger boundary -/

def setExitRequestLimitPrepared : Func :=
  (arg 0 ++ mstoreAt 0 ++ arg 1 ++ mstoreAt 1 ++
    arg 2 ++ mstoreAt 2 ++ [timestamp] ++ mstoreAt 12 ++
    loadPackedLimitWorkingWords ++
    [pushB256 1] ++ mstoreAt 11 ++ mloadWord 13 ++ [iszero]) +++
    (((mloadWord 0 ++ mstoreAt 4) +++ .call setLimitWriteSlot)
      <?> .call limitCurrentComputeSlot)

def setExitRequestLimitFrameChecked : Func :=
  (arg 2 ++ [iszero]) +++
    ((.call zeroFrameDurationSlot) <?> setExitRequestLimitPrepared)

def setExitRequestLimitRateChecked : Func :=
  (arg 0 ++ arg 1 ++ [gt]) +++
    ((.call tooLargeExitsPerFrameSlot) <?> setExitRequestLimitFrameChecked)

def setExitRequestLimitDurationChecked : Func :=
  ([pushB256 (Nat.toB256 (2 ^ 32 - 1))] ++ arg 2 ++ [gt]) +++
    ((.call tooLargeFrameDurationSlot) <?> setExitRequestLimitRateChecked)

def setExitRequestLimit : Func :=
  requireStaticArgs 3 <| onlyRole twExitLimitManagerRole <|
    ([pushB256 (Nat.toB256 (2 ^ 32 - 1))] ++ arg 0 ++ [gt]) +++
      ((.call tooLargeMaxExitRequestsLimitSlot) <?>
        setExitRequestLimitDurationChecked)

/-! The compact family runtime occupies global slots 1--17.  Trigger-local
selector-only `ResumedExpected`, arithmetic-panic and role-failure bodies are
identical to family bodies, so the integrated table maps those three calls to
slots 4, 7 and 2 and omits the duplicate table entries. -/
def triggerAuxDelta : Nat := 17

def integratedTriggerSlot (slot : Nat) : Nat :=
  if slot = Trigger.resumedExpectedSlot then resumedExpectedSlot
  else if slot = Trigger.arithmeticPanicSlot then arithmeticPanicSlot
  else if slot = Trigger.roleFailureBoundarySlot then missingRoleSlot
  else if slot < Trigger.resumedExpectedSlot then triggerAuxDelta + slot
  else if slot < Trigger.arithmeticPanicSlot then triggerAuxDelta + slot - 1
  else if slot < Trigger.roleFailureBoundarySlot then triggerAuxDelta + slot - 2
  else triggerAuxDelta + slot - 3

def rebaseIntegratedTriggerCalls : Func → Func
  | .branch left right =>
      .branch (rebaseIntegratedTriggerCalls left)
        (rebaseIntegratedTriggerCalls right)
  | .last op => .last op
  | .next op rest => .next op (rebaseIntegratedTriggerCalls rest)
  | .call slot => .call (integratedTriggerSlot slot)

def triggerFullWithdrawals (dp : DeployParams) : Func :=
  rebaseIntegratedTriggerCalls (Trigger.triggerFullWithdrawals dp)

def integratedTriggerAux (dp : DeployParams) : List Func :=
  [ Func.revert,
    Trigger.zeroMsgValueRevert,
    Trigger.zeroValidatorsDataRevert,
    Trigger.exitLimitExceededRevert,
    Trigger.insufficientFeeRevert,
    Trigger.feeRefundFailedRevert,
    Trigger.divisionPanicRevert,
    Trigger.assertionPanicRevert,
    Trigger.validateArrayLoop,
    Trigger.afterValidation,
    Trigger.consumeExitRequestLimit (.call Trigger.afterQuotaSlot),
    Trigger.afterQuota dp,
    Trigger.encodeArraysLoop,
    Trigger.afterEncoding,
    Trigger.bubbleRevert,
    Trigger.afterVaultCall dp,
    Trigger.refundCall,
    Trigger.balanceCheck,
    Trigger.afterNestedValidation ].map rebaseIntegratedTriggerCalls

/-! ## Selector dispatch -/

def funcs (dp : DeployParams) : List (B256 × Func) :=
  [ (selPauseFor, nonpayable pauseFor),
    (selIsPaused, nonpayable isPaused),
    (selTriggerFullWithdrawals, triggerFullWithdrawals dp),
    (selPauseRole,
      nonpayable (constantWord pauseRole)),
    (selResumeRole, nonpayable (constantWord resumeRole)),
    (selAddFullWithdrawalRequestRole,
      nonpayable (constantWord addFullWithdrawalRequestRole)),
    (selTwExitLimitManagerRole, nonpayable (constantWord twExitLimitManagerRole)),
    (selTwrLimitPosition, nonpayable (constantWord twrLimitPosition)),
    (selVersion, nonpayable (constantWord version)),
    (selResume, nonpayable resume),
    (selPauseUntil, nonpayable pauseUntil),
    (selSetExitRequestLimit, nonpayable setExitRequestLimit),
    (selGetExitRequestLimitFullInfo, nonpayable getExitRequestLimitFullInfo),
    (selPauseInfinitely, nonpayable (constantWord pauseInfinitely)),
    (selGetResumeSinceTimestamp, nonpayable getResumeSinceTimestamp),
    (selDefaultAdminRole, nonpayable (constantWord defaultAdminRole)),
    (selSupportsInterface, nonpayable supportsInterface),
    (selHasRole, nonpayable hasRole),
    (selGetRoleAdmin, nonpayable getRoleAdmin),
    (selGrantRole, nonpayable grantRole),
    (selRevokeRole, nonpayable revokeRole),
    (selRenounceRole, nonpayable renounceRole),
    (selGetRoleMember, nonpayable getRoleMember),
    (selGetRoleMemberCount, nonpayable getRoleMemberCount) ]

/-! The payable trigger is selected before this table.  All remaining entries
share one nonpayable guard.  Hot role views move ahead of large-margin writers;
this changes no selector semantics and targets the measured 27--194 gas
dispatcher residue without sacrificing an existing strict win. -/
def sharedNonpayableFuncs : List (B256 × Func) :=
  [ (selPauseFor, pauseFor),
    (selIsPaused, isPaused),
    (selHasRole, hasRole),
    (selGetRoleMember, getRoleMember),
    (selGetRoleMemberCount, getRoleMemberCount),
    (selSupportsInterface, supportsInterface),
    (selResume, resume),
    (selDefaultAdminRole, constantWord defaultAdminRole),
    (selPauseInfinitely, constantWord pauseInfinitely),
    (selGetResumeSinceTimestamp, getResumeSinceTimestamp),
    (selRenounceRole, renounceRole),
    (selPauseRole, constantWord pauseRole),
    (selResumeRole, constantWord resumeRole),
    (selAddFullWithdrawalRequestRole,
      constantWord addFullWithdrawalRequestRole),
    (selTwExitLimitManagerRole, constantWord twExitLimitManagerRole),
    (selTwrLimitPosition, constantWord twrLimitPosition),
    (selVersion, constantWord version),
    (selPauseUntil, pauseUntil),
    (selSetExitRequestLimit, setExitRequestLimit),
    (selGetExitRequestLimitFullInfo, getExitRequestLimitFullInfo),
    (selGetRoleAdmin, getRoleAdmin),
    (selGrantRole, grantRole),
    (selRevokeRole, revokeRole) ]

def runtimeMain (dp : DeployParams) : Func :=
  pushB256 4 ::: calldatasize ::: lt :::
    (Func.revert <?>
      (fsig +++ dup 0 ::: pushB256 selTriggerFullWithdrawals ::: eq :::
        ((pop ::: triggerFullWithdrawals dp) <?>
          (callvalue ::: iszero :::
            (linearDispatchWith fallbackSlot sharedNonpayableFuncs <?>
              Func.revert)))))

def baseAux : List Func :=
  [Func.revert,
   runtimeError "AccessControlUnauthorizedAccount",
   runtimeError "PausedExpected",
   runtimeError "ResumedExpected",
   runtimeError "ZeroPauseDuration",
   runtimeError "PauseUntilMustBeInFuture",
   Func.revertData ((signatureHash "Panic" [.uint256]).toBytes.take 4 ++
     (Nat.toB256 0x11).toBytes),
   runtimeError "TooLargeMaxExitRequestsLimit",
   runtimeError "TooLargeFrameDuration",
   runtimeError "TooLargeExitsPerFrame",
   runtimeError "ZeroFrameDuration",
   limitCurrentCompute,
   limitCurrentContinue,
   setLimitAfterCurrent,
   setLimitWrite,
   consumeAfterCurrent,
   ([pushB256 Trigger.exitLimitExceededSelector] ++ mstoreAt 0 ++
     mloadWord 14 ++ mstoreAt 1 ++ mloadWord 8 ++ mstoreAt 2 ++
     [pushB256 68, pushB256 28]) +++ .last .revert]

def aux (dp : DeployParams) : List Func :=
  baseAux ++ integratedTriggerAux dp

def runtime (dp : DeployParams) : Prog :=
  ⟨runtimeMain dp, aux dp⟩

def runtimeCode (dp : DeployParams) : Bytes :=
  (Prog.compile (runtime dp)).getD []

theorem funcs_selector_census (dp : DeployParams) :
    List.Perm ((funcs dp).map Prod.fst)
      (selectorCensus.map SelectorEntry.selector) := by
  simp only [funcs, List.map_cons, List.map_nil]
  decide

theorem runtime_compileShape_eq_zero (dp : DeployParams) :
    (runtime dp).compileShape =
      (runtime ⟨0⟩).compileShape := by
  rfl

private theorem runtimeCompilesZero :
    Prog.compiles (runtime ⟨0⟩) = true := by
  decide +kernel

theorem runtime_compiles (dp : DeployParams) :
    Prog.compiles (runtime dp) = true := by
  rw [Prog.compiles_eq_of_compileShape (runtime_compileShape_eq_zero dp)]
  exact runtimeCompilesZero

theorem runtime_compile (dp : DeployParams) :
    Prog.compile (runtime dp) = some (runtimeCode dp) := by
  simpa [runtimeCode] using
    Prog.compile_eq_some_getD_of_compiles (runtime dp) (runtime_compiles dp)

def sourceSstoreSiteCount : Func → Nat
  | .last _ => 0
  | .next (.reg .sstore) rest => 1 + sourceSstoreSiteCount rest
  | .next _ rest => sourceSstoreSiteCount rest
  | .branch left right => sourceSstoreSiteCount left + sourceSstoreSiteCount right
  | .call _ => 0

def sourceSstoreCount (dp : DeployParams) : Nat :=
  (funcs dp).foldl (fun n p => n + sourceSstoreSiteCount p.2) 0

def sourceInventory (dp : DeployParams) : SourceInventory :=
  { persistentWrites :=
      [({label := "pause", offset := 0}, .pause),
       ({label := "limit", offset := 1}, .limit),
       ({label := "roles", offset := 2}, .roleMembership),
       ({label := "enumeration", offset := 3}, .enumeration)]
    externalCalls :=
      [({label := "locatorVault", offset := 0}, .locatorVault),
       ({label := "vaultFee", offset := 1}, .vaultFee),
       ({label := "withdrawalRequests", offset := 2}, .withdrawalRequests),
       ({label := "locatorRouter", offset := 3}, .locatorRouter),
       ({label := "stakingNotification", offset := 4}, .stakingNotification),
       ({label := "refund", offset := 5}, .refund)] }

end LidoTriggerableWithdrawalsGateway
end Blanc
