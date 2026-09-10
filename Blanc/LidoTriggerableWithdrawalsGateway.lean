import Blanc.LidoTriggerableWithdrawalsGatewayTrigger
import Blanc.LinearDispatch
import Blanc.SourceSiteCount

/-!
  Source-level Blanc runtime for the Triggerable Withdrawals Gateway.

  All selectors have an executable dispatch entry, including the nested
  `ValidatorExitData[]` decoder and outbound trigger choreography.
  AccessControlEnumerable is represented with full role/account/index lookup
  records and global role/account arrays; lookup mismatches refuse rather
  than alias, and removal uses swap-pop with moved-index repair.
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
def adminZeroSlot : Nat := 3
def zeroArgumentSlot : Nat := 4
def pausedExpectedSlot : Nat := 5
def resumedExpectedSlot : Nat := 6
def zeroPauseDurationSlot : Nat := 7
def pauseUntilPastSlot : Nat := 8
def arithmeticPanicSlot : Nat := 9
def limitErrorSlot : Nat := 10
def feeErrorSlot : Nat := 11
def refundErrorSlot : Nat := 12
def triggerNestedAbiSlot : Nat := 13
def roleMemberLoopSlot : Nat := 14
def roleCountLoopSlot : Nat := 15
def collisionRefusalSlot : Nat := 16
def tooLargeMaxExitRequestsLimitSlot : Nat := 17
def tooLargeFrameDurationSlot : Nat := 18
def tooLargeExitsPerFrameSlot : Nat := 19
def zeroFrameDurationSlot : Nat := 20
def limitCurrentComputeSlot : Nat := 21
def limitCurrentContinueSlot : Nat := 22
def setLimitAfterCurrentSlot : Nat := 23
def setLimitWriteSlot : Nat := 24
def consumeExitLimitSlot : Nat := 25
def consumeAfterCurrentSlot : Nat := 26
def exitRequestsLimitExceededSlot : Nat := 27

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

def roleAccountCheck (role : B256) (body : Func) : Func :=
  roleKeyForCaller role (regionWord roleLookupAccountRegion) +++
    (sload ::: caller ::: pushB256 addressMask ::: and ::: eq :::
      (body <?> .call collisionRefusalSlot))

def roleRecordCheck (role : B256) (body : Func) : Func :=
  roleKeyForCaller role (regionWord roleLookupRoleRegion) +++
    (sload ::: pushB256 role ::: eq :::
      (roleAccountCheck role body <?> .call collisionRefusalSlot))

def onlyRole (role : B256) (body : Func) : Func :=
  roleKeyForCaller role (regionWord roleLookupIndexRegion) +++
    (sload ::: iszero :::
      ((.call missingRoleSlot) <?> roleRecordCheck role body))

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

def roleIdentityMatchesMemory : Line :=
  roleKeyFromMemory roleLookupRoleRegion ++
  [sload] ++ mloadWord 0 ++ [eq] ++
  roleKeyFromMemory roleLookupAccountRegion ++
  [sload] ++ mloadWord 1 ++ [pushB256 addressMask, and, eq, and]

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
  (mloadWord 0 ++ [pushB256 maxExitRequestsLimitSlot, sstore] ++
   mloadWord 4 ++ [pushB256 prevExitRequestsLimitSlot, sstore] ++
   mloadWord 12 ++ [pushB256 (Nat.toB256 (2 ^ 32 - 1)), and,
     pushB256 prevTimestampSlot, sstore] ++
   mloadWord 2 ++ [pushB256 frameDurationInSecSlot, sstore] ++
   mloadWord 1 ++ [pushB256 exitsPerFrameSlot, sstore] ++
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
        mloadWord 4 ++ [pushB256 prevExitRequestsLimitSlot, sstore] ++
        mloadWord 12 ++ [pushB256 prevTimestampSlot, sstore]) +++
        Func.stop))

def consumeAfterCurrent : Func :=
  (mloadWord 8 ++ mloadWord 14 ++ [gt]) +++
    ((.call exitRequestsLimitExceededSlot) <?>
      consumeAfterCurrentSuccess)

def consumeExitLimit : Func :=
  ( [pushB256 maxExitRequestsLimitSlot, sload] ++ mstoreAt 13 ++
    [pushB256 prevExitRequestsLimitSlot, sload] ++ mstoreAt 4 ++
    [pushB256 prevTimestampSlot, sload] ++ mstoreAt 5 ++
    [pushB256 frameDurationInSecSlot, sload] ++ mstoreAt 6 ++
    [pushB256 exitsPerFrameSlot, sload] ++ mstoreAt 7 ++
    [timestamp] ++ mstoreAt 12 ++ [pushB256 2] ++ mstoreAt 11) +++
    ((mloadWord 13 ++ [iszero]) +++
      (Func.stop <?> .call limitCurrentComputeSlot))

def getExitRequestLimitFullInfo : Func :=
  ( [pushB256 maxExitRequestsLimitSlot, sload] ++ mstoreAt 0 ++
    [pushB256 exitsPerFrameSlot, sload] ++ mstoreAt 1 ++
    [pushB256 frameDurationInSecSlot, sload] ++ mstoreAt 2 ++
    [pushB256 prevExitRequestsLimitSlot, sload] ++ mstoreAt 4 ++
    [pushB256 prevTimestampSlot, sload] ++ mstoreAt 5 ++
    [pushB256 frameDurationInSecSlot, sload] ++ mstoreAt 6 ++
    [pushB256 exitsPerFrameSlot, sload] ++ mstoreAt 7 ++
    [pushB256 maxExitRequestsLimitSlot, sload] ++ mstoreAt 13 ++
    [timestamp] ++ mstoreAt 12 ++ [pushB256 0] ++ mstoreAt 11) +++
    .call limitCurrentComputeSlot

def getResumeSinceTimestamp : Func :=
  pushB256 resumeSinceSlot ::: sload ::: returnWord

def getRoleAdmin : Func :=
  requireStaticArgs 1 <| pushB256 defaultAdminRole ::: returnWord

def roleMemberScanAdvance : Func :=
  (mloadWord 2 ++ [pushB256 1, add] ++ mstoreAt 2) +++
    .call roleMemberLoopSlot

def roleMemberScanMatch : Func :=
  (mloadWord 3 ++ [pushB256 1, add] ++ mstoreAt 3) +++
    roleMemberScanAdvance

def roleMemberLoop : Func :=
  ([pushB256 roleRecordLengthSlot, sload] ++ mloadWord 2 ++ [lt]) +++
    (((enumKeyFromMemoryAt 2 enumRoleRegion ++ [sload] ++ mloadWord 0 ++ [eq]) +++
        (((mloadWord 3 ++ mloadWord 1 ++ [eq]) +++
            ((enumKeyFromMemoryAt 2 enumAccountRegion ++ [sload]) +++ returnWord)
              <?> roleMemberScanMatch))
          <?> roleMemberScanAdvance)
      <?> Func.revert)

def roleCountScanAdvance : Func :=
  (mloadWord 2 ++ [pushB256 1, add] ++ mstoreAt 2) +++
    .call roleCountLoopSlot

def roleCountLoop : Func :=
  ([pushB256 roleRecordLengthSlot, sload] ++ mloadWord 2 ++ [lt]) +++
    (((enumKeyFromMemoryAt 2 enumRoleRegion ++ [sload] ++ mloadWord 0 ++ [eq]) +++
        (((mloadWord 3 ++ [pushB256 1, add] ++ mstoreAt 3) +++
            roleCountScanAdvance)
          <?> roleCountScanAdvance))
      <?> ((mloadWord 3) +++ returnWord))

def getRoleMember : Func :=
  -- memory 0 = requested role; 1 = requested zero-based ordinal;
  -- 2 = global scan index; 3 = matching-role count.
  requireStaticArgs 2 <|
    (arg 0 ++ mstoreAt 0 ++ arg 1 ++ mstoreAt 1 ++
      [pushB256 0] ++ mstoreAt 2 ++ [pushB256 0] ++ mstoreAt 3) +++
      .call roleMemberLoopSlot

def getRoleMemberCount : Func :=
  requireStaticArgs 1 <|
    (arg 0 ++ mstoreAt 0 ++ [pushB256 0] ++ mstoreAt 2 ++
      [pushB256 0] ++ mstoreAt 3) +++
      .call roleCountLoopSlot

def hasRole : Func :=
  requireStaticArgs 2 <| canonicalArg 1 <|
    (roleKeyFromArgs roleLookupIndexRegion ++ [sload, iszero, iszero] ++
      roleKeyFromArgs roleLookupRoleRegion ++ [sload] ++ arg 0 ++ [eq, and] ++
      roleKeyFromArgs roleLookupAccountRegion ++ [sload] ++ arg 1 ++
        [pushB256 addressMask, and, eq, and]) +++
      returnWord

def isPaused : Func :=
  ([pushB256 resumeSinceSlot, sload, timestamp, lt] +++ returnWord)

def supportsInterface : Func :=
  requireStaticArgs 1 <|
    ((argBytes4 0 ++ [pushB256 0x01ffc9a7, eq]) +++
      (([pushB256 1] +++ returnWord) <?>
        ((argBytes4 0 ++ [pushB256 0x7965db0b, eq]) +++
          (([pushB256 1] +++ returnWord) <?>
            ((argBytes4 0 ++ [pushB256 0x5a05180f, eq]) +++
              (([pushB256 1] +++ returnWord) <?>
                ([pushB256 0] +++ returnWord)))))))

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
      roleKeyFromMemory roleLookupIndexRegion ++ [sload, iszero]) +++
      ((([pushB256 roleRecordLengthSlot, sload] ++ mstoreAt 2 ++
          mloadWord 2 ++ [pushB256 1, add] ++
            roleKeyFromMemory roleLookupIndexRegion ++ [sstore] ++
          mloadWord 0 ++ roleKeyFromMemory roleLookupRoleRegion ++ [sstore] ++
          mloadWord 1 ++ roleKeyFromMemory roleLookupAccountRegion ++ [sstore] ++
          mloadWord 0 ++ enumKeyFromMemory enumRoleRegion ++ [sstore] ++
          mloadWord 1 ++ enumKeyFromMemory enumAccountRegion ++ [sstore] ++
          mloadWord 2 ++ [pushB256 1, add, pushB256 roleRecordLengthSlot, sstore] ++
          emitRoleGranted) +++ Func.stop)
        <?>
        (roleIdentityMatchesMemory +++ (Func.stop <?> .call collisionRefusalSlot))))

def clearRemovedLookup : Line :=
  [pushB256 0] ++ roleKeyFromMemory roleLookupIndexRegion ++ [sstore] ++
  [pushB256 0] ++ roleKeyFromMemory roleLookupRoleRegion ++ [sstore] ++
  [pushB256 0] ++ roleKeyFromMemory roleLookupAccountRegion ++ [sstore]

def clearRoleMembershipLast : Func :=
  ([pushB256 1] ++ mloadWord 2 ++ [sub] ++ mstoreAt 4 ++
   [pushB256 0] ++ enumKeyFromMemoryAt 4 enumRoleRegion ++ [sstore] ++
   [pushB256 0] ++ enumKeyFromMemoryAt 4 enumAccountRegion ++ [sstore] ++
   clearRemovedLookup ++
   [pushB256 1] ++ mloadWord 3 ++ [sub, pushB256 roleRecordLengthSlot, sstore] ++
   emitRoleRevoked) +++ Func.stop

def clearRoleMembershipSwap : Func :=
  ([pushB256 1] ++ mloadWord 3 ++ [sub] ++ mstoreAt 4 ++
   [pushB256 1] ++ mloadWord 2 ++ [sub] ++ mstoreAt 5 ++
   enumKeyFromMemoryAt 4 enumRoleRegion ++ [sload] ++ mstoreAt 6 ++
   enumKeyFromMemoryAt 4 enumAccountRegion ++ [sload] ++ mstoreAt 7 ++
   mloadWord 6 ++ enumKeyFromMemoryAt 5 enumRoleRegion ++ [sstore] ++
   mloadWord 7 ++ enumKeyFromMemoryAt 5 enumAccountRegion ++ [sstore] ++
   mloadWord 2 ++ roleKeyFromMemoryAt 6 7 roleLookupIndexRegion ++ [sstore] ++
   [pushB256 0] ++ enumKeyFromMemoryAt 4 enumRoleRegion ++ [sstore] ++
   [pushB256 0] ++ enumKeyFromMemoryAt 4 enumAccountRegion ++ [sstore] ++
   clearRemovedLookup ++
   [pushB256 1] ++ mloadWord 3 ++ [sub, pushB256 roleRecordLengthSlot, sstore] ++
   emitRoleRevoked) +++ Func.stop

def clearRoleMembership : Func :=
    (arg 0 ++ mstoreAt 0 ++ arg 1 ++ mstoreAt 1 ++
     roleKeyFromMemory roleLookupIndexRegion ++ [sload] ++ mstoreAt 2 ++
     [pushB256 roleRecordLengthSlot, sload] ++ mstoreAt 3 ++
     mloadWord 2 ++ [iszero]) +++
      (Func.stop <?>
        (roleIdentityMatchesMemory +++
          (((mloadWord 2 ++ mloadWord 3 ++ [eq]) +++
              (clearRoleMembershipLast <?> clearRoleMembershipSwap))
            <?> .call collisionRefusalSlot)))

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
    [pushB256 maxExitRequestsLimitSlot, sload] ++ mstoreAt 13 ++
    [pushB256 prevExitRequestsLimitSlot, sload] ++ mstoreAt 4 ++
    [pushB256 prevTimestampSlot, sload] ++ mstoreAt 5 ++
    [pushB256 frameDurationInSecSlot, sload] ++ mstoreAt 6 ++
    [pushB256 exitsPerFrameSlot, sload] ++ mstoreAt 7 ++
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

/-! The trigger packet owns a 22-entry local auxiliary table.  The family
runtime already occupies global slots 1--27, so local slot one is rebased to
global slot 28 by adding 27 to every local call. -/
def triggerAuxDelta : Nat := 27

def triggerFullWithdrawals (dp : DeployParams) : Func :=
  Trigger.rebasedTrigger triggerAuxDelta dp

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

def runtimeMain (dp : DeployParams) : Func :=
  pushB256 4 ::: calldatasize ::: lt :::
    (Func.revert <?> (fsig +++ linearDispatchWith fallbackSlot (funcs dp)))

def baseAux : List Func :=
  [Func.revert,
   runtimeError "AccessControlUnauthorizedAccount",
   runtimeError "AdminCannotBeZero",
   runtimeError "ZeroArgument" [.dynBytes],
   runtimeError "PausedExpected",
   runtimeError "ResumedExpected",
   runtimeError "ZeroPauseDuration",
   runtimeError "PauseUntilMustBeInFuture",
   Func.revertData ((signatureHash "Panic" [.uint256]).toBytes.take 4 ++
     (Nat.toB256 0x11).toBytes),
   runtimeError "LimitExceeded",
   runtimeError "InsufficientFee" [.uint256, .uint256],
   runtimeError "FeeRefundFailed",
   Func.revert,
   roleMemberLoop,
   roleCountLoop,
   Func.revert,
   runtimeError "TooLargeMaxExitRequestsLimit",
   runtimeError "TooLargeFrameDuration",
   runtimeError "TooLargeExitsPerFrame",
   runtimeError "ZeroFrameDuration",
   limitCurrentCompute,
   limitCurrentContinue,
   setLimitAfterCurrent,
   setLimitWrite,
   consumeExitLimit,
   consumeAfterCurrent,
   ([pushB256 Trigger.exitLimitExceededSelector] ++ mstoreAt 0 ++
     mloadWord 14 ++ mstoreAt 1 ++ mloadWord 8 ++ mstoreAt 2 ++
     [pushB256 68, pushB256 28]) +++ .last .revert]

def triggerRoleFailure : Func :=
  runtimeError "AccessControlUnauthorizedAccount"

def aux (dp : DeployParams) : List Func :=
  baseAux ++ Trigger.rebasedLocalAuxWithRoleFailure triggerAuxDelta dp
    triggerRoleFailure

/-- Name a base runtime call target.  The structural recursion is the shared
owner `Blanc.Func.mapCalls`; the base arm of `CompositeLabel` is the naming. -/
def toBaseSymbolic (f : Func) : SymbolicFunc Trigger.CompositeLabel :=
  f.mapCalls Trigger.CompositeLabel.base

/-- Base naming is totally inverted by the composite coordinate map, for any base
count, so this needs no membership side condition. -/
theorem toBaseSymbolic_erase (baseCount : Nat) (f : Func) :
    (toBaseSymbolic f).erase (Trigger.compositeSlotOf baseCount) = f :=
  Func.erase_mapCalls_of_inverse Trigger.CompositeLabel.base
    (Trigger.compositeSlotOf baseCount) (fun _ => rfl) f

def symbolicBaseAux : List (Trigger.CompositeLabel × SymbolicFunc Trigger.CompositeLabel) :=
  [ (.base fallbackSlot, toBaseSymbolic Func.revert),
    (.base missingRoleSlot, toBaseSymbolic (runtimeError "AccessControlUnauthorizedAccount")),
    (.base adminZeroSlot, toBaseSymbolic (runtimeError "AdminCannotBeZero")),
    (.base zeroArgumentSlot, toBaseSymbolic (runtimeError "ZeroArgument" [.dynBytes])),
    (.base pausedExpectedSlot, toBaseSymbolic (runtimeError "PausedExpected")),
    (.base resumedExpectedSlot, toBaseSymbolic (runtimeError "ResumedExpected")),
    (.base zeroPauseDurationSlot, toBaseSymbolic (runtimeError "ZeroPauseDuration")),
    (.base pauseUntilPastSlot, toBaseSymbolic (runtimeError "PauseUntilMustBeInFuture")),
    (.base arithmeticPanicSlot, toBaseSymbolic (Func.revertData ((signatureHash "Panic" [.uint256]).toBytes.take 4 ++ (Nat.toB256 0x11).toBytes))),
    (.base limitErrorSlot, toBaseSymbolic (runtimeError "LimitExceeded")),
    (.base feeErrorSlot, toBaseSymbolic (runtimeError "InsufficientFee" [.uint256, .uint256])),
    (.base refundErrorSlot, toBaseSymbolic (runtimeError "FeeRefundFailed")),
    (.base triggerNestedAbiSlot, toBaseSymbolic Func.revert),
    (.base roleMemberLoopSlot, toBaseSymbolic roleMemberLoop),
    (.base roleCountLoopSlot, toBaseSymbolic roleCountLoop),
    (.base collisionRefusalSlot, toBaseSymbolic Func.revert),
    (.base tooLargeMaxExitRequestsLimitSlot, toBaseSymbolic (runtimeError "TooLargeMaxExitRequestsLimit")),
    (.base tooLargeFrameDurationSlot, toBaseSymbolic (runtimeError "TooLargeFrameDuration")),
    (.base tooLargeExitsPerFrameSlot, toBaseSymbolic (runtimeError "TooLargeExitsPerFrame")),
    (.base zeroFrameDurationSlot, toBaseSymbolic (runtimeError "ZeroFrameDuration")),
    (.base limitCurrentComputeSlot, toBaseSymbolic limitCurrentCompute),
    (.base limitCurrentContinueSlot, toBaseSymbolic limitCurrentContinue),
    (.base setLimitAfterCurrentSlot, toBaseSymbolic setLimitAfterCurrent),
    (.base setLimitWriteSlot, toBaseSymbolic setLimitWrite),
    (.base consumeExitLimitSlot, toBaseSymbolic consumeExitLimit),
    (.base consumeAfterCurrentSlot, toBaseSymbolic consumeAfterCurrent),
    (.base exitRequestsLimitExceededSlot, toBaseSymbolic (([pushB256 Trigger.exitLimitExceededSelector] ++ mstoreAt 0 ++
       mloadWord 14 ++ mstoreAt 1 ++ mloadWord 8 ++ mstoreAt 2 ++
       [pushB256 68, pushB256 28]) +++ .last .revert)) ]

theorem erase_symbolicBaseAux :
    symbolicBaseAux.map (fun (_, body) => body.erase (Trigger.compositeSlotOf 27)) = baseAux := by
  simp only [symbolicBaseAux, List.map_cons, List.map_nil, toBaseSymbolic_erase, baseAux]

/-- Control: the symbolic base table's labels are exactly the 27 named runtime
slots `fallbackSlot` … `exitRequestsLimitExceededSlot`, in consecutive order
starting at one.  `erase_symbolicBaseAux` discards labels, so without this the
base coordinates would be checked by nothing: a renumbered, duplicated or
reordered slot definition fails here. -/
theorem symbolicBaseAux_labels :
    symbolicBaseAux.map Prod.fst =
      (List.range 27).map (fun i => Trigger.CompositeLabel.base (i + 1)) :=
  rfl

/-- The 27-entry resolution skeleton in `Blanc.LidoTriggerableWithdrawalsGateway.Trigger`
carries the real table's labels, so the composite resolution controls stated over
it are controls about this program. -/
theorem symbolicBaseAux_labels_eq_skeleton :
    symbolicBaseAux.map Prod.fst = Trigger.base27AuxSkeleton.map Prod.fst := by
  rw [symbolicBaseAux_labels]
  rfl

theorem symbolicBaseAux_length : symbolicBaseAux.length = 27 := rfl

def symbolicTriggerAux (dp : DeployParams) :
    List (Trigger.CompositeLabel × SymbolicFunc Trigger.CompositeLabel) :=
  Trigger.symbolicLocalAuxWithRoleFailure dp triggerRoleFailure

def symbolicAux (dp : DeployParams) :
    List (Trigger.CompositeLabel × SymbolicFunc Trigger.CompositeLabel) :=
  symbolicBaseAux ++ symbolicTriggerAux dp

def symbolicFuncs (dp : DeployParams) : List (B256 × SymbolicFunc Trigger.CompositeLabel) :=
  [ (selPauseFor, toBaseSymbolic (nonpayable pauseFor)),
    (selIsPaused, toBaseSymbolic (nonpayable isPaused)),
    (selTriggerFullWithdrawals, Trigger.toCompositeSymbolic (Trigger.triggerFullWithdrawals dp)),
    (selPauseRole, toBaseSymbolic (nonpayable (constantWord pauseRole))),
    (selResumeRole, toBaseSymbolic (nonpayable (constantWord resumeRole))),
    (selAddFullWithdrawalRequestRole, toBaseSymbolic (nonpayable (constantWord addFullWithdrawalRequestRole))),
    (selTwExitLimitManagerRole, toBaseSymbolic (nonpayable (constantWord twExitLimitManagerRole))),
    (selTwrLimitPosition, toBaseSymbolic (nonpayable (constantWord twrLimitPosition))),
    (selVersion, toBaseSymbolic (nonpayable (constantWord version))),
    (selResume, toBaseSymbolic (nonpayable resume)),
    (selPauseUntil, toBaseSymbolic (nonpayable pauseUntil)),
    (selSetExitRequestLimit, toBaseSymbolic (nonpayable setExitRequestLimit)),
    (selGetExitRequestLimitFullInfo, toBaseSymbolic (nonpayable getExitRequestLimitFullInfo)),
    (selPauseInfinitely, toBaseSymbolic (nonpayable (constantWord pauseInfinitely))),
    (selGetResumeSinceTimestamp, toBaseSymbolic (nonpayable getResumeSinceTimestamp)),
    (selDefaultAdminRole, toBaseSymbolic (nonpayable (constantWord defaultAdminRole))),
    (selSupportsInterface, toBaseSymbolic (nonpayable supportsInterface)),
    (selHasRole, toBaseSymbolic (nonpayable hasRole)),
    (selGetRoleAdmin, toBaseSymbolic (nonpayable getRoleAdmin)),
    (selGrantRole, toBaseSymbolic (nonpayable grantRole)),
    (selRevokeRole, toBaseSymbolic (nonpayable revokeRole)),
    (selRenounceRole, toBaseSymbolic (nonpayable renounceRole)),
    (selGetRoleMember, toBaseSymbolic (nonpayable getRoleMember)),
    (selGetRoleMemberCount, toBaseSymbolic (nonpayable getRoleMemberCount)) ]

local infixr:65 " ++++ " => SymbolicFunc.prepend

def symbolicRuntimeMain (dp : DeployParams) : SymbolicFunc Trigger.CompositeLabel :=
  SymbolicFunc.next (pushB256 4) <|
  SymbolicFunc.next calldatasize <|
  SymbolicFunc.next lt <|
  SymbolicFunc.branch
    (fsig ++++ Blanc.symbolicLinearDispatchWith (.base fallbackSlot) (symbolicFuncs dp))
    (toBaseSymbolic Func.revert)

def symbolicRuntime (dp : DeployParams) : SymbolicProg Trigger.CompositeLabel :=
  ⟨.root, symbolicRuntimeMain dp, symbolicAux dp⟩

theorem symbolicRuntime_findLabel_root (dp : DeployParams) :
    (symbolicRuntime dp).findLabel? .root = some 0 :=
  rfl

theorem symbolicRuntime_findLabel_trigger (dp : DeployParams) (lbl : Trigger.TriggerLabel) :
    (symbolicRuntime dp).findLabel? (.trigger lbl) = some (27 + Trigger.localSlotOf lbl) := by
  cases lbl <;> rfl

/-- The 27 base slots resolve to themselves.  `CompositeLabel.base` carries an
unbounded `Nat`, so this is *not* total: `findLabel? (.base 0)` and
`findLabel? (.base 28)` are `none` while `compositeSlotOf 27` still answers `0`
and `28`.  That is why the composite program cannot discharge
`Blanc.resolve_eq_erase` with a single `cases target <;> rfl` the way a finite
label type does, and why the agreement has to be restricted to the call targets
that occur. -/
theorem symbolicRuntime_findLabel_base (dp : DeployParams) (k : Nat)
    (h1 : 1 ≤ k) (h2 : k ≤ 27) :
    (symbolicRuntime dp).findLabel? (.base k) = some k := by
  have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
      k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨
      k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨
      k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨
      k = 25 ∨ k = 26 ∨ k = 27 := by omega
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- Negative control for the bound above: the table really does stop at 27. -/
theorem symbolicRuntime_findLabel_base_out_of_range (dp : DeployParams) :
    (symbolicRuntime dp).findLabel? (.base 0) = none ∧
      (symbolicRuntime dp).findLabel? (.base 28) = none :=
  ⟨rfl, rfl⟩

theorem symbolicRuntime_findLabel_malformedAbi (dp : DeployParams) :
    (symbolicRuntime dp).findLabel? (.trigger .malformedAbi) = some 28 :=
  rfl

theorem symbolicRuntime_findLabel_validateArrayLoop (dp : DeployParams) :
    (symbolicRuntime dp).findLabel? (.trigger .validateArrayLoop) = some 39 :=
  rfl

theorem symbolicRuntime_findLabel_afterNestedValidation (dp : DeployParams) :
    (symbolicRuntime dp).findLabel? (.trigger .afterNestedValidation) = some 49 :=
  rfl

theorem symbolicRuntime_findLabel_malformedAbi_off_by_one (dp : DeployParams) :
    (symbolicRuntime dp).findLabel? (.trigger .malformedAbi) ≠ some 29 := by
  intro h
  injection h with h_eq
  revert h_eq
  decide

theorem symbolicRuntime_validateDefinitions (dp : DeployParams) :
    (symbolicRuntime dp).validateDefinitions = .ok () :=
  rfl

def runtime (dp : DeployParams) : Prog :=
  ⟨runtimeMain dp, aux dp⟩

theorem erase_symbolicFuncs (dp : DeployParams) :
    (symbolicFuncs dp).map (fun (s, f) => (s, f.erase (Trigger.compositeSlotOf 27))) = funcs dp := by
  simp only [symbolicFuncs, List.map_cons, List.map_nil, toBaseSymbolic_erase,
    Trigger.erase_toCompositeSymbolic_trigger, funcs, triggerFullWithdrawals,
    triggerAuxDelta]

theorem erase_symbolicRuntimeMain (dp : DeployParams) :
    (symbolicRuntimeMain dp).erase (Trigger.compositeSlotOf 27) = runtimeMain dp := by
  simp only [symbolicRuntimeMain, SymbolicFunc.erase, SymbolicFunc.erase_prepend,
    erase_symbolicLinearDispatchWith, erase_symbolicFuncs, toBaseSymbolic_erase,
    Trigger.compositeSlotOf, runtimeMain, fallbackSlot]

def runtimeCode (dp : DeployParams) : Bytes :=
  (Prog.compile (runtime dp)).getD []

/-! ## Closing the symbolic link

`erase_symbolicRuntimeMain` above pins the dispatch tree.  What follows pins the
49-entry auxiliary table and then resolves the whole symbolic program. -/

/-- The symbolic Trigger half of the auxiliary table erases to the rebased
numeric half.  The side condition is discharged on a closed term: deployment
parameters reach the bodies only through PUSH immediates, which
`Func.callTargets` discards. -/
theorem erase_symbolicTriggerAux (dp : DeployParams) :
    (symbolicTriggerAux dp).map (fun (_, body) => body.erase (Trigger.compositeSlotOf 27)) =
      Trigger.rebasedLocalAuxWithRoleFailure triggerAuxDelta dp triggerRoleFailure :=
  Trigger.erase_symbolicLocalAuxWithRoleFailure dp triggerRoleFailure
    (by rw [Trigger.flatMap_callTargets_localAuxWithRoleFailure]; decide +kernel)

/-- The full 49-entry auxiliary table erases to `aux`. -/
theorem erase_symbolicAux (dp : DeployParams) :
    (symbolicAux dp).map (fun (_, body) => body.erase (Trigger.compositeSlotOf 27)) = aux dp := by
  simp only [symbolicAux, aux, List.map_append, erase_symbolicBaseAux,
    erase_symbolicTriggerAux]

/-- Whole-program structural erasure: the symbolic runtime is the production
runtime under the composite coordinate map. -/
theorem erase_symbolicRuntime (dp : DeployParams) :
    (symbolicRuntime dp).erase (Trigger.compositeSlotOf 27) = runtime dp :=
  congrArg₂ Prog.mk (erase_symbolicRuntimeMain dp) (erase_symbolicAux dp)

/-- Every call target occurring in the symbolic runtime sits at the coordinate the
composite map assigns it.  Deployment parameters do not reach
`SymbolicFunc.calls`, so the check is closed. -/
theorem symbolicRuntime_callsOk (dp : DeployParams) :
    (symbolicRuntime dp).callsOk (Trigger.compositeSlotOf 27) = true := by
  have h : (symbolicRuntime dp).callsOk (Trigger.compositeSlotOf 27) =
      (symbolicRuntime ⟨0⟩).callsOk (Trigger.compositeSlotOf 27) := rfl
  rw [h]
  decide +kernel

/-- **The resolution theorem.**  Checked symbolic linking of the gateway runtime
yields exactly the production `runtime`.  This is also the anti-drift control: if
the symbolic program and `runtime` ever diverge, this stops typechecking. -/
theorem resolve_symbolicRuntime_eq (dp : DeployParams) :
    resolve (symbolicRuntime dp) = .ok (runtime dp) := by
  have h := resolve_eq_erase_of_callsOk (symbolicRuntime dp) (Trigger.compositeSlotOf 27)
    (symbolicRuntime_validateDefinitions dp) (symbolicRuntime_callsOk dp)
  rwa [erase_symbolicRuntime dp] at h

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

/-- Checked link certificate for the symbolic gateway runtime.  `runtime` is left
exactly as it was — the certificate is a proved view of it, not its definition —
so no downstream `unfold runtime`/`simp [runtime, aux, …]` normal form moves. -/
def symbolicLinkCert (dp : DeployParams) : LinkCertificate (symbolicRuntime dp) where
  resolved := runtime dp
  resolve_eq := resolve_symbolicRuntime_eq dp
  compiles := runtime_compiles dp

theorem symbolicLinkCert_resolved (dp : DeployParams) :
    (symbolicLinkCert dp).resolved = runtime dp :=
  rfl

/-- The certificate's compiled bytes are the production runtime bytes. -/
theorem symbolicLinkCert_bytes (dp : DeployParams) :
    (symbolicLinkCert dp).bytes = runtimeCode dp :=
  rfl

/-- Structural length of the compiled runtime, evaluated in the kernel through
`Prog.length_compile` so that the 15,948 emitted bytes are never materialised.
This is the first proof of this number: the published compatibility figure was
previously quoted with no Lean theorem behind it. -/
private theorem runtimeStructuralLengthZero :
    (((runtime ⟨0⟩).main :: (runtime ⟨0⟩).aux).map fun f => 1 + compsize f).sum = 15948 := by
  decide +kernel

/-- The zero-parameter member — the constructor's runtime template — compiles to
exactly 15,948 bytes. -/
theorem runtimeCode_length_zero : (runtimeCode ⟨0⟩).length = 15948 :=
  (Prog.length_compile (runtime_compile ⟨0⟩)).trans runtimeStructuralLengthZero

/-- The structural length is the same for every deployment parameter: each one
occupies a fixed-width PUSH32 immediate, which is exactly what
`runtime_compileShape_eq_zero` records.  Transported through
`Func.CompileShape.byteSize_compileShape` rather than by reducing two 15,948-byte
compilations against each other. -/
private theorem runtimeStructuralLength_eq_zero (dp : DeployParams) :
    (((runtime dp).main :: (runtime dp).aux).map fun f => 1 + compsize f).sum =
      (((runtime ⟨0⟩).main :: (runtime ⟨0⟩).aux).map fun f => 1 + compsize f).sum := by
  have h := runtime_compileShape_eq_zero dp
  have hm : (runtime dp).main.compileShape = (runtime ⟨0⟩).main.compileShape := by
    simpa [Prog.compileShape] using congrArg Prog.CompileShape.main h
  have ha : (runtime dp).aux.map Func.compileShape =
      (runtime ⟨0⟩).aux.map Func.compileShape := by
    simpa [Prog.compileShape] using congrArg Prog.CompileShape.aux h
  have hmap : ∀ l : List Func, (l.map fun f => 1 + compsize f) =
      (l.map Func.compileShape).map (fun sh => 1 + sh.byteSize) := by
    intro l
    simp [List.map_map, Func.CompileShape.byteSize_compileShape]
  rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, hmap, hmap,
    ← Func.CompileShape.byteSize_compileShape, ← Func.CompileShape.byteSize_compileShape,
    hm, ha]

/-- Every member of the locator-parameterized family compiles to 15,948 bytes. -/
theorem runtimeCode_length (dp : DeployParams) : (runtimeCode dp).length = 15948 :=
  ((Prog.length_compile (runtime_compile dp)).trans
    (runtimeStructuralLength_eq_zero dp)).trans runtimeStructuralLengthZero

def sourceSstoreSiteCount : Func → Nat :=
  Func.sourceSiteCount fun
    | .reg .sstore => true
    | _ => false

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
