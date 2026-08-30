import Blanc.LidoTriggerableWithdrawalsGatewayTrigger
import Blanc.LinearDispatch

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
  pushB256 (count * 32) ::: pushB256 0 ::: Func.ret

def customErrorData (name : String) (args : List ArgType := []) : Bytes :=
  (signatureHash name args).toBytes.take 4

def runtimeError (name : String) (args : List ArgType := []) : Func :=
  Func.revSelector (customErrorData name args) (by
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
    (Func.rev <?> body)

def canonicalArg (index : B256) (body : Func) : Func :=
  (arg index ++ checkNonAddress) +++
    (Func.rev <?> body)

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
      <?> Func.rev)

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
      (pauseForUnpaused <?> .call pausedExpectedSlot)

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
      (pauseUntilUnpaused <?> .call pausedExpectedSlot)

def resume : Func :=
  onlyRole resumeRole <|
    ([pushB256 resumeSinceSlot, sload, timestamp, lt]) +++
      ((([timestamp, pushB256 resumeSinceSlot, sstore] ++
          emitNoData (signatureHash "Resumed" [])) +++ Func.stop)
        <?> .call resumedExpectedSlot)

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
  (mloadWord 2 ++ [pushB256 1, sub] ++ mstoreAt 4 ++
   [pushB256 0] ++ enumKeyFromMemoryAt 4 enumRoleRegion ++ [sstore] ++
   [pushB256 0] ++ enumKeyFromMemoryAt 4 enumAccountRegion ++ [sstore] ++
   clearRemovedLookup ++
   mloadWord 3 ++ [pushB256 1, sub, pushB256 roleRecordLengthSlot, sstore] ++
   emitRoleRevoked) +++ Func.stop

def clearRoleMembershipSwap : Func :=
  (mloadWord 3 ++ [pushB256 1, sub] ++ mstoreAt 4 ++
   mloadWord 2 ++ [pushB256 1, sub] ++ mstoreAt 5 ++
   enumKeyFromMemoryAt 4 enumRoleRegion ++ [sload] ++ mstoreAt 6 ++
   enumKeyFromMemoryAt 4 enumAccountRegion ++ [sload] ++ mstoreAt 7 ++
   mloadWord 6 ++ enumKeyFromMemoryAt 5 enumRoleRegion ++ [sstore] ++
   mloadWord 7 ++ enumKeyFromMemoryAt 5 enumAccountRegion ++ [sstore] ++
   mloadWord 2 ++ roleKeyFromMemoryAt 6 7 roleLookupIndexRegion ++ [sstore] ++
   [pushB256 0] ++ enumKeyFromMemoryAt 4 enumRoleRegion ++ [sstore] ++
   [pushB256 0] ++ enumKeyFromMemoryAt 4 enumAccountRegion ++ [sstore] ++
   clearRemovedLookup ++
   mloadWord 3 ++ [pushB256 1, sub, pushB256 roleRecordLengthSlot, sstore] ++
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
    (arg 1 ++ [caller, eq]) +++ (clearRoleMembership <?> Func.rev)

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
    (Func.rev <?> (fsig +++ linearDispatchWith fallbackSlot (funcs dp)))

def baseAux : List Func :=
  [Func.rev,
   runtimeError "AccessControlUnauthorizedAccount",
   runtimeError "AdminCannotBeZero",
   runtimeError "ZeroArgument" [.dynBytes],
   runtimeError "PausedExpected",
   runtimeError "ResumedExpected",
   runtimeError "ZeroPauseDuration",
   runtimeError "PauseUntilMustBeInFuture",
   Func.revData ((signatureHash "Panic" [.uint256]).toBytes.take 4 ++
     (Nat.toB256 0x11).toBytes),
   runtimeError "LimitExceeded",
   runtimeError "InsufficientFee" [.uint256, .uint256],
   runtimeError "FeeRefundFailed",
   Func.rev,
   Func.rev,
   Func.rev,
   Func.rev,
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
     [pushB256 68, pushB256 28]) +++ .last .rev]

def triggerRoleFailure : Func :=
  runtimeError "AccessControlUnauthorizedAccount"

def aux (dp : DeployParams) : List Func :=
  baseAux ++ Trigger.rebasedLocalAuxWithRoleFailure triggerAuxDelta dp
    triggerRoleFailure

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
