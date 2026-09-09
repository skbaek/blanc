import Blanc.CycleWriteFree
import Blanc.LidoCircuitBreakerCore
import Blanc.LinearDispatch
import Blanc.SourceSiteCount
import Blanc.SymbolicProgram

/-!
Production Lido CircuitBreaker v1.0.0 runtime.

This module owns only executable runtime code and bounded artifact identities.
The contract vocabulary and tagged logical projection live in
`LidoCircuitBreakerCore`; the pure Registry boundary model lives in
`LidoCircuitBreakerRegistryModel`.  The program imports no sibling contract.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

/-- Deployment words are always PUSH32, so values never alter compiler shape. -/
def pushDeployWord (word : B256) : Ninst :=
  Ninst.push word.toBytes (by rw [B256.length_toBytes])

def tagTop (region : Nat) : Line := [pushB256 (regionWord region), Ninst.or]
def loadWord (word : B256) : Line := [pushB256 (word * 32), mload]

/-! Scratch memory is intentionally separate from the ABI/event words.  The
shared Registry kernel is reached by two tail calls, so a mode word selects its
register or pause continuation. -/

def targetWord : B256 := 16
def newPauserWord : B256 := 17
def previousPauserWord : B256 := 18
def continuationWord : B256 := 19
def removedIndexWord : B256 := 20
def arrayLengthWord : B256 := 21
def lastTargetWord : B256 := 22
def durationWord : B256 := 23

def targetKey : Line := loadWord targetWord ++ tagTop assignmentRegion
def targetIndexKey : Line := loadWord targetWord ++ tagTop indexRegion
def previousCountKey : Line :=
  loadWord previousPauserWord ++ tagTop countRegion
def newCountKey : Line := loadWord newPauserWord ++ tagTop countRegion
def lastTargetIndexKey : Line := loadWord lastTargetWord ++ tagTop indexRegion

/-! ## ABI identities -/

def customErrorData (name : String) (args : List ArgType := []) : Bytes :=
  (signatureHash name args).toBytes.take 4

private def runtimeError (name : String) : Func :=
  Func.revertSelector (customErrorData name) (by
    simp [customErrorData, B256.length_toBytes])

def pausableZeroError : Func := runtimeError "PausableZero"
def senderNotAdminError : Func := runtimeError "SenderNotAdmin"
def senderNotPauserError : Func := runtimeError "SenderNotPauser"
def pauseBelowMinError : Func := runtimeError "PauseDurationBelowMin"
def pauseAboveMaxError : Func := runtimeError "PauseDurationAboveMax"
def heartbeatBelowMinError : Func :=
  runtimeError "HeartbeatIntervalBelowMin"
def heartbeatAboveMaxError : Func :=
  runtimeError "HeartbeatIntervalAboveMax"
def heartbeatExpiredError : Func := runtimeError "HeartbeatExpired"
def pauseFailedError : Func := runtimeError "PauseFailed"
def reentrantCallError : Func := runtimeError "ReentrantCall"

def pauserSetEvent : B256 :=
  signatureHash "PauserSet" [.address, .address, .address]
def pauseDurationUpdatedEvent : B256 :=
  signatureHash "PauseDurationUpdated" [.uint256, .uint256]
def heartbeatIntervalUpdatedEvent : B256 :=
  signatureHash "HeartbeatIntervalUpdated" [.uint256, .uint256]
def heartbeatUpdatedEvent : B256 :=
  signatureHash "HeartbeatUpdated" [.address, .uint256]
def pauseTriggeredEvent : B256 :=
  signatureHash "PauseTriggered" [.address, .address, .uint256]
def circuitBreakerInitializedEvent : B256 :=
  signatureHash "CircuitBreakerInitialized"
    [.address, .uint256, .uint256, .uint256, .uint256]

def pauseForSelector : B256 := selector "pauseFor" [.uint256]
def isPausedSelector : B256 := selector "isPaused" []

/-! ## Stable auxiliary coordinates and symbolic labels -/

/-- Symbolic labels for the CircuitBreaker runtime.
Root maps to index 0, and auxiliary constructors map to indices 1 through 22. -/
inductive Label : Type
  | root
  | fallback
  | pausableZeroError
  | senderNotAdminError
  | senderNotPauserError
  | pauseBelowMinError
  | pauseAboveMaxError
  | heartbeatBelowMinError
  | heartbeatAboveMaxError
  | heartbeatExpiredError
  | pauseFailedError
  | reentrantCallError
  | emptyRevert
  | bubbleRevert
  | setPauser
  | appendTarget
  | afterOldPauser
  | removeTarget
  | finishSetPauser
  | registerAfterSet
  | pauseAfterSet
  | enumLoop
  | arithmeticPanic
  deriving DecidableEq, Repr

/-- Positional auxiliary slot index corresponding to each label.

The equations are `@[simp]` so that the `*Slot` abbreviations below, which are
now defined through `slotOf`, still reduce to their numeric literal in the
downstream `simp [runtime, aux, fooSlot]` table-lookup idiom. -/
@[simp] def slotOf : Label → Nat
  | .root => 0
  | .fallback => 1
  | .pausableZeroError => 2
  | .senderNotAdminError => 3
  | .senderNotPauserError => 4
  | .pauseBelowMinError => 5
  | .pauseAboveMaxError => 6
  | .heartbeatBelowMinError => 7
  | .heartbeatAboveMaxError => 8
  | .heartbeatExpiredError => 9
  | .pauseFailedError => 10
  | .reentrantCallError => 11
  | .emptyRevert => 12
  | .bubbleRevert => 13
  | .setPauser => 14
  | .appendTarget => 15
  | .afterOldPauser => 16
  | .removeTarget => 17
  | .finishSetPauser => 18
  | .registerAfterSet => 19
  | .pauseAfterSet => 20
  | .enumLoop => 21
  | .arithmeticPanic => 22

def fallbackSlot : Nat := slotOf .fallback
def pausableZeroErrorSlot : Nat := slotOf .pausableZeroError
def senderNotAdminErrorSlot : Nat := slotOf .senderNotAdminError
def senderNotPauserErrorSlot : Nat := slotOf .senderNotPauserError
def pauseBelowMinErrorSlot : Nat := slotOf .pauseBelowMinError
def pauseAboveMaxErrorSlot : Nat := slotOf .pauseAboveMaxError
def heartbeatBelowMinErrorSlot : Nat := slotOf .heartbeatBelowMinError
def heartbeatAboveMaxErrorSlot : Nat := slotOf .heartbeatAboveMaxError
def heartbeatExpiredErrorSlot : Nat := slotOf .heartbeatExpiredError
def pauseFailedErrorSlot : Nat := slotOf .pauseFailedError
def reentrantCallErrorSlot : Nat := slotOf .reentrantCallError
def emptyRevertSlot : Nat := slotOf .emptyRevert
def bubbleRevertSlot : Nat := slotOf .bubbleRevert
def setPauserSlot : Nat := slotOf .setPauser
def appendTargetSlot : Nat := slotOf .appendTarget
def afterOldPauserSlot : Nat := slotOf .afterOldPauser
def removeTargetSlot : Nat := slotOf .removeTarget
def finishSetPauserSlot : Nat := slotOf .finishSetPauser
def registerAfterSetSlot : Nat := slotOf .registerAfterSet
def pauseAfterSetSlot : Nat := slotOf .pauseAfterSet
def enumLoopSlot : Nat := slotOf .enumLoop
def arithmeticPanicSlot : Nat := slotOf .arithmeticPanic

/-! ## Small endpoint helpers -/

def returnWord : Func := mstoreAt 0 +++ returnMemoryRange 0 32

def returnDeployWord (w : B256) : Func :=
  pushDeployWord w ::: returnWord

def onlyAdmin (dp : DeployParams) (body : Func) : Func :=
  caller ::: pushDeployWord dp.admin ::: eq :::
  (body <?> (.call senderNotAdminErrorSlot))

def canonicalAddressArg (k : B256) (body : Func) : Func :=
  arg k +++ checkNonAddress +++
  ((.call emptyRevertSlot) <?> body)

/-- Modern Solidity's static-argument decoder rejects selector-matched short
calldata instead of letting CALLDATALOAD zero-padding synthesize arguments.
Trailing bytes remain accepted. -/
def requireStaticArgs (words : Nat) (body : Func) : Func :=
  pushB256 (Nat.toB256 (4 + 32 * words)) ::: calldatasize ::: lt :::
  (Func.revert <?> body)

/-- Compute `block.timestamp + heartbeatInterval` with Solidity 0.8 checked
addition.  On overflow this emits `Panic(0x11)`; otherwise `body` receives the
sum on top of the stack. -/
def checkedHeartbeatExpiry (body : Func) : Func :=
  timestamp ::: pushB256 heartbeatIntervalSlot ::: sload ::: add :::
  dup 0 ::: timestamp ::: swap 0 ::: lt :::
  ((.call arithmeticPanicSlot) <?> body)

def storeHeartbeatExpiryFromStack : Line :=
  dup 0 :: mstoreAt 0 ++
  caller :: tagTop expiryRegion ++ [sstore] ++
  [caller, pushB256 heartbeatUpdatedEvent] ++ logWith 1 0 1

/-! ## Read surface, including the unbounded enumeration cycle -/

def admin (dp : DeployParams) : Func := returnDeployWord dp.admin
def minPauseDuration (dp : DeployParams) : Func :=
  returnDeployWord dp.minPauseDuration
def maxPauseDuration (dp : DeployParams) : Func :=
  returnDeployWord dp.maxPauseDuration
def minHeartbeatInterval (dp : DeployParams) : Func :=
  returnDeployWord dp.minHeartbeatInterval
def maxHeartbeatInterval (dp : DeployParams) : Func :=
  returnDeployWord dp.maxHeartbeatInterval

def pauseDuration : Func :=
  pushB256 pauseDurationSlot ::: sload ::: returnWord

def heartbeatInterval : Func :=
  pushB256 heartbeatIntervalSlot ::: sload ::: returnWord

def heartbeatExpiry : Func :=
  requireStaticArgs 1 <| canonicalAddressArg 0 <|
    arg 0 +++ tagTop expiryRegion +++ sload ::: returnWord

def getPauser : Func :=
  requireStaticArgs 1 <| canonicalAddressArg 0 <|
    arg 0 +++ tagTop assignmentRegion +++ sload ::: returnWord

def getPausableCount : Func :=
  requireStaticArgs 1 <| canonicalAddressArg 0 <|
    arg 0 +++ tagTop countRegion +++ sload ::: returnWord

def isPauserLive : Func :=
  requireStaticArgs 1 <| canonicalAddressArg 0 <|
    arg 0 +++ tagTop expiryRegion +++ sload ::: timestamp ::: lt ::: returnWord

/-- Loop state is one stack word, `i`; the ABI length `n` remains at memory
offset 32.  A recursive iteration performs one SLOAD and one MSTORE, increments
`i`, then tail-calls this same table slot at constant EVM stack height.  Keeping
the cursor out of memory is load-bearing: an arbitrarily long ABI tail cannot
overwrite private loop state.  The finite bytecode contains no contract-chosen
bound. -/
def enumLoop : Func :=
  pushB256 32 ::: mload ::: dup 1 ::: lt :::
  (dup 0 ::: pushB256 1 ::: add ::: tagTop arrayRegion +++ sload :::
    dup 1 ::: pushB256 32 ::: mul ::: pushB256 64 ::: add ::: mstore :::
    pushB256 1 ::: add :::
    .call enumLoopSlot) <?>
  (pop ::: pushB256 32 ::: mload ::: pushB256 32 ::: mul :::
    pushB256 64 ::: add ::: pushB256 0 ::: Func.return_)

def getPausables : Func :=
  pushB256 32 ::: mstoreAt 0 +++
  pushB256 arrayLengthSlot ::: sload ::: mstoreAt 1 +++
  pushB256 0 :::
  .call enumLoopSlot

/-! ## Admin configuration writes -/

def setPauseDuration (dp : DeployParams) : Func :=
  requireStaticArgs 1 <| onlyAdmin dp <|
    pushDeployWord dp.minPauseDuration ::: arg 0 +++ lt :::
    ((.call pauseBelowMinErrorSlot) <?>
      (pushDeployWord dp.maxPauseDuration ::: arg 0 +++ gt :::
        ((.call pauseAboveMaxErrorSlot) <?>
          (pushB256 pauseDurationSlot ::: sload ::: mstoreAt 0 +++
            arg 0 +++ mstoreAt 1 +++
            pushB256 pauseDurationUpdatedEvent ::: logWith 0 0 2 +++
            arg 0 +++ pushB256 pauseDurationSlot ::: sstore ::: Func.stop))))

def setHeartbeatInterval (dp : DeployParams) : Func :=
  requireStaticArgs 1 <| onlyAdmin dp <|
    pushDeployWord dp.minHeartbeatInterval ::: arg 0 +++ lt :::
    ((.call heartbeatBelowMinErrorSlot) <?>
      (pushDeployWord dp.maxHeartbeatInterval ::: arg 0 +++ gt :::
        ((.call heartbeatAboveMaxErrorSlot) <?>
          (pushB256 heartbeatIntervalSlot ::: sload ::: mstoreAt 0 +++
            arg 0 +++ mstoreAt 1 +++
            pushB256 heartbeatIntervalUpdatedEvent ::: logWith 0 0 2 +++
            arg 0 +++ pushB256 heartbeatIntervalSlot ::: sstore ::: Func.stop))))

/-! ## One shared, source-shaped Registry mutation kernel -/

/-- Fresh-target arm: append target, write its one-based index, then length. -/
def appendTarget : Func :=
  pushB256 arrayLengthSlot ::: sload ::: pushB256 1 ::: add :::
  dup 0 ::: mstoreAt arrayLengthWord +++
  loadWord targetWord +++ loadWord arrayLengthWord +++ tagTop arrayRegion +++
  sstore :::
  loadWord arrayLengthWord +++ targetIndexKey +++ sstore :::
  loadWord arrayLengthWord +++ pushB256 arrayLengthSlot ::: sstore :::
  .call afterOldPauserSlot

/-- Unregistration arm: exact swap-and-pop projection, including the last-slot
clear and reverse-index repair even when the removed element is already last. -/
def removeTarget : Func :=
  targetIndexKey +++ sload ::: mstoreAt removedIndexWord +++
  pushB256 arrayLengthSlot ::: sload ::: mstoreAt arrayLengthWord +++
  loadWord arrayLengthWord +++ tagTop arrayRegion +++ sload :::
  mstoreAt lastTargetWord +++
  loadWord lastTargetWord +++ loadWord removedIndexWord +++ tagTop arrayRegion +++
  sstore :::
  loadWord removedIndexWord +++ lastTargetIndexKey +++ sstore :::
  pushB256 0 ::: loadWord arrayLengthWord +++ tagTop arrayRegion +++ sstore :::
  loadWord arrayLengthWord +++ pushB256 1 ::: swap 0 ::: sub :::
  pushB256 arrayLengthSlot ::: sstore :::
  pushB256 0 ::: targetIndexKey +++ sstore :::
  .call finishSetPauserSlot

/-- Shared entry prefix through assignment replacement and old-count handling. -/
def setPauserKernel : Func :=
  loadWord targetWord +++ iszero :::
  ((.call pausableZeroErrorSlot) <?>
    (targetKey +++ sload ::: dup 0 ::: mstoreAt previousPauserWord +++
      loadWord newPauserWord +++ targetKey +++ sstore :::
      iszero :::
      ((.call appendTargetSlot) <?>
        (previousCountKey +++ sload ::: pushB256 1 ::: swap 0 ::: sub :::
          previousCountKey +++ sstore ::: .call afterOldPauserSlot))))

/-- Second Registry phase: increment the new count or perform swap-and-pop. -/
def afterOldPauser : Func :=
  loadWord newPauserWord +++ iszero :::
  ((.call removeTargetSlot) <?>
    (newCountKey +++ sload ::: pushB256 1 ::: add :::
      newCountKey +++ sstore ::: .call finishSetPauserSlot))

/-- Common event and caller-continuation suffix. -/
def finishSetPauser : Func :=
  loadWord newPauserWord +++ loadWord previousPauserWord +++
  loadWord targetWord +++ pushB256 pauserSetEvent :::
  logWith 3 0 0 +++
  loadWord continuationWord +++ iszero :::
  ((.call registerAfterSetSlot) <?> (.call pauseAfterSetSlot))

def registerPauser (dp : DeployParams) : Func :=
  requireStaticArgs 2 <| canonicalAddressArg 0 <| canonicalAddressArg 1 <|
    onlyAdmin dp <|
      arg 0 +++ mstoreAt targetWord +++
      arg 1 +++ mstoreAt newPauserWord +++
      pushB256 0 ::: mstoreAt previousPauserWord +++
      pushB256 0 ::: mstoreAt continuationWord +++
      .call setPauserSlot

def registerAfterSet : Func :=
  loadWord previousPauserWord +++ iszero :::
  (loadWord newPauserWord +++ iszero :::
    (Func.stop <?>
      (checkedHeartbeatExpiry <|
        dup 0 ::: mstoreAt 0 +++
        loadWord newPauserWord +++ tagTop expiryRegion +++ sstore :::
        loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
        logWith 1 0 1 +++ Func.stop))) <?>
  (previousCountKey +++ sload ::: iszero :::
    (pushB256 0 ::: loadWord previousPauserWord +++ tagTop expiryRegion +++
      sstore ::: pushB256 0 ::: mstoreAt 0 +++
      loadWord previousPauserWord +++ pushB256 heartbeatUpdatedEvent :::
      logWith 1 0 1 +++
      loadWord newPauserWord +++ iszero :::
      (Func.stop <?>
        (checkedHeartbeatExpiry <|
          dup 0 ::: mstoreAt 0 +++
          loadWord newPauserWord +++ tagTop expiryRegion +++ sstore :::
          loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
          logWith 1 0 1 +++ Func.stop))) <?>
    (loadWord newPauserWord +++ iszero :::
      (Func.stop <?>
        (checkedHeartbeatExpiry <|
          dup 0 ::: mstoreAt 0 +++
          loadWord newPauserWord +++ tagTop expiryRegion +++ sstore :::
          loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
          logWith 1 0 1 +++ Func.stop))))

/-! ## Heartbeat and transient-guarded pause -/

def heartbeat : Func :=
  caller ::: tagTop countRegion +++ sload ::: iszero :::
  ((.call senderNotPauserErrorSlot) <?>
    (caller ::: tagTop expiryRegion +++ sload ::: timestamp ::: lt :::
      ((checkedHeartbeatExpiry <|
        storeHeartbeatExpiryFromStack +++ Func.stop) <?>
        (.call heartbeatExpiredErrorSlot))))

def pauseExpiryFinish : Func :=
  storeHeartbeatExpiryFromStack +++
  pushB256 0 ::: pushB256 lockKey ::: tstore ::: Func.stop

def pauseSuccess : Func :=
  loadWord durationWord +++ mstoreAt 0 +++
  caller ::: loadWord targetWord +++
  pushB256 pauseTriggeredEvent ::: logWith 2 0 1 +++
  caller ::: tagTop countRegion +++ sload ::: iszero :::
  ((pushB256 0 ::: pauseExpiryFinish) <?>
    (checkedHeartbeatExpiry <|
      pauseExpiryFinish))

/-- The successful `isPaused()` STATICCALL writes at most its first word to
memory zero.  Validate the retained returndata length and canonical Boolean
without copying the unused successful tail; the caller handles failure first
and still bubbles its complete returndata. -/
def decodePausedResult : Func :=
  returnDataShorterThan 32 +++
  ((.call emptyRevertSlot) <?>
    (loadWord 0 +++
      dup 0 ::: iszero :::
      ((.call pauseFailedErrorSlot) <?>
        (pushB256 1 ::: eq :::
          (pauseSuccess <?> (.call emptyRevertSlot))))))

def pauseAfterSet : Func :=
  loadWord targetWord +++ dup 0 ::: extcodesize ::: iszero :::
  ((.call emptyRevertSlot) <?>
    (pop :::
      pushB256 pauseForSelector ::: mstoreAt 8 +++
      loadWord durationWord +++ mstoreAt 9 +++
      pushList [0, 0, 36, 0x11c, 0] +++ loadWord targetWord +++ gas ::: call :::
      iszero :::
      ((.call bubbleRevertSlot) <?>
        (pushB256 isPausedSelector ::: mstoreAt 8 +++
          pushList [32, 0, 4, 0x11c] +++ loadWord targetWord +++ gas ::: staticcall :::
          iszero :::
          ((.call bubbleRevertSlot) <?>
            decodePausedResult)))))

def pause : Func :=
  requireStaticArgs 1 <| canonicalAddressArg 0 <|
    pushB256 lockKey ::: tload ::: iszero :::
    ((pushB256 1 ::: pushB256 lockKey ::: tstore :::
      arg 0 +++ tagTop assignmentRegion +++ sload ::: caller ::: eq :::
      ((caller ::: tagTop expiryRegion +++ sload ::: timestamp ::: lt :::
        ((pushB256 pauseDurationSlot ::: sload ::: mstoreAt durationWord +++
          arg 0 +++ mstoreAt targetWord +++
          pushB256 0 ::: mstoreAt newPauserWord +++
          pushB256 0 ::: mstoreAt previousPauserWord +++
          pushB256 1 ::: mstoreAt continuationWord +++
          .call setPauserSlot) <?> (.call heartbeatExpiredErrorSlot))) <?>
        (.call senderNotPauserErrorSlot))) <?>
      (.call reentrantCallErrorSlot))

/-! ## Integrated dispatcher and compiler input -/

def funcs (dp : DeployParams) : List (B256 × Func) :=
  [ (selector "pauseDuration" [], pauseDuration),
    (selector "MAX_PAUSE_DURATION" [], maxPauseDuration dp),
    (selector "ADMIN" [], admin dp),
    (selector "registerPauser" [.address, .address],
      registerPauser dp),
    (selector "heartbeat" [], heartbeat),
    (selector "getPauser" [.address], getPauser),
    (selector "getPausables" [], getPausables),
    (selector "heartbeatInterval" [], heartbeatInterval),
    (selector "setHeartbeatInterval" [.uint256],
      setHeartbeatInterval dp),
    (selector "pause" [.address], pause),
    (selector "MIN_PAUSE_DURATION" [], minPauseDuration dp),
    (selector "MAX_HEARTBEAT_INTERVAL" [],
      maxHeartbeatInterval dp),
    (selector "getPausableCount" [.address], getPausableCount),
    (selector "MIN_HEARTBEAT_INTERVAL" [],
      minHeartbeatInterval dp),
    (selector "heartbeatExpiry" [.address], heartbeatExpiry),
    (selector "setPauseDuration" [.uint256],
      setPauseDuration dp),
    (selector "isPauserLive" [.address], isPauserLive) ]

/-! The dispatcher remains entirely in Blanc's structured `Func.branch`
language.  Its four equality chains share one entry guard and are separated by
three balanced pivots, yielding the measured 5/4/4/4 Pareto topology without
direct calls or jumps to selector destinations. -/

def splitDispatch (pivot : B256) (left right : Func) : Func :=
  dup 0 ::: pushB256 pivot ::: gt ::: (left <?> right)

def firstSelector (entries : List (B256 × Func)) : B256 :=
  entries.head?.map Prod.fst |>.getD 0

def hybridDispatchWith (k : Nat)
    (entries : List (B256 × Func)) : Func :=
  let first := entries.take 5
  let second := (entries.drop 5).take 4
  let third := (entries.drop 9).take 4
  let fourth := entries.drop 13
  let left := splitDispatch (firstSelector second)
    (linearDispatchWith k first) (linearDispatchWith k second)
  let right := splitDispatch (firstSelector fourth)
    (linearDispatchWith k third) (linearDispatchWith k fourth)
  splitDispatch (firstSelector third) left right

def runtimeMain (dp : DeployParams) : Func :=
  callvalue ::: pushB256 4 ::: calldatasize ::: lt ::: Ninst.or :::
    (Func.revert <?> (fsig +++ hybridDispatchWith fallbackSlot (funcs dp)))

def panicData : Bytes :=
  (signatureHash "Panic" [.uint256]).toBytes.take 4 ++
    (Nat.toB256 0x11).toBytes

def arithmeticPanic : Func :=
  Func.revertData panicData

def aux : List Func :=
  [ Func.revert,
    pausableZeroError,
    senderNotAdminError,
    senderNotPauserError,
    pauseBelowMinError,
    pauseAboveMaxError,
    heartbeatBelowMinError,
    heartbeatAboveMaxError,
    heartbeatExpiredError,
    pauseFailedError,
    reentrantCallError,
    Func.revert,
    Func.revertReturnData,
    setPauserKernel,
    appendTarget,
    afterOldPauser,
    removeTarget,
    finishSetPauser,
    registerAfterSet,
    pauseAfterSet,
    enumLoop,
    arithmeticPanic ]

/-! ## Symbolic owner

The following symbolic representations author the CircuitBreaker runtime
using `SymbolicFunc Label` and label-based calls.
-/

local infixr:65 " <??> " => λ (f g : SymbolicFunc Label) => SymbolicFunc.branch g f
local infixr:65 " :::: " => SymbolicFunc.next
local infixr:65 " ++++ " => SymbolicFunc.prepend

def symbolicReturnWord : SymbolicFunc Label :=
  mstoreAt 0 ++++ pushList [32, 0] ++++ .last .return_

def symbolicReturnDeployWord (w : B256) : SymbolicFunc Label :=
  pushDeployWord w :::: symbolicReturnWord

def symbolicOnlyAdmin (dp : DeployParams) (body : SymbolicFunc Label) : SymbolicFunc Label :=
  caller :::: pushDeployWord dp.admin :::: eq ::::
  (body <??> (.call .senderNotAdminError))

def symbolicCanonicalAddressArg (k : B256) (body : SymbolicFunc Label) : SymbolicFunc Label :=
  arg k ++++ checkNonAddress ++++
  ((.call .emptyRevert) <??> body)

def symbolicRequireStaticArgs (words : Nat) (body : SymbolicFunc Label) : SymbolicFunc Label :=
  pushB256 (Nat.toB256 (4 + 32 * words)) :::: calldatasize :::: lt ::::
  (Func.liftCallFree Label Func.revert <??> body)

def symbolicCheckedHeartbeatExpiry (body : SymbolicFunc Label) : SymbolicFunc Label :=
  timestamp :::: pushB256 heartbeatIntervalSlot :::: sload :::: add ::::
  dup 0 :::: timestamp :::: swap 0 :::: lt ::::
  ((.call .arithmeticPanic) <??> body)

def symbolicAdmin (dp : DeployParams) : SymbolicFunc Label :=
  symbolicReturnDeployWord dp.admin

def symbolicMinPauseDuration (dp : DeployParams) : SymbolicFunc Label :=
  symbolicReturnDeployWord dp.minPauseDuration

def symbolicMaxPauseDuration (dp : DeployParams) : SymbolicFunc Label :=
  symbolicReturnDeployWord dp.maxPauseDuration

def symbolicMinHeartbeatInterval (dp : DeployParams) : SymbolicFunc Label :=
  symbolicReturnDeployWord dp.minHeartbeatInterval

def symbolicMaxHeartbeatInterval (dp : DeployParams) : SymbolicFunc Label :=
  symbolicReturnDeployWord dp.maxHeartbeatInterval

def symbolicPauseDuration : SymbolicFunc Label :=
  pushB256 pauseDurationSlot :::: sload :::: symbolicReturnWord

def symbolicHeartbeatInterval : SymbolicFunc Label :=
  pushB256 heartbeatIntervalSlot :::: sload :::: symbolicReturnWord

def symbolicHeartbeatExpiry : SymbolicFunc Label :=
  symbolicRequireStaticArgs 1 <| symbolicCanonicalAddressArg 0 <|
    arg 0 ++++ tagTop expiryRegion ++++ sload :::: symbolicReturnWord

def symbolicGetPauser : SymbolicFunc Label :=
  symbolicRequireStaticArgs 1 <| symbolicCanonicalAddressArg 0 <|
    arg 0 ++++ tagTop assignmentRegion ++++ sload :::: symbolicReturnWord

def symbolicGetPausableCount : SymbolicFunc Label :=
  symbolicRequireStaticArgs 1 <| symbolicCanonicalAddressArg 0 <|
    arg 0 ++++ tagTop countRegion ++++ sload :::: symbolicReturnWord

def symbolicIsPauserLive : SymbolicFunc Label :=
  symbolicRequireStaticArgs 1 <| symbolicCanonicalAddressArg 0 <|
    arg 0 ++++ tagTop expiryRegion ++++ sload :::: timestamp :::: lt :::: symbolicReturnWord

def symbolicEnumLoop : SymbolicFunc Label :=
  pushB256 32 :::: mload :::: dup 1 :::: lt ::::
  (dup 0 :::: pushB256 1 :::: add :::: tagTop arrayRegion ++++ sload ::::
    dup 1 :::: pushB256 32 :::: mul :::: pushB256 64 :::: add :::: mstore ::::
    pushB256 1 :::: add ::::
    .call .enumLoop) <??>
  (pop :::: pushB256 32 :::: mload :::: pushB256 32 :::: mul ::::
    pushB256 64 :::: add :::: pushB256 0 :::: .last .return_)

def symbolicGetPausables : SymbolicFunc Label :=
  pushB256 32 :::: mstoreAt 0 ++++
  pushB256 arrayLengthSlot :::: sload :::: mstoreAt 1 ++++
  pushB256 0 ::::
  .call .enumLoop

def symbolicSetPauseDuration (dp : DeployParams) : SymbolicFunc Label :=
  symbolicRequireStaticArgs 1 <| symbolicOnlyAdmin dp <|
    pushDeployWord dp.minPauseDuration :::: arg 0 ++++ lt ::::
    ((.call .pauseBelowMinError) <??>
      (pushDeployWord dp.maxPauseDuration :::: arg 0 ++++ gt ::::
        ((.call .pauseAboveMaxError) <??>
          (pushB256 pauseDurationSlot :::: sload :::: mstoreAt 0 ++++
            arg 0 ++++ mstoreAt 1 ++++
            pushB256 pauseDurationUpdatedEvent :::: logWith 0 0 2 ++++
            arg 0 ++++ pushB256 pauseDurationSlot :::: sstore :::: .last .stop))))

def symbolicSetHeartbeatInterval (dp : DeployParams) : SymbolicFunc Label :=
  symbolicRequireStaticArgs 1 <| symbolicOnlyAdmin dp <|
    pushDeployWord dp.minHeartbeatInterval :::: arg 0 ++++ lt ::::
    ((.call .heartbeatBelowMinError) <??>
      (pushDeployWord dp.maxHeartbeatInterval :::: arg 0 ++++ gt ::::
        ((.call .heartbeatAboveMaxError) <??>
          (pushB256 heartbeatIntervalSlot :::: sload :::: mstoreAt 0 ++++
            arg 0 ++++ mstoreAt 1 ++++
            pushB256 heartbeatIntervalUpdatedEvent :::: logWith 0 0 2 ++++
            arg 0 ++++ pushB256 heartbeatIntervalSlot :::: sstore :::: .last .stop))))

def symbolicAppendTarget : SymbolicFunc Label :=
  pushB256 arrayLengthSlot :::: sload :::: pushB256 1 :::: add ::::
  dup 0 :::: mstoreAt arrayLengthWord ++++
  loadWord targetWord ++++ loadWord arrayLengthWord ++++ tagTop arrayRegion ++++
  sstore ::::
  loadWord arrayLengthWord ++++ targetIndexKey ++++ sstore ::::
  loadWord arrayLengthWord ++++ pushB256 arrayLengthSlot :::: sstore ::::
  .call .afterOldPauser

def symbolicRemoveTarget : SymbolicFunc Label :=
  targetIndexKey ++++ sload :::: mstoreAt removedIndexWord ++++
  pushB256 arrayLengthSlot :::: sload :::: mstoreAt arrayLengthWord ++++
  loadWord arrayLengthWord ++++ tagTop arrayRegion ++++ sload ::::
  mstoreAt lastTargetWord ++++
  loadWord lastTargetWord ++++ loadWord removedIndexWord ++++ tagTop arrayRegion ++++
  sstore ::::
  loadWord removedIndexWord ++++ lastTargetIndexKey ++++ sstore ::::
  pushB256 0 :::: loadWord arrayLengthWord ++++ tagTop arrayRegion ++++ sstore ::::
  loadWord arrayLengthWord ++++ pushB256 1 :::: swap 0 :::: sub ::::
  pushB256 arrayLengthSlot :::: sstore ::::
  pushB256 0 :::: targetIndexKey ++++ sstore ::::
  .call .finishSetPauser

def symbolicSetPauserKernel : SymbolicFunc Label :=
  loadWord targetWord ++++ iszero ::::
  ((.call .pausableZeroError) <??>
    (targetKey ++++ sload :::: dup 0 :::: mstoreAt previousPauserWord ++++
      loadWord newPauserWord ++++ targetKey ++++ sstore ::::
      iszero ::::
      ((.call .appendTarget) <??>
        (previousCountKey ++++ sload :::: pushB256 1 :::: swap 0 :::: sub ::::
          previousCountKey ++++ sstore :::: .call .afterOldPauser))))

def symbolicAfterOldPauser : SymbolicFunc Label :=
  loadWord newPauserWord ++++ iszero ::::
  ((.call .removeTarget) <??>
    (newCountKey ++++ sload :::: pushB256 1 :::: add ::::
      newCountKey ++++ sstore :::: .call .finishSetPauser))

def symbolicFinishSetPauser : SymbolicFunc Label :=
  loadWord newPauserWord ++++ loadWord previousPauserWord ++++
  loadWord targetWord ++++ pushB256 pauserSetEvent ::::
  logWith 3 0 0 ++++
  loadWord continuationWord ++++ iszero ::::
  ((.call .registerAfterSet) <??> (.call .pauseAfterSet))

def symbolicRegisterPauser (dp : DeployParams) : SymbolicFunc Label :=
  symbolicRequireStaticArgs 2 <| symbolicCanonicalAddressArg 0 <| symbolicCanonicalAddressArg 1 <|
    symbolicOnlyAdmin dp <|
      arg 0 ++++ mstoreAt targetWord ++++
      arg 1 ++++ mstoreAt newPauserWord ++++
      pushB256 0 :::: mstoreAt previousPauserWord ++++
      pushB256 0 :::: mstoreAt continuationWord ++++
      .call .setPauser

def symbolicRegisterAfterSet : SymbolicFunc Label :=
  loadWord previousPauserWord ++++ iszero ::::
  (loadWord newPauserWord ++++ iszero ::::
    (.last .stop <??>
      (symbolicCheckedHeartbeatExpiry <|
        dup 0 :::: mstoreAt 0 ++++
        loadWord newPauserWord ++++ tagTop expiryRegion ++++ sstore ::::
        loadWord newPauserWord ++++ pushB256 heartbeatUpdatedEvent ::::
        logWith 1 0 1 ++++ .last .stop))) <??>
  (previousCountKey ++++ sload :::: iszero ::::
    (pushB256 0 :::: loadWord previousPauserWord ++++ tagTop expiryRegion ++++
      sstore :::: pushB256 0 :::: mstoreAt 0 ++++
      loadWord previousPauserWord ++++ pushB256 heartbeatUpdatedEvent ::::
      logWith 1 0 1 ++++
      loadWord newPauserWord ++++ iszero ::::
      (.last .stop <??>
        (symbolicCheckedHeartbeatExpiry <|
          dup 0 :::: mstoreAt 0 ++++
          loadWord newPauserWord ++++ tagTop expiryRegion ++++ sstore ::::
          loadWord newPauserWord ++++ pushB256 heartbeatUpdatedEvent ::::
          logWith 1 0 1 ++++ .last .stop))) <??>
    (loadWord newPauserWord ++++ iszero ::::
      (.last .stop <??>
        (symbolicCheckedHeartbeatExpiry <|
          dup 0 :::: mstoreAt 0 ++++
          loadWord newPauserWord ++++ tagTop expiryRegion ++++ sstore ::::
          loadWord newPauserWord ++++ pushB256 heartbeatUpdatedEvent ::::
          logWith 1 0 1 ++++ .last .stop))))

def symbolicHeartbeat : SymbolicFunc Label :=
  caller :::: tagTop countRegion ++++ sload :::: iszero ::::
  ((.call .senderNotPauserError) <??>
    (caller :::: tagTop expiryRegion ++++ sload :::: timestamp :::: lt ::::
      ((symbolicCheckedHeartbeatExpiry <|
        storeHeartbeatExpiryFromStack ++++ .last .stop) <??>
        (.call .heartbeatExpiredError))))

def symbolicPauseExpiryFinish : SymbolicFunc Label :=
  storeHeartbeatExpiryFromStack ++++
  pushB256 0 :::: pushB256 lockKey :::: tstore :::: .last .stop

def symbolicPauseSuccess : SymbolicFunc Label :=
  loadWord durationWord ++++ mstoreAt 0 ++++
  caller :::: loadWord targetWord ++++
  pushB256 pauseTriggeredEvent :::: logWith 2 0 1 ++++
  caller :::: tagTop countRegion ++++ sload :::: iszero ::::
  ((pushB256 0 :::: symbolicPauseExpiryFinish) <??>
    (symbolicCheckedHeartbeatExpiry <|
      symbolicPauseExpiryFinish))

def symbolicDecodePausedResult : SymbolicFunc Label :=
  returnDataShorterThan 32 ++++
  ((.call .emptyRevert) <??>
    (loadWord 0 ++++
      dup 0 :::: iszero ::::
      ((.call .pauseFailedError) <??>
        (pushB256 1 :::: eq ::::
          (symbolicPauseSuccess <??> (.call .emptyRevert))))))

def symbolicPauseAfterSet : SymbolicFunc Label :=
  loadWord targetWord ++++ dup 0 :::: extcodesize :::: iszero ::::
  ((.call .emptyRevert) <??>
    (pop ::::
      pushB256 pauseForSelector :::: mstoreAt 8 ++++
      loadWord durationWord ++++ mstoreAt 9 ++++
      pushList [0, 0, 36, 0x11c, 0] ++++ loadWord targetWord ++++ gas :::: Ninst.call ::::
      iszero ::::
      ((.call .bubbleRevert) <??>
        (pushB256 isPausedSelector :::: mstoreAt 8 ++++
          pushList [32, 0, 4, 0x11c] ++++ loadWord targetWord ++++ gas :::: staticcall ::::
          iszero ::::
          ((.call .bubbleRevert) <??>
            symbolicDecodePausedResult)))))

def symbolicPause : SymbolicFunc Label :=
  symbolicRequireStaticArgs 1 <| symbolicCanonicalAddressArg 0 <|
    pushB256 lockKey :::: tload :::: iszero ::::
    ((pushB256 1 :::: pushB256 lockKey :::: tstore ::::
      arg 0 ++++ tagTop assignmentRegion ++++ sload :::: caller :::: eq ::::
      ((caller :::: tagTop expiryRegion ++++ sload :::: timestamp :::: lt ::::
        ((pushB256 pauseDurationSlot :::: sload :::: mstoreAt durationWord ++++
          arg 0 ++++ mstoreAt targetWord ++++
          pushB256 0 :::: mstoreAt newPauserWord ++++
          pushB256 0 :::: mstoreAt previousPauserWord ++++
          pushB256 1 :::: mstoreAt continuationWord ++++
          .call .setPauser) <??> (.call .heartbeatExpiredError))) <??>
        (.call .senderNotPauserError))) <??>
      (.call .reentrantCallError))

def symbolicFuncs (dp : DeployParams) : List (B256 × SymbolicFunc Label) :=
  [ (selector "pauseDuration" [], symbolicPauseDuration),
    (selector "MAX_PAUSE_DURATION" [], symbolicMaxPauseDuration dp),
    (selector "ADMIN" [], symbolicAdmin dp),
    (selector "registerPauser" [.address, .address],
      symbolicRegisterPauser dp),
    (selector "heartbeat" [], symbolicHeartbeat),
    (selector "getPauser" [.address], symbolicGetPauser),
    (selector "getPausables" [], symbolicGetPausables),
    (selector "heartbeatInterval" [], symbolicHeartbeatInterval),
    (selector "setHeartbeatInterval" [.uint256],
      symbolicSetHeartbeatInterval dp),
    (selector "pause" [.address], symbolicPause),
    (selector "MIN_PAUSE_DURATION" [], symbolicMinPauseDuration dp),
    (selector "MAX_HEARTBEAT_INTERVAL" [],
      symbolicMaxHeartbeatInterval dp),
    (selector "getPausableCount" [.address], symbolicGetPausableCount),
    (selector "MIN_HEARTBEAT_INTERVAL" [],
      symbolicMinHeartbeatInterval dp),
    (selector "heartbeatExpiry" [.address], symbolicHeartbeatExpiry),
    (selector "setPauseDuration" [.uint256],
      symbolicSetPauseDuration dp),
    (selector "isPauserLive" [.address], symbolicIsPauserLive) ]

def symbolicLinearDispatchWith (fb : Label) : List (B256 × SymbolicFunc Label) → SymbolicFunc Label
  | [] => .call fb
  | [(word, body)] =>
      pushB256 word :::: eq :::: (body <??> .call fb)
  | (word, body) :: rest =>
      dup 0 :::: pushB256 word :::: eq ::::
        ((pop :::: body) <??> symbolicLinearDispatchWith fb rest)

def symbolicSplitDispatch (pivot : B256) (left right : SymbolicFunc Label) : SymbolicFunc Label :=
  dup 0 :::: pushB256 pivot :::: gt :::: (left <??> right)

def symbolicFirstSelector (entries : List (B256 × SymbolicFunc Label)) : B256 :=
  entries.head?.map Prod.fst |>.getD 0

def symbolicHybridDispatchWith (k : Label)
    (entries : List (B256 × SymbolicFunc Label)) : SymbolicFunc Label :=
  let first := entries.take 5
  let second := (entries.drop 5).take 4
  let third := (entries.drop 9).take 4
  let fourth := entries.drop 13
  let left := symbolicSplitDispatch (symbolicFirstSelector second)
    (symbolicLinearDispatchWith k first) (symbolicLinearDispatchWith k second)
  let right := symbolicSplitDispatch (symbolicFirstSelector fourth)
    (symbolicLinearDispatchWith k third) (symbolicLinearDispatchWith k fourth)
  symbolicSplitDispatch (symbolicFirstSelector third) left right

def symbolicRuntimeMain (dp : DeployParams) : SymbolicFunc Label :=
  callvalue :::: pushB256 4 :::: calldatasize :::: lt :::: Ninst.or ::::
    (Func.liftCallFree Label Func.revert <??> (fsig ++++ symbolicHybridDispatchWith .fallback (symbolicFuncs dp)))
def symbolicFallback : SymbolicFunc Label := Func.liftCallFree Label Func.revert
def symbolicPausableZeroError : SymbolicFunc Label := Func.liftCallFree Label pausableZeroError
def symbolicSenderNotAdminError : SymbolicFunc Label := Func.liftCallFree Label senderNotAdminError
def symbolicSenderNotPauserError : SymbolicFunc Label := Func.liftCallFree Label senderNotPauserError
def symbolicPauseBelowMinError : SymbolicFunc Label := Func.liftCallFree Label pauseBelowMinError
def symbolicPauseAboveMaxError : SymbolicFunc Label := Func.liftCallFree Label pauseAboveMaxError
def symbolicHeartbeatBelowMinError : SymbolicFunc Label := Func.liftCallFree Label heartbeatBelowMinError
def symbolicHeartbeatAboveMaxError : SymbolicFunc Label := Func.liftCallFree Label heartbeatAboveMaxError
def symbolicHeartbeatExpiredError : SymbolicFunc Label := Func.liftCallFree Label heartbeatExpiredError
def symbolicPauseFailedError : SymbolicFunc Label := Func.liftCallFree Label pauseFailedError
def symbolicReentrantCallError : SymbolicFunc Label := Func.liftCallFree Label reentrantCallError
def symbolicEmptyRevert : SymbolicFunc Label := Func.liftCallFree Label Func.revert
def symbolicBubbleRevert : SymbolicFunc Label := Func.liftCallFree Label Func.revertReturnData
def symbolicArithmeticPanic : SymbolicFunc Label :=
  Func.liftCallFree Label arithmeticPanic (by decide +kernel)

def symbolicAux : List (Label × SymbolicFunc Label) :=
  [ (.fallback, symbolicFallback),
    (.pausableZeroError, symbolicPausableZeroError),
    (.senderNotAdminError, symbolicSenderNotAdminError),
    (.senderNotPauserError, symbolicSenderNotPauserError),
    (.pauseBelowMinError, symbolicPauseBelowMinError),
    (.pauseAboveMaxError, symbolicPauseAboveMaxError),
    (.heartbeatBelowMinError, symbolicHeartbeatBelowMinError),
    (.heartbeatAboveMaxError, symbolicHeartbeatAboveMaxError),
    (.heartbeatExpiredError, symbolicHeartbeatExpiredError),
    (.pauseFailedError, symbolicPauseFailedError),
    (.reentrantCallError, symbolicReentrantCallError),
    (.emptyRevert, symbolicEmptyRevert),
    (.bubbleRevert, symbolicBubbleRevert),
    (.setPauser, symbolicSetPauserKernel),
    (.appendTarget, symbolicAppendTarget),
    (.afterOldPauser, symbolicAfterOldPauser),
    (.removeTarget, symbolicRemoveTarget),
    (.finishSetPauser, symbolicFinishSetPauser),
    (.registerAfterSet, symbolicRegisterAfterSet),
    (.pauseAfterSet, symbolicPauseAfterSet),
    (.enumLoop, symbolicEnumLoop),
    (.arithmeticPanic, symbolicArithmeticPanic) ]

/-- Symbolic CircuitBreaker program parameterized by deployment words. -/
def symbolicRuntime (dp : DeployParams) : SymbolicProg Label :=
  ⟨.root, symbolicRuntimeMain dp, symbolicAux⟩

/-- Frozen pre-migration numeric runtime witness. -/
def legacyRuntime (dp : DeployParams) : Prog :=
  ⟨runtimeMain dp, aux⟩

/-! ## Artifact shape and source inventories -/

/-- The executable selector list is definitionally the Core metadata list. -/
theorem funcs_selectors_eq_runtimeEndpoints (dp : DeployParams) :
    (funcs dp).map Prod.fst = runtimeEndpoints.map AbiEndpoint.selector := by
  rfl

theorem funcs_sorted (dp : DeployParams) :
    DispatchTree.sorted (funcs dp) = true := by
  change DispatchTree.sorted (funcs ⟨0, 0, 0, 0, 0⟩) = true
  decide +kernel

/-! ## Parameter-independent compiler shape

The deployed words change instruction payloads but not widths.  The following
erasure propagates that fact through the exact linear-chain and hybrid
dispatcher builders without asking the elaborator to normalize the complete
runtime. -/

private def dispatchEntryShapes (xs : List (B256 × Func)) :
    List (B256 × Func.CompileShape) :=
  xs.map fun wp => (wp.1, wp.2.compileShape)

private theorem linearDispatchWith_compileShape_eq
    {xs ys : List (B256 × Func)}
    (h : dispatchEntryShapes xs = dispatchEntryShapes ys) (k : Nat) :
    (linearDispatchWith k xs).compileShape =
      (linearDispatchWith k ys).compileShape := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp [dispatchEntryShapes] at h
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases ys with
          | nil => simp [dispatchEntryShapes] at h
          | cons y ys =>
              cases ys with
              | nil =>
                  cases x with
                  | mk xw xb =>
                    cases y with
                    | mk yw yb =>
                      simp [dispatchEntryShapes] at h
                      rcases h with ⟨rfl, hb⟩
                      simp [linearDispatchWith, Func.compileShape, hb]
              | cons y' ys => simp [dispatchEntryShapes] at h
      | cons x' xs =>
          cases ys with
          | nil => simp [dispatchEntryShapes] at h
          | cons y ys =>
              cases ys with
              | nil => simp [dispatchEntryShapes] at h
              | cons y' ys =>
                  cases x with
                  | mk xw xb =>
                    cases y with
                    | mk yw yb =>
                      have hhead :
                          (xw, xb.compileShape) = (yw, yb.compileShape) := by
                        simpa [dispatchEntryShapes] using congrArg List.head? h
                      have htail :
                          dispatchEntryShapes (x' :: xs) =
                            dispatchEntryShapes (y' :: ys) := by
                        simpa [dispatchEntryShapes] using congrArg List.tail h
                      have hw : xw = yw := congrArg Prod.fst hhead
                      have hb : xb.compileShape = yb.compileShape :=
                        congrArg Prod.snd hhead
                      subst yw
                      simp only [linearDispatchWith, Func.compileShape]
                      rw [hb, ih htail]

private theorem splitDispatch_compileShape_eq
    {pivot pivot' : B256} {left right left' right' : Func}
    (hp : pivot = pivot')
    (hl : left.compileShape = left'.compileShape)
    (hr : right.compileShape = right'.compileShape) :
    (splitDispatch pivot left right).compileShape =
      (splitDispatch pivot' left' right').compileShape := by
  subst pivot'
  simp [splitDispatch, Func.compileShape, hl, hr]

private theorem firstSelector_eq_of_dispatchEntryShapes_eq
    {xs ys : List (B256 × Func)}
    (h : dispatchEntryShapes xs = dispatchEntryShapes ys) :
    firstSelector xs = firstSelector ys := by
  cases xs with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp [dispatchEntryShapes] at h
  | cons x xs =>
      cases ys with
      | nil => simp [dispatchEntryShapes] at h
      | cons y ys =>
          have hhead :
              (x.1, x.2.compileShape) = (y.1, y.2.compileShape) := by
            simpa [dispatchEntryShapes] using congrArg List.head? h
          simpa [firstSelector] using congrArg Prod.fst hhead

private theorem hybridDispatchWith_compileShape_eq
    {xs ys : List (B256 × Func)}
    (h : dispatchEntryShapes xs = dispatchEntryShapes ys) (k : Nat) :
    (hybridDispatchWith k xs).compileShape =
      (hybridDispatchWith k ys).compileShape := by
  have htake (n : Nat) :
      dispatchEntryShapes (xs.take n) = dispatchEntryShapes (ys.take n) := by
    simpa [dispatchEntryShapes] using congrArg (List.take n) h
  have hdrop (n : Nat) :
      dispatchEntryShapes (xs.drop n) = dispatchEntryShapes (ys.drop n) := by
    simpa [dispatchEntryShapes] using congrArg (List.drop n) h
  have hslice (drop take : Nat) :
      dispatchEntryShapes ((xs.drop drop).take take) =
        dispatchEntryShapes ((ys.drop drop).take take) := by
    simpa [dispatchEntryShapes] using congrArg (List.take take) (hdrop drop)
  unfold hybridDispatchWith
  apply splitDispatch_compileShape_eq
  · exact firstSelector_eq_of_dispatchEntryShapes_eq (hslice 9 4)
  · apply splitDispatch_compileShape_eq
    · exact firstSelector_eq_of_dispatchEntryShapes_eq (hslice 5 4)
    · exact linearDispatchWith_compileShape_eq (htake 5) k
    · exact linearDispatchWith_compileShape_eq (hslice 5 4) k
  · apply splitDispatch_compileShape_eq
    · exact firstSelector_eq_of_dispatchEntryShapes_eq (hdrop 13)
    · exact linearDispatchWith_compileShape_eq (hslice 9 4) k
    · exact linearDispatchWith_compileShape_eq (hdrop 13) k

set_option maxHeartbeats 800000 in
private theorem runtimeEntryShapes_eq (dp : DeployParams) :
    dispatchEntryShapes (funcs dp) =
      dispatchEntryShapes (funcs ⟨0, 0, 0, 0, 0⟩) := by
  rfl

private theorem runtimeMain_compileShape_eq (dp : DeployParams) :
    (runtimeMain dp).compileShape =
      (runtimeMain ⟨0, 0, 0, 0, 0⟩).compileShape := by
  have hd := hybridDispatchWith_compileShape_eq (runtimeEntryShapes_eq dp)
    fallbackSlot
  have hp := Func.compileShape_prepend_congr fsig hd
  unfold runtimeMain
  exact Func.compileShape_prepend_congr
    [callvalue, pushB256 4, calldatasize, lt, Ninst.or] <| by
      simp [Func.compileShape, hp]

/-- All deployment parameters occupy fixed-width PUSH32 instructions. -/
theorem legacyRuntime_compileShape_eq_zero (dp : DeployParams) :
    (legacyRuntime dp).compileShape =
      (legacyRuntime ⟨0, 0, 0, 0, 0⟩).compileShape := by
  simp [legacyRuntime, Prog.compileShape, runtimeMain_compileShape_eq dp]

private theorem legacyRuntimeCompilesZero :
    Prog.compiles (legacyRuntime ⟨0, 0, 0, 0, 0⟩) = true := by
  decide +kernel

/-- Fixed-width deployment parameters cannot change compiler success. -/
theorem legacyRuntime_compiles (dp : DeployParams) :
    Prog.compiles (legacyRuntime dp) = true := by
  rw [Prog.compiles_eq_of_compileShape (legacyRuntime_compileShape_eq_zero dp)]
  exact legacyRuntimeCompilesZero

theorem findLabel?_symbolicRuntime (dp : DeployParams) (target : Label) :
    (symbolicRuntime dp).findLabel? target = some (slotOf target) := by
  cases target <;> rfl

theorem erase_symbolicAux :
    symbolicAux.map (fun (_, body) => body.erase slotOf) = aux := by
  dsimp [symbolicAux, aux,
    symbolicFallback, symbolicPausableZeroError, symbolicSenderNotAdminError,
    symbolicSenderNotPauserError, symbolicPauseBelowMinError, symbolicPauseAboveMaxError,
    symbolicHeartbeatBelowMinError, symbolicHeartbeatAboveMaxError, symbolicHeartbeatExpiredError,
    symbolicPauseFailedError, symbolicReentrantCallError, symbolicEmptyRevert,
    symbolicBubbleRevert, symbolicArithmeticPanic]
  simp only [Func.erase_liftCallFree]
  rfl

theorem erase_symbolicRuntimeMain (dp : DeployParams) :
    (symbolicRuntimeMain dp).erase slotOf = runtimeMain dp :=
  rfl

theorem erase_symbolicRuntime (dp : DeployParams) :
    (symbolicRuntime dp).erase slotOf = legacyRuntime dp :=
  congrArg₂ Prog.mk (erase_symbolicRuntimeMain dp) erase_symbolicAux

/-- Resolution of the symbolic CircuitBreaker program yields the legacy runtime. -/
theorem resolve_symbolicRuntime_eq (dp : DeployParams) :
    resolve (symbolicRuntime dp) = .ok (legacyRuntime dp) := by
  have h_res := resolve_eq_erase (symbolicRuntime dp) slotOf rfl
    (fun target _ => findLabel?_symbolicRuntime dp target)
    (fun lbl body _ target _ => findLabel?_symbolicRuntime dp target)
  rw [erase_symbolicRuntime dp] at h_res
  exact h_res

/-- Checked link certificate for the symbolic CircuitBreaker runtime. -/
def symbolicLinkCert (dp : DeployParams) : LinkCertificate (symbolicRuntime dp) where
  resolved := legacyRuntime dp
  resolve_eq := resolve_symbolicRuntime_eq dp
  compiles := legacyRuntime_compiles dp

/-- The certificate's resolved program is the frozen numeric runtime.

This is the bridge that keeps the downstream normal form intact.  `runtime` is
now anchored on the certificate, so `simp [runtime, ...]` rewrites a goal to
`(symbolicLinkCert dp).resolved`; without this `@[simp]` lemma simp cannot
delta-unfold `symbolicLinkCert` and the 50-odd `simp [runtime, aux, fooSlot]`
table-lookup sites stall. -/
@[simp] theorem symbolicLinkCert_resolved (dp : DeployParams) :
    (symbolicLinkCert dp).resolved = legacyRuntime dp :=
  rfl

@[simp] theorem legacyRuntime_main (dp : DeployParams) :
    (legacyRuntime dp).main = runtimeMain dp :=
  rfl

@[simp] theorem legacyRuntime_aux (dp : DeployParams) :
    (legacyRuntime dp).aux = aux :=
  rfl

/-- Production runtime program obtained from the checked symbolic link certificate. -/
def runtime (dp : DeployParams) : Prog :=
  (symbolicLinkCert dp).resolved

theorem runtime_eq_legacyRuntime (dp : DeployParams) :
    runtime dp = legacyRuntime dp :=
  rfl

/-- Pair form of the production runtime, for walk idioms that cannot see
through the certificate projection. -/
theorem runtime_eq_mk (dp : DeployParams) :
    runtime dp = ⟨runtimeMain dp, aux⟩ :=
  rfl

/-- Exact resolution theorem relating the symbolic runtime to the production runtime. -/
theorem resolve_symbolicRuntime_eq_runtime (dp : DeployParams) :
    resolve (symbolicRuntime dp) = .ok (runtime dp) :=
  resolve_symbolicRuntime_eq dp

/-- All deployment parameters occupy fixed-width PUSH32 instructions. -/
theorem runtime_compileShape_eq_zero (dp : DeployParams) :
    (runtime dp).compileShape =
      (runtime ⟨0, 0, 0, 0, 0⟩).compileShape :=
  legacyRuntime_compileShape_eq_zero dp

/-- Fixed-width deployment parameters cannot change compiler success. -/
theorem runtime_compiles (dp : DeployParams) :
    Prog.compiles (runtime dp) = true :=
  (symbolicLinkCert dp).compiles

def runtimeCode (dp : DeployParams) : Bytes :=
  (Prog.compile (runtime dp)).getD []

theorem symbolicRuntime_compile_eq (dp : DeployParams) :
    Prog.compile (runtime dp) = some (runtimeCode dp) :=
  (symbolicLinkCert dp).compile_eq

theorem symbolicRuntime_bytes_eq (dp : DeployParams) :
    (symbolicLinkCert dp).bytes = runtimeCode dp :=
  rfl

def sourceSstoreSiteCount : Func → Nat :=
  Func.sourceSiteCount fun
    | .reg .sstore => true
    | _ => false

def sourceTstoreSiteCount : Func → Nat :=
  Func.sourceSiteCount fun
    | .reg .tstore => true
    | _ => false

def sourceExternalCallSiteCount : Func → Nat :=
  Func.sourceSiteCount fun
    | .exec _ => true
    | _ => false

def programSiteCount (counter : Func → Nat) (program : Prog) : Nat :=
  counter program.main + (program.aux.map counter).sum

theorem runtime_source_sstore_site_count :
    programSiteCount sourceSstoreSiteCount (runtime officialParams) = 20 := by
  decide +kernel

theorem runtime_source_tstore_site_count :
    programSiteCount sourceTstoreSiteCount (runtime officialParams) = 3 := by
  decide +kernel

theorem runtime_source_external_call_site_count :
    programSiteCount sourceExternalCallSiteCount (runtime officialParams) = 2 := by
  decide +kernel

/-- Named reconciliation of every source-level persistent write node. -/
def persistentWriteInventory : List (SourceSite × PersistentWriteClass) :=
  [ (⟨"setPauseDuration.config", 0⟩, .configuration),
    (⟨"setHeartbeatInterval.config", 1⟩, .configuration),
    (⟨"setPauser.assignment", 2⟩, .registryAssignment),
    (⟨"setPauser.oldCount", 3⟩, .registryCount),
    (⟨"append.arrayEntry", 4⟩, .registryArray),
    (⟨"append.reverseIndex", 5⟩, .registryIndex),
    (⟨"append.arrayLength", 6⟩, .registryArray),
    (⟨"afterOld.newCount", 7⟩, .registryCount),
    (⟨"remove.arrayHole", 8⟩, .registryArray),
    (⟨"remove.movedIndex", 9⟩, .registryIndex),
    (⟨"remove.clearTail", 10⟩, .registryArray),
    (⟨"remove.arrayLength", 11⟩, .registryArray),
    (⟨"remove.clearTargetIndex", 12⟩, .registryIndex),
    (⟨"register.retainedOldNewExpiry", 13⟩, .heartbeatExpiry),
    (⟨"register.lastOldClear", 14⟩, .heartbeatExpiry),
    (⟨"register.lastOldNewExpiry", 15⟩, .heartbeatExpiry),
    (⟨"register.freshExpiry", 16⟩, .heartbeatExpiry),
    (⟨"heartbeat.expiry", 17⟩, .heartbeatExpiry),
    (⟨"pause.retainedTargetExpiry", 18⟩, .heartbeatExpiry),
    (⟨"pause.lastTargetExpiry", 19⟩, .heartbeatExpiry) ]

def transientWriteInventory : List (SourceSite × TransientWriteClass) :=
  [ (⟨"pause.lock", 0⟩, .reentrancyLock),
    (⟨"pause.unlock.zeroExpiry", 1⟩, .reentrancyLock),
    (⟨"pause.unlock.extendedExpiry", 2⟩, .reentrancyLock) ]

def externalCallInventory : List (SourceSite × ExternalCallClass) :=
  [ (⟨"pause.pauseFor", 0⟩, .pauseInvoke),
    (⟨"pause.isPaused", 1⟩, .pauseQuery) ]

theorem sourceInventory_cardinalities :
    persistentWriteInventory.length =
      programSiteCount sourceSstoreSiteCount (runtime officialParams) ∧
    transientWriteInventory.length =
      programSiteCount sourceTstoreSiteCount (runtime officialParams) ∧
    externalCallInventory.length =
      programSiteCount sourceExternalCallSiteCount (runtime officialParams) := by
  rw [runtime_source_sstore_site_count, runtime_source_tstore_site_count,
    runtime_source_external_call_site_count]
  decide

/-! ## Landed cycle-write-free canary -/

def enumerationComponent : List Nat := [enumLoopSlot]

theorem enumeration_entry_sstore_free :
    (runtime officialParams).entrySstoreFree
      getPausables enumerationComponent = true := by
  decide +kernel

def enumLoopWritingMutant : Func :=
  pushB256 0 ::: pushB256 arrayLengthSlot ::: sstore ::: .call enumLoopSlot

def enumerationWritingMutant (dp : DeployParams) : Prog :=
  let mutantAux := aux.set (enumLoopSlot - 1) enumLoopWritingMutant
  ⟨runtimeMain dp, mutantAux⟩

theorem enumeration_writing_mutant_rejected :
    (enumerationWritingMutant officialParams).entrySstoreFree
      getPausables enumerationComponent = false := by
  decide +kernel


end LidoCircuitBreaker

/-- Public alias for the CircuitBreaker symbolic label type. -/
abbrev CircuitBreaker.Label := LidoCircuitBreaker.Label

end Blanc
