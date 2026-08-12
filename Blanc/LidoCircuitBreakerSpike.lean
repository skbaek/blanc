/-
`LidoCircuitBreakerSpike` is a bounded feasibility artifact, not the complete
Lido CircuitBreaker port.  It deliberately puts the five hard shapes in one
compiler input: the coupled Registry mutation, an unbounded tail-recursive
`address[]` view, heartbeat/admin writes, and the transient-lock/external-call
pause choreography.  The public compatibility and proof gaps are catalogued in
the goal completion report.

The storage representation is a Blanc implementation choice.  Six persistent
families occupy disjoint high-nibble regions; addresses and live array indices
are payloads.  No WETH10 module is imported: contracts remain siblings.
-/

import Blanc.RevertPayload

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreakerSpike

/-! ## Deployment parameters and tagged storage projection -/

structure DeployParams where
  admin : B256
  minPauseDuration : B256
  maxPauseDuration : B256
  minHeartbeatInterval : B256
  maxHeartbeatInterval : B256
deriving DecidableEq

def officialParams : DeployParams :=
  { admin := 0x3e40D73EB977Dc6a537aF587D48316feE66E9C8c
    minPauseDuration := 432000
    maxPauseDuration := 5184000
    minHeartbeatInterval := 2592000
    maxHeartbeatInterval := 94608000 }

structure ConstructorArgs extends DeployParams where
  initialPauseDuration : B256
  initialHeartbeatInterval : B256
deriving DecidableEq

def officialConstructorArgs : ConstructorArgs :=
  { officialParams with
    initialPauseDuration := 1814400
    initialHeartbeatInterval := 31536000 }

def ConstructorArgs.Valid (args : ConstructorArgs) : Prop :=
  args.admin.toNat ≠ 0 ∧
  args.minPauseDuration.toNat ≠ 0 ∧
  args.minPauseDuration.toNat ≤ args.maxPauseDuration.toNat ∧
  args.minHeartbeatInterval.toNat ≠ 0 ∧
  args.minHeartbeatInterval.toNat ≤ args.maxHeartbeatInterval.toNat ∧
  args.minPauseDuration.toNat ≤ args.initialPauseDuration.toNat ∧
  args.initialPauseDuration.toNat ≤ args.maxPauseDuration.toNat ∧
  args.minHeartbeatInterval.toNat ≤ args.initialHeartbeatInterval.toNat ∧
  args.initialHeartbeatInterval.toNat ≤ args.maxHeartbeatInterval.toNat

theorem official_constructor_args_valid : officialConstructorArgs.Valid := by
  unfold ConstructorArgs.Valid officialConstructorArgs officialParams
  decide

/-- The deployed timestamp is after Jaune's BPO2 activation.  Prague is the
Solidity code-generation target, not the active mainnet rule record. -/
theorem deployment_rules_are_bpo2 :
    mainnetChainConfig.rulesAt 1777555319 = .ok bpo2Rules := by
  decide

/-- Fixed-width runtime constants keep the compiler shape parameter-neutral. -/
def pushDeployWord (w : B256) : Ninst :=
  Ninst.push w.toBytes (by rw [B256.length_toBytes])

def regionWord (region : Nat) : B256 := Nat.toB256 (region * 2 ^ 252)
def payloadMask : B256 := Nat.toB256 (2 ^ 252 - 1)
def slot (region : Nat) (payload : B256) : B256 :=
  B256.or (regionWord region) payload

def configRegion : Nat := 1
def expiryRegion : Nat := 2
def assignmentRegion : Nat := 3
def indexRegion : Nat := 4
def countRegion : Nat := 5
def arrayRegion : Nat := 6

def pauseDurationSlot : B256 := slot configRegion 0
def heartbeatIntervalSlot : B256 := slot configRegion 1
def arrayLengthSlot : B256 := slot arrayRegion 0
def lockKey : B256 := slot 15 0

def expirySlot (pauser : B256) : B256 := slot expiryRegion pauser
def assignmentSlot (target : B256) : B256 := slot assignmentRegion target
def indexSlot (target : B256) : B256 := slot indexRegion target
def countSlot (pauser : B256) : B256 := slot countRegion pauser
def arrayEntrySlot (oneBasedIndex : B256) : B256 :=
  slot arrayRegion oneBasedIndex

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

def pausableZeroError : Func := Func.revData (customErrorData "PausableZero")
def senderNotAdminError : Func := Func.revData (customErrorData "SenderNotAdmin")
def senderNotPauserError : Func := Func.revData (customErrorData "SenderNotPauser")
def pauseBelowMinError : Func := Func.revData (customErrorData "PauseDurationBelowMin")
def pauseAboveMaxError : Func := Func.revData (customErrorData "PauseDurationAboveMax")
def heartbeatBelowMinError : Func :=
  Func.revData (customErrorData "HeartbeatIntervalBelowMin")
def heartbeatAboveMaxError : Func :=
  Func.revData (customErrorData "HeartbeatIntervalAboveMax")
def heartbeatExpiredError : Func := Func.revData (customErrorData "HeartbeatExpired")
def pauseFailedError : Func := Func.revData (customErrorData "PauseFailed")
def reentrantCallError : Func := Func.revData (customErrorData "ReentrantCall")

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

def pauseForSelector : B256 := selector "pauseFor" [.uint256]
def isPausedSelector : B256 := selector "isPaused" []

/-! ## Stable auxiliary coordinates -/

def fallbackSlot : Nat := 1
def pausableZeroErrorSlot : Nat := 2
def senderNotAdminErrorSlot : Nat := 3
def senderNotPauserErrorSlot : Nat := 4
def pauseBelowMinErrorSlot : Nat := 5
def pauseAboveMaxErrorSlot : Nat := 6
def heartbeatBelowMinErrorSlot : Nat := 7
def heartbeatAboveMaxErrorSlot : Nat := 8
def heartbeatExpiredErrorSlot : Nat := 9
def pauseFailedErrorSlot : Nat := 10
def reentrantCallErrorSlot : Nat := 11
def emptyRevertSlot : Nat := 12
def bubbleRevertSlot : Nat := 13
def setPauserSlot : Nat := 14
def appendTargetSlot : Nat := 15
def afterOldPauserSlot : Nat := 16
def removeTargetSlot : Nat := 17
def finishSetPauserSlot : Nat := 18
def registerAfterSetSlot : Nat := 19
def pauseAfterSetSlot : Nat := 20
def enumLoopSlot : Nat := 21

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
  canonicalAddressArg 0 <|
    arg 0 +++ tagTop expiryRegion +++ sload ::: returnWord

def getPauser : Func :=
  canonicalAddressArg 0 <|
    arg 0 +++ tagTop assignmentRegion +++ sload ::: returnWord

def getPausableCount : Func :=
  canonicalAddressArg 0 <|
    arg 0 +++ tagTop countRegion +++ sload ::: returnWord

def isPauserLive : Func :=
  canonicalAddressArg 0 <|
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
    pushB256 64 ::: add ::: pushB256 0 ::: Func.ret)

def getPausables : Func :=
  pushB256 32 ::: mstoreAt 0 +++
  pushB256 arrayLengthSlot ::: sload ::: mstoreAt 1 +++
  pushB256 0 :::
  .call enumLoopSlot

/-! ## Admin configuration writes -/

def setPauseDuration (dp : DeployParams) : Func :=
  onlyAdmin dp <|
    pushDeployWord dp.minPauseDuration ::: arg 0 +++ lt :::
    ((.call pauseBelowMinErrorSlot) <?>
      (pushDeployWord dp.maxPauseDuration ::: arg 0 +++ gt :::
        ((.call pauseAboveMaxErrorSlot) <?>
          (pushB256 pauseDurationSlot ::: sload ::: mstoreAt 0 +++
            arg 0 +++ mstoreAt 1 +++
            pushB256 pauseDurationUpdatedEvent ::: logWith 0 0 2 +++
            arg 0 +++ pushB256 pauseDurationSlot ::: sstore ::: Func.stop))))

def setHeartbeatInterval (dp : DeployParams) : Func :=
  onlyAdmin dp <|
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
  canonicalAddressArg 0 <| canonicalAddressArg 1 <|
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
      (timestamp ::: pushB256 heartbeatIntervalSlot ::: sload ::: add :::
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
        (timestamp ::: pushB256 heartbeatIntervalSlot ::: sload ::: add :::
          dup 0 ::: mstoreAt 0 +++
          loadWord newPauserWord +++ tagTop expiryRegion +++ sstore :::
          loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
          logWith 1 0 1 +++ Func.stop))) <?>
    (loadWord newPauserWord +++ iszero :::
      (Func.stop <?>
        (timestamp ::: pushB256 heartbeatIntervalSlot ::: sload ::: add :::
          dup 0 ::: mstoreAt 0 +++
          loadWord newPauserWord +++ tagTop expiryRegion +++ sstore :::
          loadWord newPauserWord +++ pushB256 heartbeatUpdatedEvent :::
          logWith 1 0 1 +++ Func.stop))))

/-! ## Heartbeat and transient-guarded pause -/

def heartbeat : Func :=
  caller ::: tagTop countRegion +++ sload ::: iszero :::
  ((.call senderNotPauserErrorSlot) <?>
    (caller ::: tagTop expiryRegion +++ sload ::: timestamp ::: lt :::
      ((timestamp ::: pushB256 heartbeatIntervalSlot ::: sload ::: add :::
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
    (timestamp ::: pushB256 heartbeatIntervalSlot ::: sload ::: add :::
      pauseExpiryFinish))

def decodePausedResult : Func :=
  retdataShorterThan 32 +++
  ((.call emptyRevertSlot) <?>
    (pushList [32, 0, 0] +++ retdatacopy ::: pushB256 0 ::: mload :::
      dup 0 ::: iszero :::
      ((.call pauseFailedErrorSlot) <?>
        (pushB256 1 ::: eq :::
          (pauseSuccess <?> (.call emptyRevertSlot))))))

def pauseAfterSet : Func :=
  pushB256 pauseForSelector ::: mstoreAt 8 +++
  loadWord durationWord +++ mstoreAt 9 +++
  pushList [0, 0, 36, 0x11c, 0] +++ loadWord targetWord +++ gas ::: call :::
  iszero :::
  ((.call bubbleRevertSlot) <?>
    (pushB256 isPausedSelector ::: mstoreAt 8 +++
      pushList [0, 0, 4, 0x11c] +++ loadWord targetWord +++ gas ::: statcall :::
      iszero :::
      ((.call bubbleRevertSlot) <?>
        decodePausedResult)))

def pause : Func :=
  canonicalAddressArg 0 <|
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
  [ (selector "pauseDuration" [], nonpayable pauseDuration),
    (selector "MAX_PAUSE_DURATION" [], nonpayable (maxPauseDuration dp)),
    (selector "ADMIN" [], nonpayable (admin dp)),
    (selector "registerPauser" [.address, .address],
      nonpayable (registerPauser dp)),
    (selector "heartbeat" [], nonpayable heartbeat),
    (selector "getPauser" [.address], nonpayable getPauser),
    (selector "getPausables" [], nonpayable getPausables),
    (selector "heartbeatInterval" [], nonpayable heartbeatInterval),
    (selector "setHeartbeatInterval" [.uint256],
      nonpayable (setHeartbeatInterval dp)),
    (selector "pause" [.address], nonpayable pause),
    (selector "MIN_PAUSE_DURATION" [], nonpayable (minPauseDuration dp)),
    (selector "MAX_HEARTBEAT_INTERVAL" [],
      nonpayable (maxHeartbeatInterval dp)),
    (selector "getPausableCount" [.address], nonpayable getPausableCount),
    (selector "MIN_HEARTBEAT_INTERVAL" [],
      nonpayable (minHeartbeatInterval dp)),
    (selector "heartbeatExpiry" [.address], nonpayable heartbeatExpiry),
    (selector "setPauseDuration" [.uint256],
      nonpayable (setPauseDuration dp)),
    (selector "isPauserLive" [.address], nonpayable isPauserLive) ]

def tree (dp : DeployParams) : DispatchTree := .ofSorted (funcs dp)

def aux : List Func :=
  [ Func.rev,
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
    Func.rev,
    Func.revReturnData,
    setPauserKernel,
    appendTarget,
    afterOldPauser,
    removeTarget,
    finishSetPauser,
    registerAfterSet,
    pauseAfterSet,
    enumLoop ]

def spike (dp : DeployParams) : Prog :=
  ⟨Func.mainWith fallbackSlot (tree dp), aux⟩

def spikeCode (dp : DeployParams) : Bytes :=
  (Prog.compile (spike dp)).getD []

/-! ## Executable artifact facts

These are intentionally concrete at the spike's official parameter point.
The eventual port should extract the WETH10 fixed-width `compileShape` pattern
upstream and prove compilation for every deployment parameter, but this
decision artifact needs only one reproducible integrated byte string. -/

theorem funcs_sorted_official :
    DispatchTree.sorted (funcs officialParams) = true := by
  decide +kernel

theorem spike_compiles_official :
    Prog.compiles (spike officialParams) = true := by
  decide +kernel

theorem spikeCode_compile_official :
    Prog.compile (spike officialParams) = some (spikeCode officialParams) := by
  exact Prog.compile_eq_some_getD_of_compiles _ spike_compiles_official

/-- Exact direct invocation of this compiled runtime at `ca`.  Requiring both
the storage owner and code address excludes clone storage, CALLCODE,
DELEGATECALL, and foreign-code execution from same-instance reentry claims. -/
def exactInvocation (dp : DeployParams) (ca : Adr) (e : Sevm) : Prop :=
  e.currentTarget = ca ∧ e.codeAddress = some ca ∧
    some e.code.toList = Prog.compile (spike dp)

instance (dp : DeployParams) (ca : Adr) (e : Sevm) :
    Decidable (exactInvocation dp ca e) := by
  unfold exactInvocation
  infer_instance

/-- Typed constructor boundary for the missing call-free init prefix.  The
prefix must validate `ConstructorArgs.Valid`, patch the five fixed-width words,
perform exactly these two persistent writes, and return `spikeCode args.toDeployParams`.
The 4096-byte prefix allowance is a conservative spike estimate: Blanc's
existing WETH10 copy/patch prefix is 177 bytes, while this one additionally
needs seven-word decoding, nine bounds checks, twelve patch writes, and two
SSTOREs. -/
def ConstructorArgs.initialWrites (args : ConstructorArgs) :
    List (B256 × B256) :=
  [ (pauseDurationSlot, args.initialPauseDuration),
    (heartbeatIntervalSlot, args.initialHeartbeatInterval) ]

def constructorPrefixBudget : Nat := 4096
def constructorArgsBytes : Nat := 7 * 32
def initcodeSizeEstimate : Nat :=
  constructorPrefixBudget + (spikeCode officialParams).length + constructorArgsBytes

theorem official_initcode_size_estimate : initcodeSizeEstimate = 8963 := by
  decide +kernel

theorem official_initcode_estimate_below_eip3860 :
    initcodeSizeEstimate < 49152 := by
  decide +kernel

/-! ## Pure Registry transition used to partition S2 -/

abbrev Entry := B256 × B256

def findEntry : List Entry → B256 → Option (Nat × B256)
  | [], _ => none
  | (target, pauser) :: rest, wanted =>
      if target = wanted then some (0, pauser)
      else (findEntry rest wanted).map fun (i, p) => (i + 1, p)

def setEntryAt : Nat → Entry → List Entry → List Entry
  | _, _, [] => []
  | 0, value, _ :: rest => value :: rest
  | i + 1, value, head :: rest => head :: setEntryAt i value rest

def lastEntry? : List Entry → Option Entry
  | [] => none
  | [entry] => some entry
  | _ :: rest => lastEntry? rest

def dropLastEntry : List Entry → List Entry
  | [] => []
  | [_] => []
  | head :: rest => head :: dropLastEntry rest

def swapPopEntry (entries : List Entry) (index : Nat) : List Entry :=
  match lastEntry? entries with
  | none => entries
  | some last => dropLastEntry (setEntryAt index last entries)

/-- Public-boundary logical effect of the Solidity Registry algorithm.
`none` is exactly the zero-target rejection.  A missing target with new pauser
zero is the source's append-then-swap-pop path, whose boundary result is the
unchanged list. -/
def setPauserModel (entries : List Entry) (target newPauser : B256) :
    Option (List Entry) :=
  if target = 0 then none
  else
    match findEntry entries target with
    | none =>
        if newPauser = 0 then some entries
        else some (entries ++ [(target, newPauser)])
    | some (index, _) =>
        if newPauser = 0 then some (swapPopEntry entries index)
        else some (setEntryAt index (target, newPauser) entries)

def targetAt : List Entry → Nat → B256
  | [], _ => 0
  | (target, _) :: _, 0 => target
  | _ :: rest, i + 1 => targetAt rest i

def assignmentAt : List Entry → B256 → B256
  | [], _ => 0
  | (target, pauser) :: rest, wanted =>
      if target = wanted then pauser else assignmentAt rest wanted

def oneBasedIndexAt : List Entry → B256 → Nat
  | [], _ => 0
  | (target, _) :: rest, wanted =>
      if target = wanted then 1
      else
        let tail := oneBasedIndexAt rest wanted
        if tail = 0 then 0 else tail + 1

def assignmentCount : List Entry → B256 → Nat
  | [], _ => 0
  | (_, pauser) :: rest, wanted =>
      (if pauser = wanted then 1 else 0) + assignmentCount rest wanted

def CanonicalAddress (word : B256) : Prop := word.toNat < 2 ^ 160

/-- One non-circular public-boundary relation: one list witnesses all four
coupled storage views.  Length/index/count bounds are intended consequences of
`targetsNodup` plus 160-bit nonzero targets, not extra premises. -/
structure RegistryInvariant (stor : Stor) (entries : List Entry) : Prop where
  targetsNodup : (entries.map Prod.fst).Nodup
  targetsValid : ∀ entry ∈ entries,
    entry.1 ≠ 0 ∧ CanonicalAddress entry.1
  pausersValid : ∀ entry ∈ entries,
    entry.2 ≠ 0 ∧ CanonicalAddress entry.2
  lengthWord : stor.get arrayLengthSlot = Nat.toB256 entries.length
  arrayWords : ∀ i, i < entries.length →
    stor.get (arrayEntrySlot (Nat.toB256 (i + 1))) = targetAt entries i
  assignments : ∀ target, CanonicalAddress target →
    stor.get (assignmentSlot target) = assignmentAt entries target
  indices : ∀ target, CanonicalAddress target →
    stor.get (indexSlot target) = Nat.toB256 (oneBasedIndexAt entries target)
  counts : ∀ pauser, CanonicalAddress pauser →
    stor.get (countSlot pauser) = Nat.toB256 (assignmentCount entries pauser)
  zeroCount : stor.get (countSlot 0) = 0

theorem empty_registry_invariant : RegistryInvariant Stor.empty [] := by
  constructor <;>
    simp [Stor.empty, Stor.get, targetAt, assignmentAt, oneBasedIndexAt,
      assignmentCount] <;>
    intros <;> rfl

/-! The concrete path partition is executable anti-vacuity evidence.  These
examples cover rejection, fresh registration, idempotent unregister,
same-pauser replacement, first/last removal, and a true middle removal. -/

example : setPauserModel [] 0 9 = none := by decide
example : setPauserModel [] 7 9 = some [(7, 9)] := by decide
example : setPauserModel [] 7 0 = some [] := by decide
example : setPauserModel [(7, 9)] 7 9 = some [(7, 9)] := by decide
example : setPauserModel [(7, 9)] 7 0 = some [] := by decide
example : setPauserModel [(7, 9), (8, 10)] 7 0 = some [(8, 10)] := by decide
example : setPauserModel [(7, 9), (8, 10)] 8 0 = some [(7, 9)] := by decide
example :
    setPauserModel [(7, 9), (8, 10), (11, 12)] 8 0 =
      some [(7, 9), (11, 12)] := by
  decide

/-- Canonical reverse-index rows for executable mutation fixtures. -/
def indexRowsFrom : Nat → List Entry → List (B256 × Nat)
  | _, [] => []
  | i, (target, _) :: rest =>
      (target, i + 1) :: indexRowsFrom (i + 1) rest

def indexRows (entries : List Entry) : List (B256 × Nat) :=
  indexRowsFrom 0 entries

example :
    indexRows [(7, 9), (11, 12)] = [(7, 1), (11, 2)] := by
  decide

/-- Corrupted post-removal rows obtained by omitting the moved-last index
repair after removing the middle element from `[7, 8, 11]`. -/
def movedIndexRepairOmitted : List (B256 × Nat) := [(7, 1), (11, 3)]

theorem moved_index_repair_mutant_rejected :
    movedIndexRepairOmitted ≠ indexRows [(7, 9), (11, 12)] := by
  decide

/-! ## Exact ABI image and literal source-site inventories -/

/-- ABI encoding for one dynamic `address[]` return.  Callers of this helper
must separately establish that every word is a canonical 160-bit address. -/
def abiAddressArray (xs : List B256) : Bytes :=
  (Nat.toB256 32).toBytes ++
  (Nat.toB256 xs.length).toBytes ++
  xs.flatMap B256.toBytes

theorem abiAddressArray_length (xs : List B256) :
    (abiAddressArray xs).length = 64 + 32 * xs.length := by
  simp [abiAddressArray, B256.length_toBytes]
  omega

def abiAddressArrayReversedMutant (xs : List B256) : Bytes :=
  abiAddressArray xs.reverse

example :
    abiAddressArray [] =
      (Nat.toB256 32).toBytes ++ (Nat.toB256 0).toBytes := by
  rfl

example : (abiAddressArray [7]).drop 64 = (7 : B256).toBytes := by
  decide

example :
    (abiAddressArray [7, 8, 11]).drop 64 =
      (7 : B256).toBytes ++ (8 : B256).toBytes ++ (11 : B256).toBytes := by
  decide

/-- Reversing the logical array is observably different; the order theorem in
the full port therefore cannot be discharged by a length-only argument. -/
theorem abi_reversed_order_mutant_rejected :
    abiAddressArrayReversedMutant [7, 8] ≠ abiAddressArray [7, 8] := by
  decide

inductive PersistentWriteClass
  | adminConfiguration
  | heartbeatExpiry
  | registryAssignment
  | registryCount
  | registryArray
  | registryIndex
deriving DecidableEq, Repr

structure PersistentWriteSite where
  label : String
  writeClass : PersistentWriteClass
deriving DecidableEq, Repr

/-- Named inventory of the 20 syntactic SSTORE nodes.  Branch-exclusive nodes
are listed separately because both are present in the emitted bytecode. -/
def persistentWriteInventory : List PersistentWriteSite :=
  [ ⟨"setPauseDuration.config", .adminConfiguration⟩,
    ⟨"setHeartbeatInterval.config", .adminConfiguration⟩,
    ⟨"setPauser.assignment", .registryAssignment⟩,
    ⟨"setPauser.oldCount", .registryCount⟩,
    ⟨"append.arrayEntry", .registryArray⟩,
    ⟨"append.reverseIndex", .registryIndex⟩,
    ⟨"append.arrayLength", .registryArray⟩,
    ⟨"afterOld.newCount", .registryCount⟩,
    ⟨"remove.arrayHole", .registryArray⟩,
    ⟨"remove.movedIndex", .registryIndex⟩,
    ⟨"remove.clearTail", .registryArray⟩,
    ⟨"remove.arrayLength", .registryArray⟩,
    ⟨"remove.clearTargetIndex", .registryIndex⟩,
    ⟨"register.freshExpiry", .heartbeatExpiry⟩,
    ⟨"register.lastOldClear", .heartbeatExpiry⟩,
    ⟨"register.lastOldNewExpiry", .heartbeatExpiry⟩,
    ⟨"register.retainedOldNewExpiry", .heartbeatExpiry⟩,
    ⟨"heartbeat.expiry", .heartbeatExpiry⟩,
    ⟨"pause.lastTargetExpiry", .heartbeatExpiry⟩,
    ⟨"pause.retainedTargetExpiry", .heartbeatExpiry⟩ ]

/-- Contract-neutral syntax counter duplicated locally for the spike.  The
implementation should extract the established WETH10 version into a common
Blanc module instead of horizontally importing that sibling contract. -/
def sourceSstoreSiteCount : Func → Nat
  | .last _ => 0
  | .next (.reg .sstore) rest => 1 + sourceSstoreSiteCount rest
  | .next _ rest => sourceSstoreSiteCount rest
  | .branch left right =>
      sourceSstoreSiteCount left + sourceSstoreSiteCount right
  | .call _ => 0

def progSourceSstoreSiteCount (program : Prog) : Nat :=
  sourceSstoreSiteCount program.main +
    (program.aux.map sourceSstoreSiteCount).sum

def sourceTstoreSiteCount : Func → Nat
  | .last _ => 0
  | .next (.reg .tstore) rest => 1 + sourceTstoreSiteCount rest
  | .next _ rest => sourceTstoreSiteCount rest
  | .branch left right =>
      sourceTstoreSiteCount left + sourceTstoreSiteCount right
  | .call _ => 0

def progSourceTstoreSiteCount (program : Prog) : Nat :=
  sourceTstoreSiteCount program.main +
    (program.aux.map sourceTstoreSiteCount).sum

def sourceExternalCallSiteCount : Func → Nat
  | .last _ => 0
  | .next (.exec .call) rest => 1 + sourceExternalCallSiteCount rest
  | .next (.exec .statcall) rest => 1 + sourceExternalCallSiteCount rest
  | .next _ rest => sourceExternalCallSiteCount rest
  | .branch left right =>
      sourceExternalCallSiteCount left + sourceExternalCallSiteCount right
  | .call _ => 0

def progSourceExternalCallSiteCount (program : Prog) : Nat :=
  sourceExternalCallSiteCount program.main +
    (program.aux.map sourceExternalCallSiteCount).sum

/-- Cardinality agrees with the literal generated-program syntax.  This is not
the missing all-outcomes executable-PC-to-source-site occurrence theorem. -/
theorem persistent_write_inventory_cardinality_matches_source :
    persistentWriteInventory.length =
      progSourceSstoreSiteCount (spike officialParams) := by
  decide +kernel

theorem spike_source_sstore_site_count :
    progSourceSstoreSiteCount (spike officialParams) = 20 := by
  decide +kernel

theorem spike_source_tstore_site_count :
    progSourceTstoreSiteCount (spike officialParams) = 3 := by
  decide +kernel

theorem spike_source_external_call_site_count :
    progSourceExternalCallSiteCount (spike officialParams) = 2 := by
  decide +kernel

/-! ## Cycle-safe, computable source certificate -/

def localSstoreFree : Func → Bool
  | .last _ => true
  | .call _ => true
  | .branch left right => localSstoreFree left && localSstoreFree right
  | .next (.reg .sstore) _ => false
  | .next _ rest => localSstoreFree rest

def localCallsIn : Func → List Nat
  | .last _ => []
  | .call k => [k]
  | .branch left right => localCallsIn left ++ localCallsIn right
  | .next _ rest => localCallsIn rest

def programFunc? (p : Prog) (k : Nat) : Option Func := (p.main :: p.aux)[k]?

/-- A finite set is a closed read-only certificate.  Calls are treated locally,
then every edge must remain inside the stated set.  Construction does not
recurse through edges, so a self-loop and a multi-node cycle can certify. -/
def closedReadOnly (p : Prog) (members : List Nat) : Bool :=
  members.all fun k =>
    match programFunc? p k with
    | none => false
    | some body =>
        localSstoreFree body &&
          (localCallsIn body).all (fun callee => callee ∈ members)

def enumCertificate : List Nat := [enumLoopSlot]

theorem enum_entry_calls_certified_component :
    localSstoreFree getPausables = true ∧
      localCallsIn getPausables = enumCertificate := by
  decide +kernel

/-- A reachable-write mutation used by the certificate falsifier. -/
def enumLoopWritingMutant : Func :=
  pushB256 0 ::: pushB256 arrayLengthSlot ::: sstore ::: .call enumLoopSlot

def enumMutantProgram (dp : DeployParams) : Prog :=
  let mutantAux := aux.set (enumLoopSlot - 1) enumLoopWritingMutant
  ⟨(Func.mainWith fallbackSlot (tree dp)), mutantAux⟩

theorem enum_cycle_certificate :
    closedReadOnly (spike officialParams) enumCertificate = true := by
  decide +kernel

/-- The certificate is load-bearing: a reachable SSTORE in the recursive SCC
makes the same finite certificate fail. -/
theorem enum_cycle_writing_mutant_rejected :
    closedReadOnly (enumMutantProgram officialParams) enumCertificate = false := by
  decide +kernel

end LidoCircuitBreakerSpike

end Blanc
