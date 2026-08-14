import Blanc.RevertPayload

/-!
The contract-owned static vocabulary for Lido's CircuitBreaker v1.0.0.
This file deliberately contains no executable runtime: later modules own the
program, compiler witness, and proof families.  In particular, its storage
keys are Blanc projection keys, not a claim about Solidity raw slots.
-/

namespace Blanc

open Jaune

namespace LidoCircuitBreaker

/-! ## Constructor domain -/

structure DeployParams where
  admin : B256
  minPauseDuration : B256
  maxPauseDuration : B256
  minHeartbeatInterval : B256
  maxHeartbeatInterval : B256
deriving DecidableEq

structure ConstructorArgs extends DeployParams where
  initialPauseDuration : B256
  initialHeartbeatInterval : B256
deriving DecidableEq

def officialParams : DeployParams :=
  { admin := 0x3e40D73EB977Dc6a537aF587D48316feE66E9C8c
    minPauseDuration := 432000
    maxPauseDuration := 5184000
    minHeartbeatInterval := 2592000
    maxHeartbeatInterval := 94608000 }

def officialConstructorArgs : ConstructorArgs :=
  { officialParams with
    initialPauseDuration := 1814400
    initialHeartbeatInterval := 31536000 }

/-- A non-official valid world used by artifact and differential tests. -/
def independentConstructorArgs : ConstructorArgs :=
  { admin := 0x111122223333444455556666777788889999AaAa
    minPauseDuration := 60
    maxPauseDuration := 86400
    minHeartbeatInterval := 120
    maxHeartbeatInterval := 604800
    initialPauseDuration := 3600
    initialHeartbeatInterval := 86400 }

inductive ConstructorError
  | adminZero
  | minPauseDurationZero
  | minPauseDurationExceedsMax
  | minHeartbeatIntervalZero
  | minHeartbeatIntervalExceedsMax
  | pauseDurationBelowMin
  | pauseDurationAboveMax
  | heartbeatIntervalBelowMin
  | heartbeatIntervalAboveMax
deriving DecidableEq

/-- Solidity constructor and its two internal setters, in source evaluation
order.  This is intentionally a classifier, not a conjunction of bounds. -/
def ConstructorArgs.validationError? (args : ConstructorArgs) : Option ConstructorError :=
  if args.admin = 0 then some .adminZero
  else if args.minPauseDuration = 0 then some .minPauseDurationZero
  else if args.minPauseDuration.toNat > args.maxPauseDuration.toNat then
    some .minPauseDurationExceedsMax
  else if args.minHeartbeatInterval = 0 then some .minHeartbeatIntervalZero
  else if args.minHeartbeatInterval.toNat > args.maxHeartbeatInterval.toNat then
    some .minHeartbeatIntervalExceedsMax
  else if args.initialPauseDuration.toNat < args.minPauseDuration.toNat then
    some .pauseDurationBelowMin
  else if args.initialPauseDuration.toNat > args.maxPauseDuration.toNat then
    some .pauseDurationAboveMax
  else if args.initialHeartbeatInterval.toNat < args.minHeartbeatInterval.toNat then
    some .heartbeatIntervalBelowMin
  else if args.initialHeartbeatInterval.toNat > args.maxHeartbeatInterval.toNat then
    some .heartbeatIntervalAboveMax
  else none

def ConstructorArgs.Valid (args : ConstructorArgs) : Prop :=
  args.validationError? = none

/-! ## Tagged logical storage projection -/

def canonicalAddress (word : B256) : Prop := word.toNat < 2 ^ 160
def nonzeroCanonicalAddress (word : B256) : Prop := word ≠ 0 ∧ canonicalAddress word

def regionWord (region : Nat) : B256 := Nat.toB256 (region * 2 ^ 252)
def slot (region : Nat) (payload : B256) : B256 := B256.or (regionWord region) payload

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
def arrayEntrySlot (oneBasedIndex : B256) : B256 := slot arrayRegion oneBasedIndex

/-- Only the logical regions observable by the frozen comparison projection. -/
structure LogicalStorage where
  read : B256 → B256

structure LogicalState where
  pauseDuration : B256
  heartbeatInterval : B256
  registry : LogicalStorage
  heartbeatExpiry : B256 → B256

/-! ## ABI metadata -/

structure AbiEndpoint where
  name : String
  args : List ArgType
  selector : B256
  nonpayable : Bool

def endpoint (name : String) (args : List ArgType := []) : AbiEndpoint :=
  { name, args, selector := _root_.Blanc.selector name args, nonpayable := true }

def runtimeEndpoints : List AbiEndpoint :=
  [ endpoint "pauseDuration", endpoint "MAX_PAUSE_DURATION", endpoint "ADMIN",
    endpoint "registerPauser" [.address, .address], endpoint "heartbeat",
    endpoint "getPauser" [.address], endpoint "getPausables",
    endpoint "heartbeatInterval", endpoint "setHeartbeatInterval" [.uint256],
    endpoint "pause" [.address], endpoint "MIN_PAUSE_DURATION",
    endpoint "MAX_HEARTBEAT_INTERVAL", endpoint "getPausableCount" [.address],
    endpoint "MIN_HEARTBEAT_INTERVAL", endpoint "heartbeatExpiry" [.address],
    endpoint "setPauseDuration" [.uint256], endpoint "isPauserLive" [.address] ]

inductive CustomError
  | pausableZero | senderNotAdmin | senderNotPauser | adminZero
  | minPauseDurationZero | minPauseDurationExceedsMax
  | pauseDurationBelowMin | pauseDurationAboveMax
  | minHeartbeatIntervalZero | minHeartbeatIntervalExceedsMax
  | heartbeatIntervalBelowMin | heartbeatIntervalAboveMax
  | heartbeatExpired | pauseFailed | reentrantCall
deriving DecidableEq

def CustomError.name : CustomError → String
  | .pausableZero => "PausableZero" | .senderNotAdmin => "SenderNotAdmin"
  | .senderNotPauser => "SenderNotPauser" | .adminZero => "AdminZero"
  | .minPauseDurationZero => "MinPauseDurationZero"
  | .minPauseDurationExceedsMax => "MinPauseDurationExceedsMax"
  | .pauseDurationBelowMin => "PauseDurationBelowMin"
  | .pauseDurationAboveMax => "PauseDurationAboveMax"
  | .minHeartbeatIntervalZero => "MinHeartbeatIntervalZero"
  | .minHeartbeatIntervalExceedsMax => "MinHeartbeatIntervalExceedsMax"
  | .heartbeatIntervalBelowMin => "HeartbeatIntervalBelowMin"
  | .heartbeatIntervalAboveMax => "HeartbeatIntervalAboveMax"
  | .heartbeatExpired => "HeartbeatExpired" | .pauseFailed => "PauseFailed"
  | .reentrantCall => "ReentrantCall"

def CustomError.selector (error : CustomError) : B256 := _root_.Blanc.selector error.name []
def customErrors : List CustomError :=
  [.pausableZero, .senderNotAdmin, .senderNotPauser, .adminZero,
   .minPauseDurationZero, .minPauseDurationExceedsMax,
   .pauseDurationBelowMin, .pauseDurationAboveMax,
   .minHeartbeatIntervalZero, .minHeartbeatIntervalExceedsMax,
   .heartbeatIntervalBelowMin, .heartbeatIntervalAboveMax,
   .heartbeatExpired, .pauseFailed, .reentrantCall]

structure EventMetadata where
  name : String
  args : List ArgType
  indexed : List Nat
  topic : B256

def event (name : String) (args : List ArgType) (indexed : List Nat) : EventMetadata :=
  { name, args, indexed, topic := signatureHash name args }

def events : List EventMetadata :=
  [ event "PauserSet" [.address, .address, .address] [0, 1, 2],
    event "CircuitBreakerInitialized" [.address, .uint256, .uint256, .uint256, .uint256] [0],
    event "PauseDurationUpdated" [.uint256, .uint256] [],
    event "HeartbeatIntervalUpdated" [.uint256, .uint256] [],
    event "HeartbeatUpdated" [.address, .uint256] [0],
    event "PauseTriggered" [.address, .address, .uint256] [0, 1] ]

/-! ## Contract-owned source inventory vocabulary -/

inductive PersistentWriteClass
  | configuration | heartbeatExpiry | registryAssignment | registryCount | registryArray | registryIndex
deriving DecidableEq

inductive TransientWriteClass | reentrancyLock deriving DecidableEq
inductive ExternalCallClass | pauseQuery | pauseInvoke deriving DecidableEq

structure SourceSite where
  label : String
  offset : Nat
deriving DecidableEq

structure SourceInventory where
  persistentWrites : List (SourceSite × PersistentWriteClass)
  transientWrites : List (SourceSite × TransientWriteClass)
  externalCalls : List (SourceSite × ExternalCallClass)

end LidoCircuitBreaker
end Blanc
