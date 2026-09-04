import Blanc.CommonCore
import Blanc.RevertPayload

/-!
  Source-level vocabulary for the Triggerable Withdrawals Gateway.

  The storage names below are Blanc-owned tagged projection keys.  They are
  deliberately not a claim about the unstructured Solidity slots used by the
  deployed contract.  In particular, a role lookup refuses an observed
  low-252 collision instead of silently identifying two role/account pairs.
  This makes the bounded source model honest without assuming global keccak
  injectivity.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoTriggerableWithdrawalsGateway

/-! ## Deployment and logical state -/

structure DeployParams where
  locator : B256
deriving DecidableEq

structure ValidatorExitData where
  stakingModuleId : B256
  nodeOperatorId : B256
  pubkey : Bytes
deriving DecidableEq

structure ExitLimitData where
  maxExitRequestsLimit : B256
  prevExitRequestsLimit : B256
  prevTimestamp : B256
  frameDurationInSec : B256
  exitsPerFrame : B256
deriving DecidableEq

structure LogicalState where
  resumeSince : B256
  limit : ExitLimitData
  roleRecordLength : B256
deriving DecidableEq

/-! ## Family-owned tagged storage -/

def low252Mask : B256 := Nat.toB256 (2 ^ 252 - 1)
def addressMask : B256 := Nat.toB256 (2 ^ 160 - 1)

def regionWord (region : Nat) : B256 := Nat.toB256 (region * 2 ^ 252)

def taggedSlot (region : Nat) (payload : B256) : B256 :=
  B256.or (regionWord region) (B256.and payload low252Mask)

def configRegion : Nat := 1
def roleLookupRoleRegion : Nat := 2
def roleLookupAccountRegion : Nat := 3
def roleLookupIndexRegion : Nat := 4
def enumRoleRegion : Nat := 5
def enumAccountRegion : Nat := 6

def resumeSinceSlot : B256 := taggedSlot configRegion 0
def maxExitRequestsLimitSlot : B256 := taggedSlot configRegion 1
def prevExitRequestsLimitSlot : B256 := taggedSlot configRegion 2
def prevTimestampSlot : B256 := taggedSlot configRegion 3
def frameDurationInSecSlot : B256 := taggedSlot configRegion 4
def exitsPerFrameSlot : B256 := taggedSlot configRegion 5
def roleRecordLengthSlot : B256 := taggedSlot configRegion 6

def canonicalAccount (account : B256) : B256 := B256.and account addressMask
def roleLookupPayload (role account : B256) : B256 :=
  B256.and (B256.xor role (canonicalAccount account)) low252Mask

def roleLookupRoleSlot (role account : B256) : B256 :=
  taggedSlot roleLookupRoleRegion (roleLookupPayload role account)
def roleLookupAccountSlot (role account : B256) : B256 :=
  taggedSlot roleLookupAccountRegion (roleLookupPayload role account)
def roleLookupIndexSlot (role account : B256) : B256 :=
  taggedSlot roleLookupIndexRegion (roleLookupPayload role account)
def enumRoleSlot (index : B256) : B256 := taggedSlot enumRoleRegion index
def enumAccountSlot (index : B256) : B256 := taggedSlot enumAccountRegion index

/-! ## Disposable P1 physical storage prototype

The public logical projection remains independent of raw storage.  The P1
artifact uses the source family's nested keccak domains so role membership is
one collision-resistant lookup and enumeration is direct per role.  The
literal base words are tied to their source preimages below, rather than
recomputing keccak during every program elaboration. -/

def accessControlRolesPosition : B256 :=
  0x9a627a5d4aa7c17f87ff26e3fe9a42c2b6c559e8b41a42282d0ecebb17c0e4d3
def accessControlRoleMembersPosition : B256 :=
  0x8f8c450dae5029cd48cd91dd9db65da48fb742893edfc7941250f6721d93cbbe

def limitUint32Mask : B256 := 0xffffffff

/-! Storage-key derivation may run after trigger calldata has populated words
0--40.  Words 64 and 65 are below the trigger's dynamic-memory base and are
reserved for these two-word keccak images. -/
def storageKeyScratchWord : B256 := 64
def storageKeyScratchNextWord : B256 := 65

def storageMloadWord (word : B256) : Line :=
  [pushB256 (word * 32), mload]

def keccakPairLines (first second : Line) : Line :=
  first ++ mstoreAt storageKeyScratchWord ++
  second ++ mstoreAt storageKeyScratchNextWord ++
  [pushB256 64, pushB256 (storageKeyScratchWord * 32), keccak256]

/-! Evaluate the right image before the left one.  Nested mapping bases use
the same scratch pair, so this order keeps the final image `first ++ second`
after the inner keccak has returned. -/
def keccakPairLinesRightFirst (first second : Line) : Line :=
  second ++ mstoreAt storageKeyScratchNextWord ++
  first ++ mstoreAt storageKeyScratchWord ++
  [pushB256 64, pushB256 (storageKeyScratchWord * 32), keccak256]

def keccakWordLine (word : Line) : Line :=
  word ++ mstoreAt storageKeyScratchWord ++
  [pushB256 32, pushB256 (storageKeyScratchWord * 32), keccak256]

def roleDataSlotFrom (role : Line) : Line :=
  keccakPairLines role [pushB256 accessControlRolesPosition]

def roleMembershipSlotFrom (role account : Line) : Line :=
  keccakPairLinesRightFirst account (roleDataSlotFrom role)

def roleEnumerationBaseSlotFrom (role : Line) : Line :=
  keccakPairLines role [pushB256 accessControlRoleMembersPosition]

def roleEnumerationIndexSlotFrom (role account : Line) : Line :=
  keccakPairLinesRightFirst account
    (roleEnumerationBaseSlotFrom role ++ [pushB256 1, add])

def roleEnumerationMemberSlotFrom (role index : Line) : Line :=
  keccakWordLine (roleEnumerationBaseSlotFrom role) ++ index ++ [add]

/-! Read-only/runtime-entry role checks can use the first two memory words:
their inputs are still in calldata or are immediate instructions, and callers
do not depend on earlier memory.  Keeping this separate from the general
helpers preserves constructor arguments, role-update scratch, and the
post-decoder trigger packet while avoiding word-64 memory expansion on views. -/
def viewKeccakPairLines (first second : Line) : Line :=
  first ++ mstoreAt 0 ++ second ++ mstoreAt 1 ++
  [pushB256 64, pushB256 0, keccak256]

def viewKeccakPairLinesRightFirst (first second : Line) : Line :=
  second ++ mstoreAt 1 ++ first ++ mstoreAt 0 ++
  [pushB256 64, pushB256 0, keccak256]

def viewKeccakWordLine (word : Line) : Line :=
  word ++ mstoreAt 0 ++ [pushB256 32, pushB256 0, keccak256]

def viewRoleDataSlotFrom (role : Line) : Line :=
  viewKeccakPairLines role [pushB256 accessControlRolesPosition]

def viewRoleMembershipSlotFrom (role account : Line) : Line :=
  viewKeccakPairLinesRightFirst account (viewRoleDataSlotFrom role)

def viewRoleEnumerationBaseSlotFrom (role : Line) : Line :=
  viewKeccakPairLines role [pushB256 accessControlRoleMembersPosition]

def viewRoleEnumerationMemberSlotFrom (role index : Line) : Line :=
  viewKeccakWordLine (viewRoleEnumerationBaseSlotFrom role) ++ index ++ [add]

def unpackUint32Lane (packedWord destinationWord shift : B256) : Line :=
  storageMloadWord packedWord ++ [pushB256 shift, shr,
    pushB256 limitUint32Mask, and] ++ mstoreAt destinationWord

def packFiveUint32Words
    (maximum previous previousTimestamp frameDuration exitsPerFrame : B256) : Line :=
  storageMloadWord maximum ++ [pushB256 limitUint32Mask, and] ++
  storageMloadWord previous ++ [pushB256 limitUint32Mask, and,
    pushB256 32, shl, or] ++
  storageMloadWord previousTimestamp ++ [pushB256 limitUint32Mask, and,
    pushB256 64, shl, or] ++
  storageMloadWord frameDuration ++ [pushB256 limitUint32Mask, and,
    pushB256 96, shl, or] ++
  storageMloadWord exitsPerFrame ++ [pushB256 limitUint32Mask, and,
    pushB256 128, shl, or]

def lookupRecordMatches
    (role account storedRole storedAccount storedIndex : B256) : Prop :=
  storedIndex ≠ 0 ∧ storedRole = role ∧
    storedAccount = canonicalAccount account

def lookupCollision (role account storedRole storedAccount : B256) : Prop :=
  roleLookupPayload role account = roleLookupPayload storedRole storedAccount ∧
    (role ≠ storedRole ∨ canonicalAccount account ≠ canonicalAccount storedAccount)

def collisionRefusal (role account storedRole storedAccount : B256) : Bool :=
  if roleLookupPayload role account = roleLookupPayload storedRole storedAccount
  then role = storedRole && canonicalAccount account = canonicalAccount storedAccount
  else true

/-! ## Roles, constants, errors, events, and selector census -/

def defaultAdminRole : B256 :=
  0x0000000000000000000000000000000000000000000000000000000000000000
def pauseRole : B256 :=
  0x139c2898040ef16910dc9f44dc697df79363da767d8bc92f2e310312b816e46d
def resumeRole : B256 :=
  0x2fc10cc8ae19568712f7a176fb4978616a610650813c9d05326c34abb62749c7
def addFullWithdrawalRequestRole : B256 :=
  0x15fac8ba7fe8dd5344b88c1915452ce66976f270d1cd793c3b0ab579cecd33c0
def twExitLimitManagerRole : B256 :=
  0x03c30da9b9e4d4789ac88a294d39a63058ca4a498804c2aa823e381df59d0cf4
def twrLimitPosition : B256 :=
  0x3a69583d449251314fd68e4e68fe89ca455d27f2701d2fdee1b16c585fc4e2d6
def pauseInfinitely : B256 := B256.max
def version : B256 := 1

theorem defaultAdminRole_literal :
    defaultAdminRole =
      0x0000000000000000000000000000000000000000000000000000000000000000 := by
  rfl
theorem pauseRole_hash : pauseRole = Blanc.String.keccak "PAUSE_ROLE" := by decide +kernel
theorem resumeRole_hash : resumeRole = Blanc.String.keccak "RESUME_ROLE" := by decide +kernel
theorem addFullWithdrawalRequestRole_hash :
    addFullWithdrawalRequestRole =
      Blanc.String.keccak "ADD_FULL_WITHDRAWAL_REQUEST_ROLE" := by decide +kernel
theorem twExitLimitManagerRole_hash :
    twExitLimitManagerRole = Blanc.String.keccak "TW_EXIT_LIMIT_MANAGER_ROLE" := by decide +kernel
theorem twrLimitPosition_hash :
    twrLimitPosition =
      Blanc.String.keccak "lido.TriggerableWithdrawalsGateway.maxExitRequestLimit" := by
  decide +kernel

def publicConstantNames : List String :=
  [ "ADD_FULL_WITHDRAWAL_REQUEST_ROLE", "DEFAULT_ADMIN_ROLE",
    "PAUSE_INFINITELY", "PAUSE_ROLE", "RESUME_ROLE", "TWR_LIMIT_POSITION",
    "TW_EXIT_LIMIT_MANAGER_ROLE", "VERSION" ]

def roleConstants : List B256 :=
  [defaultAdminRole, pauseRole, resumeRole, addFullWithdrawalRequestRole,
   twExitLimitManagerRole]

inductive CustomError
  | zeroArgument | adminCannotBeZero | insufficientFee | feeRefundFailed
  | exitRequestsLimitExceeded | limitExceeded | tooLargeMaxExitRequestsLimit
  | tooLargeFrameDuration | tooLargeExitsPerFrame | zeroFrameDuration
  | zeroPauseDuration | pausedExpected | resumedExpected
  | pauseUntilMustBeInFuture
deriving DecidableEq

def CustomError.name : CustomError → String
  | .zeroArgument => "ZeroArgument"
  | .adminCannotBeZero => "AdminCannotBeZero"
  | .insufficientFee => "InsufficientFee"
  | .feeRefundFailed => "FeeRefundFailed"
  | .exitRequestsLimitExceeded => "ExitRequestsLimitExceeded"
  | .limitExceeded => "LimitExceeded"
  | .tooLargeMaxExitRequestsLimit => "TooLargeMaxExitRequestsLimit"
  | .tooLargeFrameDuration => "TooLargeFrameDuration"
  | .tooLargeExitsPerFrame => "TooLargeExitsPerFrame"
  | .zeroFrameDuration => "ZeroFrameDuration"
  | .zeroPauseDuration => "ZeroPauseDuration"
  | .pausedExpected => "PausedExpected"
  | .resumedExpected => "ResumedExpected"
  | .pauseUntilMustBeInFuture => "PauseUntilMustBeInFuture"

def customErrors : List CustomError :=
  [.zeroArgument, .adminCannotBeZero, .insufficientFee, .feeRefundFailed,
   .exitRequestsLimitExceeded, .limitExceeded, .tooLargeMaxExitRequestsLimit,
   .tooLargeFrameDuration, .tooLargeExitsPerFrame, .zeroFrameDuration,
   .zeroPauseDuration, .pausedExpected, .resumedExpected,
   .pauseUntilMustBeInFuture]

def customErrorSelectors : List B256 :=
  [0x56e42893, 0x6b35b1b7, 0xa458261b, 0x7f832e95, 0x83432d28,
   0x3261c792, 0xaea5046a, 0xbbdd2da3, 0x528f4863, 0x6765a75d,
   0xad58bfc7, 0xb047186b, 0x14378398, 0x73c5d8a6]

theorem custom_error_selector_census_length : customErrorSelectors.length = 14 := by
  decide

structure EventMetadata where
  name : String
  args : List ArgType
  indexed : List Nat
  topic : B256

def event (name : String) (args : List ArgType) (indexed : List Nat) : EventMetadata :=
  { name, args, indexed, topic := signatureHash name args }

def events : List EventMetadata :=
  [ event "ExitRequestsLimitSet" [.uint256, .uint256, .uint256] [],
    event "Paused" [.uint256] [],
    event "Resumed" [] [],
    event "RoleAdminChanged" [.bytes 32, .bytes 32, .bytes 32] [0, 1, 2],
    event "RoleGranted" [.bytes 32, .address, .address] [0, 1, 2],
    event "RoleRevoked" [.bytes 32, .address, .address] [0, 1, 2] ]

def eventTopics : List B256 :=
  [ 0x3119d910326e0f179e121df55f23f45b8a5022ff10c73c02aabf2b48ae36070a,
    0x32fb7c9891bc4f963c7de9f1186d2a7755c7d6e9f4604dabe1d8bb3027c2f49e,
    0x62451d457bc659158be6e6247f56ec1df424a5c7597f71c20c2bc44e0965c8f9,
    0xbd79b86ffe0ab8e8776151514217cd7cacd52c909f66475c3af44e129f0b00ff,
    0x2f8788117e7eff1d82e926ec794901d17c78024a50270940304540a733656f0d,
    0xf6391f5c32d9c69d2a47ea670b442974b53935d1edc7fd64eb21e047a839171b ]

theorem event_topic_census_length : eventTopics.length = 6 := by decide

structure SelectorEntry where
  name : String
  signature : String
  selector : B256
  payable : Bool
deriving DecidableEq

def rawSelector (signature : String) : B256 :=
  (Blanc.String.keccak signature).shiftRight 224

/-! These literals are the census values.  Keeping them in the family
source makes the dispatcher artifact auditable; the tie theorems below keep
the literal table connected to Blanc's kernel Keccak implementation. -/
def selPauseRole : B256 := 0x389ed267
def selResumeRole : B256 := 0x2de03aa1
def selAddFullWithdrawalRequestRole : B256 := 0xa0cbdf14
def selTwExitLimitManagerRole : B256 := 0x2d44866b
def selTwrLimitPosition : B256 := 0x76b0023e
def selVersion : B256 := 0xffa1ad74
def selResume : B256 := 0x046f7da2
def selPauseFor : B256 := 0xf3f449c7
def selPauseUntil : B256 := 0xabe9cfc8
def selTriggerFullWithdrawals : B256 := 0x138b1b15
def selSetExitRequestLimit : B256 := 0x56254a97
def selGetExitRequestLimitFullInfo : B256 := 0xb6b764b2
def selPauseInfinitely : B256 := 0xa302ee38
def selIsPaused : B256 := 0xb187bd26
def selGetResumeSinceTimestamp : B256 := 0x589ff76c
def selDefaultAdminRole : B256 := 0xa217fddf
def selSupportsInterface : B256 := 0x01ffc9a7
def selHasRole : B256 := 0x91d14854
def selGetRoleAdmin : B256 := 0x248a9ca3
def selGrantRole : B256 := 0x2f2ff15d
def selRevokeRole : B256 := 0xd547741f
def selRenounceRole : B256 := 0x36568abe
def selGetRoleMember : B256 := 0x9010d07c
def selGetRoleMemberCount : B256 := 0xca15c873

theorem selector_literal_ties :
    selPauseRole = selector "PAUSE_ROLE" [] ∧
    selResumeRole = selector "RESUME_ROLE" [] ∧
    selAddFullWithdrawalRequestRole = selector "ADD_FULL_WITHDRAWAL_REQUEST_ROLE" [] ∧
    selTwExitLimitManagerRole = selector "TW_EXIT_LIMIT_MANAGER_ROLE" [] ∧
    selTwrLimitPosition = selector "TWR_LIMIT_POSITION" [] ∧
    selVersion = selector "VERSION" [] ∧
    selResume = selector "resume" [] ∧
    selPauseFor = selector "pauseFor" [.uint256] ∧
    selPauseUntil = selector "pauseUntil" [.uint256] ∧
    selSetExitRequestLimit = selector "setExitRequestLimit" [.uint256, .uint256, .uint256] ∧
    selGetExitRequestLimitFullInfo = selector "getExitRequestLimitFullInfo" [] ∧
    selPauseInfinitely = selector "PAUSE_INFINITELY" [] ∧
    selIsPaused = selector "isPaused" [] ∧
    selGetResumeSinceTimestamp = selector "getResumeSinceTimestamp" [] ∧
    selDefaultAdminRole = selector "DEFAULT_ADMIN_ROLE" [] ∧
    selSupportsInterface = selector "supportsInterface" [.bytes 4] ∧
    selHasRole = selector "hasRole" [.bytes 32, .address] ∧
    selGetRoleAdmin = selector "getRoleAdmin" [.bytes 32] ∧
    selGrantRole = selector "grantRole" [.bytes 32, .address] ∧
    selRevokeRole = selector "revokeRole" [.bytes 32, .address] ∧
    selRenounceRole = selector "renounceRole" [.bytes 32, .address] ∧
    selGetRoleMember = selector "getRoleMember" [.bytes 32, .uint256] ∧
    selGetRoleMemberCount = selector "getRoleMemberCount" [.bytes 32] := by
  decide +kernel

theorem selector_trigger_literal_tie :
    selTriggerFullWithdrawals =
      rawSelector "triggerFullWithdrawals((uint256,uint256,bytes)[],address,uint256)" := by
  decide +kernel

def entry (name signature : String) (args : List ArgType) (payable : Bool) : SelectorEntry :=
  { name, signature, selector := selector name args, payable }

def entryLiteral (name signature : String) (sel : B256) (payable : Bool) : SelectorEntry :=
  { name, signature, selector := sel, payable }

def triggerEntry : SelectorEntry :=
  { name := "triggerFullWithdrawals",
    signature := "triggerFullWithdrawals((uint256,uint256,bytes)[],address,uint256)",
    selector := selTriggerFullWithdrawals,
    payable := true }

def selectorCensus : List SelectorEntry :=
  [ entryLiteral "PAUSE_ROLE" "PAUSE_ROLE()" selPauseRole false,
    entryLiteral "RESUME_ROLE" "RESUME_ROLE()" selResumeRole false,
    entryLiteral "ADD_FULL_WITHDRAWAL_REQUEST_ROLE"
      "ADD_FULL_WITHDRAWAL_REQUEST_ROLE()" selAddFullWithdrawalRequestRole false,
    entryLiteral "TW_EXIT_LIMIT_MANAGER_ROLE" "TW_EXIT_LIMIT_MANAGER_ROLE()"
      selTwExitLimitManagerRole false,
    entryLiteral "TWR_LIMIT_POSITION" "TWR_LIMIT_POSITION()" selTwrLimitPosition false,
    entryLiteral "VERSION" "VERSION()" selVersion false,
    entryLiteral "resume" "resume()" selResume false,
    entryLiteral "pauseFor" "pauseFor(uint256)" selPauseFor false,
    entryLiteral "pauseUntil" "pauseUntil(uint256)" selPauseUntil false,
    entryLiteral "triggerFullWithdrawals"
      "triggerFullWithdrawals((uint256,uint256,bytes)[],address,uint256)"
      selTriggerFullWithdrawals true,
    entryLiteral "setExitRequestLimit"
      "setExitRequestLimit(uint256,uint256,uint256)" selSetExitRequestLimit false,
    entryLiteral "getExitRequestLimitFullInfo" "getExitRequestLimitFullInfo()"
      selGetExitRequestLimitFullInfo false,
    entryLiteral "PAUSE_INFINITELY" "PAUSE_INFINITELY()" selPauseInfinitely false,
    entryLiteral "isPaused" "isPaused()" selIsPaused false,
    entryLiteral "getResumeSinceTimestamp" "getResumeSinceTimestamp()"
      selGetResumeSinceTimestamp false,
    entryLiteral "DEFAULT_ADMIN_ROLE" "DEFAULT_ADMIN_ROLE()" selDefaultAdminRole false,
    entryLiteral "supportsInterface" "supportsInterface(bytes4)"
      selSupportsInterface false,
    entryLiteral "hasRole" "hasRole(bytes32,address)" selHasRole false,
    entryLiteral "getRoleAdmin" "getRoleAdmin(bytes32)" selGetRoleAdmin false,
    entryLiteral "grantRole" "grantRole(bytes32,address)" selGrantRole false,
    entryLiteral "revokeRole" "revokeRole(bytes32,address)" selRevokeRole false,
    entryLiteral "renounceRole" "renounceRole(bytes32,address)" selRenounceRole false,
    entryLiteral "getRoleMember" "getRoleMember(bytes32,uint256)" selGetRoleMember false,
    entryLiteral "getRoleMemberCount" "getRoleMemberCount(bytes32)" selGetRoleMemberCount false ]

theorem selector_census_length : selectorCensus.length = 24 := by decide
theorem public_constant_census_length : publicConstantNames.length = 8 := by decide
theorem custom_error_census_length : customErrors.length = 14 := by decide
theorem event_census_length : events.length = 6 := by decide
theorem role_constant_census_length : roleConstants.length = 5 := by decide

/-! ## Source inventory vocabulary -/

inductive PersistentWriteClass
  | pause | limit | roleMembership | roleIndex | roleRecord | enumeration
deriving DecidableEq

inductive ExternalCallClass
  | locatorVault | vaultFee | withdrawalRequests | locatorRouter
  | stakingNotification | refund
deriving DecidableEq

structure SourceSite where
  label : String
  offset : Nat
deriving DecidableEq

structure SourceInventory where
  persistentWrites : List (SourceSite × PersistentWriteClass)
  externalCalls : List (SourceSite × ExternalCallClass)

end LidoTriggerableWithdrawalsGateway
end Blanc
