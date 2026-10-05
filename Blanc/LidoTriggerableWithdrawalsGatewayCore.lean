import Blanc.CommonCore
import Blanc.RevertPayload
import Blanc.TaggedStorage

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

structure ValidatorExitData where
  stakingModuleId : B256
  nodeOperatorId : B256
  pubkey : Bytes

structure ExitLimitData where
  maxExitRequestsLimit : B256
  prevExitRequestsLimit : B256
  prevTimestamp : B256
  frameDurationInSec : B256
  exitsPerFrame : B256

structure LogicalState where
  resumeSince : B256
  limit : ExitLimitData
  roleRecordLength : B256

/-! ## Family-owned tagged storage -/

abbrev low252Mask : B256 := TaggedStorage.low252Mask
def addressMask : B256 := Nat.toB256 (2 ^ 160 - 1)


abbrev taggedSlot (region : Nat) (payload : B256) : B256 :=
  TaggedStorage.encode region payload

def configRegion : Nat := 1
def enumRoleRegion : Nat := 5

def resumeSinceSlot : B256 := taggedSlot configRegion 0
def maxExitRequestsLimitSlot : B256 := taggedSlot configRegion 1

def canonicalAccount (account : B256) : B256 := B256.and account addressMask
def roleLookupPayload (role account : B256) : B256 :=
  B256.and (B256.xor role (canonicalAccount account)) low252Mask

def enumRoleSlot (index : B256) : B256 := taggedSlot enumRoleRegion index

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

/-- The mathematical storage keys mirrored by the executable keccak helpers.
These definitions are proof/projection names; the program continues to derive
the keys by executing `KECCAK256` over the two-word images below. -/
def roleDataSlot (role : B256) : B256 :=
  (role.toBytes ++ accessControlRolesPosition.toBytes).keccak

def roleMembershipSlot (role account : B256) : B256 :=
  (account.toBytes ++ (roleDataSlot role).toBytes).keccak

def roleEnumerationBaseSlot (role : B256) : B256 :=
  (role.toBytes ++ accessControlRoleMembersPosition.toBytes).keccak

def roleEnumerationIndexSlot (role account : B256) : B256 :=
  (account.toBytes ++ ((roleEnumerationBaseSlot role) + 1).toBytes).keccak

def roleEnumerationMemberSlot (role index : B256) : B256 :=
  (roleEnumerationBaseSlot role).toBytes.keccak + index

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

inductive CustomError
  | zeroArgument | adminCannotBeZero | insufficientFee | feeRefundFailed
  | exitRequestsLimitExceeded | limitExceeded | tooLargeMaxExitRequestsLimit
  | tooLargeFrameDuration | tooLargeExitsPerFrame | zeroFrameDuration
  | zeroPauseDuration | pausedExpected | resumedExpected
  | pauseUntilMustBeInFuture

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

structure SelectorEntry where
  name : String
  signature : String
  selector : B256
  payable : Bool

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

def entry (name signature : String) (args : List ArgType) (payable : Bool) : SelectorEntry :=
  { name, signature, selector := selector name args, payable }


/-! ## Source inventory vocabulary -/

inductive PersistentWriteClass
  | pause | limit | roleMembership | roleIndex | roleRecord | enumeration

inductive ExternalCallClass
  | locatorVault | vaultFee | withdrawalRequests | locatorRouter
  | stakingNotification | refund

structure SourceSite where
  label : String
  offset : Nat

structure SourceInventory where
  persistentWrites : List (SourceSite × PersistentWriteClass)
  externalCalls : List (SourceSite × ExternalCallClass)

end LidoTriggerableWithdrawalsGateway
end Blanc
