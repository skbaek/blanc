-- Emit the exact Blanc artifacts consumed by the offline Lido Triggerable
-- Withdrawals Gateway differential.  This evaluator owns no byte literals or
-- offset table: it reads both from the production module family.

import Blanc.LidoTriggerableWithdrawalsGatewayDeploy

namespace Blanc.LidoTriggerableWithdrawalsGateway

open Jaune
open Jaune.Ninst Ninst

private def primaryArgs : ConstructorArgs :=
  { admin := 0x111122223333444455556666777788889999aaaa
    locator := 0x22223333444455556666777788889999aaaabbbb
    maxExitRequestsLimit := 1000
    exitsPerFrame := 10
    frameDurationInSec := 3600 }

private def independentArgs : ConstructorArgs :=
  { admin := 0xabcdefabcdefabcdefabcdefabcdefabcdefabcd
    locator := 0x9876598765987659876598765987659876598765
    maxExitRequestsLimit := 25
    exitsPerFrame := 5
    frameDurationInSec := 12 }

private def emitBytes (label : String) (code : Bytes) : IO Unit :=
  IO.println s!"{label} {code.length} {code.toHex}"

private def emitOffsets : IO Unit :=
  let values := locatorWordOffsets.map fun offset => s!"{offset}"
  IO.println s!"offsets-locator {values.length} {String.intercalate "," values}"

private def persistentClassName : PersistentWriteClass → String
  | .pause => "pause"
  | .limit => "limit"
  | .roleMembership => "role-membership"
  | .roleIndex => "role-index"
  | .roleRecord => "role-record"
  | .enumeration => "enumeration"

private def persistentSiteRows : List String :=
  constructorPersistentWriteInventory.map fun (site, cls) =>
    s!"{site.label}|{site.offset}|{persistentClassName cls}"

private def projectionSlots : List (String × B256) :=
  [ ("resume-since", resumeSinceSlot),
    ("packed-exit-limit", maxExitRequestsLimitSlot),
    ("access-control-roles-root", accessControlRolesPosition),
    ("access-control-role-members-root", accessControlRoleMembersPosition) ]

/-! ## Performance-shape controls

These checks are deliberately derived from the production source terms.  Each
accepted shape is paired with a nearby losing mutant so the artifact consumer
can require both the positive fact and a live rejection channel. -/

private def compileLine (line : Line) : Option Bytes :=
  Prog.compile ⟨line +++ Func.stop, []⟩

private def expectedPackingLine : Line :=
  storageMloadWord 0 ++ [pushB256 limitUint32Mask, and] ++
  storageMloadWord 1 ++ [pushB256 limitUint32Mask, and,
    pushB256 32, shl, or] ++
  storageMloadWord 2 ++ [pushB256 limitUint32Mask, and,
    pushB256 64, shl, or] ++
  storageMloadWord 3 ++ [pushB256 limitUint32Mask, and,
    pushB256 96, shl, or] ++
  storageMloadWord 4 ++ [pushB256 limitUint32Mask, and,
    pushB256 128, shl, or]

private def wrongShiftPackingLine : Line :=
  storageMloadWord 0 ++ [pushB256 limitUint32Mask, and] ++
  storageMloadWord 1 ++ [pushB256 limitUint32Mask, and,
    pushB256 31, shl, or] ++
  storageMloadWord 2 ++ [pushB256 limitUint32Mask, and,
    pushB256 64, shl, or] ++
  storageMloadWord 3 ++ [pushB256 limitUint32Mask, and,
    pushB256 96, shl, or] ++
  storageMloadWord 4 ++ [pushB256 limitUint32Mask, and,
    pushB256 128, shl, or]

private def packingShapeValid : Bool :=
  compileLine (packFiveUint32Words 0 1 2 3 4) ==
    compileLine expectedPackingLine

private def packingShiftMutantRejected : Bool :=
  compileLine (packFiveUint32Words 0 1 2 3 4) !=
    compileLine wrongShiftPackingLine

private def collisionRoleA : B256 :=
  0xff2624aa3dfe6144c434d0032a59d95a44e6e6f8c041c18afa71f1ba624ebbb7
private def collisionRoleB : B256 :=
  0xff2624aa3dfe6144c434d0033b48c84b55f7f7e9d150d09beb60e0ab735faaa6
private def collisionAccountA : B256 :=
  0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
private def collisionAccountB : B256 :=
  0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb

private def keccakKeySeparationValid : Bool :=
  roleLookupPayload collisionRoleA collisionAccountA ==
      roleLookupPayload collisionRoleB collisionAccountB &&
    roleMembershipSlot collisionRoleA collisionAccountA !=
      roleMembershipSlot collisionRoleB collisionAccountB

private def flatKeyMutantRejected : Bool :=
  Bool.not (roleLookupPayload collisionRoleA collisionAccountA !=
    roleLookupPayload collisionRoleB collisionAccountB)

private def enumerationRoleA : B256 :=
  0x16f600e2f463d5214cb52fe4d8bdff8216f12f6524e1d23d8280d5e3628dd00f
private def enumerationRoleB : B256 :=
  0xf1a5e1b9d05705d6191ca1138effa6db04f31f1d0ac3ead6acd5f4f54c395f64

private def enumerationPerRoleValid : Bool :=
  roleEnumerationBaseSlot enumerationRoleA !=
      roleEnumerationBaseSlot enumerationRoleB &&
    roleEnumerationMemberSlot enumerationRoleA 0 !=
      roleEnumerationMemberSlot enumerationRoleB 0 &&
    roleEnumerationIndexSlot enumerationRoleA collisionAccountA !=
      roleEnumerationIndexSlot enumerationRoleB collisionAccountA

private def globalEnumerationMutantRejected : Bool :=
  Bool.not (enumRoleSlot 0 != enumRoleSlot 0)

private def sourceSloadCount : Func → Nat
  | .last _ => 0
  | .next (.reg .sload) rest => 1 + sourceSloadCount rest
  | .next _ rest => sourceSloadCount rest
  | .branch left right => sourceSloadCount left + sourceSloadCount right
  | .call _ => 0

private def extraReadRoleGuard : Func :=
  ([pushB256 resumeSinceSlot, sload, pop] +++
    onlyRole pauseRole Func.stop)

private def compiledRoleRouteValid : Bool :=
  sourceSloadCount (onlyRole pauseRole Func.stop) == 1 &&
    (Prog.compile ⟨onlyRole pauseRole Func.stop,
      [Func.revert, Func.revert]⟩).isSome

private def extraReadRoleMutantRejected : Bool :=
  sourceSloadCount extraReadRoleGuard == 2 &&
    Prog.compile ⟨onlyRole pauseRole Func.stop,
      [Func.revert, Func.revert]⟩ !=
      Prog.compile ⟨extraReadRoleGuard, [Func.revert, Func.revert]⟩

private def performanceControls : List (String × Bool × Bool) :=
  [ ("packing", packingShapeValid, packingShiftMutantRejected),
    ("keccak-key", keccakKeySeparationValid, flatKeyMutantRejected),
    ("enumeration", enumerationPerRoleValid, globalEnumerationMutantRejected),
    ("compiled-route", compiledRoleRouteValid, extraReadRoleMutantRejected) ]

#eval show IO Unit from do
  emitBytes "creation-template" lidoTwgCreationTemplate
  emitBytes "primary-create" (lidoTwgFullCreateInput primaryArgs)
  emitBytes "primary-runtime" (lidoTwgCode primaryArgs.toDeployParams)
  emitBytes "independent-create" (lidoTwgFullCreateInput independentArgs)
  emitBytes "independent-runtime" (lidoTwgCode independentArgs.toDeployParams)
  let selectors := lidoTwgSelectors.map B256.toHex
  IO.println s!"selectors {selectors.length} {String.intercalate "," selectors}"
  emitOffsets
  IO.println s!"offset-metadata-valid {locatorWordOffsetsValid}"
  IO.println s!"patch-controls-valid {runtimePatchControlsValid}"
  for (name, production, mutantRejected) in performanceControls do
    IO.println s!"performance-control {name} {production} {mutantRejected}"
  IO.println s!"constructor-persistent-sites {persistentSiteRows.length} {String.intercalate "," persistentSiteRows}"
  IO.println s!"constructor-external-sites {constructorExternalCallInventory.length} -"
  let slots := projectionSlots.map fun (name, slot) => s!"{name}|{slot.toHex}"
  IO.println s!"projection-slots {slots.length} {String.intercalate "," slots}"
  IO.println "projection-formula packed-limit-and-nested-keccak-per-role"
  IO.println "constructor-arguments admin,locator,max-exit-requests,exits-per-frame,frame-duration"
  IO.println "constructor-events RoleGranted,ExitRequestsLimitSet"
  IO.println s!"limits {eip170RuntimeLimit} {eip3860InitcodeLimit} {constructorArgumentBytes}"
  IO.println s!"sizes {runtimeTemplateCodeSize} {lidoTwgCodeSize primaryArgs.toDeployParams} {lidoTwgCodeSize independentArgs.toDeployParams} {lidoTwgCodeHeadroom primaryArgs.toDeployParams} {lidoTwgCodeHeadroom independentArgs.toDeployParams} {eip3860InitcodeLimit - lidoTwgCreationTemplate.length} {eip3860InitcodeLimit - (lidoTwgFullCreateInput primaryArgs).length} {eip3860InitcodeLimit - (lidoTwgFullCreateInput independentArgs).length}"

end Blanc.LidoTriggerableWithdrawalsGateway
