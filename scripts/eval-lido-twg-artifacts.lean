-- Emit the exact Blanc artifacts consumed by the offline Lido Triggerable
-- Withdrawals Gateway differential.  This evaluator owns no byte literals or
-- offset table: it reads both from the production module family.

import Blanc.LidoTriggerableWithdrawalsGatewayDeploy

namespace Blanc.LidoTriggerableWithdrawalsGateway

open Jaune

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
  let values := locatorWordOffsets.map toString
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

private def projectionRegions : List (String × Nat) :=
  [ ("config", configRegion),
    ("role-lookup-role", roleLookupRoleRegion),
    ("role-lookup-account", roleLookupAccountRegion),
    ("role-lookup-index", roleLookupIndexRegion),
    ("enum-role", enumRoleRegion),
    ("enum-account", enumAccountRegion) ]

private def projectionSlots : List (String × B256) :=
  [ ("resume-since", resumeSinceSlot),
    ("max-exit-requests", maxExitRequestsLimitSlot),
    ("previous-exit-requests", prevExitRequestsLimitSlot),
    ("previous-timestamp", prevTimestampSlot),
    ("frame-duration", frameDurationInSecSlot),
    ("exits-per-frame", exitsPerFrameSlot),
    ("role-record-length", roleRecordLengthSlot) ]

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
  IO.println s!"constructor-persistent-sites {persistentSiteRows.length} {String.intercalate "," persistentSiteRows}"
  IO.println s!"constructor-external-sites {constructorExternalCallInventory.length} -"
  let regions := projectionRegions.map fun (name, region) => s!"{name}|{region}"
  let regionWords := projectionRegions.map fun (name, region) =>
    s!"{name}|{(regionWord region).toHex}"
  let slots := projectionSlots.map fun (name, slot) => s!"{name}|{slot.toHex}"
  IO.println s!"projection-regions {regions.length} {String.intercalate "," regions}"
  IO.println s!"projection-region-words {regionWords.length} {String.intercalate "," regionWords}"
  IO.println s!"projection-slots {slots.length} {String.intercalate "," slots}"
  IO.println "projection-formula bitwise-or(region-times-two-pow-252,payload)"
  IO.println "constructor-arguments admin,locator,max-exit-requests,exits-per-frame,frame-duration"
  IO.println "constructor-events RoleGranted,ExitRequestsLimitSet"
  IO.println s!"limits {eip170RuntimeLimit} {eip3860InitcodeLimit} {constructorArgumentBytes}"
  IO.println s!"sizes {runtimeTemplateCodeSize} {lidoTwgCodeSize primaryArgs.toDeployParams} {lidoTwgCodeSize independentArgs.toDeployParams} {lidoTwgCodeHeadroom primaryArgs.toDeployParams} {lidoTwgCodeHeadroom independentArgs.toDeployParams} {eip3860InitcodeLimit - lidoTwgCreationTemplate.length} {eip3860InitcodeLimit - (lidoTwgFullCreateInput primaryArgs).length} {eip3860InitcodeLimit - (lidoTwgFullCreateInput independentArgs).length}"

end Blanc.LidoTriggerableWithdrawalsGateway
