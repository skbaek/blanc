-- Emit the exact Blanc artifacts consumed by the offline Lido differential.
--
-- This file is an evaluator, not a second artifact owner.  Runtime bytes,
-- creation bytes, selector identities, and immutable patch locations are all
-- read from the production Lido module family.
-- SHA-256 is deliberately not reimplemented here: the differential derives
-- digests downstream from these exact evaluator-emitted bytes.

import Blanc.LidoCircuitBreakerDeploy

namespace Blanc.LidoCircuitBreaker

open Jaune

private def emitBytes (label : String) (code : Bytes) : IO Unit :=
  IO.println s!"{label} {code.length} {code.toHex}"

private def emitOffsets (field : ImmutableParameter) : IO Unit :=
  let name := match field with
    | .admin => "admin"
    | .minPauseDuration => "min-pause"
    | .maxPauseDuration => "max-pause"
    | .minHeartbeatInterval => "min-heartbeat"
    | .maxHeartbeatInterval => "max-heartbeat"
  let values := immutableWordOffsets field |>.map toString
  IO.println s!"offsets-{name} {values.length} {String.intercalate "," values}"

private def persistentClassName : PersistentWriteClass → String
  | .configuration => "configuration"
  | .heartbeatExpiry => "heartbeat-expiry"
  | .registryAssignment => "registry-assignment"
  | .registryCount => "registry-count"
  | .registryArray => "registry-array"
  | .registryIndex => "registry-index"

private def transientClassName : TransientWriteClass → String
  | .reentrancyLock => "reentrancy-lock"

private def externalClassName : ExternalCallClass → String
  | .pauseQuery => "pause-query"
  | .pauseInvoke => "pause-invoke"

private def emitSites (label : String) (rows : List String) : IO Unit :=
  IO.println s!"{label} {rows.length} {if rows.isEmpty then "-" else String.intercalate "," rows}"

private def persistentSiteRows
    (inventory : List (SourceSite × PersistentWriteClass)) : List String :=
  inventory.map fun (site, cls) =>
    s!"{site.label}|{site.offset}|{persistentClassName cls}"

private def transientSiteRows
    (inventory : List (SourceSite × TransientWriteClass)) : List String :=
  inventory.map fun (site, cls) =>
    s!"{site.label}|{site.offset}|{transientClassName cls}"

private def externalSiteRows
    (inventory : List (SourceSite × ExternalCallClass)) : List String :=
  inventory.map fun (site, cls) =>
    s!"{site.label}|{site.offset}|{externalClassName cls}"

private def projectionRegions : List (String × Nat) :=
  [ ("config", configRegion), ("expiry", expiryRegion),
    ("assignment", assignmentRegion), ("index", indexRegion),
    ("count", countRegion), ("array", arrayRegion) ]

#eval show IO Unit from do
  emitBytes "creation-template" lidoCircuitBreakerCreationTemplate
  emitBytes "official-create" officialFullCreateInput
  emitBytes "official-runtime" (lidoCircuitBreakerCode officialParams)
  emitBytes "independent-create" independentFullCreateInput
  emitBytes "independent-runtime"
    (lidoCircuitBreakerCode independentConstructorArgs.toDeployParams)
  let selectors := lidoCircuitBreakerSelectors.map (fun value => value.toHex)
  IO.println s!"selectors {selectors.length} {String.intercalate "," selectors}"
  for field in immutableParameters do
    emitOffsets field
  IO.println s!"offset-metadata-valid {immutableOffsetMetadataValid}"
  IO.println s!"patch-controls-valid {runtimePatchControlsValid}"
  emitSites "runtime-persistent-sites"
    (persistentSiteRows persistentWriteInventory)
  emitSites "runtime-transient-sites"
    (transientSiteRows transientWriteInventory)
  emitSites "runtime-external-sites"
    (externalSiteRows externalCallInventory)
  IO.println s!"runtime-site-counts {programSiteCount sourceSstoreSiteCount (runtime officialParams)} {programSiteCount sourceTstoreSiteCount (runtime officialParams)} {programSiteCount sourceExternalCallSiteCount (runtime officialParams)}"
  emitSites "constructor-persistent-sites"
    (persistentSiteRows constructorPersistentWriteInventory)
  emitSites "constructor-transient-sites"
    (transientSiteRows constructorTransientWriteInventory)
  emitSites "constructor-external-sites"
    (externalSiteRows constructorExternalCallInventory)
  IO.println s!"constructor-site-counts {constructorProgramSiteCounts.1} {constructorProgramSiteCounts.2.1} {constructorProgramSiteCounts.2.2}"
  let regions := projectionRegions.map fun (name, region) => s!"{name}|{region}"
  let regionWords := projectionRegions.map fun (name, region) =>
    s!"{name}|{(regionWord region).toHex}"
  IO.println s!"projection-regions {regions.length} {String.intercalate "," regions}"
  IO.println s!"projection-region-words {regionWords.length} {String.intercalate "," regionWords}"
  IO.println "projection-formula bitwise-or(region-times-two-pow-252,payload)"
  IO.println "projection-domain canonical-address-bits=160,tag-payload-upper-bound-exclusive=2^252,array-index=one-based,zero-count-explicit=true,targets-nodup=true,targets-nonzero=true,pausers-nonzero=true"
  IO.println s!"limits {eip170RuntimeLimit} {eip3860InitcodeLimit} {constructorArgumentBytes}"
  IO.println s!"sizes {runtimeTemplateCodeSize} {lidoCircuitBreakerCodeSize officialParams} {lidoCircuitBreakerCodeSize independentConstructorArgs.toDeployParams} {lidoCircuitBreakerCodeHeadroom officialParams} {lidoCircuitBreakerCodeHeadroom independentConstructorArgs.toDeployParams} {eip3860InitcodeLimit - lidoCircuitBreakerCreationTemplate.length} {eip3860InitcodeLimit - officialFullCreateInput.length} {eip3860InitcodeLimit - independentFullCreateInput.length}"

end Blanc.LidoCircuitBreaker
