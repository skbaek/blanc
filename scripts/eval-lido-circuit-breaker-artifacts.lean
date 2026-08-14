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

/-! Read-only compiler layout metadata for the artifact profiler.  These rows
are derived from the exact `Prog` values whose bytes this evaluator emits.  In
particular, they neither compile a second program nor carry byte literals. -/

private structure LayoutSpan where
  label : String
  start : Nat
  length : Nat

private def lineSize (line : Line) : Nat :=
  line.foldl (fun total inst => total + inst.size) 0

/-- Endpoint bodies are inline in the balanced dispatcher.  Walk the same
`DispatchTree` and the same `dispatchWith` size equation to expose each leaf's
exact byte interval. -/
private def endpointSpans (start : Nat) : DispatchTree → List LayoutSpan
  | .leaf word body =>
      let prefixSize := lineSize [Ninst.pushB256 word, Ninst.eq]
      -- `body <?> .call fallbackSlot` is `Func.branch (.call ...) body`:
      -- compile the fallback call first, then JUMPDEST, then the body.
      [{ label := word.toHex,
         start := start + prefixSize + 4 + compsize (.call fallbackSlot) + 1,
         length := compsize body }]
  | .fork left right =>
      let prefixSize := lineSize
        [Ninst.dup 0, Ninst.pushB256 (leftmostFsig right), Ninst.gt]
      -- `left <?> right` is `Func.branch right left`: compiler byte order is
      -- the right subtree, JUMPDEST, then the left subtree.
      let rightStart := start + prefixSize + 4
      let leftStart := rightStart + compsize (dispatchWith fallbackSlot right) + 1
      endpointSpans rightStart right ++ endpointSpans leftStart left

private def runtimeEndpointSpans : List LayoutSpan :=
  -- Byte zero is the main table entry's JUMPDEST; `fsig` precedes dispatch.
  endpointSpans (1 + lineSize fsig) (tree officialParams)

private def runtimeTableNames : List String :=
  [ "main", "fallback", "error-pausable-zero", "error-sender-not-admin",
    "error-sender-not-pauser", "error-pause-below-min",
    "error-pause-above-max", "error-heartbeat-below-min",
    "error-heartbeat-above-max", "error-heartbeat-expired",
    "error-pause-failed", "error-reentrant-call", "empty-revert",
    "bubble-revert", "set-pauser-kernel", "append-target",
    "after-old-pauser", "remove-target", "finish-set-pauser",
    "register-after-set", "pause-after-set", "enumeration-loop",
    "arithmetic-panic" ]

private def constructorTableNames : List String :=
  [ "main", "empty-revert", "error-admin-zero",
    "error-min-pause-zero", "error-min-pause-above-max",
    "error-min-heartbeat-zero", "error-min-heartbeat-above-max",
    "error-pause-below-min", "error-pause-above-max",
    "error-heartbeat-below-min", "error-heartbeat-above-max" ]

private def emitTableLayout
    (label : String) (names : List String) (program : Prog) : IO Unit := do
  let entries := table 0 (program.main :: program.aux)
  let rows := (List.zip names entries).map fun (name, start, body) =>
    s!"{name}|{start}|{compsize body + 1}"
  IO.println s!"{label} {rows.length} {String.intercalate "," rows}"

private def emitLayoutSpans (label : String) (spans : List LayoutSpan) : IO Unit :=
  let rows := spans.map fun span =>
    s!"{span.label}|{span.start}|{span.length}"
  IO.println s!"{label} {rows.length} {String.intercalate "," rows}"

#eval show IO Unit from do
  emitBytes "creation-template" lidoCircuitBreakerCreationTemplate
  emitBytes "official-create" officialFullCreateInput
  emitBytes "official-runtime" (lidoCircuitBreakerCode officialParams)
  emitBytes "independent-create" independentFullCreateInput
  emitBytes "independent-runtime"
    (lidoCircuitBreakerCode independentConstructorArgs.toDeployParams)
  emitTableLayout "runtime-table-layout" runtimeTableNames
    (runtime officialParams)
  emitLayoutSpans "runtime-endpoint-layout" runtimeEndpointSpans
  emitTableLayout "constructor-table-layout" constructorTableNames
    lidoCircuitBreakerConstructorProgram
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
