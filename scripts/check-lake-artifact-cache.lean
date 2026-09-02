import Lake.Build.Trace
import Std.Data.HashSet

open Lake System

private def refuse (message : String) : IO α :=
  throw <| IO.userError message

private def cacheHash (name : String) : IO Hash := do
  let parts := name.splitOn "."
  let digestText ← match parts.head? with
    | some value => pure value
    | none => refuse s!"cache artifact has no hash prefix: {name}"
  if parts.length > 1 && (parts.drop 1).all (·.isEmpty) then
    refuse s!"cache artifact has an empty extension: {name}"
  match Hash.ofHex? digestText with
  | some hash => return hash
  | none => refuse s!"cache artifact has an invalid hash prefix: {name}"

private def checkCache (artifacts : FilePath) : IO (Std.HashSet Hash × Nat) := do
  let entries ← artifacts.readDir
  let mut hashes : Std.HashSet Hash := {}
  let mut count := 0
  for entry in entries do
    let metadata ← entry.path.symlinkMetadata
    if metadata.type != .file then
      refuse s!"cache artifact is not a regular file: {entry.path}"
    let expected ← cacheHash entry.fileName
    let actual ← computeBinFileHash entry.path
    if actual != expected then
      refuse s!"cache artifact hash mismatch: {entry.path}; expected {expected}, got {actual}"
    hashes := hashes.insert expected
    count := count + 1
  return (hashes, count)

private def checkMaterialized
    (lakeDir : FilePath) (cacheHashes : Std.HashSet Hash) : IO Nat := do
  let paths ← lakeDir.walkDir
  let mut count := 0
  for sidecar in paths do
    if sidecar.toString.endsWith ".hash" then
      let metadata ← sidecar.symlinkMetadata
      if metadata.type != .file then
        refuse s!"output hash sidecar is not a regular file: {sidecar}"
      let recorded := (← IO.FS.readFile sidecar).trimAscii.toString
      let some expected := Hash.ofHex? recorded
        | continue -- legacy pre-cache decimal sidecar
      if cacheHashes.contains expected then
        let output := FilePath.mk <| sidecar.toString.dropEnd 5 |>.toString
        let outputMetadata ← output.symlinkMetadata
        if outputMetadata.type != .file then
          refuse s!"cached output is not a regular file: {output}"
        let actual ← computeBinFileHash output
        if actual != expected then
          refuse s!"materialized output hash mismatch: {output}; expected {expected}, got {actual}"
        count := count + 1
  return count

def main (args : List String) : IO UInt32 := do
  let [cacheArg, lakeArg] := args
    | refuse "usage: check-lake-artifact-cache.lean CACHE_DIR WORKTREE_LAKE_DIR"
  let cacheDir := FilePath.mk cacheArg
  let lakeDir := FilePath.mk lakeArg
  let (cacheHashes, cacheCount) ← checkCache (cacheDir / "artifacts")
  let materializedCount ← checkMaterialized lakeDir cacheHashes
  IO.println s!"OK — Lake artifact cache: verified {cacheCount} cache artifacts and {materializedCount} materialized outputs"
  return 0
