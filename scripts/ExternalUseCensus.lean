import Lean
import Lean.Elab.Frontend
import Lean.Server.InfoUtils

/-!
Resolved external references for `leaf_audit.py`. The launcher supplies Lake's exact
setup, captures source identity, admits each elaboration and gives command-time IO
an isolated working directory containing the source inputs. No source rewriting or
Lean artifact export occurs here. `#eval` is elaborated normally, including its
implicit instances; generated files remain in the temporary working directory.
-/

namespace BlancExternalUseCensus

open Lean Lean.Elab

abbrev ParsedCommand := Lean.Language.Lean.CommandParsedSnapshot

def object (fields : List (String × Json)) : Json := Json.mkObj fields

def rangeJson (map : FileMap) (stx : Syntax) : Json :=
  toJson (stx.getRange? |>.map map.utf8RangeToLspRange)

def constantJson (env : Environment) (name : Name) : Option Json := do
  let idx ← env.getModuleIdxFor? name
  let module := env.header.moduleNames[idx.toNat]!
  if module.getRoot != `Blanc then none else do
    let ci ← env.find? name
    let hash := String.ofList (Nat.toDigits 16 ci.type.hash.toNat)
    return object [("name", toJson (name.toString (escape := false))),
      ("module", toJson (module.toString (escape := false))),
      ("fp", toJson ("".pushn '0' (16 - hash.length) ++ hash))]

/-- Resolve actual constants after elaboration, including field notation and instances. -/
def references (tree : InfoTree) : IO (Array Json) :=
  tree.foldInfoM (init := #[]) fun ctx info acc => do
    let exprs ← match info with
      | .ofTermInfo ti => ctx.runMetaM ti.lctx do
          return #[(← instantiateMVars ti.expr)]
      | .ofFieldInfo fi => ctx.runMetaM fi.lctx do
          return #[(← instantiateMVars fi.val), .const fi.projName []]
      | _ => pure #[]
    let mut result := acc
    for expr in exprs do
      for name in expr.getUsedConstants do
        if let some row := constantJson ctx.env name then
          result := result.push <| object [("constant", row),
            ("range", rangeJson ctx.fileMap info.stx)]
    return result

partial def commands (cmd : ParsedCommand) (map : FileMap) : IO (Array Json) := do
  let info := cmd.elabSnap.infoTreeSnap.get
  let some tree := info.infoTree?
    | throw <| IO.userError "COLLECTOR missing completed command InfoTree"
  if cmd.stx.isMissing then
    throw <| IO.userError "COLLECTOR missing command syntax"
  let here ← references tree
  if let some next := cmd.nextCmdSnap? then
    let rest ← commands next.get map
    return here ++ rest
  return here

/-- Hash the exact captured UTF-8 buffer, not a later read of its path. -/
def sha256 (bytes : ByteArray) : IO String := do
  let child ← IO.Process.spawn {
    cmd := "/usr/bin/shasum", args := #["-a", "256"],
    stdin := .piped, stdout := .piped, stderr := .piped }
  -- Keep the stdin handle in this scope so its last reference is released
  -- before waiting for the child's output (which requires EOF).
  let child ← do
    let (stdin, remaining) ← child.takeStdin
    stdin.write bytes
    stdin.flush
    pure remaining
  let stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let status ← child.wait
  if status != 0 then throw <| IO.userError s!"COLLECTOR SHA256 failed: {stderr}"
  let hash := stdout.take 64 |>.toString
  unless hash.length == 64 && hash.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
    throw <| IO.userError "COLLECTOR malformed SHA256 result"
  return hash

def setupImports (setup : ModuleSetup) (header : Elab.HeaderSyntax) :
    Lean.Language.ProcessingT IO
      (Except Lean.Language.Lean.HeaderProcessedSnapshot Lean.Language.Lean.SetupImportsResult) := do
  liftM <| setup.dynlibs.forM Lean.loadDynlib
  let opts := Lean.Elab.async.setIfNotSet
    (Lean.internal.cmdlineSnapshots.set setup.options.toOptions false) true
  return .ok {
    mainModuleName := setup.name, package? := setup.package?,
    isModule := strictOr setup.isModule header.isModule,
    imports := setup.imports?.getD header.imports, opts,
    importArts := setup.importArts, plugins := setup.plugins }

unsafe def collectInto (original buffer setupPath executionDir : System.FilePath)
    (output : IO.FS.Handle) : IO Unit := do
  let source ← IO.FS.readFile buffer
  let sourceHash ← sha256 source.toUTF8
  let originalSource ← IO.FS.readFile original
  let originalHash ← sha256 originalSource.toUTF8
  unless source == originalSource do
    throw <| IO.userError "COLLECTOR source buffer differs from original"
  let setupSource ← IO.FS.readFile setupPath
  let setupHash ← sha256 setupSource.toUTF8
  let setup : ModuleSetup ← match Json.parse setupSource >>= fromJson? with
    | .ok setup => pure setup
    | .error error => throw <| IO.userError s!"COLLECTOR invalid captured setup: {error}"
  let expectedName ← moduleNameOfFileName original none
  unless setup.name == expectedName || setup.name == `_unknown do
    throw <| IO.userError s!"COLLECTOR setup module mismatch: {setup.name} != {expectedName}"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  IO.Process.setCurrentDir executionDir
  let input := Parser.mkInputContext source original.toString
  let snap ← Lean.Language.Lean.process (setupImports setup) none { input with }
  let all := Lean.Language.toSnapshotTree snap
  -- All asynchronous diagnostic tasks finish before any accepted edit output.
  let hasErrors ← all.runAndReport setup.options.toOptions (json := true)
  let hasSorry := all.getAll.any fun s => s.diagnostics.msgLog.toList.any fun m =>
    m.data.hasTag (· == `hasSorry)
  if hasErrors || hasSorry then
    throw <| IO.userError "COLLECTOR failed diagnostics (errors or sorry)"
  let some parsed := snap.result?
    | throw <| IO.userError "COLLECTOR failed header parse"
  let some processed := parsed.processedSnap.get.result?
    | throw <| IO.userError "COLLECTOR failed header imports/setup"
  let inventory ← commands processed.firstCmdSnap.get input.fileMap
  let some finalState := Lean.Language.Lean.waitForFinalCmdState? snap
    | throw <| IO.userError "COLLECTOR missing completed final environment"
  let env := finalState.env
  let mut declarationUses : Array Json := #[]
  for (user, ci) in env.constants.toList do
    if (env.getModuleIdxFor? user).isNone then
      let constants := ci.type.getUsedConstants ++ (match ci with
        | .thmInfo v => v.value.getUsedConstants
        | .defnInfo v => v.value.getUsedConstants
        | .opaqueInfo v => v.value.getUsedConstants
        | _ => #[])
      for name in constants do
        if let some row := constantJson env name then
          declarationUses := declarationUses.push <| object [
            ("constant", row), ("user", toJson user.toString)]
  let result := object [
    ("schema", toJson (1 : Nat)), ("source_sha256", toJson sourceHash),
    ("original_sha256", toJson originalHash), ("setup_sha256", toJson setupHash),
    ("original_path", toJson original.toString), ("buffer_path", toJson buffer.toString),
    ("module", toJson setup.name.toString), ("setup_path", toJson setupPath.toString),
    ("setup_options", toJson setup.options),
    ("instrumentation", toJson #["internal.cmdlineSnapshots=false", "Elab.async default=true"]),
    ("resolved_uses", toJson inventory), ("declaration_uses", toJson declarationUses), ("execution_directory", toJson executionDir.toString)]
  output.putStr (result.pretty ++ "\n")
  output.flush

/-- Exclusive reservation precedes all frontend work and refuses even dangling
symlinks. Only our own fresh reservation is removed after a failed collection. -/
unsafe def collect (original buffer setupPath output executionDir : System.FilePath) : IO Unit := do
  let handle ← try IO.FS.Handle.mk output .writeNew catch error =>
    throw <| IO.userError s!"COLLECTOR fresh output required: {output}: {error}"
  try
    collectInto original buffer setupPath executionDir handle
  catch error =>
    IO.FS.removeFile output
    throw error

end BlancExternalUseCensus

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [original, buffer, setup, output, executionDir] =>
    try
      BlancExternalUseCensus.collect original buffer setup output executionDir
      return 0
    catch error =>
      IO.eprintln error.toString
      return 1
  | _ =>
    IO.eprintln "usage: ExternalUseCensus ORIGINAL BUFFER CANDIDATE_SETUP OUTPUT_JSON EXECUTION_DIRECTORY"
    return 2
