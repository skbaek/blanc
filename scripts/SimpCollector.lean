import Lean
import Lean.Elab.Frontend
import Lean.Server.InfoUtils
import Lean.Meta.Tactic.TryThis

/-!
One-file collection of parser sites and simplifier TryThis TextEdits. This
executable does not export Lean artifacts or apply edits. Its launcher admits
the elaboration, supplies this checkout's exact Lake setup and preserves the
original file/module identity when reading an instrumented buffer.
-/

namespace BlancSimpCollector

open Lean Lean.Elab

abbrev ParsedCommand := Lean.Language.Lean.CommandParsedSnapshot

def object (fields : List (String × Json)) : Json := Json.mkObj fields

def rangeJson (map : FileMap) (stx : Syntax) : Json :=
  toJson (stx.getRange? |>.map map.utf8RangeToLspRange)

def textOf (map : FileMap) (stx : Syntax) : String :=
  match stx.getRange? with
  | some r => String.Pos.Raw.extract map.source r.start r.stop
  | none => ""

/-- Pinned parser shapes, including compact macro wrappers; never lexical names. -/
def simpFamily? (stx : Syntax) : Option String :=
  let kind := stx.getKind
  if #[``Lean.Parser.Tactic.simp, ``Lean.Parser.Tactic.simpTrace,
      ``Lean.Parser.Tactic.simpAutoUnfold].contains kind then
    some "simp"
  else if #[``Lean.Parser.Tactic.simpAll, ``Lean.Parser.Tactic.simpAllTrace,
      ``Lean.Parser.Tactic.simpAllAutoUnfold].contains kind then
    some "simp_all"
  else if #[``Lean.Parser.Tactic.dsimp, ``Lean.Parser.Tactic.dsimpTrace,
      ``Lean.Parser.Tactic.dsimpAutoUnfold].contains kind then
    some "dsimp"
  else if #[``Lean.Parser.Tactic.simpa, ``Lean.Parser.Tactic.simpaUsingBang].contains kind then
    some "simpa"
  else if stx.getArgs.size == 2 then
    let head := stx[0].getAtomVal
    let rest := stx[1].getKind
    if head == "simp?!" && rest == ``Lean.Parser.Tactic.simpTraceArgsRest then some "simp"
    else if head == "simp_all?!" && rest == ``Lean.Parser.Tactic.simpAllTraceArgsRest then some "simp_all"
    else if head == "dsimp?!" && rest == ``Lean.Parser.Tactic.dsimpTraceArgsRest then some "dsimp"
    else if #["simpa!", "simpa?", "simpa?!"].contains head &&
        #[``Lean.Parser.Tactic.simpaArgsRest, ``Lean.Parser.Tactic.simpaUsingBangArgsRest].contains rest then
      some "simpa"
    else none
  else none

/-- Exact optional keyword slots in Init/Tactics.lean and Init/Meta.lean.
No config, term, discharger, or location descendant can set this flag. -/
def onlyNode (stx : Syntax) : Syntax :=
  let kind := stx.getKind
  if #[``Lean.Parser.Tactic.simpTrace, ``Lean.Parser.Tactic.simpAllTrace].contains kind then stx[2][2]
  else if kind == ``Lean.Parser.Tactic.dsimpTrace then stx[2][1]
  else if #[``Lean.Parser.Tactic.simpa, ``Lean.Parser.Tactic.simpaUsingBang].contains kind then stx[3][2]
  else if stx.getArgs.size == 2 then
    if stx[1].getKind == ``Lean.Parser.Tactic.dsimpTraceArgsRest then stx[1][1]
    else stx[1][2]
  else stx[3]

partial def sites (map : FileMap) (command : Syntax) (stx : Syntax) : Array Json := Id.run do
  let mut rows := #[]
  if let some family := simpFamily? stx then
    let head := stx[0].getAtomVal
    let only := !(onlyNode stx).isNone
    rows := rows.push <| object [
      ("family", toJson family), ("head", toJson head),
      ("kind", toJson stx.getKind.toString), ("only", toJson only),
      ("onlyRange", rangeJson map (onlyNode stx)),
      ("argumentKinds", toJson (stx.getArgs.map (·.getKind.toString))),
      ("range", rangeJson map stx), ("headRange", rangeJson map stx[0]),
      ("commandRange", rangeJson map command), ("source", toJson (textOf map stx))]
  for child in stx.getArgs do
    rows := rows ++ sites map command child
  return rows

def edits (tree : InfoTree) (command : Syntax) : Array Json :=
  tree.foldInfo (init := #[]) fun ctx info acc =>
    match info with
    | .ofCustomInfo ci =>
      match ci.value.get? Lean.Meta.Tactic.TryThis.TryThisInfo with
      | some ti => acc.push <| object [
          ("range", toJson ti.edit.range), ("newText", toJson ti.edit.newText),
          ("referenceRange", rangeJson ctx.fileMap ci.stx),
          ("commandRange", rangeJson ctx.fileMap command),
          ("parentDeclaration", toJson (ctx.parentDecl?.map Name.toString))]
      | none => acc
    | _ => acc

partial def commands (cmd : ParsedCommand) (map : FileMap) : IO (Array Json × Array Json) := do
  let info := cmd.elabSnap.infoTreeSnap.get
  let some tree := info.infoTree?
    | throw <| IO.userError "COLLECTOR missing completed command InfoTree"
  if cmd.stx.isMissing then
    throw <| IO.userError "COLLECTOR missing command syntax"
  let hereSites := sites map cmd.stx cmd.stx
  let hereEdits := edits tree cmd.stx
  if let some next := cmd.nextCmdSnap? then
    let (restSites, restEdits) ← commands next.get map
    return (hereSites ++ restSites, hereEdits ++ restEdits)
  return (hereSites, hereEdits)

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

unsafe def collectInto (original buffer setupPath : System.FilePath)
    (output : IO.FS.Handle) : IO Unit := do
  let source ← IO.FS.readFile buffer
  let sourceHash ← sha256 source.toUTF8
  let originalSource ← IO.FS.readFile original
  let originalHash ← sha256 originalSource.toUTF8
  let setupSource ← IO.FS.readFile setupPath
  let setupHash ← sha256 setupSource.toUTF8
  let setup : ModuleSetup ← match Json.parse setupSource >>= fromJson? with
    | .ok setup => pure setup
    | .error error => throw <| IO.userError s!"COLLECTOR invalid captured setup: {error}"
  let expectedName ← moduleNameOfFileName original none
  unless setup.name == expectedName do
    throw <| IO.userError s!"COLLECTOR setup module mismatch: {setup.name} != {expectedName}"
  initSearchPath (← findSysroot)
  enableInitializersExecution
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
  let (inventory, replacements) ← commands processed.firstCmdSnap.get input.fileMap
  let result := object [
    ("schema", toJson (1 : Nat)), ("source_sha256", toJson sourceHash),
    ("original_sha256", toJson originalHash), ("setup_sha256", toJson setupHash),
    ("original_path", toJson original.toString), ("buffer_path", toJson buffer.toString),
    ("module", toJson setup.name.toString), ("setup_path", toJson setupPath.toString),
    ("setup_options", toJson setup.options),
    ("instrumentation", toJson #["internal.cmdlineSnapshots=false", "Elab.async default=true"]),
    ("inventory", toJson inventory), ("edits", toJson replacements)]
  output.putStr (result.pretty ++ "\n")
  output.flush

/-- Exclusive reservation precedes all frontend work and refuses even dangling
symlinks. Only our own fresh reservation is removed after a failed collection. -/
unsafe def collect (original buffer setupPath output : System.FilePath) : IO Unit := do
  let handle ← try IO.FS.Handle.mk output .writeNew catch error =>
    throw <| IO.userError s!"COLLECTOR fresh output required: {output}: {error}"
  try
    collectInto original buffer setupPath handle
  catch error =>
    IO.FS.removeFile output
    throw error

end BlancSimpCollector

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [original, buffer, setup, output] =>
    try
      BlancSimpCollector.collect original buffer setup output
      return 0
    catch error =>
      IO.eprintln error.toString
      return 1
  | _ =>
    IO.eprintln "usage: simpCollector ORIGINAL BUFFER CANDIDATE_SETUP OUTPUT_JSON"
    return 2
