import Lean
import Lean.Elab.Frontend
import Lean.Server.InfoUtils

/-! Evidence-only parser/owner control. It exports no Lean artifacts and never
edits production sources. Its executable frontend needs separate admission. -/

namespace SimpaUsingSyntaxControl

open Lean Lean.Elab

private def object (fields : List (String × Json)) : Json := Json.mkObj fields

private partial def nameJson : Name → Json
  | .anonymous => object [("tag", toJson "anonymous")]
  | .str parent value => object [("tag", toJson "str"), ("parent", nameJson parent), ("value", toJson value)]
  | .num parent value => object [("tag", toJson "num"), ("parent", nameJson parent), ("value", toJson value)]

private def preresolvedJson : Syntax.Preresolved → Json
  | .namespace name => object [("tag", toJson "namespace"), ("name", nameJson name)]
  | .decl name fields => object [("tag", toJson "decl"), ("name", nameJson name), ("fields", toJson fields)]

/-- Preserve every semantic syntax constructor field, excluding only SourceInfo.
No range equality, whitespace masking, identifier normalization or macro expansion. -/
private partial def structureJson : Syntax → Json
  | .missing => object [("tag", toJson "missing")]
  | .node _ kind children => object [("tag", toJson "node"), ("kind", nameJson kind),
      ("children", Json.arr (children.map structureJson))]
  | .atom _ value => object [("tag", toJson "atom"), ("value", toJson value)]
  | .ident _ raw name preresolved => object [("tag", toJson "ident"), ("raw", toJson raw.toString),
      ("name", nameJson name), ("preresolved", Json.arr (preresolved.toArray.map preresolvedJson))]

private def rangeJson (map : FileMap) (stx : Syntax) : Json :=
  toJson (stx.getRange? |>.map map.utf8RangeToLspRange)

private def textOf (map : FileMap) (stx : Syntax) : String :=
  match stx.getRange? with
  | some range => String.Pos.Raw.extract map.source range.start range.stop
  | none => ""

private structure View where
  head : Syntax
  cfg : Syntax
  discharger : Syntax
  bang : Bool
  only : Syntax
  args : Syntax
  usingToken : Syntax
  usingTerm : Syntax

/-- Exact pinned Init/Tactics simpa parser shape; compact/bang/quoted owners excluded. -/
private def view (stx : Syntax) : Except String View := do
  unless stx.getKind == ``Lean.Parser.Tactic.simpa do
    throw "unsupported original/raw owner kind"
  match stx with
  | `(tactic| simpa%$head $[?%$question]? $[!%$bang]? $cfg:optConfig $(discharger)?
      $[only%$only]? $[[$args,*]]? $[using%$usingToken $usingTerm]?) =>
    if question.isSome then throw "question owner is not an admitted final head"
    let some usingToken := usingToken | throw "missing using token"
    let some usingTerm := usingTerm | throw "missing using term"
    return {
      head := head
      cfg := cfg.raw
      discharger := (discharger.map (·.raw)).getD .missing
      bang := bang.isSome
      only := only.getD .missing
      args := stx[3][3] -- optConfig0/discharger1/only2/simpArgs3/using4
      usingToken := usingToken
      usingTerm := usingTerm.raw
    }
  | _ => throw "unsupported simpa syntax shape"

private partial def findOwner (map : FileMap) (stx : Syntax) (wanted : Json) : Array Syntax := Id.run do
  let mut found := #[]
  if stx.getKind == ``Lean.Parser.Tactic.simpa && rangeJson map stx == wanted then
    found := found.push stx
  for child in stx.getArgs do
    found := found ++ findOwner map child wanted
  return found

private def environments (tree : InfoTree) (map : FileMap) (wanted : Json) : Array ContextInfo :=
  tree.foldInfo (init := #[]) fun ctx info found =>
    match info with
    | .ofTacticInfo tactic =>
      if rangeJson map tactic.stx == wanted && tactic.stx.getKind == ``Lean.Parser.Tactic.simpa then
        found.push ctx
      else found
    | _ => found

private def required (json : Json) (key : String) : IO Json :=
  match json.getObjVal? key with
  | .ok value => pure value
  | .error error => throw <| IO.userError error

private def stringField (json : Json) (key : String) : IO String :=
  match json.getObjValAs? String key with
  | .ok value => pure value
  | .error error => throw <| IO.userError error

private def parseOwner (env : Environment) (source : String) : IO Syntax :=
  match Parser.runParserCategory env `tactic source "<source-owned-head>" with
  | .ok parsed => pure parsed
  | .error error => throw <| IO.userError s!"head syntax parse refused: {error}"

private def getView (parsed : Syntax) : IO View :=
  match view parsed with
  | .ok value => pure value
  | .error error => throw <| IO.userError error

private def checkedSyntax (map : FileMap) (command owner : Syntax) (ctx : ContextInfo)
    (request : Json) : IO Json := do
  let originalText ← stringField request "original_source"
  let rawText ← stringField request "raw_action_source"
  unless textOf map owner == originalText do
    throw <| IO.userError "original source owner bytes mismatch"
  let originalParsed ← parseOwner ctx.env originalText
  let rawParsed ← parseOwner ctx.env rawText
  unless structureJson originalParsed == structureJson owner do
    throw <| IO.userError "actual owner environment reparse structure mismatch"
  let original ← getView owner
  let raw ← getView rawParsed
  unless structureJson original.usingTerm == structureJson raw.usingTerm do
    throw <| IO.userError "genuine action using term structural mismatch"
  unless structureJson original.cfg == structureJson raw.cfg &&
      structureJson original.discharger == structureJson raw.discharger && original.bang == raw.bang do
    throw <| IO.userError "genuine action configuration/flags/discharger mismatch"
  unless !raw.only.isMissing && !raw.args.isNone && raw.head.getAtomVal == "simpa" do
    throw <| IO.userError "genuine action lacks exact explicit native head/list"
  let rawMap := (Parser.mkInputContext rawText "<native-action>").fileMap
  return object [
    ("original_range", rangeJson map owner), ("command_range", rangeJson map command),
    ("parent_declaration", toJson (ctx.parentDecl?.map Name.toString)),
    ("actual_owner_structure", structureJson owner),
    ("original_reparse_structure", structureJson originalParsed),
    ("raw_action_structure", structureJson rawParsed),
    ("original_using_structure", structureJson original.usingTerm),
    ("raw_using_structure", structureJson raw.usingTerm),
    ("original_config_structure", structureJson original.cfg),
    ("raw_config_structure", structureJson raw.cfg),
    ("original_discharger_structure", structureJson original.discharger),
    ("raw_discharger_structure", structureJson raw.discharger),
    ("original_bang", toJson original.bang), ("raw_bang", toJson raw.bang),
    ("original_head_range", rangeJson map original.head),
    ("original_using_token_range", rangeJson map original.usingToken),
    ("original_using_term_range", rangeJson map original.usingTerm),
    ("raw_head_range", rangeJson rawMap raw.head),
    ("raw_only_range", rangeJson rawMap raw.only),
    ("raw_list_range", rangeJson rawMap raw.args),
    ("raw_using_token_range", rangeJson rawMap raw.usingToken),
    ("raw_using_term_range", rangeJson rawMap raw.usingTerm)]

private partial def inspect (cmd : Lean.Language.Lean.CommandParsedSnapshot) (map : FileMap)
    (request : Json) : IO (Array Json) := do
  let wanted ← required request "owner_range"
  let wantedCommand ← required request "command_range"
  let mut results := #[]
  if rangeJson map cmd.stx == wantedCommand then
    let owners := findOwner map cmd.stx wanted
    unless owners.size == 1 do throw <| IO.userError "missing/ambiguous exact source owner"
    let some tree := cmd.elabSnap.infoTreeSnap.get.infoTree?
      | throw <| IO.userError "missing completed owner InfoTree"
    let contexts := environments tree map wanted
    unless contexts.size == 1 do throw <| IO.userError "missing/ambiguous exact owner environment"
    let some owner := owners[0]? | throw <| IO.userError "missing owner"
    let some ctx := contexts[0]? | throw <| IO.userError "missing owner context"
    results := results.push (← checkedSyntax map cmd.stx owner ctx request)
  if let some next := cmd.nextCmdSnap? then
    results := results ++ (← inspect next.get map request)
  return results

private def sha256 (bytes : ByteArray) : IO String := do
  let child ← IO.Process.spawn {
    cmd := "/usr/bin/shasum", args := #["-a", "256"],
    stdin := .piped, stdout := .piped, stderr := .piped }
  let child ← do
    let (stdin, remaining) ← child.takeStdin
    stdin.write bytes
    stdin.flush
    pure remaining
  let stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let status ← child.wait
  if status != 0 then throw <| IO.userError s!"syntax SHA256 failed: {stderr}"
  let hash := stdout.take 64 |>.toString
  unless hash.length == 64 && hash.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
    throw <| IO.userError "syntax malformed SHA256 result"
  return hash

private def setupImports (setup : ModuleSetup) (header : Elab.HeaderSyntax) :
    Lean.Language.ProcessingT IO
      (Except Lean.Language.Lean.HeaderProcessedSnapshot Lean.Language.Lean.SetupImportsResult) := do
  unless setup.dynlibs.isEmpty && setup.plugins.isEmpty do
    throw <| IO.userError "syntax control rejects plugin/dynlib setup"
  let opts := Lean.Elab.async.setIfNotSet
    (Lean.internal.cmdlineSnapshots.set setup.options.toOptions false) true
  return .ok {
    mainModuleName := setup.name, package? := setup.package?,
    isModule := strictOr setup.isModule header.isModule,
    imports := setup.imports?.getD header.imports, opts,
    importArts := setup.importArts, plugins := setup.plugins }

private unsafe def controlInto (original input setupPath requestPath : System.FilePath)
    (output : IO.FS.Handle) : IO Unit := do
  let source ← IO.FS.readFile input
  let originalSource ← IO.FS.readFile original
  let setupSource ← IO.FS.readFile setupPath
  let requestSource ← IO.FS.readFile requestPath
  let request ← match Json.parse requestSource with
    | .ok value => pure value
    | .error error => throw <| IO.userError error
  unless (← required request "schema") == toJson (1 : Nat) do
    throw <| IO.userError "syntax request schema mismatch"
  let sourceHash ← sha256 source.toUTF8
  let originalHash ← sha256 originalSource.toUTF8
  let setupHash ← sha256 setupSource.toUTF8
  for (key, actual) in [("original_sha256", originalHash), ("input_source_sha256", sourceHash),
                        ("setup_sha256", setupHash)] do
    unless (← stringField request key) == actual do
      throw <| IO.userError s!"syntax request {key} mismatch"
  let setup : ModuleSetup ← match Json.parse setupSource >>= fromJson? with
    | .ok value => pure value
    | .error error => throw <| IO.userError error
  let moduleName ← moduleNameOfFileName original none
  unless setup.name == moduleName do throw <| IO.userError "syntax setup module mismatch"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let context := Parser.mkInputContext source original.toString
  let snap ← Lean.Language.Lean.process (setupImports setup) none { context with }
  let all := Lean.Language.toSnapshotTree snap
  let hasErrors ← all.runAndReport setup.options.toOptions (json := true)
  let hasSorry := all.getAll.any fun s => s.diagnostics.msgLog.toList.any fun m =>
    m.data.hasTag (· == `hasSorry)
  if hasErrors || hasSorry then throw <| IO.userError "syntax original input diagnostics failed"
  let some parsed := snap.result? | throw <| IO.userError "syntax header parse failed"
  let some processed := parsed.processedSnap.get.result?
    | throw <| IO.userError "syntax header imports/setup failed"
  let results ← inspect processed.firstCmdSnap.get context.fileMap request
  unless results.size == 1 do throw <| IO.userError "syntax owner result missing/ambiguous"
  let result := object [
    ("schema", toJson (1 : Nat)), ("original_sha256", toJson originalHash),
    ("input_source_sha256", toJson sourceHash), ("setup_sha256", toJson setupHash),
    ("request_sha256", toJson (← sha256 requestSource.toUTF8)),
    ("original_path", toJson original.toString), ("input_path", toJson input.toString),
    ("setup_path", toJson setupPath.toString), ("module", toJson setup.name.toString),
    ("owner", results[0]!)]
  output.putStr (result.pretty ++ "\n")
  output.flush

unsafe def control (original input setup request output : System.FilePath) : IO Unit := do
  let handle ← IO.FS.Handle.mk output .writeNew
  -- Keep fresh empty/partial output on failure; exit1 prevents payload credit.
  controlInto original input setup request handle

end SimpaUsingSyntaxControl

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [original, input, setup, request, output] =>
    try
      SimpaUsingSyntaxControl.control original input setup request output
      return 0
    catch error =>
      IO.eprintln error.toString
      return 1
  | _ =>
    IO.eprintln "usage: SimpaUsingSyntaxControl ORIGINAL INPUT SETUP REQUEST OUTPUT"
    return 2
