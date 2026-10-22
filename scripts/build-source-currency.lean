import Lake
import Lake.Load.Workspace
import Lean.Elab.ParseImportsFast

/-!
Lake's own module-input facts for `scripts/gate-cache.py`'s build-certificate
source-currency check.

The helper loads the Lake workspace with Lake's own loader (as `lake env`
does: the root configuration and every dependency at its manifest revision; it
never updates the manifest and never builds), then, starting from the modules
named in the request, walks the import closure with Lake's own module
resolution (`Workspace.findModules`) and the `needs` of every library it
reaches. For each module it prints, from the toolchain's own code, the values
Lake mixes into the module's input trace (`Module.recFetchPreSetup` in
`Lake/Build/Module.lean`):

* `src`: `computeTextFileHash` of the source Lake would read (`Module.leanFile`),
  the same value `recFetchInput` computes (`Hash.ofText` of `IO.FS.readFile`);
* `name`, `isModule`, `pkgId`, `leanArgs`: `pureHash` of `Module.name`, the
  header's `isModule`, `Package.id?` and `Module.leanArgs`;
* `options`: the `options` trace hash (`traceOptions` over `Module.leanOptions`);
* the header imports with their flags (`Lean.parseImports'`) and, for each,
  the workspace modules Lake resolves it to;
* the configuration the trace shape depends on (platform independence,
  precompilation, dynlibs, plugins, extern libs, extra-dep targets), so the
  caller can refuse a shape it does not replay;
* `olean`: optionally, `computeBinFileHash` of each output file named.

Each library reached is printed with its `needs`, `defaultFacets` and local
module collection order (`LeanLib.recCollectLocalModules`), which fix its
`extraDep` trace. The first line carries Lake's Lean trace hash (`pureHash` of
`Env.leanGithash`). Output is JSON lines.

Input: a request file of lines `root<TAB>MODULE` (closure roots) and
`bin<TAB>PATH` (files whose `computeBinFileHash` to print).
-/

open Lake System Lean

private def refuse (message : String) : IO α :=
  throw <| IO.userError message

private def hex (hash : Hash) : Json := toJson hash.toString

private def optionsHash (opts : LeanOptions) : Hash :=
  opts.values.foldl (init := Hash.nil) fun h n v =>
    h.mix (pureHash s!"-D{n}={v.asCliFlagValue}")

private def keyOf (mod : Lake.Module) : String :=
  s!"{mod.pkg.baseName}/{mod.name}"

structure ModuleFacts where
  header : ModuleHeader
  json : Json

private def moduleFacts (ws : Workspace) (mod : Lake.Module) : IO ModuleFacts := do
  let path := mod.leanFile
  let contents ← IO.FS.readFile path
  let header ← Lean.parseImports' contents path.toString
  let imports := header.imports.map fun imp =>
    Json.mkObj [
      ("module", toJson imp.module.toString),
      ("importAll", toJson imp.importAll),
      ("isExported", toJson imp.isExported),
      ("isMeta", toJson imp.isMeta),
      ("resolved", toJson ((ws.findModules imp.module).map keyOf))
    ]
  let json := Json.mkObj [
    ("kind", "module"),
    ("key", toJson (keyOf mod)),
    ("module", toJson mod.name.toString),
    ("package", toJson mod.pkg.baseName.toString),
    ("lib", toJson mod.lib.name.toString),
    ("path", toJson path.toString),
    ("trace", toJson mod.traceFile.toString),
    ("src", hex (← computeTextFileHash path)),
    ("name", hex (pureHash mod.name)),
    ("isModule", toJson header.isModule),
    ("isModuleHash", hex (pureHash header.isModule)),
    ("pkgId", hex (pureHash mod.pkg.id?)),
    ("leanArgs", hex (pureHash mod.leanArgs)),
    ("options", hex (optionsHash mod.leanOptions)),
    ("platformIndependent", toJson mod.platformIndependent),
    ("precompile", toJson (mod.shouldPrecompile || mod.shouldPrecompileImports)),
    ("dynlibs", toJson mod.dynlibs.size),
    ("plugins", toJson mod.plugins.size),
    ("externLibs", toJson mod.pkg.externLibs.size),
    ("imports", toJson imports)
  ]
  return {header, json}

/-- `LeanLib.recCollectLocalModules`: roots in order, each preceded by its
local (same-library) transitive imports, depth first. -/
private partial def collectLocal (ws : Workspace) (lib : LeanLib)
    (headers : Std.HashMap String ModuleHeader) : IO (Array String) := do
  let mut seen : Std.HashSet String := {}
  let mut out : Array String := #[]
  for root in (← lib.getModuleArray) do
    (seen, out) ← go root seen out
  return out
where
  go (mod : Lake.Module) (seen : Std.HashSet String) (out : Array String) :
      IO (Std.HashSet String × Array String) := do
    if seen.contains (keyOf mod) then return (seen, out)
    let mut seen := seen.insert (keyOf mod)
    let mut out := out
    let some header := headers[keyOf mod]?
      | refuse s!"library {lib.name}: no header for {mod.name}"
    for imp in header.imports do
      for dep in ws.findModules imp.module do
        if dep.lib.name == lib.name && dep.pkg.baseName == lib.pkg.baseName then
          (seen, out) ← go dep seen out
    return (seen, out.push (keyOf mod))

/-- The Lean library a `needs` key names (`@pkg/lib` or `pkg/lib`), if any. -/
private def needLib? (ws : Workspace) (key : PartialBuildKey) : Option LeanLib :=
  match ((toString key).dropWhile (· == '@')).toString.splitOn "/" with
  | [pkgName, libName] => do
    let pkg ← ws.findPackageByName? pkgName.toName
    pkg.findLeanLib? libName.toName
  | _ => none

def main (args : List String) : IO UInt32 := do
  let [request] := args
    | refuse "usage: build-source-currency.lean REQUEST_FILE"
  let mut roots : Array Name := #[]
  let mut binaries : Array String := #[]
  for row in (← IO.FS.lines (FilePath.mk request)) do
    if row.isEmpty then continue
    match row.splitOn "\t" with
    | ["root", module] => roots := roots.push module.toName
    | ["bin", path] => binaries := binaries.push path
    | _ => refuse s!"malformed request line: {row}"
  let (elan?, lean?, lake?) ← findInstall?
  let some lean := lean? | refuse "no Lean installation found"
  let some lake := lake? | refuse "no Lake installation found"
  let env ← match (← (Env.compute lake lean elan?).toBaseIO) with
    | .ok env => pure env
    | .error e => refuse s!"cannot compute the Lake environment: {e}"
  let some wsDir ← resolvePath? (← IO.currentDir)
    | refuse "no workspace directory"
  let loadConfig : LoadConfig := {lakeEnv := env, wsDir}
  let some ws ← (loadWorkspace loadConfig).toBaseIO {out := .stderr, outLv := .warning}
    | refuse "Lake could not load the workspace"
  let out ← IO.getStdout
  let githash := env.leanGithash
  out.putStrLn (Json.mkObj [("kind", "lean"), ("githash", toJson githash),
    ("hash", hex (pureHash githash))]).compress
  -- Import closure (Lake resolution) plus the modules of every library `needs`.
  let mut queue : Array Lake.Module := #[]
  for root in roots do
    match ws.findModules root with
    | #[mod] => queue := queue.push mod
    | found => refuse s!"root {root} resolves to {found.size} workspace modules"
  let mut seen : Std.HashSet String := {}
  let mut headers : Std.HashMap String ModuleHeader := {}
  let mut libs : Std.HashMap String LeanLib := {}
  while h : queue.size > 0 do
    let mod := queue.back
    queue := queue.pop
    if seen.contains (keyOf mod) then continue
    seen := seen.insert (keyOf mod)
    let facts ← moduleFacts ws mod
    out.putStrLn facts.json.compress
    headers := headers.insert (keyOf mod) facts.header
    for imp in facts.header.imports do
      for dep in ws.findModules imp.module do
        queue := queue.push dep
    let libKey := s!"{mod.pkg.baseName}/{mod.lib.name}"
    unless libs.contains libKey do
      libs := libs.insert libKey mod.lib
      for key in mod.lib.config.needs do
        if let some lib := needLib? ws key then
          for dep in (← lib.getModuleArray) do
            queue := queue.push dep
  for (key, lib) in libs.toList do
    let needs ← lib.config.needs.mapM fun need => do
      -- Only a `needs` naming a Lean library is replayable; any other target
      -- (a custom build step) is reported so the caller can refuse to
      -- replay modules whose `extraDep` trace depends on it.
      match needLib? ws need with
      | some needLib => return Json.mkObj [
          ("key", toJson (toString need)),
          ("supported", toJson true),
          ("defaultFacets", toJson (needLib.defaultFacets.map (·.toString))),
          ("modules", toJson (← collectLocal ws needLib headers))
        ]
      | none => return Json.mkObj [("key", toJson (toString need)), ("supported", toJson false)]
    out.putStrLn (Json.mkObj [
      ("kind", "lib"),
      ("key", toJson key),
      ("package", toJson lib.pkg.baseName.toString),
      ("lib", toJson lib.name.toString),
      ("isRoot", toJson lib.pkg.isRoot),
      ("libExtraDepTargets", toJson lib.extraDepTargets.size),
      ("pkgExtraDepTargets", toJson lib.pkg.extraDepTargets.size),
      ("needs", toJson needs)
    ]).compress
  for path in binaries do
    let hash ← computeBinFileHash (FilePath.mk path)
    out.putStrLn (Json.mkObj [("kind", "bin"), ("path", toJson path), ("hash", hex hash)]).compress
  return 0
