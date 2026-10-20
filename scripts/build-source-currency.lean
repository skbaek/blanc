import Lake.Build.Trace
import Lean.Elab.ParseImportsFast

/-!
Lake's own module-input facts for `scripts/gate-cache.py`'s build-certificate
source-currency check.

For each requested module this prints, using the active toolchain's own code,
exactly the values Lake mixes into a module's input trace
(`Lake.Module.recFetchInput` and `Lake.Module.recComputeInputs` in this
toolchain's `Lake/Build/Module.lean`):

* `src`: `Lake.computeTextFileHash` of the current source, i.e.
  `Hash.ofText` (`String.crlfToLf`, then the Lean string hash) of
  `IO.FS.readFile`; Lake's `recFetchInput` computes `.ofText contents` from the
  same read;
* `name`: `pureHash` of the module `Name` (`Module.name` trace);
* `isModule`: `pureHash` of the header's `isModule` flag (`isModule` trace);
* the header imports, parsed with `Lean.parseImports'`, the parser Lake uses.

The trace structure and its replay live in `gate-cache.py`; this file only
supplies the hashes Python cannot reproduce from documented sources (Lean's
string and `Name` hashes are runtime externs whose C source is not shipped
with the toolchain). Input: a request file of `KIND<TAB>MODULE<TAB>PATH`
lines, where `KIND` is `src` (hash and header) or `hdr` (header only).
Output: one TSV line per request, `MODULE`, `SRC`, `NAME`, `ISMODULE`, the
`isModule` flag and the space-separated imported module names (or
`MODULE`, `!`, the error), preceded by a `#lean` line carrying the githash
Lake uses for its Lean trace (`LEAN_GITHASH` when set, as in
`Lake.Env.leanGithash`) and its `pureHash`.
-/

open Lake System Lean

private def refuse (message : String) : IO α :=
  throw <| IO.userError message

private def line (kind module path : String) : IO String := do
  let file := FilePath.mk path
  let contents ← IO.FS.readFile file
  let header ← Lean.parseImports' contents path
  let imports := header.imports.map (·.module.toString) |>.toList
  let isModuleHash := (pureHash header.isModule : Hash)
  let flag := if header.isModule then "true" else "false"
  let (src, name) ← match kind with
    | "src" =>
      let srcHash ← computeTextFileHash file
      pure (srcHash.toString, (pureHash module.toName : Hash).toString)
    | "hdr" => pure ("-", "-")
    | other => refuse s!"unknown request kind {other} for {module}"
  return s!"{module}\t{src}\t{name}\t{isModuleHash}\t{flag}\t{" ".intercalate imports}"

def main (args : List String) : IO UInt32 := do
  let [request] := args
    | refuse "usage: build-source-currency.lean REQUEST_FILE"
  let githash ← match (← IO.getEnv "LEAN_GITHASH") with
    | some value => if value.isEmpty then pure Lean.githash else pure value
    | none => pure Lean.githash
  let out ← IO.getStdout
  out.putStrLn s!"#lean\t{githash}\t{(pureHash githash : Hash)}"
  for row in (← IO.FS.lines (FilePath.mk request)) do
    if row.isEmpty then continue
    match row.splitOn "\t" with
    | [kind, module, path] =>
      -- A header that does not parse is reported per module, not fatal: only
      -- the caller knows whether that module is in a covered import closure.
      match (← (line kind module path).toBaseIO) with
      | .ok text => out.putStrLn text
      | .error error =>
        let message := (toString error).replace "\t" " " |>.replace "\n" " "
        out.putStrLn s!"{module}\t!\t{message}"
    | _ => refuse s!"malformed request line: {row}"
  return 0
