import Lean

/-! # The from-scratch axiom walker every Blanc axiom gate uses

This file is the single definition of how a Blanc gate learns which axioms a
declaration depends on. It is not a Lake module: `scripts/axiom_audit.py`
splices it, after the imports, into every audit file a gate elaborates
(`scripts/AxiomCheck.lean`, `scripts/ProxyPairUpgradeAxiomCheck.lean`, and the
probe files the Lido gates generate), so there is exactly one copy of the walk.

Why not Lean's own report. Since Lean v4.30.0 `#print axioms` on an imported
constant reads a per-module result that was precomputed when that module's
`.olean` was written. The precomputation shares one cache across the module
and breaks the inductive/constructor cycle with an empty sentinel entry that it
cannot tell apart from a finished result, so an inductive reached first through
its own constructor can be exported as axiom-free, and every declaration that
reaches the axiom only through that inductive inherits the under-report
(https://github.com/leanprover/lean4/issues/15226). Which names are hit depends
on hash iteration order, so an unrelated edit can turn such an audit green or
red. By the user's decision of 2026-09-24, no Blanc audit takes its verdict from
that report until the issue is fixed.

What this walk does instead. For each audited name it starts with an empty
visited set and follows, through `Environment.find?` alone, every constant used
by a declaration's type, by the value of a definition, theorem or opaque, and
every constructor of an inductive. It keeps no per-constant result between
names or within a name (a constant is visited at most once per name, and
visiting it only adds that constant's direct references), and it reads no
precomputed per-module table, so the inductive/constructor cycle cannot hide
anything: whichever end the walk enters first, it reaches the other and walks
it. The result is the set of `axiom` declarations reached, which includes
`sorryAx`, `Lean.ofReduceBool` and `native_decide`/`bv_decide` auxiliary axioms.

Each name is walked in its own task, so the audit runs on every core. Tasks
share only the immutable environment.

Output, one line per audited name, sorted by the axiom names' text:

    FULL-AXIOMS '<name>': [<axiom>, <axiom>, ...]

An empty list means no axiom at all. A name that does not resolve exactly (no
namespace resolution is applied) is an elaboration error, as is a referenced
constant that the environment does not contain.
-/

namespace BlancAxiomAudit

open Lean Elab Command

/-- The axioms reachable from `root`, and any referenced constants that the
environment does not contain. A fresh visited set per call; nothing cached. -/
def walk (env : Environment) (root : Name) : NameSet × NameSet := Id.run do
  -- Outside the module system this is the identity. Under it, imported
  -- private bodies are only visible with exporting off.
  let env := env.setExporting false
  let mut seen : Std.HashSet Name := ({} : Std.HashSet Name).insert root
  let mut stack : Array Name := #[root]
  let mut axioms : NameSet := {}
  let mut missing : NameSet := {}
  while h : 0 < stack.size do
    let c := stack.back
    stack := stack.pop
    match env.find? c with
    | none => missing := missing.insert c
    | some info =>
      if info matches .axiomInfo _ then
        axioms := axioms.insert c
      let mut refs := info.type.getUsedConstants
      match info with
      | .defnInfo v => refs := refs ++ v.value.getUsedConstants
      | .thmInfo v => refs := refs ++ v.value.getUsedConstants
      | .opaqueInfo v => refs := refs ++ v.value.getUsedConstants
      | .inductInfo v => refs := refs ++ v.ctors.toArray
      | _ => pure ()
      for n in refs do
        unless seen.contains n do
          seen := seen.insert n
          stack := stack.push n
  return (axioms, missing)

/-- `#full_axioms X` reports the from-scratch axiom set of the exact constant
`X` as one `FULL-AXIOMS` line. -/
elab "#full_axioms " id:ident : command => do
  let env ← getEnv
  let c := id.getId
  unless env.contains c do
    throwError "#full_axioms: unknown constant {c}"
  let report ← wrapAsyncAsSnapshot (cancelTk? := none) fun (_ : Unit) => do
    let (axioms, missing) := walk env c
    unless missing.isEmpty do
      throwError "#full_axioms: {c} reaches constants absent from the environment: \
        {missing.toList}"
    let names := (axioms.toList.map toString).toArray.qsort (· < ·)
    logInfo (MessageData.ofFormat (.text
      s!"FULL-AXIOMS '{c}': [{", ".intercalate names.toList}]"))
  logSnapshotTask { stx? := none, task := (← BaseIO.asTask (report ())), cancelTk? := none }

end BlancAxiomAudit
