import Blanc
import Blanc.ProofRecipeTactic
import Blanc.ProofRecipesGenerated

-- LEAF-CENSUS-BODY
/-!
# Leaf census: which Blanc theorems are leaves

Driver for `scripts/leaf_audit.py` (the leaf search, `scripts/GATES.md` "Leaf audit"). It is run by
`lake env lean scripts/LeafCensus.lean` from the repository root. It is NOT a module of the `Blanc`
library, is not imported by `Blanc.lean`, and declares no theorem.

The header above (three `import` lines) is the only thing the self-test replaces: the fixture mode
of `leaf_audit.py` splices `import Lean`, a fixture, and everything from the marker line to the end
of this file, so production and fixtures are decided by byte-identical code.

Population: every theorem declared in a `Blanc.*` module of the environment (in production that is
every module reachable from `Blanc` plus `Blanc.ProofRecipeTactic` and `Blanc.ProofRecipesGenerated`,
the only certified modules outside `Blanc.lean`'s closure) and, for fixtures, every theorem declared
in the elaborated file itself. This driver's own definitions live in `LeafCensusDriver` and are
never population, users or dependencies.

A theorem is USED when

* some Blanc declaration's type or value mentions it (a "term user"), compiler and elaborator
  auxiliaries (`_proof_N`, `match_N`, `eq_def`, `eq_N`, `_private` prefixes, recursors, constructors
  of a structure...) being attributed to their parent declaration and a parentless auxiliary being
  looked through to its own users; or
* it carries an attribute that uses it without leaving a term trace: membership in any registered
  simp set (`@[simp]`, `attribute [simp]`, `@[simp ←]`, every other `register_simp_attr` set),
  `@[ext]`, or instance membership.

A use that leaves no trace in the environment at all (an `rfl`-proved lemma named in a `simp only
[..]`, `rw [..]`, `dsimp` or `simpa` call, or in a tactic macro) cannot be seen here: the Python
side reads those from the sources and removes the theorems they name from the leaf set.

A LEAF (of this census) is a used-by-nothing theorem: no term user and no attribute. Each leaf row
carries a fingerprint of its statement, the hash of the theorem's TYPE (never its proof), so that a
later review can tell a new or changed leaf from one already reviewed.

Input (environment, so the file is byte-identical in every mode): `BLANC_LEAF_OUT`, the JSON file
written.
-/

open Lean Elab Command Meta

namespace LeafCensusDriver

/-- Components naming compiler/elaborator auxiliaries under their parent declaration. -/
def auxComponent (s : String) : Bool :=
  s.startsWith "_" ||
  ["eq_def", "induct", "mutual_induct", "induct_unfolding", "fun_cases", "congr_simp",
    "splitter", "sizeOf_spec", "injEq", "inj", "noConfusion", "noConfusionType", "below",
    "brecOn", "binductionOn", "ibelow", "rec", "recOn", "casesOn", "ctorIdx",
    "eq_unfold", "ofNat_ctorIdx", "eq_iff_enumToBitVec_eq"].contains s ||
  (["match_", "proof_", "eq_", "sunfold_", "unfold_"].any fun p =>
    s.startsWith p && (s.drop p.length).toString.all Char.isDigit && s.length > p.length)

/-- Keep the components before the first auxiliary component. -/
def cutAux (n : Name) : Name × Bool :=
  let comps := n.components
  let rec go : List Name → Name → Name × Bool
    | [], acc => (acc, false)
    | c :: cs, acc =>
      match c with
      | .str _ s => if auxComponent s then (acc, true) else go cs (acc ++ c)
      | _ => go cs (acc ++ c)
  go comps .anonymous

/-- `some owner` for a constant attributable to a real declaration; `none` for a parentless
auxiliary (looked through to its own users). -/
def owner (env : Environment) (n : Name) : Option Name :=
  match env.find? n with
  | some (.ctorInfo v) => some v.induct
  | some (.recInfo v) => some v.getMajorInduct
  | _ =>
    if let some info := env.getProjectionFnInfo? n then
      some info.ctorName.getPrefix
    else
      let (pfx, rest) := match privatePrefix? n with
        | some p => (p, n.replacePrefix p .anonymous)
        | none => (.anonymous, n)
      let (kept, cut) := cutAux rest
      if !cut then some n
      else if kept.isAnonymous then none
      else
        let parent := pfx ++ kept
        if env.contains parent then some parent else none

/-- The module a constant came from; `_current` for a constant of the elaborated file. -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => `_current

/-- Population and dependency scope: a `Blanc` module, or the elaborated file itself minus this
driver's own namespace. -/
def inScope (env : Environment) (n : Name) : Bool :=
  let m := moduleOf env n
  if m == `_current then !(`LeafCensusDriver).isPrefixOf n
  else m == `Blanc || m.getRoot == `Blanc

def showName (n : Name) : String := n.toString (escape := false)

def constantsOf (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++ (match ci with
    | .thmInfo v => v.value.getUsedConstants
    | .defnInfo v => v.value.getUsedConstants
    | .opaqueInfo v => v.value.getUsedConstants
    | _ => #[])

/-- The statement fingerprint: `Expr.hash` of the theorem's type, 16 hex digits. It is structural
and independent of binder names, the proof, and the process. -/
def fingerprint (ci : ConstantInfo) : String :=
  let h := ci.type.hash.toNat
  let s := String.ofList (Nat.toDigits 16 h)
  "".pushn '0' (16 - s.length) ++ s

end LeafCensusDriver

open LeafCensusDriver in
run_cmd do
  let env ← getEnv
  let some outPath ← IO.getEnv "BLANC_LEAF_OUT"
    | throwError "BLANC_LEAF_OUT is not set"
  -- Population, and the reverse dependency edges of every in-scope constant.
  let mut pop : Array (Name × ConstantInfo) := #[]
  let mut excluded : Nat := 0
  let mut rev : Std.HashMap Name NameSet := {}
  let mut orphanOwners : NameSet := {}
  let allConstants : Array (Name × ConstantInfo) :=
    env.constants.fold (fun acc n ci => if inScope env n then acc.push (n, ci) else acc) #[]
  for (n, ci) in allConstants do
    let own := owner env n
    if let .thmInfo _ := ci then
      if own == some n then pop := pop.push (n, ci) else excluded := excluded + 1
    let userKey : Name := own.getD n
    if own.isNone then orphanOwners := orphanOwners.insert n
    for u in constantsOf ci do
      if u != n then
        rev := rev.insert u ((rev.getD u {}).insert userKey)
  -- The term users of `t`, looking through parentless auxiliaries.
  let hasTermUser (t : Name) : Bool := Id.run do
    let mut seen : NameSet := {}
    let mut stack : Array Name := #[t]
    while h : stack.size > 0 do
      let x := stack.back
      stack := stack.pop
      for u in (rev.getD x {}).toList do
        if orphanOwners.contains u then
          if !seen.contains u then
            seen := seen.insert u
            stack := stack.push u
        else if u != t then
          return true
    return false
  -- Attribute state: every registered simp set, `@[ext]`, instances.
  let simpMap ← simpExtensionMapRef.get
  let simpSets : Array (Name × SimpTheorems) := simpMap.toArray.map fun (k, ext) =>
    (k, ext.getState env)
  let instState := Meta.instanceExtension.getState env
  let extNames : NameSet := (Meta.Ext.extExtension.getState env).tree.values.foldl
    (fun s e => s.insert e.declName) {}
  let attrKinds (t : Name) : Array String := Id.run do
    let mut ks : Array String := #[]
    for (k, st) in simpSets do
      if st.isLemma (.decl t) || st.isLemma (.decl t (inv := true)) then
        ks := ks.push s!"simp-set:{showName k}"
    if extNames.contains t then ks := ks.push "ext"
    if instState.instanceNames.contains t then ks := ks.push "instance"
    return ks
  -- Classification.
  let mut leaves : Array Json := #[]
  let mut attrOnly : Array Json := #[]
  let mut popNames : Array String := #[]
  for (t, ci) in pop do
    let user := (privateToUserName? t).getD t
    popNames := popNames.push (showName user)
    let m := moduleOf env t
    let ks := attrKinds t
    unless hasTermUser t do
      let row := Json.mkObj [("name", toJson (showName user)), ("module", toJson (showName m)),
        ("private", toJson (isPrivateName t)), ("attributes", toJson ks),
        ("fp", toJson (fingerprint ci))]
      if ks.isEmpty then leaves := leaves.push row else attrOnly := attrOnly.push row
  IO.FS.writeFile outPath
    ((Json.mkObj [
      ("schema", toJson (2 : Nat)),
      ("population", toJson pop.size),
      ("excluded_auxiliary_theorems", toJson excluded),
      ("parentless_auxiliaries", toJson orphanOwners.size),
      ("simp_sets_registered", toJson (simpSets.map (showName ·.1))),
      ("population_names", toJson popNames),
      ("leaves", Json.arr leaves),
      ("attribute_only", Json.arr attrOnly)]).compress ++ "\n")
  logInfo m!"LEAF-CENSUS population {pop.size}; leaves {leaves.size}; attribute-only {attrOnly.size}"
