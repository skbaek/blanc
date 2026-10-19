import Lean
import Lean.Elab.Frontend

/-!
# Closure serializer for the ClaimCheck pins

Driver for `scripts/check-claim-hash.py`; run through `lake env lean --run`, never
imported by `Blanc`, so no module or audited-theorem count moves.

`scripts/ClaimCheck.lean` pins each claim as an `example`.  An `example` leaves
nothing in the environment, so this driver elaborates a copy of the file in
memory in which every pin line counted by `scripts/check-claims.sh` (a line whose
first word is `example`) has that keyword replaced by
`noncomputable def «claimPinHash_NNNN»`.  An `example` is elaborated as a `def`,
so the replacement changes no elaboration; it only keeps the pinned statement.
Any elaboration error fails the run.

From the pinned statements it then walks the definitional closure once, with a
visited set (the in-run memo), and writes one JSON line per reached constant: a
canonical serialization of what the constant contributes, plus the ordered
list of constants that serialization refers to.  The Python step turns these
records into a Merkle SHA-256 table with its own in-run memo.

What each constant contributes:
* definitions: kind, universe arity, type and value (content-addressed: the
  definition's own name is not part of it);
* theorems: universe arity and type (proof irrelevance);
* opaque constants (including `partial` definitions) and axioms: name and type;
* inductive types, constructors and recursors (generative constants): the whole
  mutual block (universe arity, parameters, indices, every type and every
  constructor with its full name and type), with references into the block
  written as block-local indices; each member record carries its own full name
  and is attributed to its block.  Two isomorphic but distinct types therefore
  never share a digest, and renaming a generative constant is a change;
* constants whose defining module is outside `Blanc` (Lean core, Std, Batteries,
  Mathlib, Jaune and every other dependency): the boundary; name, module and
  owning package only, the package being resolved from the `.olean` location
  and later bound by Python to the pinned toolchain or `lake-manifest.json` rev.
  A shallow serialization of the boundary constant's own content (references by
  name) is emitted beside it for diagnostics only.

Binder names, binder info and `mdata` are not serialized, universe parameters
are written by position, and every subterm is hash-consed on its canonical
line, so the bytes depend only on the normalized term.

Each pin is keyed by a label that does not depend on its position: `thm:N` for a
pin whose proof is the constant `N` applied (`:= @N`), `iff:N` / `eq:N` for an
unfolding pin whose statement is `N … ↔ …` / `N … = …`, `stmt:N` for a pin whose
statement's head is `N`, `uses:N` for the first Blanc constant the statement
uses, and `anon` otherwise.  Records are named by ordinal and carry that label;
the Python step turns labels into keys (a repeated label is disambiguated by the
pin's statement digest, not by file order).

Every run also builds a fixture of declaration pairs that differ in exactly one
feature (or, for the equality controls, only in what must be ignored), each side
added to its own copy of the environment under the same names, and emits both
sides' closure records; the Python step requires every differing pair to get
different digests and every equality pair equal ones.
-/

namespace BlancClaimPinHash

open Lean Lean.Elab

/-- The `scripts/check-claims.sh` pin regex `^[[:space:]]*example([[:space:]]|$)`. -/
def pinLine? (line : String) : Option (String × String) :=
  let isSpace (c : Char) := c == ' ' || c == '\t' || c == '\r' || c == '\x0b' || c == '\x0c'
  let indent := String.ofList (line.toList.takeWhile isSpace)
  let rest := String.ofList (line.toList.drop indent.length)
  if rest.startsWith "example" then
    let tail := String.ofList (rest.toList.drop "example".length)
    match tail.toList.head? with
    | none => some (indent, tail)
    | some c => if isSpace c then some (indent, tail) else none
  else none

def pad4 (n : Nat) : String :=
  let s := toString n
  "".pushn '0' (4 - s.length) ++ s

def pinName (n : Nat) : String := s!"claimPinHash_{pad4 n}"

/-- Rewrite the pin lines; returns the new source and the 1-based line of each pin. -/
def rewrite (source : String) : String × Array Nat := Id.run do
  let lines := source.splitOn "\n"
  let mut out : Array String := #[]
  let mut pins : Array Nat := #[]
  let mut lineNo := 0
  for line in lines do
    lineNo := lineNo + 1
    match pinLine? line with
    | some (indent, tail) =>
      pins := pins.push lineNo
      out := out.push s!"{indent}noncomputable def «{pinName pins.size}»{tail}"
    | none => out := out.push line
  return ("\n".intercalate out.toList, pins)

/-- Serialization state for one record. -/
structure RecState where
  lines : Array String := #[]
  lineIds : Std.HashMap String Nat := {}
  exprIds : Std.HashMap Expr Nat := {}
  refs : Array Name := #[]
  refIds : Std.HashMap Name Nat := {}
  exprHits : Nat := 0
  /-- Anything that cannot occur in a closed, well-formed constant; any entry fails the run. -/
  bad : Array String := #[]

abbrev RecM := StateT RecState (ReaderT (Std.HashMap Name Nat × Std.HashMap Name Nat) Id)

partial def lvl (ps : List Name) : Level → Except String String
  | .zero => pure "z"
  | .succ l => return s!"s({← lvl ps l})"
  | .max a b => return s!"m({← lvl ps a},{← lvl ps b})"
  | .imax a b => return s!"i({← lvl ps a},{← lvl ps b})"
  | .param n => match ps.idxOf? n with
    | some i => pure s!"p{i}"
    | none => throw s!"undeclared universe parameter {n}"
  | .mvar _ => throw "universe metavariable"

def markBad (why : String) : RecM String := do
  modify fun s => { s with bad := s.bad.push why }
  return "?"

def lvlM (ps : List Name) (l : Level) : RecM String :=
  match lvl ps l with
  | .ok s => pure s
  | .error e => markBad e

def lvls (ps : List Name) (ls : List Level) : RecM String := do
  let parts ← ls.mapM (lvlM ps)
  return "{" ++ ",".intercalate parts ++ "}"

def ref (n : Name) : RecM Nat := do
  let s ← get
  match s.refIds[n]? with
  | some i => return i
  | none =>
    let i := s.refs.size
    set { s with refs := s.refs.push n, refIds := s.refIds.insert n i }
    return i

def emit (line : String) : RecM Nat := do
  let s ← get
  match s.lineIds[line]? with
  | some i => return i
  | none =>
    let i := s.lines.size
    set { s with lines := s.lines.push line, lineIds := s.lineIds.insert line i }
    return i

/-- Canonical, injective serialization: strings are length-prefixed. -/
partial def ser (ps : List Name) (e : Expr) : RecM Nat := do
  if let some i := (← get).exprIds[e]? then
    modify fun s => { s with exprHits := s.exprHits + 1 }
    return i
  let i ← match e with
    | .bvar k => emit s!"B{k}"
    | .sort l => emit s!"S{← lvlM ps l}"
    | .const n ls => do
      let (selfIdx, _) ← read
      match selfIdx[n]? with
      | some j => emit s!"X{j}{← lvls ps ls}"
      | none => emit s!"C{← ref n}{← lvls ps ls}"
    | .app f a => do
      let fi ← ser ps f
      let ai ← ser ps a
      emit s!"A{fi},{ai}"
    | .lam _ t b _ => do
      let ti ← ser ps t
      let bi ← ser ps b
      emit s!"L{ti},{bi}"
    | .forallE _ t b _ => do
      let ti ← ser ps t
      let bi ← ser ps b
      emit s!"F{ti},{bi}"
    | .letE _ t v b _ => do
      let ti ← ser ps t
      let vi ← ser ps v
      let bi ← ser ps b
      emit s!"E{ti},{vi},{bi}"
    | .lit (.natVal n) => emit s!"N{n}"
    | .lit (.strVal s) => emit s!"T{s.utf8ByteSize}:{s}"
    | .mdata _ b => ser ps b
    | .proj n k b => do
      let bi ← ser ps b
      let (selfIdx, _) ← read
      match selfIdx[n]? with
      | some j => emit s!"Jx{j},{k},{bi}"
      | none => emit s!"J{← ref n},{k},{bi}"
    | .fvar _ => do emit (← markBad "free variable")
    | .mvar _ => do emit (← markBad "metavariable")
  modify fun s => { s with exprIds := s.exprIds.insert e i }
  return i

structure Record where
  name : String
  kind : String
  module : String
  package : String := ""
  ser : String := ""
  refs : Array String := #[]
  extra : List (String × Json) := []

def Record.toJson (r : Record) : Json :=
  Json.mkObj ([("n", Json.str r.name), ("k", Json.str r.kind), ("m", Json.str r.module),
    ("p", Json.str r.package), ("s", Json.str r.ser),
    ("r", Json.arr (r.refs.map Json.str))] ++ r.extra)


def runRec (selfIdx : Std.HashMap Name Nat) (body : RecM String) :
    Except String (String × Array Name × Nat) :=
  let ((head, st)) := (body.run {}).run (selfIdx, {}) |>.run
  if let some why := st.bad[0]? then throw s!"not a closed term ({why})" else
  let text := head ++ "\n" ++ "\n".intercalate st.lines.toList
  return (text, st.refs, st.exprHits)

def blockName (n : Name) : String := s!"block:{n}"

/-- A length-prefixed name, so a name never runs into the next field. -/
def lp (n : Name) : String := let s := toString n; s!"{s.utf8ByteSize}:{s}"

/-- Kind-specific serialization of a non-boundary constant. -/
def serializeConst (env : Environment) (ci : ConstantInfo) :
    Except String (String × String × Array Name × Nat) := do
  let ps := ci.levelParams
  let arity := ps.length
  match ci with
  | .defnInfo v =>
    if v.safety == .unsafe then throw s!"unsafe definition reached: {ci.name}"
    let (s, r, h) ← runRec {} do
      let t ← ser ps v.type
      let b ← ser ps v.value
      return s!"def u={arity} type={t} value={b}"
    return ("def", s, r, h)
  | .thmInfo v =>
    let (s, r, h) ← runRec {} do
      let t ← ser ps v.type
      return s!"theorem u={arity} type={t}"
    return ("theorem", s, r, h)
  | .opaqueInfo v =>
    let (s, r, h) ← runRec {} do
      let t ← ser ps v.type
      return s!"opaque name={lp ci.name} u={arity} type={t}"
    return ("opaque", s, r, h)
  | .axiomInfo v =>
    let (s, r, h) ← runRec {} do
      let t ← ser ps v.type
      return s!"axiom name={lp ci.name} u={arity} type={t}"
    return ("axiom", s, r, h)
  | .quotInfo _ => throw s!"quotient constant outside the core boundary: {ci.name}"
  | .inductInfo v =>
    let some j := v.all.idxOf? ci.name | throw s!"inductive not in its block: {ci.name}"
    return ("inductive", s!"member type={j} name={lp ci.name}", #[], 0)
  | .ctorInfo v =>
    let some ind := env.find? v.induct | throw s!"missing inductive {v.induct}"
    let .inductInfo iv := ind | throw s!"constructor of non-inductive {ci.name}"
    let some j := iv.all.idxOf? v.induct | throw s!"inductive not in its block: {v.induct}"
    return ("ctor", s!"member type={j} ctor={v.cidx} name={lp ci.name}", #[], 0)
  | .recInfo v =>
    let major := ci.name.getPrefix
    let some j := v.all.idxOf? major | throw s!"recursor outside its block: {ci.name}"
    return ("rec", s!"member type={j} name={lp ci.name}", #[], 0)

/-- The whole mutual block, self references as block-local indices, every member named. -/
def serializeBlock (env : Environment) (all : List Name) :
    Except String (String × Array Name × Nat) := do
  let mut selfIdx : Std.HashMap Name Nat := {}
  let mut vals : Array InductiveVal := #[]
  for n in all do
    let some (.inductInfo v) := env.find? n | throw s!"block member is not inductive: {n}"
    selfIdx := selfIdx.insert n selfIdx.size
    vals := vals.push v
  for v in vals do
    for c in v.ctors do
      selfIdx := selfIdx.insert c selfIdx.size
  let ps := vals[0]!.levelParams
  let mut ctorInfos : Array (Array ConstructorVal) := #[]
  for v in vals do
    let mut cs := #[]
    for c in v.ctors do
      let some (.ctorInfo cv) := env.find? c | throw s!"missing constructor {c}"
      cs := cs.push cv
    ctorInfos := ctorInfos.push cs
  let selfIdx' := selfIdx
  let vals' := vals
  let ctorInfos' := ctorInfos
  runRec selfIdx' do
    let mut parts : Array String := #[]
    for i in [0:vals'.size] do
      let v := vals'[i]!
      let t ← ser ps v.type
      parts := parts.push
        s!"type {i} name={lp v.name} params={v.numParams} indices={v.numIndices} nested={v.numNested} unsafe={v.isUnsafe} type={t} ctors={v.ctors.length}"
      for cv in ctorInfos'[i]! do
        let ct ← ser ps cv.type
        parts := parts.push
          s!"ctor {cv.cidx} name={lp cv.name} params={cv.numParams} fields={cv.numFields} type={ct}"
    return s!"block u={ps.length} types={vals'.size} " ++ " ".intercalate parts.toList

/-- Diagnostic-only shallow serialization of a boundary constant: its own content,
references by name.  Never part of any digest the verdict reads. -/
def shallowBoundary (env : Environment) (ci : ConstantInfo) : Option (String × Array Name) :=
  let r : Except String (String × String × Array Name × Nat) := match ci with
    | .inductInfo v => do
      let (s, r, h) ← serializeBlock env v.all
      return ("block", s!"member name={lp ci.name}\n{s}", r, h)
    | .quotInfo _ => do
      let (s, r, h) ← runRec {} do
        let t ← ser ci.levelParams ci.type
        return s!"quot name={lp ci.name} type={t}"
      return ("quot", s, r, h)
    | .defnInfo v => if v.safety == .unsafe then throw "unsafe" else serializeConst env ci
    | _ => serializeConst env ci
  match r with
  | .ok (k, s, refs, _) => some (k ++ "\n" ++ s, refs)
  | .error _ => none

/-- Package of a boundary module, from where its `.olean` lives. -/
def packageOf (sysroot : System.FilePath) (mod : Name) : IO String := do
  let path := (← findOLean mod).toString
  if path.startsWith sysroot.toString then return "@toolchain"
  let parts := path.splitOn "/.lake/packages/"
  if parts.length < 2 then
    throw <| IO.userError s!"HASH boundary module outside every pinned package: {mod} at {path}"
  return (parts.getLast!.splitOn "/").head!

/-- Peak resident set, best effort: `/proc` exists on Linux only; elsewhere 0. -/
def peakRssKiB : IO Nat := do
  try
    let status ← IO.FS.readFile "/proc/self/status"
    for line in status.splitOn "\n" do
      if line.startsWith "VmHWM:" then
        let digits := line.toList.filter Char.isDigit
        return (String.ofList digits).toNat!
    return 0
  catch _ => return 0

structure Stats where
  constants : Nat := 0
  blanc : Nat := 0
  local_ : Nat := 0
  boundary : Nat := 0
  blocks : Nat := 0
  exprHits : Nat := 0
  refEdges : Nat := 0
  visitHits : Nat := 0
  serBytes : Nat := 0

/-- Which constants are fully hashed. -/
inductive Scope where
  /-- the claim run: modules under `Blanc`, and the file being elaborated -/
  | blanc
  /-- the fixture: only the constants the fixture added (no defining module) -/
  | fixture

/-- Walk the closure of `roots`, emitting one record per reached constant. -/
def walk (env : Environment) (sysroot : System.FilePath) (scope : Scope)
    (roots : Array Name) (moduleCache : IO.Ref (Std.HashMap Name String))
    (emitRec : Record → IO Unit) (stats : IO.Ref Stats) : IO Unit := do
  let mut visited : Std.HashSet Name := {}
  let mut blocksDone : Std.HashSet Name := {}
  let mut queue : Array Name := #[]
  for x in roots do
    if visited.contains x then stats.modify fun s => { s with visitHits := s.visitHits + 1 }
    else
      visited := visited.insert x
      queue := queue.push x
  let mut qi := 0
  while qi < queue.size do
    let n := queue[qi]!
    qi := qi + 1
    let some ci := env.find? n | throw <| IO.userError s!"HASH unknown constant {n}"
    stats.modify fun s => { s with constants := s.constants + 1 }
    let mod? := (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!
    let internal := match scope, mod? with
      | _, none => true
      | .blanc, some m => m.getRoot == `Blanc
      | .fixture, some _ => false
    let modStr := match mod? with
      | none => "scripts.ClaimCheck"
      | some m => m.toString
    if !internal then
      let some m := mod? | throw <| IO.userError "HASH unreachable"
      let pkg ← match (← moduleCache.get)[m]? with
        | some p => pure p
        | none => do
          let p ← packageOf sysroot m
          moduleCache.modify (·.insert m p)
          pure p
      stats.modify fun s => { s with boundary := s.boundary + 1 }
      let diag : List (String × Json) := match shallowBoundary env ci with
        | some (s, r) => [("d", Json.str s), ("dr", Json.arr (r.map fun x => Json.str x.toString))]
        | none => []
      emitRec { name := n.toString, kind := "boundary", module := modStr, package := pkg,
                extra := diag }
      continue
    if mod?.isNone then stats.modify fun s => { s with local_ := s.local_ + 1 }
    else stats.modify fun s => { s with blanc := s.blanc + 1 }
    let blockAll? : Option (List Name) := match ci with
      | .inductInfo v => some v.all
      | .ctorInfo v => match env.find? v.induct with
        | some (.inductInfo iv) => some iv.all
        | _ => none
      | .recInfo v => some v.all
      | _ => none
    let mut refs : Array Name := #[]
    let mut blockRef : Option String := none
    if let some all := blockAll? then
      let head := all.head!
      blockRef := some (blockName head)
      if !blocksDone.contains head then
        blocksDone := blocksDone.insert head
        match serializeBlock env all with
        | .error e => throw <| IO.userError s!"HASH {e}"
        | .ok (s, r, h) =>
          stats.modify fun st => { st with blocks := st.blocks + 1, exprHits := st.exprHits + h, refEdges := st.refEdges + r.size, serBytes := st.serBytes + s.utf8ByteSize }
          emitRec { name := blockName head, kind := "block", module := modStr, ser := s,
                    refs := r.map toString }
          refs := r
    match serializeConst env ci with
    | .error e => throw <| IO.userError s!"HASH {e}"
    | .ok (kind, s, r, h) =>
      stats.modify fun st => { st with exprHits := st.exprHits + h, refEdges := st.refEdges + r.size, serBytes := st.serBytes + s.utf8ByteSize }
      let recRefs := match blockRef with
        | some b => #[b]
        | none => r.map toString
      emitRec { name := n.toString, kind, module := modStr, ser := s, refs := recRefs }
      refs := refs ++ r
    for x in refs do
      if visited.contains x then stats.modify fun s => { s with visitHits := s.visitHits + 1 }
      else
        visited := visited.insert x
        queue := queue.push x

/-! ## Pin labels -/

/-- Proof plumbing that says nothing about which claim a pin pins. -/
def plumbing : List Name :=
  [`Iff.rfl, `rfl, `Eq.refl, `Eq.mpr, `Eq.mp, `id, `Iff.intro, `propext, `cast,
   `Eq.symm, `Eq.trans, `Iff.of_eq, `of_eq_true, `HEq.refl, `Eq.ndrec, `Eq.rec,
   `Iff.mpr, `Iff.mp, `trivial, `True.intro, `And.intro, `Exists.intro, `id_eq,
   `Iff.refl, `Eq.mpr_prop, `Eq.mpr_not, `letFun]

partial def stripLam : Expr → Expr
  | .lam _ _ b _ => stripLam b
  | .mdata _ e => stripLam e
  | e => e

partial def stripForall : Expr → Expr
  | .forallE _ _ b _ => stripForall b
  | .mdata _ e => stripForall e
  | e => e

def headConst? (e : Expr) : Option Name :=
  match e.consumeMData.getAppFn.consumeMData with
  | .const c _ => some c
  | _ => none

def isBlanc (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some idx => env.header.moduleNames[idx.toNat]!.getRoot == `Blanc
  | none => false

/-- The position-independent label of one pin (before de-duplication): the Blanc
constant the proof applies, else the Blanc head of an unfolding equation's left
side, else the Blanc head of the statement, else the first Blanc constant the
statement uses. -/
def pinLabel (env : Environment) (ci : ConstantInfo) : String := Id.run do
  let blanc? : Option Name → Option Name := fun c? => c?.filter (isBlanc env)
  if let .defnInfo d := ci then
    if let some c := blanc? (headConst? (stripLam d.value)) then
      if !plumbing.contains c then return s!"thm:{c}"
  let t := stripForall ci.type
  match headConst? t with
  | some `Iff =>
    if let some c := blanc? (headConst? t.appFn!.appArg!) then return s!"iff:{c}"
  | some `Eq =>
    if let some c := blanc? (headConst? t.appFn!.appArg!) then return s!"eq:{c}"
  | _ => pure ()
  if let some c := blanc? (headConst? t) then return s!"stmt:{c}"
  if let some c := ci.type.getUsedConstants.find? (isBlanc env) then return s!"uses:{c}"
  return "anon"

/-! ## The serializer fixture -/

def fx (s : String) : Name := (`ClaimPinHashFixture).str s

def nat : Expr := .const ``Nat []
def str : Expr := .const ``String []

def sortDef (name : Name) (lps : List Name) (l : Level) : Declaration :=
  .defnDecl { name, levelParams := lps, type := .sort l.succ, value := .sort l,
              hints := .abbrev, safety := .safe, all := [name] }

def natDef (name : Name) (type value : Expr) : Declaration :=
  .defnDecl { name, levelParams := [], type, value, hints := .abbrev, safety := .safe,
              all := [name] }

/-- A structure-like inductive `name : Type` with one constructor of the given fields. -/
def structDecl (name ctor : Name) (fields : List Expr) : Declaration :=
  let ty := fields.foldr (fun f acc => .forallE `x f acc .default) (.const name [])
  .inductDecl [] 0 [{ name, type := .sort 1, ctors := [{ name := ctor, type := ty }] }] false

def enumDecl (name : Name) (ctors : List Name) : Declaration :=
  let ty : InductiveType :=
    { name, type := .sort 1, ctors := ctors.map fun c => { name := c, type := .const name [] } }
  .inductDecl [] 0 [ty] false

/-- `I : Type → Type 1` with constructor `∀ (α : Type), α → I α`, `n` parameters. -/
def paramDecl (nparams : Nat) : Declaration :=
  let i := fx "I"
  let ctorTy : Expr := .forallE `α (.sort 1)
    (.forallE `a (.bvar 0) (.app (.const i []) (.bvar 1)) .default) .default
  let ty : InductiveType :=
    { name := i, type := .forallE `α (.sort 1) (.sort 2) .default,
      ctors := [{ name := i.str "mk", type := ctorTy }] }
  .inductDecl [] nparams [ty] false

def projDef (s : Name) (k : Nat) : Declaration :=
  natDef (fx "pj") (.forallE `s (.const s []) nat .default)
    (.lam `s (.const s []) (.proj s k (.bvar 0)) .default)

/-- `name : n = n := rfl` at the literal `n`. -/
def thmEq (name : Name) (n : Expr) : Declaration :=
  .thmDecl { name, levelParams := [], type := mkApp3 (.const ``Eq [1]) nat n n,
             value := mkApp2 (.const ``Eq.refl [1]) nat n, all := [name] }

def thmTrue (name : Name) (proof : Expr) : Declaration :=
  .thmDecl { name, levelParams := [], type := .const ``True [], value := proof, all := [name] }

def structDeclU (name ctor : Name) (fields : List Expr) (isUnsafe : Bool) : Declaration :=
  match structDecl name ctor fields with
  | .inductDecl lps n tys _ => .inductDecl lps n tys isUnsafe
  | d => d

def opaqueNat (name : Name) : Declaration :=
  .opaqueDecl { name, levelParams := [], type := nat, value := .lit (.natVal 1),
                isUnsafe := false, all := [name] }

structure Pair where
  label : String
  expect : String  -- "differ" or "equal"
  /-- Kernel-check the declarations; off only for pairs whose point is a term
  shape no well-typed pair can isolate (the serializer is under test, not Lean). -/
  check : Bool := true
  a : List Declaration
  rootA : Name
  b : List Declaration
  rootB : Name

def fixturePairs : List Pair :=
  let u : Level := .param `u
  let v : Level := .param `v
  let s := fx "S"
  let s' := fx "S'"
  let sFields := [nat, nat]
  let one : Expr := .lit (.natVal 1)
  let two : Expr := .lit (.natVal 2)
  [ { label := "level succ", expect := "differ",
      a := [sortDef (fx "lv") [`u] u], rootA := fx "lv",
      b := [sortDef (fx "lv") [`u] u.succ], rootB := fx "lv" },
    { label := "level max vs imax", expect := "differ",
      a := [sortDef (fx "lv") [`u, `v] (.max u v)], rootA := fx "lv",
      b := [sortDef (fx "lv") [`u, `v] (.imax u v)], rootB := fx "lv" },
    { label := "level param position", expect := "differ",
      a := [sortDef (fx "lv") [`u, `v] (.max u v)], rootA := fx "lv",
      b := [sortDef (fx "lv") [`u, `v] (.max v u)], rootB := fx "lv" },
    { label := "universe parameter order", expect := "differ",
      a := [sortDef (fx "lv") [`u, `v] (.max u v)], rootA := fx "lv",
      b := [sortDef (fx "lv") [`v, `u] (.max u v)], rootB := fx "lv" },
    { label := "proj index", expect := "differ",
      a := [structDecl s (s.str "mk") sFields, projDef s 0], rootA := fx "pj",
      b := [structDecl s (s.str "mk") sFields, projDef s 1], rootB := fx "pj" },
    { label := "proj struct name (isomorphic structures)", expect := "differ",
      a := [structDecl s (s.str "mk") sFields, projDef s 0], rootA := fx "pj",
      b := [structDecl s' (s'.str "mk") sFields, projDef s' 0], rootB := fx "pj" },
    { label := "let value", expect := "differ",
      a := [natDef (fx "le") nat (.letE `x nat one (.bvar 0) false)], rootA := fx "le",
      b := [natDef (fx "le") nat (.letE `x nat two (.bvar 0) false)], rootB := fx "le" },
    { label := "literal Nat vs String", expect := "differ",
      a := [natDef (fx "li") nat (.lit (.natVal 3))], rootA := fx "li",
      b := [natDef (fx "li") str (.lit (.strVal "3"))], rootB := fx "li" },
    { label := "constructor order", expect := "differ",
      a := [enumDecl (fx "T") [fx "T" |>.str "a", fx "T" |>.str "b"]], rootA := fx "T",
      b := [enumDecl (fx "T") [fx "T" |>.str "b", fx "T" |>.str "a"]], rootB := fx "T" },
    { label := "field order", expect := "differ",
      a := [structDecl (fx "T") (fx "T" |>.str "mk") [nat, str]], rootA := fx "T",
      b := [structDecl (fx "T") (fx "T" |>.str "mk") [str, nat]], rootB := fx "T" },
    { label := "numParams vs numIndices", expect := "differ",
      a := [paramDecl 1], rootA := fx "I", b := [paramDecl 0], rootB := fx "I" },
    { label := "definition value", expect := "differ",
      a := [natDef (fx "d") nat one], rootA := fx "d",
      b := [natDef (fx "d") nat two], rootB := fx "d" },
    { label := "definition type", expect := "differ",
      a := [natDef (fx "d") nat (.const ``Nat.zero [])], rootA := fx "d",
      b := [natDef (fx "d") (mkApp2 (.const ``id [2]) (.sort 1) nat) (.const ``Nat.zero [])],
      rootB := fx "d" },
    { label := "opaque name", expect := "differ",
      a := [opaqueNat (fx "o1")], rootA := fx "o1",
      b := [opaqueNat (fx "o2")], rootB := fx "o2" },
    { label := "inductive name (isomorphic types)", expect := "differ",
      a := [structDecl s (s.str "mk") sFields], rootA := s,
      b := [structDecl s' (s'.str "mk") sFields], rootB := s' },
    { label := "constructor name", expect := "differ",
      a := [structDecl s (s.str "mk") sFields], rootA := s.str "mk",
      b := [structDecl s (s.str "mk2") sFields], rootB := s.str "mk2" },
    { label := "use of isomorphic types in a definition", expect := "differ",
      a := [structDecl s (s.str "mk") sFields, structDecl s' (s'.str "mk") sFields,
            natDef (fx "use") (.forallE `x (.const s []) nat .default)
              (.lam `x (.const s []) one .default)], rootA := fx "use",
      b := [structDecl s (s.str "mk") sFields, structDecl s' (s'.str "mk") sFields,
            natDef (fx "use") (.forallE `x (.const s' []) nat .default)
              (.lam `x (.const s' []) one .default)], rootB := fx "use" },
    { label := "universe arguments of a constant", expect := "differ", check := false,
      a := [natDef (fx "ua") nat (mkApp2 (.const ``id [1]) nat one)], rootA := fx "ua",
      b := [natDef (fx "ua") nat (mkApp2 (.const ``id [2]) nat one)], rootB := fx "ua" },
    { label := "application argument order", expect := "differ",
      a := [natDef (fx "ap") nat (mkApp2 (.const ``Nat.add []) one two)], rootA := fx "ap",
      b := [natDef (fx "ap") nat (mkApp2 (.const ``Nat.add []) two one)], rootB := fx "ap" },
    { label := "lambda vs forall", expect := "differ", check := false,
      a := [natDef (fx "lf") (.sort 1) (.lam `x nat nat .default)], rootA := fx "lf",
      b := [natDef (fx "lf") (.sort 1) (.forallE `x nat nat .default)], rootB := fx "lf" },
    { label := "theorem statement", expect := "differ",
      a := [thmEq (fx "t") one], rootA := fx "t", b := [thmEq (fx "t") two], rootB := fx "t" },
    { label := "inductive unsafe flag", expect := "differ",
      a := [structDeclU s (s.str "mk") sFields false], rootA := s,
      b := [structDeclU s (s.str "mk") sFields true], rootB := s },
    { label := "theorem proof (must be equal)", expect := "equal",
      a := [thmTrue (fx "tp") (.const ``True.intro [])], rootA := fx "tp",
      b := [thmTrue (fx "tp") (.const ``trivial [])], rootB := fx "tp" },
    { label := "binder name (must be equal)", expect := "equal",
      a := [natDef (fx "f") (.forallE `x nat nat .default) (.lam `x nat (.bvar 0) .default)],
      rootA := fx "f",
      b := [natDef (fx "f") (.forallE `y nat nat .default) (.lam `y nat (.bvar 0) .default)],
      rootB := fx "f" },
    { label := "binder info (must be equal)", expect := "equal",
      a := [natDef (fx "f") (.forallE `x nat nat .default) (.lam `x nat (.bvar 0) .default)],
      rootA := fx "f",
      b := [natDef (fx "f") (.forallE `x nat nat .implicit) (.lam `x nat (.bvar 0) .implicit)],
      rootB := fx "f" },
    { label := "metadata (must be equal)", expect := "equal",
      a := [natDef (fx "d") nat one], rootA := fx "d",
      b := [natDef (fx "d") nat (.mdata (KVMap.empty.insert `note (.ofBool true)) one)],
      rootB := fx "d" },
    { label := "definition name (content-addressed, must be equal)", expect := "equal",
      a := [natDef (fx "d1") nat one], rootA := fx "d1",
      b := [natDef (fx "d2") nat one], rootB := fx "d2" } ]

def addAll (env : Environment) (decls : List Declaration) (check : Bool) :
    Except String Environment := do
  let mut e := env
  for d in decls do
    match e.addDeclCore 0 512 d none (doCheck := check) with
    | .ok e' => e := e'
    | .error _ => throw s!"fixture declaration rejected by the kernel: {decl_names d}"
  return e
where decl_names (d : Declaration) : String := toString d.getTopLevelNames

/-- Serialize both sides of every fixture pair into `out`, one JSON line per pair. -/
def runFixture (base : Environment) (sysroot : System.FilePath)
    (moduleCache : IO.Ref (Std.HashMap Name String)) (out : IO.FS.Handle) : IO Nat := do
  let mut count := 0
  for p in fixturePairs do
    let mut sides : Array Json := #[]
    for (decls, root) in [(p.a, p.rootA), (p.b, p.rootB)] do
      let env ← match addAll base decls p.check with
        | .ok e => pure e
        | .error e => throw <| IO.userError s!"HASH fixture {p.label}: {e}"
      let recs ← IO.mkRef (#[] : Array Json)
      let stats ← IO.mkRef ({} : Stats)
      walk env sysroot .fixture #[root] moduleCache (fun r => recs.modify (·.push r.toJson)) stats
      sides := sides.push (Json.mkObj [("root", Json.str root.toString),
        ("records", Json.arr (← recs.get))])
    out.putStrLn (Json.mkObj [("label", Json.str p.label), ("expect", Json.str p.expect),
      ("a", sides[0]!), ("b", sides[1]!)]).compress
    count := count + 1
  return count

/-- Exact single-feature checks on the serializer itself, independent of digests. -/
def serializerChecks : List (String × Expr × Expr × Bool) :=
  [ ("literal Nat vs String", .lit (.natVal 3), .lit (.strVal "3"), false),
    ("string length prefix", .lit (.strVal "ab"), .lit (.strVal "a"), false),
    ("binder name ignored", .lam `x nat (.bvar 0) .default, .lam `y nat (.bvar 0) .default, true),
    ("binder info ignored", .lam `x nat (.bvar 0) .default, .lam `x nat (.bvar 0) .instImplicit, true),
    ("mdata ignored", .lit (.natVal 1), .mdata (KVMap.empty.insert `k (.ofBool true)) (.lit (.natVal 1)), true),
    ("let value", .letE `x nat (.lit (.natVal 1)) (.bvar 0) false,
      .letE `x nat (.lit (.natVal 2)) (.bvar 0) false, false),
    ("proj index", .proj ``Prod 0 (.bvar 0), .proj ``Prod 1 (.bvar 0), false),
    ("bound variable index", .lam `x nat (.lam `y nat (.bvar 0) .default) .default,
      .lam `x nat (.lam `y nat (.bvar 1) .default) .default, false) ]

def checkSerializer : Except String Nat := do
  let mut n := 0
  for (label, x, y, same) in serializerChecks do
    let sx ← runRec {} (do return s!"{← ser [] x}")
    let sy ← runRec {} (do return s!"{← ser [] y}")
    let eq := sx.1 == sy.1 && sx.2.1 == sy.2.1
    if eq != same then
      throw s!"serializer check failed: {label} ({if same then "differs" else "collides"})"
    n := n + 1
  return n

/-! ## The run -/

unsafe def generate (claimCheck output fixtureOut : System.FilePath) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let source ← IO.FS.readFile claimCheck
  let (rewritten, pinLines) := rewrite source
  let serializerOk ← match checkSerializer with
    | .ok n => pure n
    | .error e => IO.eprintln s!"HASH {e}"; return 1
  let sysroot ← findSysroot
  initSearchPath sysroot
  enableInitializersExecution
  -- The two warnings the `example` → `def` rewrite itself would add are silenced;
  -- neither option changes elaboration.
  let opts : Options := ({} : Options)
    |>.setBool `linter.defProp false |>.setBool `warn.classDefReducibility false
  let some env ← Lean.Elab.runFrontend rewritten opts claimCheck.toString `ClaimPinHashInput
    | IO.eprintln "HASH ClaimCheck copy failed to elaborate"; return 1
  let tElab ← IO.monoMsNow
  -- locate the pins
  let mut pinDecl : Std.HashMap String Name := {}
  for (n, _) in env.constants.map₂.toList do
    if let .str _ s := n then
      if s.startsWith "claimPinHash_" then
        if pinDecl.contains s then
          IO.eprintln s!"HASH duplicate pin declaration {s}"; return 1
        pinDecl := pinDecl.insert s n
  if pinDecl.size != pinLines.size then
    IO.eprintln s!"HASH pin count mismatch: {pinLines.size} pin lines, {pinDecl.size} pin declarations"
    return 1
  let out ← IO.FS.Handle.mk output .write
  let stats ← IO.mkRef ({} : Stats)
  let moduleCache ← IO.mkRef ({} : Std.HashMap Name String)
  let emitRec (r : Record) : IO Unit := out.putStrLn r.toJson.compress
  -- pin roots, labelled independently of position
  let mut roots : Array Name := #[]
  for i in [0:pinLines.size] do
    let some n := pinDecl[pinName (i + 1)]? |
      IO.eprintln s!"HASH missing pin declaration {pinName (i+1)}"; return 1
    let some ci := env.find? n | IO.eprintln s!"HASH missing {n}"; return 1
    let base := pinLabel env ci
    let ps := ci.levelParams
    let pinSer := runRec {} do
      let t ← ser ps ci.type
      return s!"pin u={ps.length} type={t}"
    let (s, r, h) ← match pinSer with
      | .ok v => pure v
      | .error e => IO.eprintln s!"HASH pin {i+1}: {e}"; return 1
    stats.modify fun st => { st with exprHits := st.exprHits + h, refEdges := st.refEdges + r.size, serBytes := st.serBytes + s.utf8ByteSize }
    let pinRec : Record := {
      name := s!"pin:{pad4 (i + 1)}", kind := "pin", module := "scripts.ClaimCheck",
      ser := s, refs := r.map toString,
      extra := [("label", Json.str base), ("line", toJson pinLines[i]!), ("ordinal", toJson (i + 1)),
                ("ns", Json.str n.getPrefix.toString)] }
    emitRec pinRec
    roots := roots ++ r
  try
    walk env sysroot .blanc roots moduleCache emitRec stats
  catch e => IO.eprintln e.toString; return 1
  let tEnd ← IO.monoMsNow
  -- the serializer fixture, on every run
  let fixtureHandle ← IO.FS.Handle.mk fixtureOut .write
  let fixturePairsN ← try runFixture env sysroot moduleCache fixtureHandle
    catch e => IO.eprintln e.toString; return 1
  fixtureHandle.flush
  let rss ← peakRssKiB
  let st ← stats.get
  out.putStrLn (Json.mkObj [("k", Json.str "stats"), ("pins", toJson pinLines.size),
    ("constants", toJson st.constants), ("blanc", toJson st.blanc),
    ("local", toJson st.local_), ("boundary", toJson st.boundary),
    ("blocks", toJson st.blocks), ("expr_memo_hits", toJson st.exprHits),
    ("ref_edges", toJson st.refEdges), ("visit_memo_hits", toJson st.visitHits),
    ("serialized_bytes", toJson st.serBytes),
    ("elab_ms", toJson (tElab - t0)), ("walk_ms", toJson (tEnd - tElab)),
    ("fixture_pairs", toJson fixturePairsN), ("serializer_checks", toJson serializerOk),
    ("lean_version", Json.str Lean.versionString),
    ("peak_rss_kib", toJson rss)]).compress
  out.flush
  return 0

end BlancClaimPinHash

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [claimCheck, output, fixtureOut] =>
    try BlancClaimPinHash.generate claimCheck output fixtureOut
    catch e => IO.eprintln s!"HASH {e}"; return 1
  | _ =>
    IO.eprintln "usage: lake env lean --run scripts/ClaimPinHash.lean CLAIMCHECK OUTPUT_JSONL FIXTURE_JSONL"
    return 2
