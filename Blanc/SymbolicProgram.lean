import Blanc.CommonCore

/-!
# Symbolic programs and checked linking

This module provides symbolic auxiliary-call linking over `Blanc.CommonCore`.
Instead of manually coordinating numeric indices in a program table, callers
author programs using `SymbolicFunc Label` with qualified labels.

Resolution checks:
1. Definition domain validity: no root reuse in the auxiliary table, and no
   duplicate auxiliary labels (including unused duplicates).
2. Reference completeness: every called label must exist (as root or auxiliary).
   Missing-label errors record the enclosing body label and structural branch path.
3. Structural erasure: resolving maps root to index 0, and auxiliary entries to
   `i + 1` according to their list order.

Linking:
`checkLink` combines successful resolution with `Prog.compiles resolved = true`,
yielding a `LinkCertificate` that witnesses the exact compiled bytes,
compiler success, and structural length.
-/

namespace Blanc

open Jaune

/-- Symbolic functions mirror `Func` with label-based call targets. -/
inductive SymbolicFunc (Label : Type) : Type
  | branch : SymbolicFunc Label → SymbolicFunc Label → SymbolicFunc Label
  | last : Linst → SymbolicFunc Label
  | next : Ninst → SymbolicFunc Label → SymbolicFunc Label
  | call : Label → SymbolicFunc Label

/-- A symbolic program with a distinguished root label and ordered auxiliary bodies. -/
structure SymbolicProg (Label : Type) : Type where
  root : Label
  main : SymbolicFunc Label
  aux : List (Label × SymbolicFunc Label)

/-- Structural branch path step: left (condition zero) or right (condition nonzero). -/
inductive BranchArm : Type
  | left
  | right
  deriving DecidableEq, Repr

/-- Errors reported during symbolic resolution. -/
inductive ResolveError (Label : Type) : Type
  | rootReuse (label : Label) (auxPosition : Nat)
  | duplicateAux (label : Label) (firstPosition secondPosition : Nat)
  | missingLabel (owner : Label) (path : List BranchArm) (target : Label)
  deriving DecidableEq, Repr

/-- Check that the auxiliary table does not reuse the root label. -/
def checkRootReuse [DecidableEq Label] (root : Label) (aux : List (Label × SymbolicFunc Label)) :
    Except (ResolveError Label) Unit :=
  let rec loop (idx : Nat) : List (Label × SymbolicFunc Label) → Except (ResolveError Label) Unit
    | [] => .ok ()
    | (l, _) :: rest =>
      if l = root then
        .error (.rootReuse l idx)
      else
        loop (idx + 1) rest
  loop 0 aux

/-- Check that no auxiliary label is defined more than once, even if unused. -/
def checkDuplicateAux [DecidableEq Label] (aux : List (Label × SymbolicFunc Label)) :
    Except (ResolveError Label) Unit :=
  let rec loopOuter (i : Nat) : List (Label × SymbolicFunc Label) → Except (ResolveError Label) Unit
    | [] => .ok ()
    | (l1, _) :: rest =>
      let rec loopInner (j : Nat) : List (Label × SymbolicFunc Label) → Except (ResolveError Label) Unit
        | [] => .ok ()
        | (l2, _) :: restInner =>
          if l1 = l2 then
            .error (.duplicateAux l1 i j)
          else
            loopInner (j + 1) restInner
      match loopInner (i + 1) rest with
      | .error e => .error e
      | .ok () => loopOuter (i + 1) rest
  loopOuter 0 aux

/-- Phase 1 validation: reject root reuse and duplicate auxiliary labels. -/
def SymbolicProg.validateDefinitions [DecidableEq Label] (p : SymbolicProg Label) :
    Except (ResolveError Label) Unit :=
  match checkRootReuse p.root p.aux with
  | .error e => .error e
  | .ok () => checkDuplicateAux p.aux

/-- Helper for auxiliary label search. -/
def findAux [DecidableEq Label] (target : Label) : Nat → List (Label × SymbolicFunc Label) → Option Nat
  | _, [] => none
  | idx, (l, _) :: rest =>
    if l = target then
      some (idx + 1)
    else
      findAux target (idx + 1) rest

/-- Look up a label's positional target index in a symbolic program.
Root maps to 0; auxiliary entries map to `1 + index`. -/
def SymbolicProg.findLabel? [DecidableEq Label] (p : SymbolicProg Label) (target : Label) : Option Nat :=
  if target = p.root then
    some 0
  else
    findAux target 0 p.aux

/-- Total structural erasure from `SymbolicFunc Label` to `Func` under an explicit label mapping. -/
def SymbolicFunc.erase (map : Label → Nat) : SymbolicFunc Label → Func
  | .last o => .last o
  | .next i f => .next i (f.erase map)
  | .branch f g => .branch (f.erase map) (g.erase map)
  | .call target => .call (map target)

/-- Total structural erasure of a complete `SymbolicProg` to `Prog`. -/
def SymbolicProg.erase (map : Label → Nat) (p : SymbolicProg Label) : Prog :=
  ⟨p.main.erase map, p.aux.map (fun (_, body) => body.erase map)⟩

/-- Collect all call target labels referenced in a symbolic function. -/
def SymbolicFunc.calls : SymbolicFunc Label → List Label
  | .last _ => []
  | .next _ f => f.calls
  | .branch f g => f.calls ++ g.calls
  | .call target => [target]

/-- Resolve a single symbolic function body, tracking the owner body label and branch path. -/
def resolveFunc [DecidableEq Label] (p : SymbolicProg Label) (owner : Label) (path : List BranchArm) :
    SymbolicFunc Label → Except (ResolveError Label) Func
  | .last o => .ok (.last o)
  | .next i f =>
    match resolveFunc p owner path f with
    | .ok f' => .ok (.next i f')
    | .error e => .error e
  | .branch f g =>
    match resolveFunc p owner (path ++ [.left]) f with
    | .error e => .error e
    | .ok f' =>
      match resolveFunc p owner (path ++ [.right]) g with
      | .error e => .error e
      | .ok g' => .ok (.branch f' g')
  | .call target =>
    match p.findLabel? target with
    | some idx => .ok (.call idx)
    | none => .error (.missingLabel owner path target)

/-- Resolve an ordered list of auxiliary bodies. -/
def resolveAux [DecidableEq Label] (p : SymbolicProg Label) :
    List (Label × SymbolicFunc Label) → Except (ResolveError Label) (List Func)
  | [] => .ok []
  | (lbl, body) :: rest =>
    match resolveFunc p lbl [] body with
    | .error e => .error e
    | .ok body' =>
      match resolveAux p rest with
      | .error e => .error e
      | .ok rest' => .ok (body' :: rest')

/-- Full program resolution: validates definitions then resolves main and all auxiliary bodies. -/
def resolve [DecidableEq Label] (p : SymbolicProg Label) : Except (ResolveError Label) Prog :=
  match p.validateDefinitions with
  | .error e => .error e
  | .ok () =>
    match resolveFunc p p.root [] p.main with
    | .error e => .error e
    | .ok main' =>
      match resolveAux p p.aux with
      | .error e => .error e
      | .ok aux' => .ok ⟨main', aux'⟩

/-! ## Call-free lifting -/

/-- Decides whether an existing positional `Func` contains any numeric calls. -/
def Func.isCallFree : Func → Bool
  | .last _ => true
  | .next _ f => f.isCallFree
  | .branch f g => f.isCallFree && g.isCallFree
  | .call _ => false

/-- Translate a positional `Func` into a `SymbolicFunc Label` if it is call-free. -/
def Func.toSymbolic? (Label : Type) : Func → Option (SymbolicFunc Label)
  | .last o => some (.last o)
  | .next i f =>
    match f.toSymbolic? Label with
    | some f' => some (.next i f')
    | none => none
  | .branch f g =>
    match f.toSymbolic? Label with
    | none => none
    | some f' =>
      match g.toSymbolic? Label with
      | some g' => some (.branch f' g')
      | none => none
  | .call _ => none

/-- Structural erasure of a call-free lifted function recovers the original `Func`. -/
theorem Func.erase_toSymbolic (f : Func) (sym : SymbolicFunc Label)
    (h : f.toSymbolic? Label = some sym) (map : Label → Nat) :
    sym.erase map = f := by
  induction f generalizing sym with
  | last o =>
    simp [Func.toSymbolic?] at h
    subst h
    rfl
  | next i f ih =>
    simp only [Func.toSymbolic?] at h
    cases hf : f.toSymbolic? Label with
    | none =>
      rw [hf] at h
      contradiction
    | some f' =>
      rw [hf] at h
      injection h with h_eq
      subst h_eq
      simp [SymbolicFunc.erase, ih f' hf]
  | branch f g ihf ihg =>
    simp only [Func.toSymbolic?] at h
    cases hf : f.toSymbolic? Label with
    | none =>
      rw [hf] at h
      contradiction
    | some f' =>
      rw [hf] at h
      cases hg : g.toSymbolic? Label with
      | none =>
        rw [hg] at h
        contradiction
      | some g' =>
        rw [hg] at h
        injection h with h_eq
        subst h_eq
        simp [SymbolicFunc.erase, ihf f' hf, ihg g' hg]
  | call n =>
    simp [Func.toSymbolic?] at h

/-- `Func.toSymbolic?` succeeds if and only if `Func.isCallFree` is true. -/
theorem Func.isSome_toSymbolic (Label : Type) (f : Func) :
    (f.toSymbolic? Label).isSome = f.isCallFree := by
  induction f with
  | last o => rfl
  | next i f ih =>
    simp only [Func.toSymbolic?, Func.isCallFree]
    cases hf : f.toSymbolic? Label with
    | none =>
      rw [hf] at ih
      simp only [Option.isSome_none] at ih
      simp [ih]
    | some s =>
      rw [hf] at ih
      simp only [Option.isSome_some] at ih
      simp [ih]
  | branch f g ihf ihg =>
    simp only [Func.toSymbolic?, Func.isCallFree]
    cases hf : f.toSymbolic? Label with
    | none =>
      rw [hf] at ihf
      simp only [Option.isSome_none] at ihf
      simp [ihf]
    | some sf =>
      rw [hf] at ihf
      simp only [Option.isSome_some] at ihf
      cases hg : g.toSymbolic? Label with
      | none =>
        rw [hg] at ihg
        simp only [Option.isSome_none] at ihg
        simp [ihf, ihg]
      | some sg =>
        rw [hg] at ihg
        simp only [Option.isSome_some] at ihg
        rw [← ihf, ← ihg]
        rfl
  | call n => rfl

/-! ## Structural erasure theorems -/

/-- Successful label lookups imply `resolveFunc` matches total erasure. -/
theorem resolveFunc_eq_erase [DecidableEq Label]
    (p : SymbolicProg Label) (owner : Label) (path : List BranchArm)
    (map : Label → Nat) (f : SymbolicFunc Label)
    (h_lookup : ∀ target ∈ f.calls, p.findLabel? target = some (map target)) :
    resolveFunc p owner path f = .ok (f.erase map) := by
  induction f generalizing path with
  | last o => rfl
  | next i f ih =>
    simp only [SymbolicFunc.calls] at h_lookup
    have ih_app := ih path h_lookup
    simp [resolveFunc, ih_app, SymbolicFunc.erase]
  | branch f g ihf ihg =>
    simp only [SymbolicFunc.calls, List.mem_append] at h_lookup
    have hf : ∀ target ∈ f.calls, p.findLabel? target = some (map target) :=
      fun target ht => h_lookup target (Or.inl ht)
    have hg : ∀ target ∈ g.calls, p.findLabel? target = some (map target) :=
      fun target ht => h_lookup target (Or.inr ht)
    have ihf_app := ihf (path ++ [.left]) hf
    have ihg_app := ihg (path ++ [.right]) hg
    simp [resolveFunc, ihf_app, ihg_app, SymbolicFunc.erase]
  | call target =>
    simp only [SymbolicFunc.calls, List.mem_singleton] at h_lookup
    have ht : p.findLabel? target = some (map target) := h_lookup target rfl
    simp [resolveFunc, ht, SymbolicFunc.erase]

/-- Successful resolution of auxiliary bodies equals their pointwise erasure. -/
theorem resolveAux_eq_erase [DecidableEq Label]
    (p : SymbolicProg Label) (map : Label → Nat)
    (aux : List (Label × SymbolicFunc Label))
    (h_lookup : ∀ lbl body, (lbl, body) ∈ aux → ∀ target ∈ body.calls, p.findLabel? target = some (map target)) :
    resolveAux p aux = .ok (aux.map fun (_, body) => body.erase map) := by
  induction aux with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨lbl, body⟩
    have h_body : ∀ target ∈ body.calls, p.findLabel? target = some (map target) :=
      fun t ht => h_lookup lbl body (List.Mem.head _) t ht
    have h_tail : ∀ l b, (l, b) ∈ tail → ∀ target ∈ b.calls, p.findLabel? target = some (map target) :=
      fun l b hb => h_lookup l b (List.Mem.tail _ hb)
    have h_res := resolveFunc_eq_erase p lbl [] map body h_body
    have ih_app := ih h_tail
    simp [resolveAux, h_res, ih_app]

/-- Full program resolution equals whole-program erasure when all calls resolve. -/
theorem resolve_eq_erase [DecidableEq Label]
    (p : SymbolicProg Label) (map : Label → Nat)
    (h_valid : p.validateDefinitions = .ok ())
    (h_main : ∀ target ∈ p.main.calls, p.findLabel? target = some (map target))
    (h_aux : ∀ lbl body, (lbl, body) ∈ p.aux → ∀ target ∈ body.calls, p.findLabel? target = some (map target)) :
    resolve p = .ok (p.erase map) := by
  have h_res_main := resolveFunc_eq_erase p p.root [] map p.main h_main
  have h_res_aux := resolveAux_eq_erase p map p.aux h_aux
  simp [resolve, h_valid, h_res_main, h_res_aux, SymbolicProg.erase]

/-- Conversely, any successfully resolved function equals structural erasure with respect to any agreeing map. -/
theorem erase_eq_of_resolveFunc [DecidableEq Label]
    (p : SymbolicProg Label) (owner : Label) (path : List BranchArm)
    (map : Label → Nat) (f : SymbolicFunc Label) (f' : Func)
    (h_res : resolveFunc p owner path f = .ok f')
    (h_agree : ∀ target n, p.findLabel? target = some n → map target = n) :
    f' = f.erase map := by
  induction f generalizing path f' with
  | last o =>
    simp [resolveFunc] at h_res
    subst h_res
    rfl
  | next i f ih =>
    simp [resolveFunc] at h_res
    cases hf : resolveFunc p owner path f with
    | error e =>
      rw [hf] at h_res
      contradiction
    | ok f_sub =>
      rw [hf] at h_res
      injection h_res with h_eq
      subst h_eq
      simp [SymbolicFunc.erase, ih path f_sub hf]
  | branch f g ihf ihg =>
    simp [resolveFunc] at h_res
    cases hf : resolveFunc p owner (path ++ [.left]) f with
    | error e =>
      rw [hf] at h_res
      contradiction
    | ok f_sub =>
      rw [hf] at h_res
      cases hg : resolveFunc p owner (path ++ [.right]) g with
      | error e =>
        rw [hg] at h_res
        contradiction
      | ok g_sub =>
        rw [hg] at h_res
        injection h_res with h_eq
        subst h_eq
        simp [SymbolicFunc.erase, ihf (path ++ [.left]) f_sub hf, ihg (path ++ [.right]) g_sub hg]
  | call target =>
    simp [resolveFunc] at h_res
    cases h_opt : p.findLabel? target with
    | none =>
      rw [h_opt] at h_res
      contradiction
    | some idx =>
      rw [h_opt] at h_res
      injection h_res with h_eq
      subst h_eq
      have h_idx := h_agree target idx h_opt
      subst h_idx
      rfl

/-- Successfully resolved auxiliary bodies equal structural pointwise erasure. -/
theorem aux_erase_eq_of_resolveAux [DecidableEq Label]
    (p : SymbolicProg Label) (map : Label → Nat)
    (aux : List (Label × SymbolicFunc Label)) (fs : List Func)
    (h_res : resolveAux p aux = .ok fs)
    (h_agree : ∀ target n, p.findLabel? target = some n → map target = n) :
    fs = aux.map fun (_, body) => body.erase map := by
  induction aux generalizing fs with
  | nil =>
    simp [resolveAux] at h_res
    subst h_res
    rfl
  | cons head tail ih =>
    rcases head with ⟨lbl, body⟩
    simp [resolveAux] at h_res
    cases hb : resolveFunc p lbl [] body with
    | error e =>
      rw [hb] at h_res
      contradiction
    | ok body' =>
      rw [hb] at h_res
      cases ht : resolveAux p tail with
      | error e =>
        rw [ht] at h_res
        contradiction
      | ok tail' =>
        rw [ht] at h_res
        injection h_res with h_eq
        subst h_eq
        have hb_eq := erase_eq_of_resolveFunc p lbl [] map body body' hb h_agree
        have ht_eq := ih tail' ht
        simp [List.map_cons, hb_eq, ht_eq]

/-- Successfully resolved complete programs equal structural erasure. -/
theorem erase_eq_of_resolve [DecidableEq Label]
    (p : SymbolicProg Label) (map : Label → Nat) (prog : Prog)
    (h_res : resolve p = .ok prog)
    (h_agree : ∀ target n, p.findLabel? target = some n → map target = n) :
    prog = p.erase map := by
  simp [resolve] at h_res
  cases hv : p.validateDefinitions with
  | error e =>
    rw [hv] at h_res
    contradiction
  | ok u =>
    rw [hv] at h_res
    cases hm : resolveFunc p p.root [] p.main with
    | error e =>
      rw [hm] at h_res
      contradiction
    | ok main' =>
      rw [hm] at h_res
      cases ha : resolveAux p p.aux with
      | error e =>
        rw [ha] at h_res
        contradiction
      | ok aux' =>
        rw [ha] at h_res
        injection h_res with h_eq
        subst h_eq
        have hm_eq := erase_eq_of_resolveFunc p p.root [] map p.main main' hm h_agree
        have ha_eq := aux_erase_eq_of_resolveAux p map p.aux aux' ha h_agree
        simp [SymbolicProg.erase, hm_eq, ha_eq]

/-! ## Unique label lookup properties -/

theorem findLabel?_root [DecidableEq Label] (p : SymbolicProg Label) :
    p.findLabel? p.root = some 0 := by
  simp [SymbolicProg.findLabel?]

theorem findAux_ne_zero [DecidableEq Label] (target : Label) (idx : Nat)
    (aux : List (Label × SymbolicFunc Label)) :
    findAux target idx aux ≠ some 0 := by
  induction aux generalizing idx with
  | nil => simp [findAux]
  | cons head tail ih =>
    rcases head with ⟨l, body⟩
    simp [findAux]
    split
    · intro h
      injection h with h
      omega
    · exact ih (idx + 1)

theorem findLabel?_eq_zero_iff [DecidableEq Label] (p : SymbolicProg Label) (lbl : Label) :
    p.findLabel? lbl = some 0 ↔ lbl = p.root := by
  simp only [SymbolicProg.findLabel?]
  split <;> rename_i h
  · simp [h]
  · have h_ne := findAux_ne_zero lbl 0 p.aux
    constructor
    · intro h_zero
      exact False.elim (h_ne h_zero)
    · intro h_root
      exact False.elim (h h_root)

/-! ## Checked linking and certificates -/

/-- Errors reported during checked linking. -/
inductive LinkError (Label : Type) : Type
  | resolve (e : ResolveError Label)
  | compileFailed (prog : Prog)

/-- Certificate of successful label resolution and compilation. -/
structure LinkCertificate {Label : Type} [DecidableEq Label] (sp : SymbolicProg Label) where
  resolved : Prog
  resolve_eq : resolve sp = .ok resolved
  compiles : Prog.compiles resolved = true

namespace LinkCertificate

variable {Label : Type} [DecidableEq Label] {sp : SymbolicProg Label}

/-- The exact compiled byte payload from the compiler. -/
def bytes (cert : LinkCertificate sp) : Bytes :=
  (Prog.compile cert.resolved).getD []

/-- Compiler success reflects to an exact `some bytes` output. -/
theorem compile_eq (cert : LinkCertificate sp) :
    Prog.compile cert.resolved = some cert.bytes :=
  Prog.compile_eq_some_getD_of_compiles cert.resolved cert.compiles

/-- Exact compiler success from `Prog.isSome_compile`. -/
theorem isSome_compile (cert : LinkCertificate sp) :
    (Prog.compile cert.resolved).isSome = true := by
  rw [Prog.isSome_compile, cert.compiles]

/-- Compiled length equation derived directly from `Prog.length_compile`. -/
theorem length_compile (cert : LinkCertificate sp) :
    cert.bytes.length = ((cert.resolved.main :: cert.resolved.aux).map fun f => 1 + compsize f).sum :=
  Prog.length_compile cert.compile_eq

/-- Table lookup binding: root resolves to entry 0. -/
theorem table_get_root (cert : LinkCertificate sp) :
    (Prod.snd <$> (table 0 (cert.resolved.main :: cert.resolved.aux))[0]? : Option Func) =
      some cert.resolved.main := by
  have h := @Prog.get?_table 0 0 (cert.resolved.main :: cert.resolved.aux)
  exact h

/-- Table lookup binding: auxiliary index i resolves to entry i + 1. -/
theorem table_get_aux (cert : LinkCertificate sp) (i : Nat) :
    (Prod.snd <$> (table 0 (cert.resolved.main :: cert.resolved.aux))[i + 1]? : Option Func) =
      cert.resolved.aux[i]? := by
  have h := @Prog.get?_table 0 (i + 1) (cert.resolved.main :: cert.resolved.aux)
  exact h

end LinkCertificate

/-- Perform checked linking: resolve labels and verify `Prog.compiles`. -/
def checkLink [DecidableEq Label] (sp : SymbolicProg Label) :
    Except (LinkError Label) (LinkCertificate sp) :=
  match h_res : resolve sp with
  | .error err => .error (.resolve err)
  | .ok resolved =>
    if h_comp : Prog.compiles resolved = true then
      .ok {
        resolved := resolved
        resolve_eq := h_res
        compiles := h_comp
      }
    else
      .error (.compileFailed resolved)

/-! ## Verification controls -/

namespace Control

/-- Synthetic labels for exercising resolution controls. -/
inductive TestLabel : Type
  | root
  | loop
  | ping
  | pong
  | dead
  | missing
  deriving DecidableEq, Repr

-- Positive control: nested branches with valid calls
def nestedBranchProg : SymbolicProg TestLabel where
  root := .root
  main := .branch (.branch (.call .loop) (.last .stop)) (.branch (.last .stop) (.call .loop))
  aux := [(.loop, .last .stop)]

theorem nestedBranch_checkLink : (checkLink nestedBranchProg).isOk = true := by
  rfl

-- Positive control: self-recursion
def selfRecursionProg : SymbolicProg TestLabel where
  root := .root
  main := .call .loop
  aux := [(.loop, .branch (.last .stop) (.call .loop))]

theorem selfRecursion_checkLink : (checkLink selfRecursionProg).isOk = true := by
  rfl

-- Positive control: mutual recursion
def mutualRecursionProg : SymbolicProg TestLabel where
  root := .root
  main := .call .ping
  aux := [
    (.ping, .branch (.last .stop) (.call .pong)),
    (.pong, .branch (.last .stop) (.call .ping))
  ]

theorem mutualRecursion_checkLink : (checkLink mutualRecursionProg).isOk = true := by
  rfl

-- Negative control: missing label in main
def missingMainProg : SymbolicProg TestLabel where
  root := .root
  main := .call .missing
  aux := []

theorem missingLabel_main_rejects :
    resolve missingMainProg = .error (.missingLabel .root [] .missing) := by
  rfl

-- Negative control: missing label in nested branch (left arm)
def missingBranchLeftProg : SymbolicProg TestLabel where
  root := .root
  main := .branch (.call .missing) (.last .stop)
  aux := []

theorem missingLabel_branchLeft_rejects :
    resolve missingBranchLeftProg = .error (.missingLabel .root [.left] .missing) := by
  rfl

-- Negative control: missing label in nested branch (right arm)
def missingBranchRightProg : SymbolicProg TestLabel where
  root := .root
  main := .branch (.last .stop) (.call .missing)
  aux := []

theorem missingLabel_branchRight_rejects :
    resolve missingBranchRightProg = .error (.missingLabel .root [.right] .missing) := by
  rfl

-- Negative control: missing label in auxiliary body
def missingAuxProg : SymbolicProg TestLabel where
  root := .root
  main := .call .loop
  aux := [(.loop, .call .missing)]

theorem missingLabel_aux_rejects :
    resolve missingAuxProg = .error (.missingLabel .loop [] .missing) := by
  rfl

-- Negative control: root label reused in auxiliary table
def rootReuseProg : SymbolicProg TestLabel where
  root := .root
  main := .last .stop
  aux := [(.root, .last .stop)]

theorem rootReuse_rejects :
    resolve rootReuseProg = .error (.rootReuse .root 0) := by
  rfl

-- Negative control: duplicate auxiliary label (even when unused)
def duplicateAuxProg : SymbolicProg TestLabel where
  root := .root
  main := .last .stop
  aux := [(.dead, .last .stop), (.dead, .last .stop)]

theorem duplicateAux_rejects :
    resolve duplicateAuxProg = .error (.duplicateAux .dead 0 1) := by
  rfl

end Control

end Blanc
