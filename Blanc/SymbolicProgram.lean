import Blanc.CommonCore
import Blanc.LinearDispatch

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

/-- Lift a call-free `Func` into `SymbolicFunc Label`. Fails at compile time if `f` contains calls. -/
def Func.liftCallFree (Label : Type) (f : Func) (h : (f.toSymbolic? Label).isSome = true := by rfl) :
    SymbolicFunc Label :=
  (f.toSymbolic? Label).get h

@[simp]
theorem Func.erase_liftCallFree (f : Func) (h : (f.toSymbolic? Label).isSome = true) (map : Label → Nat) :
    (f.liftCallFree Label h).erase map = f := by
  have h_eq : f.toSymbolic? Label = some (f.liftCallFree Label h) := Option.get_mem h
  exact Func.erase_toSymbolic f (f.liftCallFree Label h) h_eq map


/-! ## Generic call naming

`Func.toSymbolic?` above covers only the call-free case.  A runtime that is
being migrated off hand-maintained numeric coordinates needs the general case:
lift an existing positional `Func` by *naming* each numeric call target.  One
definition and one erasure lemma serve every label type, so a consumer does not
author its own structural recursion. -/

/-- The numeric call targets occurring in a positional `Func`, in source order. -/
def Func.callTargets : Func → List Nat
  | .last _ => []
  | .next _ f => f.callTargets
  | .branch f g => f.callTargets ++ g.callTargets
  | .call n => [n]

/-- Lift a positional `Func` into `SymbolicFunc Label` by naming every call
target through `g`.  Unlike `Func.toSymbolic?` this is total. -/
def Func.mapCalls (g : Nat → Label) : Func → SymbolicFunc Label
  | .last o => .last o
  | .next i f => .next i (f.mapCalls g)
  | .branch f h => .branch (f.mapCalls g) (h.mapCalls g)
  | .call n => .call (g n)

/-- Renumber every call target of a positional `Func`.  The general
target-renumbering owner: a local-to-global table rebase is `mapTargets (delta + ·)`. -/
def Func.mapTargets (t : Nat → Nat) : Func → Func
  | .last o => .last o
  | .next i f => .next i (f.mapTargets t)
  | .branch f g => .branch (f.mapTargets t) (g.mapTargets t)
  | .call n => .call (t n)

@[simp] theorem Func.mapTargets_id (f : Func) : f.mapTargets id = f := by
  induction f with
  | last o => rfl
  | next i f ih => simp only [Func.mapTargets, ih]
  | branch f g ihf ihg => simp only [Func.mapTargets, ihf, ihg]
  | call n => rfl

/-- Erasing a named lift is the renumbering that `map ∘ g` performs, provided the
two agree on the targets that actually occur.  The membership restriction is the
whole content: a naming function that decodes only a bounded window of slots
still behaves, as long as no body calls outside that window. -/
theorem Func.erase_mapCalls_eq_mapTargets (g : Nat → Label) (map : Label → Nat)
    (t : Nat → Nat) (f : Func) (hmap : ∀ n ∈ f.callTargets, map (g n) = t n) :
    (f.mapCalls g).erase map = f.mapTargets t := by
  induction f with
  | last o => rfl
  | next i f ih =>
      simp only [Func.callTargets] at hmap
      simp only [Func.mapCalls, Func.mapTargets, SymbolicFunc.erase, ih hmap]
  | branch f g' ihf ihg =>
      simp only [Func.callTargets, List.mem_append] at hmap
      have hf : ∀ n ∈ f.callTargets, map (g n) = t n := fun n hn => hmap n (Or.inl hn)
      have hg : ∀ n ∈ g'.callTargets, map (g n) = t n := fun n hn => hmap n (Or.inr hn)
      simp only [Func.mapCalls, Func.mapTargets, SymbolicFunc.erase, ihf hf, ihg hg]
  | call n =>
      simp only [Func.callTargets, List.mem_singleton] at hmap
      simp only [Func.mapCalls, Func.mapTargets, SymbolicFunc.erase, hmap n rfl]

/-- Erasure inverts `Func.mapCalls` as soon as `map` inverts `g` on the targets
that actually occur. -/
theorem Func.erase_mapCalls (g : Nat → Label) (map : Label → Nat) (f : Func)
    (hmap : ∀ n ∈ f.callTargets, map (g n) = n) :
    (f.mapCalls g).erase map = f := by
  have h := Func.erase_mapCalls_eq_mapTargets g map id f hmap
  simpa using h

/-- Totally inverted naming needs no membership side condition. -/
theorem Func.erase_mapCalls_of_inverse (g : Nat → Label) (map : Label → Nat)
    (hmap : ∀ n, map (g n) = n) (f : Func) :
    (f.mapCalls g).erase map = f :=
  Func.erase_mapCalls g map f (fun n _ => hmap n)

/-- List form: one agreement hypothesis over a whole auxiliary table.  A table
authored symbolically and a table authored numerically erase to each other under
a single renumbering. -/
theorem Func.erase_map_mapCalls (g : Nat → Label) (map : Label → Nat) (t : Nat → Nat)
    (bodies : List Func)
    (h : ∀ f ∈ bodies, ∀ n ∈ f.callTargets, map (g n) = t n) :
    bodies.map (fun f => (f.mapCalls g).erase map) = bodies.map (Func.mapTargets t) := by
  induction bodies with
  | nil => rfl
  | cons b bs ih =>
      have hb : ∀ n ∈ b.callTargets, map (g n) = t n := h b (List.mem_cons_self ..)
      have hbs : ∀ f ∈ bs, ∀ n ∈ f.callTargets, map (g n) = t n :=
        fun f hf => h f (List.mem_cons_of_mem _ hf)
      simp only [List.map_cons, Func.erase_mapCalls_eq_mapTargets g map t b hb, ih hbs]
/-- Prepend a `Line` of instructions to a `SymbolicFunc`. -/
def SymbolicFunc.prepend (l : Line) (f : SymbolicFunc Label) : SymbolicFunc Label :=
  match l with
  | [] => f
  | x :: xs => .next x (SymbolicFunc.prepend xs f)

@[simp]
theorem SymbolicFunc.erase_prepend (l : Line) (f : SymbolicFunc Label) (map : Label → Nat) :
    (SymbolicFunc.prepend l f).erase map = l +++ (f.erase map) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [SymbolicFunc.prepend, SymbolicFunc.erase, ih]
    rfl

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

/-! ### A decidable front end for `resolve_eq_erase`

`resolve_eq_erase` takes two membership-restricted agreement hypotheses.  A
program over a *finite* label type discharges them with `cases target <;> rfl`.
A program over a label type carrying an unbounded payload — a composite table
whose base arm is `base (slot : Nat)`, say — cannot: agreement holds exactly on
the slots the table actually defines, and `findLabel?` returns `none` elsewhere.

`callsOk` turns both hypotheses into one Boolean over the call targets that
actually occur.  `SymbolicFunc.calls` discards every instruction payload, so for
a runtime whose deployment parameters appear only inside PUSH immediates the
check is independent of those parameters and closes by `decide +kernel` even
with the parameter record still a free variable. -/

/-- Every call target occurring anywhere in a symbolic program, in order. -/
def SymbolicProg.allCalls (p : SymbolicProg Label) : List Label :=
  p.main.calls ++ p.aux.flatMap (fun entry => entry.2.calls)

/-- Decidable table agreement: every occurring call target is defined in the
table, at exactly the coordinate `map` assigns it. -/
def SymbolicProg.callsOk [DecidableEq Label] (p : SymbolicProg Label) (map : Label → Nat) : Bool :=
  p.allCalls.all (fun target => decide (p.findLabel? target = some (map target)))

theorem SymbolicProg.findLabel?_of_callsOk [DecidableEq Label]
    {p : SymbolicProg Label} {map : Label → Nat} (h : p.callsOk map = true)
    {target : Label} (ht : target ∈ p.allCalls) :
    p.findLabel? target = some (map target) :=
  of_decide_eq_true (List.all_eq_true.mp h target ht)

theorem SymbolicProg.mem_allCalls_main (p : SymbolicProg Label) {target : Label}
    (ht : target ∈ p.main.calls) : target ∈ p.allCalls :=
  List.mem_append_left _ ht

theorem SymbolicProg.mem_allCalls_aux (p : SymbolicProg Label) {lbl : Label}
    {body : SymbolicFunc Label} (hb : (lbl, body) ∈ p.aux) {target : Label}
    (ht : target ∈ body.calls) : target ∈ p.allCalls :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨(lbl, body), hb, ht⟩)

/-- Resolution equals whole-program erasure whenever definition validity holds
and the decidable agreement check passes.  This is the reusable composite-table
front end: both membership-restricted hypotheses of `resolve_eq_erase` come out
of one `Bool`. -/
theorem resolve_eq_erase_of_callsOk [DecidableEq Label]
    (p : SymbolicProg Label) (map : Label → Nat)
    (h_valid : p.validateDefinitions = .ok ())
    (h_calls : p.callsOk map = true) :
    resolve p = .ok (p.erase map) :=
  resolve_eq_erase p map h_valid
    (fun _ ht => SymbolicProg.findLabel?_of_callsOk h_calls (p.mem_allCalls_main ht))
    (fun _ _ hb _ ht => SymbolicProg.findLabel?_of_callsOk h_calls (p.mem_allCalls_aux hb ht))
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

/-! ## Generic symbolic dispatch

`Blanc.linearDispatchWith` (`Blanc/LinearDispatch.lean`) is the one positional
owner of the structured linear selector chain.  Its symbolic twin is authored
once here, for every label type, with the erasure lemma that carries a symbolic
dispatcher back to that owner.  A runtime migrating to symbolic labels therefore
does not re-derive the chain shape, and the two cannot drift.
-/

/-- Symbolic linear selector dispatch: the exact shape of
`Blanc.linearDispatchWith`, with a named fallback label. -/
def symbolicLinearDispatchWith (fallback : Label) :
    List (B256 × SymbolicFunc Label) → SymbolicFunc Label
  | [] => .call fallback
  | [(word, body)] =>
      .next (Ninst.pushB256 word) (.next Ninst.eq (.branch (.call fallback) body))
  | (word, body) :: rest =>
      .next (Ninst.dup 0) (.next (Ninst.pushB256 word) (.next Ninst.eq
        (.branch (symbolicLinearDispatchWith fallback rest) (.next Ninst.pop body))))

/-- Erasing a symbolic linear dispatcher yields the positional dispatcher over
the erased bodies, with the fallback label at its assigned coordinate. -/
@[simp] theorem erase_symbolicLinearDispatchWith (map : Label → Nat) (fallback : Label)
    (entries : List (B256 × SymbolicFunc Label)) :
    (symbolicLinearDispatchWith fallback entries).erase map =
      linearDispatchWith (map fallback)
        (entries.map (fun (word, body) => (word, body.erase map))) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
    cases tail with
    | nil => rfl
    | cons second rest =>
      simp only [symbolicLinearDispatchWith, linearDispatchWith, SymbolicFunc.erase,
        List.map_cons, ih]

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

/-- Checked linking reports `compileFailed` exactly when label resolution
succeeds and the resolved program still fails the compiler's own decision. -/
theorem checkLink_eq_error_compileFailed [DecidableEq Label]
    {sp : SymbolicProg Label} {resolved : Prog}
    (h_res : resolve sp = .ok resolved)
    (h_comp : Prog.compiles resolved = false) :
    checkLink sp = .error (.compileFailed resolved) := by
  unfold checkLink
  split
  · rename_i e h
    rw [h_res] at h
    exact absurd h (by simp)
  · rename_i r h
    rw [h_res] at h
    obtain rfl : r = resolved := (Except.ok.inj h).symm
    simp [h_comp]

/-- Checked linking succeeds exactly when resolution succeeds and the resolved
program passes the compiler's own decision. -/
theorem checkLink_isOk [DecidableEq Label]
    {sp : SymbolicProg Label} {resolved : Prog}
    (h_res : resolve sp = .ok resolved)
    (h_comp : Prog.compiles resolved = true) :
    (checkLink sp).isOk = true := by
  unfold checkLink
  split
  · rename_i e h
    rw [h_res] at h
    exact absurd h (by simp)
  · rename_i r h
    rw [h_res] at h
    obtain rfl : r = resolved := (Except.ok.inj h).symm
    simp only [h_comp, dif_pos]
    rfl

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

/-! ### Compiler target boundary: 65535 accepted, 65536 rejected

`Func.compile` emits every jump destination in a `PUSH2` immediate, so it admits
a table call or a forward branch only while `loc < 2 ^ 16`.  These controls pin
that exact boundary against a synthetic table and program counter, for both the
table-call target and the branch continuation target.  A destination of 65535 is
accepted; 65536 is rejected, and the byte producer returns `none`. -/

/-- Two-entry synthetic table whose callable entry sits at an exact location. -/
def boundaryTable (loc : Nat) : List (Nat × Func) :=
  [(0, .last .stop), (loc, .last .stop)]

/-- Positive boundary: a call whose target sits at exactly 65535 compiles. -/
theorem call_target_65535_compiles :
    Func.compiles (boundaryTable 65535) 0 (.call 1) = true := by
  decide +kernel

/-- Negative boundary: one byte past the 16-bit window the same call is
rejected by the decision procedure. -/
theorem call_target_65536_rejects :
    Func.compiles (boundaryTable 65536) 0 (.call 1) = false := by
  decide +kernel

/-- Negative boundary, exact rejection: the byte producer returns `none`. -/
theorem call_target_65536_compile_eq_none :
    Func.compile (boundaryTable 65536) 0 (.call 1) = none := by
  decide +kernel

/-- Positive boundary: a forward branch landing at exactly 65535 compiles. -/
theorem branch_target_65535_compiles :
    Func.compiles (boundaryTable 0) 65530
        (.branch (.last .stop) (.last .stop)) = true := by
  decide +kernel

/-- Negative boundary: the same branch one program counter later lands at
65536 and is rejected. -/
theorem branch_target_65536_rejects :
    Func.compiles (boundaryTable 0) 65531
        (.branch (.last .stop) (.last .stop)) = false := by
  decide +kernel

/-- Negative boundary, exact rejection: the byte producer returns `none`. -/
theorem branch_target_65536_compile_eq_none :
    Func.compile (boundaryTable 0) 65531
        (.branch (.last .stop) (.last .stop)) = none := by
  decide +kernel

/-! ### `LinkError.compileFailed` at the same boundary

`checkLink` can only report `compileFailed` for a program that resolves cleanly
and still exceeds the 16-bit jump window, which needs a witness just over 64 KiB
of code: in a resolved program every call index is in range and every location is
determined by `compsize`, so no smaller program can fail the compiler.  The
witness is therefore built from an uninterpreted pad, and every lemma below is general
in the pad length so that nothing is ever evaluated 65 000 times; only the final
arithmetic sees the literal. -/

/-- `padFunc n f` prefixes `n` one-byte `POP` instructions to `f`. -/
def padFunc : Nat → Func → Func
  | 0, f => f
  | n + 1, f => .next (.reg .pop) (padFunc n f)

/-- Symbolic counterpart of `padFunc`. -/
def padSymbolic : Nat → SymbolicFunc TestLabel → SymbolicFunc TestLabel
  | 0, f => f
  | n + 1, f => .next (.reg .pop) (padSymbolic n f)

theorem erase_padSymbolic (map : TestLabel → Nat) (n : Nat)
    (f : SymbolicFunc TestLabel) :
    (padSymbolic n f).erase map = padFunc n (f.erase map) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [padSymbolic, padFunc, SymbolicFunc.erase, ih]

theorem calls_padSymbolic (n : Nat) (f : SymbolicFunc TestLabel) :
    (padSymbolic n f).calls = f.calls := by
  induction n with
  | zero => rfl
  | succ n ih => simp [padSymbolic, SymbolicFunc.calls, ih]

theorem compsize_padFunc (n : Nat) (f : Func) :
    compsize (padFunc n f) = n + compsize f := by
  induction n with
  | zero => simp [padFunc]
  | succ n ih =>
      simp only [padFunc, compsize, ih, Ninst.toBytes, List.length_cons,
        List.length_nil]
      omega

theorem isSome_compile_next_pop (l : List (Nat × Func)) (m : Nat) (p : Func) :
    (Func.compile l m (.next (.reg .pop) p)).isSome
      = (Func.compile l (m + 1) p).isSome := by
  cases h : Func.compile l (m + 1) p with
  | none => simp [Func.compile, Ninst.size, h]
  | some bs => simp [Func.compile, Ninst.size, h]

theorem isSome_compile_padFunc (l : List (Nat × Func)) (f : Func) :
    ∀ (n m : Nat), (Func.compile l m (padFunc n f)).isSome
      = (Func.compile l (m + n) f).isSome := by
  intro n
  induction n with
  | zero => intro m; simp [padFunc]
  | succ n ih =>
      intro m
      rw [show padFunc (n + 1) f = .next (.reg .pop) (padFunc n f) from rfl,
        isSome_compile_next_pop, ih (m + 1),
        show m + 1 + n = m + (n + 1) from by omega]

/-- Label map for the boundary witness: its single auxiliary entry is index 1. -/
def boundaryMap : TestLabel → Nat
  | .loop => 1
  | _ => 0

/-- Otherwise-valid program: `padding` one-byte instructions, then a call to the
single auxiliary entry.  `compsize main = padding + 4`, so that entry's table
location, and hence the call's jump destination, is `padding + 5`. -/
def boundaryCallProg (padding : Nat) : SymbolicProg TestLabel where
  root := .root
  main := padSymbolic padding (.call .loop)
  aux := [(.loop, .last .stop)]

/-- Resolved form of the boundary witness. -/
def boundaryResolved (padding : Nat) : Prog :=
  ⟨padFunc padding (.call 1), [.last .stop]⟩

/-- Table of the resolved witness: the auxiliary entry sits at `padding + 5`. -/
def boundaryProgTable (padding : Nat) : List (Nat × Func) :=
  [(0, padFunc padding (.call 1)), (padding + 5, .last .stop)]

/-- Label resolution itself never fails on the witness, which is what leaves the
compiler's target check as the only thing under test. -/
theorem boundaryCallProg_resolve (padding : Nat) :
    resolve (boundaryCallProg padding) = .ok (boundaryResolved padding) := by
  have h := resolve_eq_erase (boundaryCallProg padding) boundaryMap rfl ?_ ?_
  · rw [h]
    simp [SymbolicProg.erase, boundaryResolved, boundaryCallProg,
      erase_padSymbolic, SymbolicFunc.erase, boundaryMap]
  · intro target htarget
    rw [show (boundaryCallProg padding).main
        = padSymbolic padding (.call .loop) from rfl,
      calls_padSymbolic] at htarget
    simp only [SymbolicFunc.calls, List.mem_singleton] at htarget
    subst htarget
    rfl
  · intro lbl body hmem target htarget
    simp only [boundaryCallProg, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨-, rfl⟩ := hmem
    simp only [SymbolicFunc.calls, List.not_mem_nil] at htarget

theorem boundaryResolved_compile_eq_table (padding : Nat) :
    Prog.compile (boundaryResolved padding)
      = Table.compile (boundaryProgTable padding) (boundaryProgTable padding) := by
  have ht : table 0 ((boundaryResolved padding).main
      :: (boundaryResolved padding).aux) = boundaryProgTable padding := by
    show (0, padFunc padding (Func.call 1))
        :: table (0 + compsize (padFunc padding (Func.call 1)) + 1)
            [(.last .stop : Func)]
      = boundaryProgTable padding
    rw [compsize_padFunc,
      show 0 + (padding + compsize (Func.call 1)) + 1 = padding + 5 from by
        simp only [compsize]; omega]
    rfl
  simp only [Prog.compile, ht]

/-- The witness compiles exactly while its one jump destination is in range. -/
theorem isSome_boundaryResolved_compile (padding : Nat) :
    (Prog.compile (boundaryResolved padding)).isSome
      = decide (padding + 5 < 2 ^ 16) := by
  have hkey : (Func.compile (boundaryProgTable padding) 1
      (padFunc padding (.call 1))).isSome = decide (padding + 5 < 2 ^ 16) := by
    rw [isSome_compile_padFunc]
    by_cases hlt : padding + 5 < 65536
    · simp [boundaryProgTable, Func.compile, guard, hlt]
    · simp [boundaryProgTable, Func.compile, guard, hlt]
  have htail : Table.compile (boundaryProgTable padding)
        (boundaryProgTable padding)
      = (Func.compile (boundaryProgTable padding) 1
          (padFunc padding (.call 1))).bind
          (fun bs => some (Jinst.toUInt8 .jumpdest :: bs ++
            [Jinst.toUInt8 .jumpdest, Linst.stop.toUInt8])) := rfl
  rw [boundaryResolved_compile_eq_table, htail, ← hkey]
  cases Func.compile (boundaryProgTable padding) 1
      (padFunc padding (.call 1)) with
  | none => rfl
  | some bs => rfl

/-- Positive control: the witness whose call lands at exactly 65535 links. -/
theorem checkLink_ok_at_target_65535 :
    (checkLink (boundaryCallProg 65530)).isOk = true := by
  refine checkLink_isOk (boundaryCallProg_resolve 65530) ?_
  rw [← Prog.isSome_compile, isSome_boundaryResolved_compile]
  decide

/-- Negative control: the same witness one byte longer lands at 65536 and
checked linking rejects it with the exact `compileFailed` payload. -/
theorem checkLink_compileFailed_at_target_65536 :
    checkLink (boundaryCallProg 65531)
      = .error (.compileFailed (boundaryResolved 65531)) := by
  refine checkLink_eq_error_compileFailed (boundaryCallProg_resolve 65531) ?_
  rw [← Prog.isSome_compile, isSome_boundaryResolved_compile]
  decide

end Control

end Blanc
