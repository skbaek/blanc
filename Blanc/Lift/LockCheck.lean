import Blanc.Lift.Check

/-!
# The reentrancy-lock certificate checker

`LockCheck.lockCert` is one Boolean pass over a lift certificate
(`Blanc/Lift/Check.lean`) that establishes, for the code the certificate
describes, the per-code *dominance* obligation of a reentrancy lock
(`Blanc/LockExclusion.lean`, `LockSpec.Dominance`) together with its strong
form (only release sites write the lock slot inside a guarded mutating body).
`Blanc/Lift/LockCheckSound.lean` proves it sound along the all-outcome
certificate cursor (`Blanc/Lift/Cursor.lean`); this module holds only the
checker, so a contract's kernel decision imports nothing heavier.

**Walk.**  `lockNode` recurses over each entry tree exactly as `checkNode`
does (same pc and abstract-frame bookkeeping, `absNinst`), carrying an
abstract lock state `LSt`:

* `kv` names every word of the current function's frame by a *symbol*; words
  with the same symbol are equal.  Copies (`DUP`, `SWAP`, …) move symbols
  through the same index labels `ninstTransfer` computes for `absNinst`; each
  computed word gets a fresh symbol.
* `facts` constrain the symbols (`Fact`): numeric bounds, `≠ slot` (a
  `KECCAK256` digest, under the trace-local `HashAvoid`), order between two
  symbols, the meaning of a comparison result (`GT` against a constant,
  `ISZERO`, `XOR`), a value read from the lock slot (`lockv`), and an
  `EQ(lockv, locked)` result (`lockeq`).  A `JUMPI` refines the facts of the
  words below its condition on each branch; every fact is stable as the
  frame's same-frame chain grows, because it speaks of word values or of some
  earlier node of the chain.
* `passed`: some earlier node of the frame read the lock slot unequal to
  `locked` (set on the zero branch of a `lockeq` condition);
  `setNow`: the lock slot holds `locked` now (set by `SSTORE(slot, locked)`,
  kept by writes to other slots, cleared by any other write and by any call);
  `noMut`: no earlier node of the frame was a mutating body start.

**Requirements.**  Every body start needs `passed`; every mutating body start
needs `setNow`; an `SSTORE` whose key may equal the slot is accepted only if
the key is the constant slot, `passed` holds, and the pc is a release pc or
(before any mutating body start) a set pc; `SELFDESTRUCT` and every `PC` node (`SFunc.pcAt`, which no lock-checked
certificate uses) are rejected (the
certificate itself admits no `DELEGATECALL`, `CALLCODE`, `CREATE` or
`CREATE2`).

**Joins.**  Gotos, loop heads and callee entries carry an annotation `ann[k]`
(an `LSt` over position symbols) produced by the untrusted producer
(`scripts/lift/lift.py --lock-annotations`).  An incoming state must entail it
(`compat`): every annotated flag holds on the incoming path, the annotation's
symbol partition is respected, and every annotated fact follows from the
incoming facts.  A callee is entered with the incoming state restricted to its
frame; its continuation resumes with the caller's facts about the words below
the callee's frame, the caller's `passed`, and `setNow = noMut = false`.
-/

namespace Blanc.Lift.LockCheck

open Jaune AbstractStackSafety

/-- The lock a certificate is checked against: the slot, its held word, the
guarded body starts (`bodies`), the mutating ones (`mutBodies`), and the pcs
of the `SSTORE`s that set and release the lock. -/
structure Spec : Type where
  slot : B256
  locked : B256
  bodies : List Nat
  mutBodies : List Nat
  setPcs : List Nat
  releasePcs : List Nat

/-- A fact about symbols (`Blanc/Lift/LockCheckSound.lean`, `Fact.Holds`). -/
inductive Fact : Type
  /-- `lo ≤ s ≤ hi` as natural numbers. -/
  | bnd (s lo hi : Nat)
  /-- `s ≠ slot`. -/
  | nsl (s : Nat)
  /-- `s < t` as natural numbers. -/
  | lt (s t : Nat)
  /-- `s ≤ t` as natural numbers. -/
  | le (s t : Nat)
  /-- `r = GT(s, k)`: `r = 0` iff `s ≤ k`. -/
  | gt (r s k : Nat)
  /-- `r = ISZERO(s)`. -/
  | isz (r s : Nat)
  /-- `r = XOR(s, t)`: `r ≠ 0` implies `s ≠ t`. -/
  | xor (r s t : Nat)
  /-- `s` is the lock slot's word at some earlier node of the frame. -/
  | lockv (s : Nat)
  /-- `r = 0` implies the lock slot was not `locked` at some earlier node. -/
  | lockeq (r : Nat)
deriving DecidableEq, Repr

def Fact.syms : Fact → List Nat
  | .bnd s _ _ => [s]
  | .nsl s => [s]
  | .lt s t => [s, t]
  | .le s t => [s, t]
  | .gt r s _ => [r, s]
  | .isz r s => [r, s]
  | .xor r s t => [r, s, t]
  | .lockv s => [s]
  | .lockeq r => [r]

def Fact.rename (m : Nat → Nat) : Fact → Fact
  | .bnd s lo hi => .bnd (m s) lo hi
  | .nsl s => .nsl (m s)
  | .lt s t => .lt (m s) (m t)
  | .le s t => .le (m s) (m t)
  | .gt r s k => .gt (m r) (m s) k
  | .isz r s => .isz (m r) (m s)
  | .xor r s t => .xor (m r) (m s) (m t)
  | .lockv s => .lockv (m s)
  | .lockeq r => .lockeq (m r)

/-- An abstract lock state: symbols of the frame's words, facts, flags. -/
structure LSt : Type where
  kv : List Nat
  facts : List Fact
  passed : Bool
  setNow : Bool
  noMut : Bool
deriving DecidableEq, Repr

/-- The state a frame starts in (entry `0`'s required annotation). -/
def LSt.init : LSt := ⟨[], [], false, false, true⟩

def maxW : Nat := 2 ^ 256 - 1

/-- The bounds the `bnd` facts give a symbol. -/
def bndOf (fs : List Fact) (s : Nat) : Nat × Nat :=
  fs.foldl (fun p f => match f with
    | .bnd s' lo hi => if s' = s then (max p.1 lo, min p.2 hi) else p
    | _ => p) (0, maxW)

/-- `bndOf`, refined once through the order facts. -/
def bnd2 (fs : List Fact) (s : Nat) : Nat × Nat :=
  fs.foldl (fun p f => match f with
    | .lt a b =>
      if a = s then (p.1, min p.2 ((bndOf fs b).2 - 1))
      else if b = s then (max p.1 ((bndOf fs a).1 + 1), p.2) else p
    | .le a b =>
      if a = s then (p.1, min p.2 (bndOf fs b).2)
      else if b = s then (max p.1 (bndOf fs a).1, p.2) else p
    | _ => p) (bndOf fs s)

/-- A fact the facts `fs` entail. -/
def entails (fs : List Fact) : Fact → Bool
  | .bnd s lo hi => decide (lo ≤ (bnd2 fs s).1) && decide ((bnd2 fs s).2 ≤ hi)
  | .lt s t => fs.contains (.lt s t) || decide ((bnd2 fs s).2 < (bnd2 fs t).1)
  | .le s t => fs.contains (.le s t) || fs.contains (.lt s t) ||
      decide ((bnd2 fs s).2 ≤ (bnd2 fs t).1)
  | f => fs.contains f

def constOf (fs : List Fact) (s : Nat) : Option Nat :=
  if (bnd2 fs s).1 = (bnd2 fs s).2 then some (bnd2 fs s).1 else none

/-- The symbol `s` provably differs from the slot. -/
def excluded (sp : Spec) (fs : List Fact) (s : Nat) : Bool :=
  !(decide ((bnd2 fs s).1 ≤ sp.slot.toNat) && decide (sp.slot.toNat ≤ (bnd2 fs s).2)) ||
    fs.contains (.nsl s)

/-- A symbol no word or fact of the state uses. -/
def freshSym (kv : List Nat) (fs : List Fact) : Nat :=
  (kv ++ fs.flatMap Fact.syms).foldr max 0 + 1

/-- Keep the facts all of whose symbols name words of `kv`. -/
def live (kv : List Nat) (f : Fact) : Bool := f.syms.all (kv.contains ·)

def addFacts (fs : List Fact) (kv : List Nat) (x y r : Nat) : List Fact :=
  (if (bnd2 fs x).2 + (bnd2 fs y).2 ≤ maxW then
      [.bnd r ((bnd2 fs x).1 + (bnd2 fs y).1) ((bnd2 fs x).2 + (bnd2 fs y).2)]
    else []) ++
  (if constOf fs y = some 1 then (kv.filter (fun t => entails fs (.lt x t))).map (.le r)
    else []) ++
  (if constOf fs x = some 1 then (kv.filter (fun t => entails fs (.lt y t))).map (.le r)
    else [])

/-- The facts about the fresh result `r` of instruction `n` over input
symbols `kv`. -/
def opFacts (sp : Spec) (fs : List Fact) (kv : List Nat) (n : Ninst) (r : Nat) :
    List Fact :=
  match n, kv with
  | .reg .sload, x :: _ =>
    if constOf fs x = some sp.slot.toNat then [.lockv r] else []
  | .reg .eq, x :: y :: _ =>
    if (fs.contains (.lockv x) && decide (constOf fs y = some sp.locked.toNat)) ||
        (fs.contains (.lockv y) && decide (constOf fs x = some sp.locked.toNat)) then
      [.lockeq r]
    else []
  | .reg .keccak256, _ => [.nsl r]
  | .reg .add, x :: y :: _ => addFacts fs kv x y r
  | .reg .gt, x :: y :: _ =>
    match constOf fs y with
    | some k => [.gt r x k]
    | none => []
  | .reg .iszero, x :: _ => [.isz r x]
  | .reg .xor, x :: y :: _ => [.xor r x y]
  | _, _ => []

/-- The `SSTORE` rule and the `setNow` update of one instruction; `none`
rejects. -/
def effSetNow (sp : Spec) (pc : Nat) (n : Ninst) (σ : LSt) : Option Bool :=
  match n, σ.kv with
  | .reg .sstore, k :: v :: _ =>
    if excluded sp σ.facts k then some σ.setNow
    else if constOf σ.facts k = some sp.slot.toNat && σ.passed &&
        (sp.releasePcs.contains pc || (σ.noMut && sp.setPcs.contains pc)) then
      some (decide (constOf σ.facts v = some sp.locked.toNat))
    else none
  | .reg .sstore, _ => none
  | .exec _, _ => some false
  | _, _ => some σ.setNow

/-- One non-jump instruction on the lock state. -/
def lstep (sp : Spec) (pc : Nat) (n : Ninst) (σ : LSt) : Option LSt :=
  match n with
  | .push bs _ =>
    let r := freshSym σ.kv σ.facts
    let c := (Bytes.toB256 bs).toNat
    some ⟨r :: σ.kv, .bnd r c c :: σ.facts, σ.passed, σ.setNow, σ.noMut⟩
  | n => do
    let out ← ninstTransfer n (indexPattern σ.kv.length)
    guard (out.count none ≤ 1)
    let r := freshSym σ.kv σ.facts
    let kv' ← out.mapM (fun l => match l with
      | none => some r
      | some j => σ.kv[j.toNat]?)
    let setNow' ← effSetNow sp pc n σ
    some ⟨kv', (opFacts sp σ.facts σ.kv n r ++ σ.facts).filter (live kv'), σ.passed,
      setNow', σ.noMut⟩

def refineFacts (fs : List Fact) (c : Nat) (zero : Bool) : List Fact :=
  fs.flatMap fun f => match f with
    | .gt r s k =>
      if r = c then (if zero then [.bnd s 0 k] else [.bnd s (k + 1) maxW]) else []
    | .isz r s =>
      if r = c then (if zero then [.bnd s 1 maxW] else [.bnd s 0 0]) else []
    | .xor r s t =>
      if r = c && !zero then
        (if entails fs (.le s t) then [.lt s t] else []) ++
          (if entails fs (.le t s) then [.lt t s] else [])
      else []
    | _ => []

/-- A `JUMPI` whose condition has symbol `c`, on its zero (`zero = true`) or
nonzero branch, leaving the words `kv`. -/
def refine (σ : LSt) (c : Nat) (kv : List Nat) (zero : Bool) : LSt :=
  ⟨kv, (refineFacts σ.facts c zero ++ σ.facts).filter (live kv),
    σ.passed || (zero && σ.facts.contains (.lockeq c)), σ.setNow, σ.noMut⟩

/-- The state after popping a jump destination. -/
def popped (σ : LSt) (kv : List Nat) : LSt :=
  ⟨kv, σ.facts.filter (live kv), σ.passed, σ.setNow, σ.noMut⟩

/-- The symbol an annotation symbol `a` names in the incoming words. -/
def symMap (A kv : List Nat) (a : Nat) : Nat := ((A.zip kv).lookup a).getD 0

/-- The incoming state `σ` satisfies the annotation `A`. -/
def compat (σ A : LSt) : Bool :=
  σ.kv.length == A.kv.length &&
    (A.kv.zip σ.kv).all (fun p => symMap A.kv σ.kv p.1 == p.2) &&
    (!A.passed || σ.passed) && (!A.setNow || σ.setNow) && (!A.noMut || σ.noMut) &&
    A.facts.all (fun f => entails σ.facts (f.rename (symMap A.kv σ.kv)))

/-- The saved caller state below a callee's frame. -/
def saved (σ : LSt) (kv : List Nat) : LSt :=
  ⟨kv, σ.facts.filter (live kv), σ.passed, false, false⟩

/-- The state a continuation resumes in: `rets` fresh words above the saved
words. -/
def resume (σ : LSt) (rets : Nat) : LSt :=
  ⟨(List.range rets).map (freshSym σ.kv σ.facts + ·) ++ σ.kv, σ.facts, σ.passed, false, false⟩

/-- Enter a node at `pc`: record a mutating body start, then require the
body-start flags. -/
def visit (sp : Spec) (pc : Nat) (σ : LSt) : Option LSt :=
  let σ := if sp.mutBodies.contains pc then { σ with noMut := false } else σ
  if (!sp.bodies.contains pc || σ.passed) && (!sp.mutBodies.contains pc || σ.setNow) then
    some σ
  else none

def lockNode (sp : Spec) (es : List Entry) (ann : List LSt) :
    Nat → List AVal → LSt → SFunc → Bool
  | pc, a, σ, .next n f =>
    match visit sp pc σ with
    | none => false
    | some σ =>
      match absNinst n a, lstep sp pc n σ with
      | some a', some σ' => lockNode sp es ann (pc + n.size) a' σ' f
      | _, _ => false
  | pc, _, σ, .last l => (visit sp pc σ).isSome && l != .selfdestruct
  | pc, a, σ, .dest f =>
    match visit sp pc σ with
    | none => false
    | some σ => lockNode sp es ann (pc + 1) a σ f
  | pc, a, σ, .branch f g =>
    match visit sp pc σ with
    | none => false
    | some σ =>
      match a, σ.kv with
      | .const t :: _ :: a', _ :: c :: kv =>
        lockNode sp es ann (pc + 1) a' (refine σ c kv true) f &&
          lockNode sp es ann t.toNat a' (refine σ c kv false) g
      | _, _ => false
  | pc, a, σ, .branchTo f k =>
    match visit sp pc σ with
    | none => false
    | some σ =>
      match a, σ.kv, ann[k]? with
      | .const _ :: _ :: a', _ :: c :: kv, some A =>
        lockNode sp es ann (pc + 1) a' (refine σ c kv true) f &&
          compat (refine σ c kv false) A
      | _, _, _ => false
  | pc, _, σ, .jump k =>
    match visit sp pc σ with
    | none => false
    | some σ =>
      match σ.kv, ann[k]? with
      | _ :: kv, some A => compat (popped σ kv) A
      | _, _ => false
  | pc, a, σ, .callNext k f =>
    match visit sp pc σ with
    | none => false
    | some σ =>
      match a, σ.kv, es[k]?, ann[k]? with
      | .const _ :: a', _ :: kv, some e, some A =>
        compat (popped σ (kv.take e.frame.length)) A &&
          match e.frame.findIdx? (· == .ret) with
          | some i =>
            match a'[i]? with
            | some (.const r) =>
              lockNode sp es ann r.toNat
                (List.replicate e.rets .unk ++ a'.drop e.frame.length)
                (resume (saved σ (kv.drop e.frame.length)) e.rets) f
            | _ => false
          | none => true
      | _, _, _, _ => false
  | pc, _, σ, .ret => (visit sp pc σ).isSome
  | _, _, _, .pcAt _ _ => false
  | pc, _, σ, .undefined => (visit sp pc σ).isSome

/-- The lock check of a whole certificate: one annotation per entry, entry
`0` annotated with the initial state, and every entry tree accepted from its
annotation. -/
def lockCert (sp : Spec) (c : Cert) (ann : List LSt) : Bool :=
  ann.length == c.length && ann[0]? == some LSt.init &&
    (c.zip ann).all fun p => lockNode sp c.entries ann p.1.1.pc p.1.1.frame p.2 p.1.2

end Blanc.Lift.LockCheck
