import Blanc.Lift.FrameSkip

/-!
# In-frame shuffle skip: crossing silent stack-shuffling segments by one decision

A walk that inverts a cut run (`SFunc.RunCut`) one node at a time pays for every instruction it
crosses.  Long stretches of solc code (hashing an EIP-712 struct, ABI-encoding a call, checking a
call's result) never write the world and only shuffle, duplicate and drop the words they were
given.  This module crosses such a stretch with one kernel decision and one theorem.

**Domain.**  An abstract word (`SVal`) is an input word (`arg i`, the `i`-th word of the segment's
input stack), a literal (`lit w`, pushed by the segment), or unknown (`unk`, computed).  This is the
copy-only fragment of a term domain: a richer checker extends `SVal` with computed terms and keeps
every rule below.  `Carried X a Y` reads an abstract stack `a` against a concrete one `Y`, with the
inputs `X`.

**Checker.**  `shuffle fs es Fw tgt pB fuel pc a f` explores every path of the tree `f` from the
abstract stack `a` until the target tree `tgt`, recognised at the program counter `pB` (a hint
only: the check compares the trees).  Each instruction must be state-silent; its stack effect is
the lift's own transfer (`ninstTransfer`) run on index labels and read back (`shNinst`), so no
opcode effect is restated.  A `JUMPI` over a literal condition follows the decided arm; otherwise
both arms are explored and their results met (`shJoin`).  A `REVERT` or undefined byte is a path
with no successful run (`some none`): this is how branches whose other arm reverts are pruned.
Gotos are followed into entries of the list `Fw`, which must be disjoint from the run's cut list.
Calls, returns, halts and every other node are rejected.

**Theorem.**  `ric_shuffle`: if the check yields `π`, every cut run of `f` from `St b (X ++ R) M G`
(with `X.length` input words) reaches `tgt` from a state with `b`'s world state and the stack
`Y ++ R`, where `Carried X π Y`: output word `j` is input word `i` when `π[j] = arg i`, the literal
`w` when `π[j] = lit w`.  `R` is never read.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety

/-! ## The domain -/

/-- An abstract word: an input word, a literal, or unknown. -/
inductive SVal : Type
  | arg : Nat → SVal
  | lit : B256 → SVal
  | unk : SVal
deriving DecidableEq

/-- The concrete words an abstract word admits, given the segment's inputs `X`. -/
def SVal.Den (X : List B256) : SVal → B256 → Prop
  | .arg i, w => X[i]? = some w
  | .lit c, w => w = c
  | .unk, _ => True

/-- The concrete stack `Y` is described by `a` over the inputs `X`. -/
def Carried (X : List B256) (a : List SVal) (Y : List B256) : Prop :=
  List.Forall₂ (SVal.Den X) a Y

/-- The segment's input frame: `n` input words, in order. -/
def argFrame (n : Nat) : List SVal := (List.range n).map SVal.arg

/-- Read one transferred index label back into the abstract stack. -/
def SVal.readBack (a : List SVal) : Option B256 → Option SVal
  | none => some .unk
  | some i => a[i.toNat]?

/-- The abstract effect of one state-silent non-jump instruction. -/
def shNinst (n : Ninst) (a : List SVal) : Option (List SVal) :=
  match n with
  | .push bs _ => some (.lit (Bytes.toB256 bs) :: a)
  | n =>
    if n.stateSilent && decide (a.length ≤ 1024) then
      (ninstTransfer n (indexPattern a.length)).bind fun out => out.mapM (SVal.readBack a)
    else none

/-- `x` is at least as precise as `y`. -/
def SVal.Le (x y : SVal) : Prop := y = .unk ∨ y = x

/-- The meet of two abstract words: equal words stay, different ones become unknown. -/
def SVal.meet (x y : SVal) : SVal := if x = y then x else .unk

/-- A checked result: `none` rejects, `some none` says no successful run reaches the target,
`some (some π)` describes every stack the target is reached with. -/
abbrev ShRes : Type := Option (Option (List SVal))

/-- The result of two explored arms. -/
def shJoin : ShRes → ShRes → ShRes
  | some none, r => r
  | some (some p), some none => some (some p)
  | some (some p), some (some q) =>
    if p.length = q.length then some (some (List.zipWith SVal.meet p q)) else none
  | _, _ => none

/-- A `JUMPI` over the condition `v`: a literal decides it. -/
def shBranch (v : SVal) (r0 r1 : ShRes) : ShRes :=
  match v with
  | .lit w => if w = 0 then r0 else r1
  | _ => shJoin r0 r1

/-- The program counter a destination word names, as a hint. -/
def SVal.pcHint : SVal → Nat
  | .lit w => w.toNat
  | _ => 0

/-- Structural equality of synthetic trees, as a function the kernel evaluates. -/
def SFunc.same : SFunc → SFunc → Bool
  | .branch f g, .branch f' g' => f.same f' && g.same g'
  | .branchTo f k, .branchTo f' k' => k == k' && f.same f'
  | .last l, .last l' => decide (l = l')
  | .next n f, .next n' f' => decide (n = n') && f.same f'
  | .dest f, .dest f' => f.same f'
  | .jump k, .jump k' => k == k'
  | .callNext k f, .callNext k' f' => k == k' && f.same f'
  | .ret, .ret => true
  | .pcAt p f, .pcAt p' f' => p == p' && f.same f'
  | .undefined, .undefined => true
  | _, _ => false

/-- **The shuffle checker** (see the module doc). -/
def shuffle (fs : List SFunc) (es : List Entry) (Fw : List Nat) (tgt : SFunc) (pB : Nat) :
    Nat → Nat → List SVal → SFunc → ShRes
  | 0, _, _, _ => none
  | fuel + 1, pc, a, f =>
    if pc = pB then (if f.same tgt then some (some a) else none) else
    match f with
    | .next n g =>
      (shNinst n a).bind fun a' => shuffle fs es Fw tgt pB fuel (pc + n.size) a' g
    | .dest g => shuffle fs es Fw tgt pB fuel (pc + 1) a g
    | .branch g h =>
      match a with
      | t :: v :: a =>
        shBranch v (shuffle fs es Fw tgt pB fuel (pc + 1) a g)
          (shuffle fs es Fw tgt pB fuel t.pcHint a h)
      | _ => none
    | .branchTo g k =>
      match a, fs[k]?, es[k]? with
      | _ :: v :: a, some h, some e =>
        if k ∈ Fw then
          shBranch v (shuffle fs es Fw tgt pB fuel (pc + 1) a g)
            (shuffle fs es Fw tgt pB fuel e.pc a h)
        else none
      | _, _, _ => none
    | .jump k =>
      match a, fs[k]?, es[k]? with
      | _ :: a, some h, some e => if k ∈ Fw then shuffle fs es Fw tgt pB fuel e.pc a h else none
      | _, _, _ => none
    | .last l => if l = .revert then some none else none
    | .undefined => some none
    | .callNext _ _ => none
    | .ret => none
    | .pcAt _ _ => none

/-! ## Domain facts -/

theorem SFunc.eq_of_same : ∀ {f g : SFunc}, f.same g = true → f = g := by
  intro f
  induction f with
  | branch f g ihf ihg =>
    intro h hs
    cases h <;> simp only [SFunc.same, Bool.false_eq_true, Bool.and_eq_true] at hs
    rw [ihf hs.1, ihg hs.2]
  | branchTo f k ih =>
    intro h hs
    cases h <;> simp only [SFunc.same, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at hs
    rw [hs.1, ih hs.2]
  | last l =>
    intro h hs
    cases h <;> simp only [SFunc.same, Bool.false_eq_true, decide_eq_true_eq] at hs
    rw [hs]
  | next n f ih =>
    intro h hs
    cases h <;> simp only [SFunc.same, Bool.false_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hs
    rw [hs.1, ih hs.2]
  | dest f ih =>
    intro h hs
    cases h <;> simp only [SFunc.same, Bool.false_eq_true] at hs
    rw [ih hs]
  | jump k =>
    intro h hs
    cases h <;> simp only [SFunc.same, Bool.false_eq_true, beq_iff_eq] at hs
    rw [hs]
  | callNext k f ih =>
    intro h hs
    cases h <;> simp only [SFunc.same, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at hs
    rw [hs.1, ih hs.2]
  | ret =>
    intro h hs
    cases h <;> simp only [SFunc.same, Bool.false_eq_true] at hs
    rfl
  | pcAt p f ih =>
    intro h hs
    cases h <;> simp only [SFunc.same, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at hs
    rw [hs.1, ih hs.2]
  | undefined =>
    intro h hs
    cases h <;> simp only [SFunc.same, Bool.false_eq_true] at hs
    rfl

theorem carried_argFrame (X : List B256) : Carried X (argFrame X.length) X := by
  unfold Carried argFrame
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp only [List.length_map, List.length_range], ?_⟩
  intro i h1 h2
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range, SVal.Den,
    List.getElem?_eq_getElem h2]

theorem SVal.le_refl (x : SVal) : SVal.Le x x := .inr rfl

theorem SVal.Le.den {X : List B256} {x y : SVal} {w : B256} (hle : SVal.Le x y)
    (h : SVal.Den X x w) : SVal.Den X y w := by
  rcases hle with rfl | rfl
  · trivial
  · exact h

theorem SVal.le_meet_left (x y : SVal) : SVal.Le x (SVal.meet x y) := by
  unfold SVal.meet
  split
  · exact .inr rfl
  · exact .inl rfl

theorem SVal.le_meet_right (x y : SVal) : SVal.Le y (SVal.meet x y) := by
  unfold SVal.meet
  split
  · rename_i h; exact .inr h
  · exact .inl rfl

theorem le_zipWith_meet_left : ∀ {p q : List SVal}, p.length = q.length →
    List.Forall₂ SVal.Le p (List.zipWith SVal.meet p q)
  | [], [], _ => .nil
  | x :: p, y :: q, h => .cons (SVal.le_meet_left x y)
      (le_zipWith_meet_left (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using h))

theorem le_zipWith_meet_right : ∀ {p q : List SVal}, p.length = q.length →
    List.Forall₂ SVal.Le q (List.zipWith SVal.meet p q)
  | [], [], _ => .nil
  | x :: p, y :: q, h => .cons (SVal.le_meet_right x y)
      (le_zipWith_meet_right (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using h))

theorem Carried.mono {X : List B256} {p q : List SVal} {Y : List B256}
    (hle : List.Forall₂ SVal.Le p q) (h : Carried X p Y) : Carried X q Y := by
  induction hle generalizing Y with
  | nil => exact h
  | cons hxy _ ih =>
    cases h with
    | cons hx hrest => exact .cons (hxy.den hx) (ih hrest)

theorem Carried.cons_inv {X : List B256} {v : SVal} {π : List SVal} {Y : List B256}
    (h : Carried X (v :: π) Y) : ∃ y Y', Y = y :: Y' ∧ SVal.Den X v y ∧ Carried X π Y' := by
  cases h with
  | cons hv hrest => exact ⟨_, _, rfl, hv, hrest⟩

theorem Carried.nil_inv {X Y : List B256} (h : Carried X [] Y) : Y = [] := by
  cases h
  rfl

/-- `o` is at least as precise as `o'` (no successful run is the most precise). -/
def ShLe : Option (List SVal) → Option (List SVal) → Prop
  | none, _ => True
  | some p, some q => List.Forall₂ SVal.Le p q
  | some _, none => False

theorem ShLe.refl : ∀ o : Option (List SVal), ShLe o o
  | none => trivial
  | some _ => List.forall₂_same.mpr fun x _ => SVal.le_refl x

theorem shJoin_le {r0 r1 : ShRes} {o : Option (List SVal)} (h : shJoin r0 r1 = some o) :
    ∃ o0 o1, r0 = some o0 ∧ r1 = some o1 ∧ ShLe o0 o ∧ ShLe o1 o := by
  match r0, r1, h with
  | some none, some o1, h =>
    simp only [shJoin, Option.some.injEq] at h
    subst h
    exact ⟨none, o1, rfl, rfl, trivial, ShLe.refl o1⟩
  | some (some p), some none, h =>
    simp only [shJoin, Option.some.injEq] at h
    subst h
    exact ⟨some p, none, rfl, rfl, ShLe.refl _, trivial⟩
  | some (some p), some (some q), h =>
    by_cases hl : p.length = q.length
    · simp only [shJoin, hl, ite_true, Option.some.injEq] at h
      subst h
      exact ⟨some p, some q, rfl, rfl, le_zipWith_meet_left hl, le_zipWith_meet_right hl⟩
    · simp only [shJoin, hl, ite_false, reduceCtorEq] at h
  | some none, none, h => simp only [shJoin, reduceCtorEq] at h
  | some (some _), none, h => simp only [shJoin, reduceCtorEq] at h
  | none, _, h => simp only [shJoin, reduceCtorEq] at h

theorem shBranch_zero {X : List B256} {v : SVal} {r0 r1 : ShRes} {o : Option (List SVal)}
    (h : shBranch v r0 r1 = some o) (hv : SVal.Den X v 0) :
    ∃ o0, r0 = some o0 ∧ ShLe o0 o := by
  cases v with
  | lit w =>
    simp only [SVal.Den] at hv
    subst hv
    simp only [shBranch, ite_true] at h
    exact ⟨o, h, ShLe.refl o⟩
  | arg i =>
    obtain ⟨o0, _, h0, _, hl, _⟩ := shJoin_le h
    exact ⟨o0, h0, hl⟩
  | unk =>
    obtain ⟨o0, _, h0, _, hl, _⟩ := shJoin_le h
    exact ⟨o0, h0, hl⟩

theorem shBranch_succ {X : List B256} {v : SVal} {r0 r1 : ShRes} {o : Option (List SVal)}
    {w : B256} (h : shBranch v r0 r1 = some o) (hv : SVal.Den X v w) (hw : w ≠ 0) :
    ∃ o1, r1 = some o1 ∧ ShLe o1 o := by
  cases v with
  | lit c =>
    simp only [SVal.Den] at hv
    subst hv
    simp only [shBranch, hw, ite_false] at h
    exact ⟨o, h, ShLe.refl o⟩
  | arg i =>
    obtain ⟨_, o1, _, h1, _, hl⟩ := shJoin_le h
    exact ⟨o1, h1, hl⟩
  | unk =>
    obtain ⟨_, o1, _, h1, _, hl⟩ := shJoin_le h
    exact ⟨o1, h1, hl⟩

/-! ## One instruction -/

theorem forall₂_getElem? {α β : Type} {Rel : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β} {i : Nat} {x : α}, List.Forall₂ Rel l1 l2 → l1[i]? = some x →
      ∃ y, l2[i]? = some y ∧ Rel x y
  | _, _, _, _, .nil, h => by simp only [List.getElem?_nil, reduceCtorEq] at h
  | _, _, 0, _, .cons hr _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h ⊢
    subst h
    exact ⟨_, rfl, hr⟩
  | _, _, i + 1, _, .cons _ hrest, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact forall₂_getElem? hrest h

theorem indexPattern_map_get {Y : List B256} (hlen : Y.length ≤ 1024) :
    (indexPattern Y.length).map (fun o => o.bind fun i => Y[i.toNat]?) = Y.map some := by
  apply List.ext_getElem
  · simp only [indexPattern, List.length_map, List.length_range]
  · intro i h1 h2
    have hi : i < Y.length := by
      simpa only [indexPattern, List.length_map, List.length_range] using h1
    simp only [indexPattern, List.getElem_map, List.getElem_range, Option.bind_some,
      B256.toNat_toB256_of_lt (by omega : i < 2 ^ 256), List.getElem?_eq_getElem hi]

theorem readBack_carried {X Y : List B256} {a : List SVal} (hY : Carried X a Y) :
    ∀ {out : List (Option B256)} {a' : List SVal} {s : List B256},
      out.mapM (SVal.readBack a) = some a' →
      Matches (out.map fun o => o.bind fun i => Y[i.toNat]?) s → Carried X a' s
  | [], a', s, h, hm => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    cases s with
    | nil => exact .nil
    | cons _ _ => exact hm.elim
  | o :: out, a', s, h, hm => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨v, hv, vs, hvs, rfl⟩ := h
    cases s with
    | nil => exact hm.elim
    | cons w s =>
      obtain ⟨hw, hrest⟩ := hm
      refine .cons ?_ (readBack_carried hY hvs hrest)
      cases o with
      | none =>
        simp only [SVal.readBack, Option.some.injEq] at hv
        subst hv
        trivial
      | some i =>
        simp only [SVal.readBack] at hv
        obtain ⟨y, hy, hden⟩ := forall₂_getElem? hY hv
        simp only [Option.bind_some, hy] at hw
        rw [hw.eq_of_some]
        exact hden

/-- A state-silent instruction leaves the world state alone. -/
theorem ninst_state_of_stateSilent {sevm : Sevm} {d d' : Devm} {n : Ninst}
    (hn : n.stateSilent = true) (run : Ninst.Run sevm d n d') : d'.state = d.state := by
  have stop : Linst.Run sevm d' .stop (.ok d') := rfl
  have h := SFunc.Run.state_of_silent (fs := []) (S := []) rfl
    (f := .next n (.last .stop)) (by simp only [SFunc.silent, hn, Bool.true_and]; rfl) rfl
    (.next run (.last stop))
  simpa only [Outcome.devm] using h

theorem shNinst_nonpush {n : Ninst} {a : List SVal}
    (hn : ∀ (bs : Bytes) (fits : bs.length ≤ 32), n ≠ .push bs fits) :
    shNinst n a =
      if n.stateSilent && decide (a.length ≤ 1024) then
        (ninstTransfer n (indexPattern a.length)).bind fun out => out.mapM (SVal.readBack a)
      else none := by
  cases n with
  | push bs fits => exact (hn bs fits rfl).elim
  | reg r => rfl
  | exec x => rfl
  | dupn i => rfl
  | swapn i => rfl
  | exchange i => rfl

/-- **One instruction**: a checked state-silent step keeps the world state, never reads below
the abstract stack, and leaves words described by the transferred abstract stack. -/
theorem shNinst_run_noStateGas {sevm : Sevm} {d d' : Devm} {n : Ninst} {a a' : List SVal}
    {X Y R : List B256} (hstateGas : sevm.benvStat.rules.stateGas = none) (h : shNinst n a = some a')
    (hst : d.stack = Y ++ R) (hY : Carried X a Y) (run : Ninst.Run sevm d n d') :
    d'.state = d.state ∧ ∃ Y', d'.stack = Y' ++ R ∧ Carried X a' Y' := by
  by_cases hpush : ∃ (bs : Bytes) (fits : bs.length ≤ 32), n = .push bs fits
  · obtain ⟨bs, fits, rfl⟩ := hpush
    simp only [shNinst, Option.some.injEq] at h
    subst h
    refine ⟨ninst_state_of_stateSilent rfl run, Bytes.toB256 bs :: Y, ?_, .cons rfl hY⟩
    rw [push_run_stack run, hst]
    rfl
  · have hn : ∀ (bs : Bytes) (fits : bs.length ≤ 32), n ≠ .push bs fits :=
      fun bs fits he => hpush ⟨bs, fits, he⟩
    rw [shNinst_nonpush hn] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hsil, hlen⟩ := hc
      obtain ⟨out, htr, hout⟩ := Option.bind_eq_some_iff.mp h
      have hYlen : Y.length = a.length := (List.Forall₂.length_eq hY).symm
      have hidx := indexPattern_map_get (Y := Y) (by omega)
      rw [hYlen] at hidx
      have ht := ninstTransfer_append (R.map some)
        (ninstTransfer_map (fun o => o.bind fun i => Y[i.toNat]?) rfl htr)
      rw [hidx] at ht
      have hin : Matches (Y.map some ++ R.map some) d.stack := by
        rw [hst]
        exact matches_append (matches_some_map Y) (matches_some_map R)
      obtain ⟨s1, s2, hs, h1, h2⟩ := matches_split (ninstTransfer_run_noStateGas hstateGas hin ht run)
      rw [matches_some_map_eq h2] at hs
      exact ⟨ninst_state_of_stateSilent hsil run, s1, hs, readBack_carried hY hout h1⟩
    · cases h

/-- Covered-fork compatibility projection of `shNinst_run_noStateGas`. -/
theorem shNinst_run {sevm : Sevm} {d d' : Devm} {n : Ninst} {a a' : List SVal}
    {X Y R : List B256} (fork : CoveredFork sevm.benvStat.fork) (h : shNinst n a = some a')
    (hst : d.stack = Y ++ R) (hY : Carried X a Y) (run : Ninst.Run sevm d n d') :
    d'.state = d.state ∧ ∃ Y', d'.stack = Y' ++ R ∧ Carried X a' Y' := by
  exact shNinst_run_noStateGas fork.rules_stateGas_none h hst hY run

/-! ## The skip theorem -/

/-- What a checked result promises for a cut run from `d0`: none can succeed (`none`), or every
one reaches `tgt` from a state with `d0`'s world state and a stack `Y ++ R` described by `π`. -/
def ShReach (P : Sevm → Devm → Ninst → Devm → Prop) (fs : List SFunc) (sevm : Sevm)
    (C : List Nat) (X R : List B256) (d0 : Devm) (tgt : SFunc) (r : Seg) :
    Option (List SVal) → Prop
  | none => False
  | some π => ∃ d, d.state = d0.state ∧ ∃ Y, d.stack = Y ++ R ∧ Carried X π Y ∧
      SFunc.RunCutP P fs sevm C d tgt r

section Sound

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {es : List Entry}
  {Fw C : List Nat} {tgt : SFunc} {pB : Nat} {sevm : Sevm} {X R : List B256} {r : Seg}

theorem ShReach.mono {d0 : Devm} {o o' : Option (List SVal)}
    (h : ShReach P fs sevm C X R d0 tgt r o) (hle : ShLe o o') :
    ShReach P fs sevm C X R d0 tgt r o' := by
  match o, o', h, hle with
  | some _, some _, ⟨d, hs, Y, hst, hY, run⟩, hle => exact ⟨d, hs, Y, hst, hY.mono hle, run⟩

theorem ShReach.state {d0 d1 : Devm} {o : Option (List SVal)}
    (h : ShReach P fs sevm C X R d1 tgt r o) (hs : d1.state = d0.state) :
    ShReach P fs sevm C X R d0 tgt r o := by
  match o, h with
  | some _, ⟨d, hd, rest⟩ => exact ⟨d, hd.trans hs, rest⟩

/-- **Soundness of the shuffle checker**, for every cut run under any instruction relation that
implies Jaune's steps. -/
theorem shuffle_sound_noStateGas (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (hstateGas : sevm.benvStat.rules.stateGas = none) (hFw : ∀ k ∈ Fw, k ∉ C) :
    ∀ (fuel pc : Nat) (a : List SVal) (f : SFunc) (o : Option (List SVal)) (d : Devm)
      (Y : List B256), shuffle fs es Fw tgt pB fuel pc a f = some o →
      SFunc.RunCutP P fs sevm C d f r → d.stack = Y ++ R → Carried X a Y →
      ShReach P fs sevm C X R d tgt r o := by
  intro fuel
  induction fuel with
  | zero => intro pc a f o d Y h; simp only [shuffle, reduceCtorEq] at h
  | succ fuel ih =>
    intro pc a f o d Y h run hst hY
    simp only [shuffle] at h
    split at h
    · split at h
      · rename_i hsame
        simp only [Option.some.injEq] at h
        subst h
        rw [SFunc.eq_of_same hsame] at run
        exact ⟨d, rfl, Y, hst, hY, run⟩
      · cases h
    · cases f with
      | next n g =>
        simp only at h
        obtain ⟨a', hn, h'⟩ := Option.bind_eq_some_iff.mp h
        cases run with
        | next hrun rest =>
          obtain ⟨hs, Y', hst', hY'⟩ := shNinst_run_noStateGas hstateGas hn hst hY (hP hrun)
          exact (ih _ _ _ _ _ _ h' rest hst' hY').state hs
      | dest g =>
        simp only at h
        cases run with
        | dest burn rest =>
          exact (ih _ _ _ _ _ _ h rest (by rw [← burn.stack, hst]) hY).state burn.state.symm
      | branch g g' =>
        rcases a with _ | ⟨t, _ | ⟨v, a⟩⟩
        · simp only [reduceCtorEq] at h
        · simp only [reduceCtorEq] at h
        · simp only at h
          rcases hY with _ | ⟨_, hY1⟩
          rcases hY1 with _ | ⟨hv, hY'⟩
          rename_i y0 Y0 y1 Y'
          cases run with
          | zero dd pop rest =>
            have hp := popBurn_two_stack pop
            rw [hst] at hp
            simp only [List.cons_append, List.cons.injEq] at hp
            obtain ⟨_, rfl, hp⟩ := hp
            obtain ⟨o0, h0, hle⟩ := shBranch_zero h hv
            exact ((ih _ _ _ _ _ _ h0 rest hp.symm hY').mono hle).state pop.state.symm
          | succ dd w hw pop rest =>
            have hp := popBurn_two_stack pop
            rw [hst] at hp
            simp only [List.cons_append, List.cons.injEq] at hp
            obtain ⟨_, rfl, hp⟩ := hp
            obtain ⟨o1, h1, hle⟩ := shBranch_succ h hv hw
            exact ((ih _ _ _ _ _ _ h1 rest hp.symm hY').mono hle).state pop.state.symm
      | branchTo g k =>
        rcases a with _ | ⟨t, _ | ⟨v, a⟩⟩
        · simp only [reduceCtorEq] at h
        · simp only [reduceCtorEq] at h
        · simp only at h
          rcases hY with _ | ⟨_, hY1⟩
          rcases hY1 with _ | ⟨hv, hY'⟩
          rename_i y0 Y0 y1 Y'
          cases hk : fs[k]? with
          | none => simp only [hk, reduceCtorEq] at h
          | some g' =>
            cases he : es[k]? with
            | none => simp only [hk, he, reduceCtorEq] at h
            | some e =>
              simp only [hk, he] at h
              split at h
              · rename_i hkFw
                cases run with
                | toZero dd pop rest =>
                  have hp := popBurn_two_stack pop
                  rw [hst] at hp
                  simp only [List.cons_append, List.cons.injEq] at hp
                  obtain ⟨_, rfl, hp⟩ := hp
                  obtain ⟨o0, h0, hle⟩ := shBranch_zero h hv
                  exact ((ih _ _ _ _ _ _ h0 rest hp.symm hY').mono hle).state pop.state.symm
                | toSuccCut _ _ _ hkC _ => exact (hFw k hkFw hkC).elim
                | toSucc dd w hw _ hk' pop rest =>
                  rw [hk] at hk'
                  cases hk'
                  have hp := popBurn_two_stack pop
                  rw [hst] at hp
                  simp only [List.cons_append, List.cons.injEq] at hp
                  obtain ⟨_, rfl, hp⟩ := hp
                  obtain ⟨o1, h1, hle⟩ := shBranch_succ h hv hw
                  exact ((ih _ _ _ _ _ _ h1 rest hp.symm hY').mono hle).state pop.state.symm
              · cases h
      | jump k =>
        rcases a with _ | ⟨t, a⟩
        · simp only [reduceCtorEq] at h
        · simp only at h
          rcases hY with _ | ⟨_, hY'⟩
          rename_i y0 Y'
          cases hk : fs[k]? with
          | none => simp only [hk, reduceCtorEq] at h
          | some g' =>
            cases he : es[k]? with
            | none => simp only [hk, he, reduceCtorEq] at h
            | some e =>
              simp only [hk, he] at h
              split at h
              · rename_i hkFw
                cases run with
                | jumpCut _ hkC _ => exact (hFw k hkFw hkC).elim
                | jump dd _ hk' pop rest =>
                  rw [hk] at hk'
                  cases hk'
                  have hp := popBurn_one_stack pop
                  rw [hst] at hp
                  simp only [List.cons_append, List.cons.injEq] at hp
                  exact (ih _ _ _ _ _ _ h rest hp.2.symm hY').state pop.state.symm
              · cases h
      | last l =>
        simp only at h
        split at h
        · rename_i hl
          subst hl
          simp only [Option.some.injEq] at h
          subst h
          cases run with
          | last hl => exact Linst.not_run_revert_ok hl
        · cases h
      | undefined => cases run
      | callNext _ _ => simp only [reduceCtorEq] at h
      | ret => simp only [reduceCtorEq] at h
      | pcAt _ _ => simp only [reduceCtorEq] at h

/-- Covered-fork compatibility projection of `shuffle_sound_noStateGas`. -/
theorem shuffle_sound (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (fork : CoveredFork sevm.benvStat.fork) (hFw : ∀ k ∈ Fw, k ∉ C) :
    ∀ (fuel pc : Nat) (a : List SVal) (f : SFunc) (o : Option (List SVal)) (d : Devm)
      (Y : List B256), shuffle fs es Fw tgt pB fuel pc a f = some o →
      SFunc.RunCutP P fs sevm C d f r → d.stack = Y ++ R → Carried X a Y →
      ShReach P fs sevm C X R d tgt r o := by
  exact shuffle_sound_noStateGas hP fork.rules_stateGas_none hFw

end Sound

/-- **The shuffle skip.**  A checked segment from `f` to `tgt` over `n` input words: every cut
run of `f` from `St b (X ++ R) M G` with `X.length = n` reaches `tgt` from a state with `b`'s
world state and the stack `Y ++ R`, where `Y` is described by `π` over the inputs `X`.  Gotos
the check follows (`Fw`) must not be cut.  The run's instruction relation `P` (any relation
implying Jaune's steps) is kept in the continuation. -/
theorem ric_shuffle_noStateGas {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {fs : List SFunc} {es : List Entry}
    {Fw C : List Nat} {tgt f : SFunc} {pB pA fuel n : Nat} {π : List SVal} {sevm : Sevm} {r : Seg}
    (hstateGas : sevm.benvStat.rules.stateGas = none) (hFw : ∀ k ∈ Fw, k ∉ C)
    (hchk : shuffle fs es Fw tgt pB fuel pA (argFrame n) f = some (some π))
    {X R : List B256} (hX : X.length = n) {b : Devm} {M : Mem} {G : Nat}
    (run : SFunc.RunCutP P fs sevm C (St b (X ++ R) M G) f r) :
    ∃ b' Y M' G', b'.state = b.state ∧ Carried X π Y ∧
      SFunc.RunCutP P fs sevm C (St b' (Y ++ R) M' G') tgt r := by
  subst hX
  obtain ⟨d, hs, Y, hst, hY, run'⟩ :=
    shuffle_sound_noStateGas hP hstateGas hFw _ _ _ _ _ _ _ hchk run rfl (carried_argFrame X)
  refine ⟨d, Y, d.memory, d.gasLeft, hs, hY, ?_⟩
  rw [← St.self hst rfl]
  exact run'

/-- Covered-fork compatibility projection of `ric_shuffle_noStateGas`. -/
theorem ric_shuffle {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {fs : List SFunc} {es : List Entry}
    {Fw C : List Nat} {tgt f : SFunc} {pB pA fuel n : Nat} {π : List SVal} {sevm : Sevm} {r : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (hFw : ∀ k ∈ Fw, k ∉ C)
    (hchk : shuffle fs es Fw tgt pB fuel pA (argFrame n) f = some (some π))
    {X R : List B256} (hX : X.length = n) {b : Devm} {M : Mem} {G : Nat}
    (run : SFunc.RunCutP P fs sevm C (St b (X ++ R) M G) f r) :
    ∃ b' Y M' G', b'.state = b.state ∧ Carried X π Y ∧
      SFunc.RunCutP P fs sevm C (St b' (Y ++ R) M' G') tgt r := by
  exact ric_shuffle_noStateGas hP fork.rules_stateGas_none hFw hchk hX run

set_option hygiene false in
/-- Read a `Carried X π Y` hypothesis `hY` over explicit `X` and `π` back into the stack of
the run `h`: every output word becomes its input word, its literal, or a fresh variable. -/
macro "carried_out " hY:ident h:ident : tactic => `(tactic|
  ((repeat obtain ⟨_, _, rfl, _, $hY:ident⟩ := Carried.cons_inv $hY)
   rw [Carried.nil_inv $hY] at $h:ident
   simp only [SVal.Den, List.getElem?_cons_zero, List.getElem?_cons_succ,
     Option.some.injEq] at *
   subst_vars))

end Blanc.Lift
