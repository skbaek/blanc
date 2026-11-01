-- CommonProofs/Base.lean : silent-structure, storage and code-read foundations shared by every proof layer.

import Blanc.Tactics
import Blanc.ExecutionSettlement
import Jaune.DevmProjections

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat
open Jaune.Ninst Ninst
open DispatchTree

/-- Read a single storage update as an equality branch at the observed key. -/
theorem Stor.get_set_ite (s : Stor) (key value probe : B256) :
    (s.set key value).get probe =
      if key = probe then value else s.get probe := by
  by_cases h : key = probe
  · subst probe
    simp only [Stor.get_set_self, ↓reduceIte]
  · simp only [Stor.get_set_ne _ h, h, ↓reduceIte]

-- Splitting a body's line at any point and prepending the pieces in order is
-- the same as prepending the whole line. Every module that decomposes a
-- compiled body into named line segments needs this, so it is stated once here
-- rather than re-derived beside each decomposition.
lemma prepend_append (left right : Line) (tail : Func) :
    (left ++ right) +++ tail = left +++ (right +++ tail) := by
  induction left with
  | nil => rfl
  | cons head left ih => simp only [cons_append, prepend, ih]

/-- Prepending the same instruction line preserves equality of compile shapes. -/
theorem Func.compileShape_prepend_congr (l : Line) {p q : Func}
    (h : p.compileShape = q.compileShape) :
    (l +++ p).compileShape = (l +++ q).compileShape := by
  induction l with
  | nil => exact h
  | cons i l ih => simp only [prepend, compileShape, ih]

-- The statement is unchanged by the `.revert` normalization (`Func.revert` in
-- `Blanc/CommonCore.lean`); only the walk is. `Func.revert` is now two `PUSH0`s
-- ahead of the failing `.revert`, so the run is peeled through two `next` binds
-- before the `Linst.Run` contradiction that has always closed this.
lemma not_run_revert {c e s r} : ¬ Func.Run c e s Func.revert r := by
  intro h
  cases h with
  | next _ h' =>
  cases h' with
  | next _ h'' =>
  cases h'' with
  | last h_run =>
    simp only [Linst.Run, Linst.run] at h_run
    rcases Except.bind_eq_ok h_run with ⟨v1, h1, h2⟩
    rcases Except.bind_eq_ok h2 with ⟨v2, h3, h4⟩
    rcases Except.bind_eq_ok h4 with ⟨v3, h5, h6⟩
    contradiction

lemma of_run_branch_revert {c e s r} {p : Func} (h : Func.Run c e s (.revert <?> p) r) :
    ∃ s', Devm.PopBurn [0] s s' ∧ Func.Run c e s' p r := by
  rcases of_run_branch h with ⟨s', h_pb, h_run⟩ | ⟨w, s', s'', h_ne, h_pb, h_b, h_run⟩
  · exact ⟨s', h_pb, h_run⟩
  · exfalso; exact not_run_revert h_run

lemma dispatchWith_inv {c k f}
    (σ : Sevm → Devm → Prop)
    (ρ : Sevm → Devm → Prop)
    ( h0 :
      ∀ {e s x w s' s''},
        σ e s →
        Line.Run e s [pushB256 x, eq] s' →
        Devm.PopBurn [w] s' s'' →
        σ e s'' )
    ( h1 :
      ∀ {e s x w s' s''},
        σ e s →
        Line.Run e s [dup 0, pushB256 x, gt] s' →
        Devm.PopBurn [w] s' s'' →
        σ e s'' )
    (h2 : c[k]? = some f)
    (h3 : ∀ {e s s' r}, σ e s → Devm.Burn s s' → Func.Run c e s' f r → ρ e r) :
    ∀ t : DispatchTree,
      (∀ {e s r}, ∀ wf ∈ t, σ e s → Func.Run c e s wf.2 r → ρ e r) →
    ∀ (e s r), σ e s → Func.Run c e s (dispatchWith k t) r → ρ e r := by
  intro t
  induction t with
  | fork t t' ih ih' =>
    intro htt' e s r hs
    have ht : ∀ {e s r}, ∀ wp ∈ t, σ e s → Func.Run c e s wp.2 r → ρ e r := by
      intro e s r wp h_in; apply htt' _ (Or.inl h_in)
    have ht' : ∀ {e s r}, ∀ wp ∈ t', σ e s → Func.Run c e s wp.2 r → ρ e r := by
      intro e s r wp h_in; apply htt' _ (Or.inr h_in)
    func_execute 3; intro h₂
    rcases of_run_branch h₂ with ⟨s₂, h_pop, h_run'⟩ | ⟨w, s₂, s₃, hw, h_pop, h_burn, h_run'⟩
    · apply ih' ht' e s₂ r (h1 hs h₁ h_pop) h_run'
    · apply ih ht e s₃ r (h1 hs h₁ (Devm.popBurn_of_popBurn_of_pop h_pop h_burn)) h_run'
  | leaf w p =>
    intro htt' e s r hs
    func_execute 2; intro h'
    rcases of_run_branch h' with ⟨s₂, h_pop, h_run'⟩ | ⟨w', s₂, s₃, hw', h_pop, h_burn, h_run'⟩
    · cases h_run' with
      | call h_eq_f h_burn' h_run_f =>
        have hh := Eq.trans h2.symm h_eq_f
        injection hh with heq
        subst heq
        apply h3 (h0 hs h₁ h_pop) h_burn' h_run_f
    · apply htt' ⟨w, p⟩ rfl (h0 hs h₁ (Devm.popBurn_of_popBurn_of_pop h_pop h_burn)) h_run'

/-- Transfer an invariant through the inline-revert dispatcher used by
contracts whose selector miss is a direct `Func.revert`, rather than an indexed
fallback call.  This is the exact analogue of `dispatchWith_inv`: comparison
lines preserve the carried entry predicate, a successful leaf reaches its
body, and the miss arm is impossible because `Func.revert` has no successful
run. -/
lemma dispatch_inv {c}
    (σ : Sevm → Devm → Prop)
    (ρ : Sevm → Devm → Prop)
    (h0 :
      ∀ {e s x w s' s''},
        σ e s →
        Line.Run e s [pushB256 x, eq] s' →
        Devm.PopBurn [w] s' s'' →
        σ e s'')
    (h1 :
      ∀ {e s x w s' s''},
        σ e s →
        Line.Run e s [dup 0, pushB256 x, gt] s' →
        Devm.PopBurn [w] s' s'' →
        σ e s'') :
    ∀ t : DispatchTree,
      (∀ {e s r}, ∀ wf ∈ t,
        σ e s → Func.Run c e s wf.2 r → ρ e r) →
      ∀ (e s r), σ e s → Func.Run c e s (dispatch t) r → ρ e r := by
  intro t
  induction t with
  | fork t t' ih ih' =>
      intro htt' e s r hs
      have ht : ∀ {e s r}, ∀ wp ∈ t,
          σ e s → Func.Run c e s wp.2 r → ρ e r := by
        intro e s r wp h_in
        exact htt' wp (Or.inl h_in)
      have ht' : ∀ {e s r}, ∀ wp ∈ t',
          σ e s → Func.Run c e s wp.2 r → ρ e r := by
        intro e s r wp h_in
        exact htt' wp (Or.inr h_in)
      func_execute 3
      intro h₂
      rcases of_run_branch h₂ with
        ⟨s₂, h_pop, h_run'⟩ |
          ⟨w, s₂, s₃, hw, h_pop, h_burn, h_run'⟩
      · exact ih' ht' e s₂ r (h1 hs h₁ h_pop) h_run'
      · exact ih ht e s₃ r
          (h1 hs h₁ (Devm.popBurn_of_popBurn_of_pop h_pop h_burn)) h_run'
  | leaf w p =>
      intro htt' e s r hs
      func_execute 2
      intro h'
      rcases of_run_branch h' with
        ⟨s₂, h_pop, h_run'⟩ |
          ⟨w', s₂, s₃, hw', h_pop, h_burn, h_run'⟩
      · exact absurd h_run' not_run_revert
      · exact htt' ⟨w, p⟩ rfl
          (h0 hs h₁ (Devm.popBurn_of_popBurn_of_pop h_pop h_burn)) h_run'

-- Tree membership implies list membership. `dispatchWith_inv` puts `wf ∈ t` in
-- hypothesis position, so a contract built with `ofSorted` needs to discharge
-- its per-leaf obligation over its own *list* rather than over the balanced
-- tree shape. Only the forward direction is needed.
--
-- The fuel bound is the lemma's content, not decoration: `build`'s two
-- degenerate rows (`| _, [] => leaf 0 .revert` and `| 0, (x :: _ :: _) =>
-- leaf x.fst x.snd`) both manufacture a leaf that need not be in the list.
-- `xs ≠ []` kills the first; `xs.length ≤ n + 1` kills the second, because at
-- fuel `0` the list then has length at most one and rows 1-2 fire instead.
-- The bound survives the split at `k = (xs.length + 1) / 2` in both branches,
-- which is what makes the induction go through.
theorem DispatchTree.mem_of_mem_build :
    ∀ {n : Nat} {xs : List (B256 × Func)} {wp : B256 × Func},
      xs ≠ [] → xs.length ≤ n + 1 → wp ∈ DispatchTree.build n xs → wp ∈ xs := by
  intro n
  induction n with
  | zero =>
    intro xs wp h_ne h_len h_mem
    rcases xs with _ | ⟨⟨w, p⟩, xs'⟩
    · exact absurd rfl h_ne
    · rcases xs' with _ | ⟨y, ys⟩
      · have h : wp = (w, p) := h_mem
        simp only [h, mem_cons, not_mem_nil, or_false]
      · simp only [List.length_cons] at h_len; omega
  | succ n ih =>
    intro xs wp h_ne h_len h_mem
    rcases xs with _ | ⟨⟨w, p⟩, xs'⟩
    · exact absurd rfl h_ne
    · rcases xs' with _ | ⟨y, ys⟩
      · have h : wp = (w, p) := h_mem
        simp only [h, mem_cons, not_mem_nil, or_false]
      · have h_len' : ys.length ≤ n := by
          simp only [List.length_cons] at h_len; omega
        have h_split :
            wp ∈ DispatchTree.build n
                   (((w, p) :: y :: ys).take ((((w, p) :: y :: ys).length + 1) / 2)) ∨
            wp ∈ DispatchTree.build n
                   (((w, p) :: y :: ys).drop ((((w, p) :: y :: ys).length + 1) / 2)) := h_mem
        have h_take_len :
            (((w, p) :: y :: ys).take ((((w, p) :: y :: ys).length + 1) / 2)).length ≤ n + 1 := by
          simp only [List.length_take, List.length_cons]; omega
        have h_drop_len :
            (((w, p) :: y :: ys).drop ((((w, p) :: y :: ys).length + 1) / 2)).length ≤ n + 1 := by
          simp only [List.length_drop, List.length_cons]; omega
        have h_take_ne :
            ((w, p) :: y :: ys).take ((((w, p) :: y :: ys).length + 1) / 2) ≠ [] := by
          intro hc
          have hcl := congrArg List.length hc
          simp only [List.length_take, List.length_cons, List.length_nil] at hcl
          omega
        have h_drop_ne :
            ((w, p) :: y :: ys).drop ((((w, p) :: y :: ys).length + 1) / 2) ≠ [] := by
          intro hc
          have hcl := congrArg List.length hc
          simp only [List.length_drop, List.length_cons, List.length_nil] at hcl
          omega
        rcases h_split with h | h
        · exact List.mem_of_mem_take (ih h_take_ne h_take_len h)
        · exact List.mem_of_mem_drop (ih h_drop_ne h_drop_len h)

-- `ofSorted` passes fuel `xs.length`, so `mem_of_mem_build`'s side condition is
-- the trivial `xs.length ≤ xs.length + 1`.
theorem DispatchTree.mem_of_mem_ofSorted {xs : List (B256 × Func)} {wp : B256 × Func}
    (h_ne : xs ≠ []) (h_mem : wp ∈ DispatchTree.ofSorted xs) : wp ∈ xs :=
  DispatchTree.mem_of_mem_build h_ne (Nat.le_succ _) h_mem

/-! ### The `sorted` order API

`DispatchTree.sorted` had no lemmas before this block: its only consumers were
the two contract-level `decide +kernel` facts, because `sound_of_dispatch`
deliberately dropped sortedness — it governs reachability, not safety.  The
reachability theorem (`reach_of_dispatchWith`, further down with the
run-level machinery it needs) is where sortedness finally becomes
load-bearing, and these are the order facts it consumes.  Everything here is
abstract in the signature words — nothing forces a `String.keccak`
(fixed decision 3 of the arc that added this; see `DispatchTree.build`'s note
on why the leaves must stay opaque). -/

/-- The tail of a sorted list is sorted. -/
lemma DispatchTree.sorted_of_sorted_cons {x : B256 × Func} {l : List (B256 × Func)}
    (h : DispatchTree.sorted (x :: l) = true) : DispatchTree.sorted l = true := by
  cases l with
  | nil => rfl
  | cons y l =>
    simp only [DispatchTree.sorted, Bool.and_eq_true] at h
    exact h.right

/-- In a sorted list, the head's signature is strictly below every later
entry's. -/
lemma DispatchTree.fst_lt_of_sorted_cons {x wp : B256 × Func} {l : List (B256 × Func)}
    (h : DispatchTree.sorted (x :: l) = true) (h_mem : wp ∈ l) : x.fst < wp.fst := by
  induction l generalizing x with
  | nil => cases h_mem
  | cons y l ih =>
    simp only [DispatchTree.sorted, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp h_mem with h_eq | h_mem'
    · rw [h_eq]; exact h.left
    · exact B256.lt_of_toNat_lt_toNat
        (Nat.lt_trans (B256.toNat_lt_toNat h.left)
          (B256.toNat_lt_toNat (ih h.right h_mem')))

/-- Head-minimality: in a sorted list the head's signature is a lower bound. -/
lemma DispatchTree.fst_le_of_sorted_mem {x wp : B256 × Func} {l : List (B256 × Func)}
    (h : DispatchTree.sorted (x :: l) = true) (h_mem : wp ∈ x :: l) :
    x.fst ≤ wp.fst := by
  rcases List.mem_cons.mp h_mem with h_eq | h_mem'
  · rw [h_eq]
  · exact B256.le_of_lt (DispatchTree.fst_lt_of_sorted_cons h h_mem')

/-- Sortedness restricts to a prefix. -/
lemma DispatchTree.sorted_append_left {l₁ l₂ : List (B256 × Func)}
    (h : DispatchTree.sorted (l₁ ++ l₂) = true) : DispatchTree.sorted l₁ = true := by
  induction l₁ with
  | nil => rfl
  | cons x l₁ ih =>
    cases l₁ with
    | nil => rfl
    | cons y l =>
      simp only [List.cons_append, DispatchTree.sorted, Bool.and_eq_true,
        decide_eq_true_eq] at h ⊢
      exact ⟨h.left, ih h.right⟩

/-- Sortedness restricts to a suffix. -/
lemma DispatchTree.sorted_append_right {l₁ l₂ : List (B256 × Func)}
    (h : DispatchTree.sorted (l₁ ++ l₂) = true) : DispatchTree.sorted l₂ = true := by
  induction l₁ with
  | nil => exact h
  | cons x l₁ ih =>
    exact ih (DispatchTree.sorted_of_sorted_cons
      (show DispatchTree.sorted (x :: (l₁ ++ l₂)) = true from h))

/-- The cross bound: in a sorted concatenation, every left signature is
strictly below every right signature.  `DispatchTree.build` splits by
`List.take`/`drop` and compares nothing, so this — through `take_append_drop` —
is the only link between list order and the shape `dispatchWith`'s binary
search runs on. -/
lemma DispatchTree.fst_lt_of_sorted_append {l₁ l₂ : List (B256 × Func)}
    {wp wq : B256 × Func} (h : DispatchTree.sorted (l₁ ++ l₂) = true)
    (h₁ : wp ∈ l₁) (h₂ : wq ∈ l₂) : wp.fst < wq.fst := by
  induction l₁ with
  | nil => cases h₁
  | cons x l₁ ih =>
    rcases List.mem_cons.mp h₁ with h_eq | h_mem
    · subst h_eq
      exact DispatchTree.fst_lt_of_sorted_cons
        (show DispatchTree.sorted (wp :: (l₁ ++ l₂)) = true from h)
        (List.mem_append_right _ h₂)
    · exact ih (DispatchTree.sorted_of_sorted_cons
        (show DispatchTree.sorted (x :: (l₁ ++ l₂)) = true from h)) h_mem

/-- `leftmostFsig` of a built tree is the head signature of its list: `build`
always sends the head into the left subtree, because the split point
`(length + 1) / 2` is at least one on a list of two or more.  This is what
lets a fork's comparison word be named from the *list* while the proof stays
abstract in it. -/
lemma DispatchTree.leftmostFsig_build :
    ∀ {n : Nat} {x : B256 × Func} {l : List (B256 × Func)},
      leftmostFsig (DispatchTree.build n (x :: l)) = x.fst := by
  intro n
  induction n with
  | zero =>
    intro x l
    rcases x with ⟨w, p⟩
    cases l with
    | nil => rfl
    | cons y l => rfl
  | succ n ih =>
    intro x l
    rcases x with ⟨w, p⟩
    cases l with
    | nil => rfl
    | cons y l =>
      show leftmostFsig
        (DispatchTree.build n
          (((w, p) :: y :: l).take ((((w, p) :: y :: l).length + 1) / 2))) = _
      obtain ⟨m, h_m⟩ : ∃ m, (((w, p) :: y :: l).length + 1) / 2 = m + 1 :=
        ⟨(l.length + 1) / 2, by simp only [List.length_cons]; omega⟩
      rw [h_m, List.take_succ_cons]
      exact ih

def ifOk {ε α} (π : α → Prop) : Except ε α → Prop
  | .error _ => True
  | .ok a => π a

def Prog.At (p : Prog) (ca : Adr)
    (pc : Nat) (sevm : Sevm) (devm : Devm) : Prop :=
  some (devm.getCode ca).toList = Prog.compile p ∧
  (sevm.currentTarget = ca → (some sevm.code.toList = Prog.compile p ∧ pc = 0))

def ForallSubExec (k : Nat) (ca : Adr) (p : Prog)
    (R : Sevm → Devm → Devm → Prop) : Prop :=
  ∀ pc sevm devm post,
    Exec pc sevm devm (.ok post) →
    sevm.depth < k →
    p.At ca pc sevm devm →
    R sevm devm post

def Exec.Wkn (ca : Adr) (p : Prog)
    (π : Exec.Pred)
    (pc sevm devm exn) (ex : Exec pc sevm devm exn) : Prop :=
  p.At ca pc sevm devm → π pc sevm devm exn ex

def ForallDeeper (k : Nat) (ε : Exec.Pred) : Prop :=
  ∀ pc sevm devm exn (ex : Exec pc sevm devm exn), sevm.depth < k → ε pc sevm devm exn ex

def ForallDeeperAt (k : Nat) (ca : Adr) (p : Prog) (ε : Exec.Pred) : Prop :=
  ForallDeeper k (fun pc sevm devm exn ex => p.At ca pc sevm devm → ε pc sevm devm exn ex)

/-! The solvency-facing world relation. -/

def Devm.WorldEq (d d' : Devm) : Prop :=
  d.state = d'.state ∧ d.transientStorage = d'.transientStorage

lemma Devm.worldEq_setMach (d : Devm) (mach : Mach) :
    Devm.WorldEq d (d.setMach mach) := by
  exact ⟨rfl, rfl⟩

lemma liftMachPure_worldEq (core : Mach → Mach) (d : Devm) :
    Devm.WorldEq d (liftMachPure core d) := by
  exact Devm.worldEq_setMach d _

lemma liftMachMetaPure_worldEq
    (core : Mach → Meta → Mach × Meta) (d : Devm) :
    Devm.WorldEq d (liftMachMetaPure core d) := by
  exact ⟨rfl, rfl⟩

lemma addAccessedAddress_worldEq (d : Devm) (a : Adr) :
    Devm.WorldEq d (addAccessedAddress d a) := by
  exact liftMachMetaPure_worldEq _ _

lemma addAccessedStorageKey_worldEq (d : Devm) (a : Adr) (k : B256) :
    Devm.WorldEq d (addAccessedStorageKey d a k) := by
  exact liftMachMetaPure_worldEq _ _

lemma liftMach_worldEq_of_ok {core : Mach → Footprint.Outcome Mach α}
    {d d' : Devm} {x : α} (h : liftMach core d = .ok (x, d')) :
    Devm.WorldEq d d' := by
  unfold liftMach Footprint.liftOutcome at h
  cases hc : core d.mach with
  | error err => simp only [hc, reduceCtorEq] at h
  | ok out =>
    simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    exact Devm.worldEq_setMach d out.2

lemma liftMach_worldEq_of_error {core : Mach → Footprint.Outcome Mach α}
    {d : Devm} {err : EvmError × Devm} (h : liftMach core d = .error err) :
    Devm.WorldEq d err.2 := by
  unfold liftMach Footprint.liftOutcome at h
  cases hc : core d.mach with
  | error out =>
    simp only [hc, Except.error.injEq] at h
    rcases h with ⟨_, rfl⟩
    exact Devm.worldEq_setMach d out.2
  | ok out => simp only [hc, reduceCtorEq] at h

lemma liftMach_error_of_ok {core : Mach → Footprint.Outcome Mach α}
    {d d' : Devm} {x : α} (h : liftMach core d = .ok (x, d')) :
    d'.error = d.error := by
  unfold liftMach Footprint.liftOutcome at h
  cases hc : core d.mach with
  | error err => simp only [hc, reduceCtorEq] at h
  | ok out =>
    simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    exact Devm.setMach_error d out.2

lemma liftMachExecution_worldEq_of_ok {core : Mach → Footprint.Outcome Mach Unit}
    {d d' : Devm} (h : liftMachExecution core d = .ok d') :
    Devm.WorldEq d d' := by
  unfold liftMachExecution Footprint.toExecution at h
  split at h
  · cases h
  · rename_i out heq
    cases h
    exact liftMach_worldEq_of_ok heq

lemma liftMachExecution_worldEq_of_error {core : Mach → Footprint.Outcome Mach Unit}
    {d : Devm} {err : EvmError × Devm} (h : liftMachExecution core d = .error err) :
    Devm.WorldEq d err.2 := by
  unfold liftMachExecution Footprint.toExecution at h
  split at h
  · rename_i e heq
    cases h
    exact liftMach_worldEq_of_error heq
  · cases h

lemma chargeGas_worldEq_of_ok {cost : Nat} {d d' : Devm}
    (h : chargeGas cost d = .ok d') : Devm.WorldEq d d' := by
  exact liftMachExecution_worldEq_of_ok (core := Mach.chargeGas cost) h

lemma chargeGas_worldEq_of_error {cost : Nat} {d : Devm} {err : EvmError × Devm}
    (h : chargeGas cost d = .error err) : Devm.WorldEq d err.2 := by
  exact liftMachExecution_worldEq_of_error (core := Mach.chargeGas cost) h

lemma chargeStateGas_worldEq_of_ok {amount : Nat} {d d' : Devm}
    (h : chargeStateGas amount d = .ok d') : Devm.WorldEq d d' := by
  exact liftMachExecution_worldEq_of_ok (core := Mach.chargeStateGas amount) h

lemma chargeStateGas_worldEq_of_error {amount : Nat} {d : Devm} {err : EvmError × Devm}
    (h : chargeStateGas amount d = .error err) : Devm.WorldEq d err.2 := by
  exact liftMachExecution_worldEq_of_error (core := Mach.chargeStateGas amount) h

lemma Devm.WorldEq.getCode {d d' : Devm} (h : Devm.WorldEq d d') (a : Adr) :
    d.getCode a = d'.getCode a := by
  unfold Devm.getCode Devm.getAcct
  rw [h.1]

lemma Devm.WorldEq.getBal {d d' : Devm} (h : Devm.WorldEq d d') (a : Adr) :
    d.getBal a = d'.getBal a := by
  unfold Devm.getBal Devm.getAcct
  rw [h.1]

lemma chargeGas_getCode {devm devm' : Devm} {cost : ℕ} {a : Adr}
    (h : chargeGas cost devm = Except.ok devm') :
    devm'.getCode a = devm.getCode a := by
  exact (chargeGas_worldEq_of_ok h).getCode a |>.symm

lemma Devm.pop_worldEq_of_ok {devm devm' : Devm} {x : B256}
    (h : devm.pop = .ok (x, devm')) : Devm.WorldEq devm devm' := by
  exact liftMach_worldEq_of_ok (core := Mach.pop) h

lemma Devm.pop_getCode {devm devm' : Devm} {val : B256} {a : Adr}
    (h : devm.pop = Except.ok (val, devm')) : devm'.getCode a = devm.getCode a := by
  exact (Devm.pop_worldEq_of_ok h).getCode a |>.symm

lemma Devm.popToNat_worldEq_of_ok {devm devm' : Devm} {n : Nat}
    (h : devm.popToNat = .ok (n, devm')) : Devm.WorldEq devm devm' := by
  exact liftMach_worldEq_of_ok (core := Mach.popToNat) h

lemma Devm.popToNat_getCode {devm devm' : Devm} {val : ℕ} {a : Adr}
    (h : devm.popToNat = Except.ok (val, devm')) :
    devm'.getCode a = devm.getCode a := by
  exact (Devm.popToNat_worldEq_of_ok h).getCode a |>.symm

lemma Devm.popToAdr_getCode {devm devm' : Devm} {val : Adr} {a : Adr}
    (h : devm.popToAdr = Except.ok (val, devm')) :
    devm'.getCode a = devm.getCode a := by
  exact (liftMach_worldEq_of_ok (core := Mach.popToAdr) h).getCode a |>.symm

lemma Devm.balReadAccount_getCode {rules : ForkRules} {adr : Adr}
    {devm : Devm} {a : Adr} :
    (Devm.balReadAccount rules adr devm).getCode a = devm.getCode a := rfl

lemma Devm.withholdCreateGas_getCode {devm : Devm} {a : Adr} :
    (devm.withholdCreateGas.2).getCode a = devm.getCode a := rfl

lemma Devm.drainStateGasReservoir_getCode {devm : Devm} {a : Adr} :
    (devm.drainStateGasReservoir.2).getCode a = devm.getCode a := rfl

lemma Devm.creditStateGasRefund_getCode {amount : Nat} {devm : Devm} {a : Adr} :
    (Devm.creditStateGasRefund amount devm).getCode a = devm.getCode a := rfl

lemma Devm.restoreChildGas_getCode {gas reservoir : Nat} {devm : Devm}
    {a : Adr} :
    (Devm.restoreChildGas gas reservoir devm).getCode a = devm.getCode a := rfl

lemma addCreatedAccount_getCode {benv : Benv} {adr a : Adr} : (addCreatedAccount benv adr).state.getCode a = benv.state.getCode a := by
  rfl

lemma Benv.setStor_getCode {benv : Benv} {adr a : Adr} {stor : Stor} : (benv.setStor adr stor).state.getCode a = benv.state.getCode a := by
  change ((benv.state.setStor adr stor).get a).code = (benv.state.get a).code
  by_cases h : adr = a
  · subst a
    unfold State.setStor
    split
    · rw [State.get_setPresent_self]
    · rw [State.get_set_self]
  · unfold State.setStor
    split
    · rw [State.get_setPresent_ne _ h]
    · rw [State.get_set_ne _ h]

lemma ExecuteCode.depth_eq
    {msg : Msg} {evm_ exn_ ex}
    (run : ExecuteCode msg (.some ⟨evm_, exn_⟩) ex) :
    evm_.sta.depth = msg.depth := by
  rw [(ExecuteCode.some_inv run).1]; rfl

lemma GenericCall.depth_lt
    {sevm devm msgCallGas value caller currentTarget target
      shouldTransferValue isStatic inputIndex inputSize
      outputIndex outputSize code disablePrecompiles}
    {evm_ exn_ ex}
    (run : GenericCall sevm devm msgCallGas value caller currentTarget target
      shouldTransferValue isStatic inputIndex inputSize
      outputIndex outputSize code disablePrecompiles (.some ⟨evm_, exn_⟩) ex) :
    evm_.sta.depth < sevm.depth := by
  obtain ⟨f, rsm, hs, henter, _⟩ := XStep.Run.some_inv run
  rw [Frame.enter_run_depth henter]
  exact genericCall.step_spawn_depth hs

lemma GenericCreate.depth_lt
    {sevm devm endowment newAddress memoryIndex memorySize}
    {evm_ exn_ ex}
    (run : GenericCreate sevm devm endowment
      newAddress memoryIndex memorySize (.some ⟨evm_, exn_⟩) ex) :
    evm_.sta.depth < sevm.depth := by
  obtain ⟨f, rsm, hs, henter, _⟩ := XStep.Run.some_inv run
  rw [Frame.enter_run_depth henter]
  exact genericCreate.step_spawn_depth hs

lemma Xinst.depth_lt
    {sevm devm x} {evm_ exn_ ex}
    (run : Xinst.Run sevm devm x (.some ⟨evm_, exn_⟩) ex) :
    evm_.sta.depth < sevm.depth := by
  obtain ⟨f, rsm, hs, henter, _⟩ := XStep.Run.some_inv run
  rw [Frame.enter_run_depth henter]
  exact Xinst.step_spawn_depth hs

/-- The actual entered child inherits the parent block environment. -/
lemma Xinst.Run.some_child_benvStat {sevm : Sevm} {pre : Devm} {x : Xinst}
    {evm' : Evm} {exn' : Execution} {out : Execution}
    (h : Xinst.Run sevm pre x (.some ⟨evm', exn'⟩) out) : evm'.sta.benvStat = sevm.benvStat := by
  obtain ⟨f, rsm, hs, henter, _⟩ := XStep.Run.some_inv h
  exact (Frame.enter_run_benvStat henter).trans (Xinst.step_spawn_benvStat hs)

lemma Xinst.Run.some_child_fork {sevm : Sevm} {pre : Devm} {x : Xinst}
    {evm' : Evm} {exn' : Execution} {out : Execution}
    (h : Xinst.Run sevm pre x (.some ⟨evm', exn'⟩) out)
    (hfork : CoveredFork sevm.benvStat.fork) :
    CoveredFork evm'.sta.benvStat.fork := by
  rw [Xinst.Run.some_child_benvStat h]
  exact hfork

/-- The actual entered child inherits the parent block environment. -/
lemma Evm.step_spawn_child_benvStat {pc : Nat} {sevm : Sevm} {pre : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat} {child : Evm}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc')
    (henter : f.enter = .run child) : child.sta.benvStat = sevm.benvStat := by
  obtain ⟨x, _, hspawn, _⟩ := Evm.step_spawn_inv hstep
  exact (Frame.enter_run_benvStat henter).trans (Xinst.step_spawn_benvStat hspawn)

lemma Evm.step_spawn_child_fork {pc : Nat} {sevm : Sevm} {pre : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat} {child : Evm}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc')
    (henter : f.enter = .run child)
    (hfork : CoveredFork sevm.benvStat.fork) :
    CoveredFork child.sta.benvStat.fork := by
  rw [Evm.step_spawn_child_benvStat hstep henter]
  exact hfork

lemma chargeGas_getCode_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') (a : Adr) : devm'.getCode a = devm.getCode a := by
  exact (chargeGas_worldEq_of_ok h).getCode a |>.symm

lemma chargeStateGas_getCode_eq {amount devm devm'} (h : chargeStateGas amount devm = .ok devm') (a : Adr) : devm'.getCode a = devm.getCode a := by
  exact (chargeStateGas_worldEq_of_ok h).getCode a |>.symm

lemma chargeStateGas_error_eq {amount devm devm'} (h : chargeStateGas amount devm = .ok devm') : devm'.error = devm.error := by
  unfold chargeStateGas liftMachExecution Footprint.toExecution at h
  split at h
  · cases h
  · rename_i heq
    cases h
    exact liftMach_error_of_ok heq

lemma Devm.push_getCode_eq {v devm devm'} (h : Devm.push v devm = .ok devm') (a : Adr) : devm'.getCode a = devm.getCode a := by
  exact (liftMachExecution_worldEq_of_ok (core := Mach.push v) h).getCode a |>.symm

lemma Devm.popToAdr_getCode_eq {devm devm' adr} (h : Devm.popToAdr devm = .ok ⟨adr, devm'⟩) (a : Adr) : devm'.getCode a = devm.getCode a := by
  exact (liftMach_worldEq_of_ok (core := Mach.popToAdr) h).getCode a |>.symm

lemma Except.bind_error {α β ε} (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = Except.error e := rfl
lemma Except.bind_ok {α β ε} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

lemma chargeGas_getBal_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') (a : Adr) : devm'.getBal a = devm.getBal a := by
  exact (chargeGas_worldEq_of_ok h).getBal a |>.symm

lemma Devm.push_getBal_eq {v devm devm'} (h : Devm.push v devm = .ok devm') (a : Adr) : devm'.getBal a = devm.getBal a := by
  exact (liftMachExecution_worldEq_of_ok (core := Mach.push v) h).getBal a |>.symm

lemma Devm.popToAdr_getBal_eq {devm devm' adr} (h : Devm.popToAdr devm = .ok ⟨adr, devm'⟩) (a : Adr) : devm'.getBal a = devm.getBal a := by
  exact (liftMach_worldEq_of_ok (core := Mach.popToAdr) h).getBal a |>.symm

lemma Devm.popToNat_getBal_eq {devm devm' n} (h : Devm.popToNat devm = .ok ⟨n, devm'⟩) (a : Adr) : devm'.getBal a = devm.getBal a := by
  exact (Devm.popToNat_worldEq_of_ok h).getBal a |>.symm

lemma Devm.withRefundCounter_getStor (devm : Devm) (refundCounter : Int) :
    Devm.getStor (devm.withRefundCounter refundCounter) = Devm.getStor devm := by
  rfl

lemma Devm.addLog_getStor (devm : Devm) (log : Log) :
    Devm.getStor (devm.addLog log) = Devm.getStor devm := by
  rfl

/-- A machine whose created-account set is `E` is itself with that set replaced by `E`. -/
theorem Devm.withCreatedAccounts_of_eq {d : Devm} {E : AdrSet} (h : d.createdAccounts = E) :
    d.withCreatedAccounts E = d := by
  rcases d with ⟨_, ⟨_, _, _, _, _, _, _, _, _, _, _⟩, _⟩
  simp only [Devm.createdAccounts] at h
  subst h
  rfl

lemma Devm.WorldEq.getStor {d d' : Devm} (h : Devm.WorldEq d d') (a : Adr) :
    Devm.getStor d a = Devm.getStor d' a := by
  unfold Devm.getStor Devm.getAcct
  rw [h.1]

lemma Devm.Burn.getStor {s s' : Devm} (h : Devm.Burn s s') (a : Adr) :
    Devm.getStor s' a = Devm.getStor s a := by
  simp only [Devm.getStor, Devm.getAcct]; rw [h.state]

lemma Devm.PopBurn.getStor {xs} {s s' : Devm} (h : Devm.PopBurn xs s s') (a : Adr) :
    Devm.getStor s' a = Devm.getStor s a := by
  simp only [Devm.getStor, Devm.getAcct]; rw [h.state]

instance : PopBurn.Inv Devm.getStor := ⟨by
  intros xs s s' h
  funext a
  exact (Devm.PopBurn.getStor h a).symm
⟩

instance : Burn.Inv Devm.getStor := ⟨by
  intros s s' h
  funext a
  exact (Devm.Burn.getStor h a).symm
⟩

lemma addAccessedStorageKey_getStor {devm : Devm} {adr : Adr} {key : B256} :
    Devm.getStor (addAccessedStorageKey devm adr key) = Devm.getStor devm := by
  funext a
  exact Devm.WorldEq.getStor (addAccessedStorageKey_worldEq devm adr key) a |>.symm

lemma setStorVal_getStor_self {devm : Devm} {adr : Adr} {key val : B256} :
    Devm.getStor (devm.setStorVal adr key val) adr = (Devm.getStor devm adr).set key val := by
  exact congrArg Acct.stor (State.setStorVal_get_self devm.state adr key val)

lemma setStorVal_getStor_ne {devm : Devm} {adr a : Adr}
    {key val : B256} (h : adr ≠ a) :
    Devm.getStor (devm.setStorVal adr key val) a = Devm.getStor devm a := by
  change ((devm.state.setStorVal adr key val).get a).stor = (devm.state.get a).stor
  rw [State.setStorVal_get_ne _ h]

lemma Devm.pop_getStor_eq {x devm devm'} (h : Devm.pop devm = .ok ⟨x, devm'⟩) :
    Devm.getStor devm = Devm.getStor devm' := by
  funext a
  exact Devm.WorldEq.getStor (Devm.pop_worldEq_of_ok h) a

lemma chargeGas_getStor_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') :
    Devm.getStor devm = Devm.getStor devm' := by
  funext a
  exact Devm.WorldEq.getStor (chargeGas_worldEq_of_ok h) a

lemma Devm.push_getStor_eq {v devm devm'} (h : Devm.push v devm = .ok devm') :
    Devm.getStor devm = Devm.getStor devm' := by
  funext a
  exact Devm.WorldEq.getStor
    (liftMachExecution_worldEq_of_ok (core := Mach.push v) h) a

lemma Devm.popToAdr_getStor_eq {devm devm' adr}
    (h : Devm.popToAdr devm = .ok ⟨adr, devm'⟩) :
    Devm.getStor devm = Devm.getStor devm' := by
  funext a
  exact Devm.WorldEq.getStor (liftMach_worldEq_of_ok (core := Mach.popToAdr) h) a

lemma Devm.popToNat_getStor_eq {devm devm' n}
    (h : Devm.popToNat devm = .ok ⟨n, devm'⟩) :
    Devm.getStor devm = Devm.getStor devm' := by
  funext a
  exact Devm.WorldEq.getStor (Devm.popToNat_worldEq_of_ok h) a

/-- A fixed-context syntactic certificate for preservation of an arbitrary
machine observation.  Tail calls are admitted only at indices selected by
`P`; `observe_eq_of_run_silentIn` checks that those lookups are closed. -/
def Func.SilentIn {Observation : Type}
    (observe : Devm → Observation) (P : Nat → Prop) : Func → Prop
  | .branch f g => Func.SilentIn observe P f ∧ Func.SilentIn observe P g
  | .last l => Linst.Inv observe observe l
  | .next i body => Ninst.Inv observe i ∧ Func.SilentIn observe P body
  | .call k => P k

/-- A fixed-`Sevm` variant of `Func.SilentIn`.  Its nonterminal leaves need
only preserve the supplied context, which permits a caller to use a
context-local semantic fact without manufacturing a universal `Ninst.Hinv`. -/
def Func.SilentAt {Observation : Type}
    (observe : Devm → Observation) (sevm : Sevm) (P : Nat → Prop) : Func → Prop
  | .branch f g => Func.SilentAt observe sevm P f ∧ Func.SilentAt observe sevm P g
  | .last l => Linst.Inv observe observe l
  | .next i body =>
      (∀ {s r : Devm}, Ninst.Run sevm s i r → observe s = observe r) ∧
        Func.SilentAt observe sevm P body
  | .call k => P k

/-- A universal silence certificate specializes to every fixed execution
context. -/
theorem Func.SilentIn.toSilentAt
    {Observation : Type} {observe : Devm → Observation}
    {P : Nat → Prop} {sevm : Sevm} {f : Func}
    (silent : Func.SilentIn observe P f) :
    Func.SilentAt observe sevm P f := by
  induction f with
  | branch f g ihf ihg =>
      exact ⟨ihf silent.1, ihg silent.2⟩
  | last l => exact silent
  | next i body ih =>
      exact ⟨fun run => silent.1 run, ih silent.2⟩
  | call k => exact silent

/-- Walk a `Func.SilentIn` goal structurally: `And.intro` at each `branch` and
`next`, the synthesised `Ninst`/`Linst` instance at each leaf.  A tail call
leaves the slot obligation `P k` open; supply `with tac` to close those, since
what makes a slot permitted is contract-specific.

Two consumers: the beacon deposit root's mutually recursive loop and the
WETH-backed PRORATA vault's live-quoting views. -/
syntax "silent_structure" (ppSpace "with" ppSpace tacticSeq)? : tactic
macro_rules
| `(tactic| silent_structure) =>
  `(tactic| repeat' first
      | exact Ninst.Hinv.inv
      | exact Linst.Hinv.inv
      | apply And.intro)
| `(tactic| silent_structure with $d:tacticSeq) =>
  `(tactic| repeat' first
      | exact Ninst.Hinv.inv
      | exact Linst.Hinv.inv
      | apply And.intro
      | ($d))

/-- A `SilentAt` body preserves its observation in its fixed execution
context.  Function calls retain that `Sevm`, so a closed set of recursive slots
needs no separate fork-transport premise. -/
theorem Func.observe_eq_of_run_silentAt
    {Observation : Type} {observe : Devm → Observation}
    {P : Nat → Prop} {fs : List Func}
    [PopBurn.Inv observe] [Burn.Inv observe]
    {sevm : Sevm}
    (hclosed : ∀ k g, P k → fs[k]? = some g →
      Func.SilentAt observe sevm P g)
    {s r : Devm} {f : Func}
    (run : Func.Run fs sevm s f r)
    (silent : Func.SilentAt observe sevm P f) :
    observe r = observe s := by
  induction run with
  | zero hpop _ ih =>
      exact (ih silent.1).trans (PopBurn.Inv.inv hpop).symm
  | succ _ hpop hburn _ ih =>
      exact (ih silent.2).trans
        ((Burn.Inv.inv hburn).symm.trans (PopBurn.Inv.inv hpop).symm)
  | last hlast =>
      exact (silent hlast).symm
  | next hinst _ ih =>
      exact (ih silent.2).trans (silent.1 hinst).symm
  | call hget hburn _ ih =>
      exact (ih (hclosed _ _ silent hget)).trans (Burn.Inv.inv hburn).symm

/-- A fixed-context syntactic certificate that a function cannot change
persistent storage.  Tail calls are admitted only at indices selected by
`P`; the companion theorem below checks that every such lookup resolves to a
body carrying the same certificate. -/
def Func.StorSilentIn (P : Nat → Prop) : Func → Prop
  | .branch f g => Func.StorSilentIn P f ∧ Func.StorSilentIn P g
  | .last l => Linst.Inv Devm.getStor Devm.getStor l
  | .next i body => Ninst.Inv Devm.getStor i ∧ Func.StorSilentIn P body
  | .call k => P k

/-- A `StorSilentIn` body preserves the complete persistent-storage map in a
fixed function context closed under its permitted tail calls.  Recursion is
on the successful `Func.Run` derivation, so self-recursive loop slots need no
fuel or termination premise. -/
theorem Func.getStor_eq_of_run_storSilentIn
    {P : Nat → Prop} {fs : List Func}
    (hclosed : ∀ k g, P k → fs[k]? = some g → Func.StorSilentIn P g)
    {sevm : Sevm} {s r : Devm} {f : Func}
    (run : Func.Run fs sevm s f r)
    (silent : Func.StorSilentIn P f) :
    Devm.getStor r = Devm.getStor s := by
  induction run with
  | zero hpop _ ih =>
      exact (ih silent.1).trans
        (funext (Devm.PopBurn.getStor hpop))
  | succ _ hpop hburn _ ih =>
      exact (ih silent.2).trans
        ((funext (Devm.Burn.getStor hburn)).trans
          (funext (Devm.PopBurn.getStor hpop)))
  | last hlast =>
      exact (silent hlast).symm
  | next hinst _ ih =>
      exact (ih silent.2).trans (silent.1 hinst).symm
  | call hget hburn _ ih =>
      exact (ih (hclosed _ _ silent hget)).trans
        (funext (Devm.Burn.getStor hburn))

lemma setCode_getCode {evm : Devm} {a b : Adr} {code : ByteArray} (h : a ≠ b) :
  (evm.setCode a code).getCode b = evm.getCode b := by
  show ((evm.state.setCode a code).get b).code = (evm.state.get b).code
  rw [State.setCode, State.setAccount_get_ne _ h]

namespace AdrSet

theorem not_mem_insert {a b : Adr} {s : AdrSet} (hne : a ≠ b) (hs : a ∉ s) :
    a ∉ s.insert b := by
  simp only [Std.HashSet.mem_insert, not_or]
  exact ⟨by simpa only [beq_iff_eq, ne_eq] using Ne.symm hne, hs⟩

end AdrSet

end Blanc
